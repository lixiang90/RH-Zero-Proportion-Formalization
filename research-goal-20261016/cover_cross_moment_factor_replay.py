"""Stdlib standalone replay of compact nonnegative affine-factor proofs.

Only canonical old-row metadata, active scalar slabs, affine factors and
one energy packet are stored. Rebuild old rows from GraphReplay, decompose
each nonnegative factor into base and signed RLT products, compare the
unmerged multiplier audit, then independently round and aggregate. No LP,
new point-kernel evaluations, general PSD test or Lean execution is used.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,gzip,hashlib,json,sys,time
import cover_cross_moment_old_rows_replay as support
HERE=Path(__file__).parent;ROOT=HERE.parent;exact=support.exact
SC,DS,D,Q=exact.SC,exact.DS,exact.D,exact.Q
sha=lambda b:hashlib.sha256(b).hexdigest()


def add(total,row,weight=1):
    for i,v in row['coeff'].items():
        total['coeff'][i]=total['coeff'].get(i,F(0))+weight*v
        if not total['coeff'][i]:total['coeff'].pop(i)
    total['bound']+=weight*row['bound']


def digest(row):
    data=[[[i,str(row['coeff'].get(i,F(0)))] for i in range(exact.V)],str(row['bound'])]
    return sha(json.dumps(data,separators=(',',':')).encode())


def old_row(meta,state,slabs,params,checker):
    terms=[r for r in params['a_upper'] if r[2]];ag=[0]*9;au=[0]*41;kind=meta[0]
    if kind=='DBM':
        _,z,sign=meta;assert isinstance(z,int) and 0<=z<45 and sign in [-1,1];i,j=support.graph.a.PAIRS[z]
        ag=[sign*Q if i<=r<j else 0 for r in range(9)];B=sign*2*DS*D*state[1 if sign==1 else 0][z]
    elif kind=='KKT':
        _,r,sign=meta;assert isinstance(r,int) and 0<=r<9 and sign in [-1,1]
        assert sign==-1 or state[0][r]>123*SC//128
        au=[sign*2*SC*DS*a if i<=r<j else 0 for i,j,a in terms];B=-sign*2*SC*DS*params['b_numerators'][r]
    else:
        assert kind in ['facet','slab'];t,sign=meta[1:3];assert isinstance(t,int) and 0<=t<41 and sign in [-1,1]
        i,j,a=terms[t];z=support.graph.a.INDEX[i,j];au[t]=sign*Q
        if kind=='slab':
            assert len(meta)==3 and t in slabs;P,m0,m1,err,_=checker.slab(state[0][z],state[1][z],slabs[t])
            ag=[-sign*2*SC*m1*D if i<=r<j else 0 for r in range(9)];B=D*(sign*(2*SC*m0-m1*P)+2*SC*err)
        else:
            assert len(meta)==5;S,C=map(exact.integer,meta[3:]);rect=checker.rectangles(state[0][z],state[1][z])
            wanted=max(SC*U-S*(l if S>=0 else u) for l,u,L,U in rect) if sign==1 else min(SC*L-S*(u if S>=0 else l) for l,u,L,U in rect)
            assert wanted==C;ag=[-sign*2*SC*S*D if i<=r<j else 0 for r in range(9)];B=sign*2*D*C
    return {'coeff':{i:F(v,Q) for i,v in enumerate(ag+au) if v},'bound':F(B,Q)}


def rlt(row,center,radius,s,sign):
    # Independently expand (R-B)*(1+sign*y_s) using x=m+r*y.
    assert sign in [-1,1] and 0<=s<9
    result={'coeff':dict(row['coeff']),'bound':row['bound']}
    ag=[row['coeff'].get(i,F(0)) for i in range(9)];K=sum(v*c for v,c in zip(ag,center))-row['bound']
    extra={'coeff':{s:sign*K/radius[s]},'bound':sign*K*center[s]/radius[s]}
    for r,v in enumerate(ag):
        index=50+[(i,j) for i in range(9) for j in range(i,9)].index((min(r,s),max(r,s)))
        extra['coeff'][index]=extra['coeff'].get(index,F(0))+sign*v*radius[r]
    for t in range(41):
        value=sign*row['coeff'].get(9+t,F(0))
        if value:extra['coeff'][95+41*s+t]=value
    add(result,extra);return result


def boxes(state,params,checker):
    lower=[F(x,SC) for x in state[0][:9]];upper=[F(x,SC) for x in state[1][:9]]
    mid=[(l+u)/2 for l,u in zip(lower,upper)];rad=[(u-l)/2 for l,u in zip(lower,upper)];assert min(rad)>0
    ub=[]
    for i,j,a in params['a_upper']:
        if not a:continue
        z=support.graph.a.INDEX[i,j];rect=checker.rectangles(state[0][z],state[1][z]);L=F(min(r[2] for r in rect),DS);U=F(max(r[3] for r in rect),DS)
        assert -7<=L<=U<=7;ub.append((L,U))
    bound=list(zip(lower,upper))+ub+[(F(0),F(1)) if i==j else (F(-1),F(1)) for i in range(9) for j in range(i,9)]
    bound += [(-max(abs(l),abs(u)),max(abs(l),abs(u))) for _ in range(9) for l,u in ub]
    assert len(bound)==464;return bound,mid,rad


def group_rows(case,state,params,checker):
    bound,mid,rad=boxes(state,params,checker);slabs={t:r for t,r in case['scalar_affine_data']};rows=[];old=[]
    assert len(slabs)==len(case['scalar_affine_data'])
    for factor in case['factors']:
        base=old_row(factor['old_meta'],state,slabs,params,checker);A=exact.integer(factor['A']);b=[0]*9
        for s,v in factor['b']:
            assert isinstance(s,int) and 0<=s<9 and not b[s];b[s]=exact.integer(v);assert b[s]
        assert A>0 and A>=sum(map(abs,b))
        group={'coeff':{},'bound':F(0)};add(group,base,A-sum(map(abs,b)))
        for s,v in enumerate(b):
            if v:add(group,rlt(base,mid,rad,s,1 if v>0 else -1),abs(v))
        old.append(base);rows.append(group)
    packet=case['energy_packet'];mu=exact.integer(case['energy_weight']);assert mu>0
    energy={'coeff':{i:F(v) for i,v in packet['row']},'bound':F(packet['bound'])}
    erow={'coeff':{},'bound':F(0)};add(erow,energy,mu);rows.append(erow)
    return rows,old,bound,mid,rad


def energy_algebra(case,state,params):
    p=case['energy_packet'];point=list(map(F,p['centre']));lo=[F(x,SC) for x in state[0][:9]];hi=[F(x,SC) for x in state[1][:9]]
    assert all(F(l,SC)<=sum(point[i:j])<=F(u,SC) for (i,j),l,u in zip(support.graph.a.PAIRS,*state))
    mid=[(l+u)/2 for l,u in zip(lo,hi)];rad=[(u-l)/2 for l,u in zip(lo,hi)]
    if 'F_lower' in p:
        F0=F(p['F_lower']);gm=list(map(F,p['gradient_midpoint']));err=list(map(F,p['gradient_error']))
    else:
        F0=F(p['F_interval'][0]);intervals=[list(map(F,r)) for r in p['gradient_interval']]
        gm=[(l+u)/2 for l,u in intervals];err=[(u-l)/2 for l,u in intervals]
    assert all(e>=0 for e in err)
    payment=sum(e*max(abs(l-c),abs(u-c)) for e,l,u,c in zip(err,lo,hi,point));assert payment==F(p['uniform_gradient_error_payment'])
    coeff={i:v for i,v in enumerate(gm) if v};constant=F0-payment-sum(v*c for v,c in zip(gm,point))
    terms=[r for r in params['a_upper'] if r[2]];assert len(p['whole_span_second_lower'])==len(terms)==41
    def insert(i,v):
        coeff[i]=coeff.get(i,F(0))+v
        if not coeff[i]:coeff.pop(i)
    for (i,j,a),L in zip(terms,p['whole_span_second_lower']):
        weight=F(a,D)*F(L)/2;delta=sum(mid[i:j])-sum(point[i:j]);constant+=weight*delta**2
        for r in range(i,j):
            insert(r,2*weight*delta);constant-=2*weight*delta*mid[r]
            for s in range(r,j):insert(exact.hindex(r,s),(1 if r==s else 2)*weight*rad[r]*rad[s])
    assert coeff=={i:F(v) for i,v in p['row']} and constant==F(p['quadratic_constant']) and F(p['bound'])==F(11,1250)-constant
    return {'finite_energy_polynomial_checked':True,'point_intervals_are_input':True,'whole_span_second_bounds_are_input':True}


def aggregate(rows,bound,N):
    coeff={};B=0;payment=F(0)
    for row in rows:
        a,rhs,error=support.independent_integer_row(row,bound,N);B+=rhs;payment+=error
        for i,v in a.items():coeff[i]=coeff.get(i,0)+v
    coeff={i:v for i,v in coeff.items() if v};minimum=sum(v*bound[i][0 if v>=0 else 1] for i,v in coeff.items())
    return coeff,B,minimum,minimum-B,payment


def friendly_composition(document,case,state,params):
    """Check coarse energy inputs' finite composition, not their analytic API."""
    path=ROOT/document['provenance']['friendly_packets_path'];raw=path.read_bytes()
    assert sha(raw)==document['provenance']['friendly_packets_sha256'];supplies=json.loads(raw)
    stored=next(r['energy0'] for r in supplies['rows'] if r['path']==case['path']);assert stored==case['energy_packet'];p=stored
    point=list(map(F,p['centre']));terms=[r for r in params['a_upper'] if r[2]]
    f0=sum(F(b,D)*x for b,x in zip(params['b_numerators'],point));gm=[F(b,D) for b in params['b_numerators']];ge=[F(0)]*9
    assert len(p['point_indices'])==len(p['grid_ranges'])==41
    active_raw=(HERE/'cover-curvature-actual-active.json').read_bytes();assert sha(active_raw)==supplies['inputs_sha256']['existing_curvature_grid']
    existing={r['k']:F(r['q2'][1],10**15) for r in json.loads(active_raw)['grid_rows'] if 'q2' in r}
    new={r['k']:F(r['lower']) for r in supplies['new_q2_rows']};grid_bounds={**existing,**new}
    for t,((i,j,a),index) in enumerate(zip(terms,p['point_indices'])):
        r=supplies['point_rows'][index];assert F(r['p'])==sum(point[i:j]);f0+=F(a,D)*F(r['value_lower'])
        for s in range(i,j):gm[s]+=F(a,D)*F(r['slope']);ge[s]+=F(a,D)*F(r['slope_error'])
        z=support.graph.a.INDEX[i,j];first=state[0][z]//512;last=(max(state[0][z]+1,state[1][z])+511)//512-1
        assert p['grid_ranges'][t]==[first,last] and F(p['whole_span_second_lower'][t])<=min(grid_bounds[k] for k in range(first,last+1))
    assert f0==F(p['F_lower']) and gm==list(map(F,p['gradient_midpoint'])) and ge==list(map(F,p['gradient_error']))
    return {'coarse_point_and_grid_composition_checked':True,'point_rows':41,
      'new_point_and_grid_analytic_soundness_is_input':True,'friendly_packets_sha256':sha(raw)}


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--folder',type=Path,default=HERE/'cover-cross-moment-factor-evidence');args=ap.parse_args();start=time.monotonic();folder=args.folder
    packed=(folder/'proof.json.gz').read_bytes();doc=json.loads(gzip.decompress(packed));m=json.loads((folder/'manifest.json').read_bytes())
    assert sha(packed)==m['proof_gzip_sha256'];compacked=(folder/'comparison.json.gz').read_bytes();compare=json.loads(gzip.decompress(compacked))
    assert sha(compacked)==m['comparison_gzip_sha256'] and compare['proof_gzip_sha256']==sha(packed)
    params_raw=(ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes();table_raw=(HERE/'cover_newjet.json').read_bytes()
    assert sha(params_raw)==doc['provenance']['parameters_sha256'] and sha(table_raw)==doc['provenance']['derivative_table_sha256']
    params=json.loads(params_raw);checker=support.graph.GraphReplay(json.loads(table_raw));wanted={r['path'] for r in doc['records']}
    target=F(doc['source']['target'])*support.graph.energy.g.DEN;assert target.denominator==1
    states,ancestors=support.graph.reconstruct(doc['source'],wanted,params,checker,target.numerator);cases=[]
    cmap={r['path']:r for r in compare['records']}
    for case in doc['records']:
        state=states[case['path']];rows,old,bound,mid,rad=group_rows(case,state,params,checker);ec=energy_algebra(case,state,params)
        if case.get('energy_packet_kind')=='friendly-centre-zero':ec.update(friendly_composition(doc,case,state,params))
        audit=cmap[case['path']];assert len(audit['unmerged_terms_by_factor'])==len(old)
        original={'coeff':{},'bound':F(0)};combined={'coeff':{},'bound':F(0)}
        for base,factor,terms in zip(old,case['factors'],audit['unmerged_terms_by_factor']):
            A=0;b=[0]*9
            for s,sign,rawmu in terms:
                mu=exact.integer(rawmu);assert mu>0;A+=mu
                if s==-1:assert sign==0;add(original,base,mu)
                else:b[s]+=sign*mu;add(original,rlt(base,mid,rad,s,sign),mu)
            assert A==int(factor['A']) and [[s,str(v)] for s,v in enumerate(b) if v]==factor['b']
        add(original,rows[-1]);assert case['energy_weight']==audit['original_energy_weight']
        for row in rows:add(combined,row)
        assert all(original['coeff'].get(i,F(0))==combined['coeff'].get(i,F(0)) for i in range(464)) and original['bound']==combined['bound']
        expected=case['unrounded_full_464_row_sha256'];assert digest(original)==digest(combined)==expected
        assert audit['unrounded_original_464_row_sha256']==audit['unrounded_grouped_464_row_sha256']==expected
        N=exact.integer(case['integerization_denominator']);assert N==10**30
        coeff,B,minimum,margin,payment=aggregate(rows,bound,N)
        assert margin==F(case['expected_strict_margin'])>0 and minimum==F(case['expected_box_minimum']) and B==int(case['expected_aggregate_bound'])
        cases.append({'path':case['path'],'nonnegative_affine_factors':len(old),'integer_rows_with_energy':len(rows),
          'all_464_unrounded_coefficients_and_constant_equal':True,'strict_margin':str(margin),'strict_integer_system':True,
          'finite_energy_polynomial':ec,'actual_Lean_exclusion_proven':False})
        print(json.dumps({'path':case['path'],'factors':len(old),'strict':True,'seconds':time.monotonic()-start}),flush=True)
    assert not any(name in sys.modules for name in ['numpy','scipy','networkx'])
    result={'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'proof_gzip_sha256':sha(packed),'comparison_gzip_sha256':sha(compacked),
      'parameters_sha256':sha(params_raw),'table_sha256':sha(table_raw),'dependency_sources_sha256':support.dependency_hashes(),
      'all_checks_passed':True,'ancestor_counts':ancestors,'cases':cases,'no_site_packages':sys.flags.no_site,
      'point_kernel_evaluations_rerun':False,'no_optimization_packages_imported':True,'strict_local_integer_systems':len(cases),
      'new_cell_exclusions':0,'actual_Lean_exclusions':0,'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    p=folder/'independent-replay.json';p.write_text(json.dumps(result,indent=2)+'\n',encoding='utf8');print(json.dumps({'all_checks_passed':True,'seconds':result['seconds'],'receipt_sha256':sha(p.read_bytes())}),flush=True)
if __name__=='__main__':main()
