"""Exact affine-factor compression of the two frozen moment certificates.

No LP, sampling, threshold change or Lean execution is used. For one old
row R<=B, combine base/RLT multipliers into (R-B)*(A+sum b_s*y_s)<=0,
checking A>=sum abs(b_s). Compare the complete unrounded polynomial, then
round each weighted group once at 1e30 and recheck the strict box margin.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import defaultdict
import gzip,hashlib,json,time
import cover_cross_moment_exact_rows as exact
HERE=Path(__file__).parent;ROOT=HERE.parent;sha=lambda b:hashlib.sha256(b).hexdigest()


def canonical(meta):
    kind=meta[0];assert kind in ['DBM','slab','facet','KKT']
    if kind=='facet':
        assert len(meta)==5;return [kind,int(meta[1]),int(meta[2]),str(exact.integer(meta[3])),str(exact.integer(meta[4]))]
    assert len(meta)==3;return [kind,int(meta[1]),int(meta[2])]


def factor_row(old,center,radius,A,b):
    assert A>=sum(map(abs,b)) and A>0
    ag=[old['coeff'].get(i,F(0)) for i in range(9)];au=[old['coeff'].get(9+t,F(0)) for t in range(41)]
    row={i:A*v for i,v in old['coeff'].items()};bound=A*old['bound'];K=sum(v*c for v,c in zip(ag,center))-old['bound']
    def add(i,v):
        row[i]=row.get(i,F(0))+v
        if not row[i]:row.pop(i)
    for s,v in enumerate(b):
        if not v:continue
        add(s,v*K/radius[s]);bound+=v*K*center[s]/radius[s]
        for r,a in enumerate(ag):add(exact.hindex(s,r),v*a*radius[r])
        for t,a in enumerate(au):add(exact.qindex(s,t),v*a)
    return {'coeff':row,'bound':bound,'meta':['factor',canonical(old['meta'][2])]}


def digest_row(row):
    data=[[[i,str(row['coeff'].get(i,F(0)))] for i in range(exact.V)],str(row['bound'])]
    return sha(json.dumps(data,separators=(',',':')).encode())


def add_weighted(total,row,mu):
    for i,a in row['coeff'].items():
        total['coeff'][i]=total['coeff'].get(i,F(0))+mu*a
        if not total['coeff'][i]:total['coeff'].pop(i)
    total['bound']+=mu*row['bound']


def main():
    start=time.monotonic();cert_path=HERE/'cover-cross-moment-integer-two.json';raw=cert_path.read_bytes();cert=json.loads(raw)
    parent_raw=(HERE/'cover-curvature-parent64.input.json.gz').read_bytes();source=json.loads(gzip.decompress(parent_raw));rows=[];audit=[];stats=[]
    for case in cert['rows']:
        state=case['cell'];integer=[(ag,au,B) for ag,au,B in case['old_integer_rows']]
        model=exact.inputs(state,integer,case['old_meta'],case['u_bounds'],case['energy_packets'])
        groups={}; original={'coeff':{},'bound':F(0)};energy_weight=0;selected_packet=[];original_weight_sum=0
        for saved in case['selected_integer_rows']:
            mu=int(saved['weight']);assert mu>0;original_weight_sum+=mu;index=saved['row_index'];r=model['rows'][index]
            assert r['meta']==saved['meta'];kind=r['meta'][0];add_weighted(original,r,mu)
            if kind=='energy':
                assert r['meta']==['energy',0];energy_weight+=mu;continue
            assert kind in ['base','RLT'];old_id=r['meta'][1];meta=canonical(case['old_meta'][old_id]);key=json.dumps(meta,separators=(',',':'))
            if key not in groups:groups[key]={'old_id':old_id,'meta':meta,'A':0,'b':[0]*9,'unmerged':[]}
            group=groups[key];assert model['rows'][19*old_id]['coeff']==model['rows'][19*group['old_id']]['coeff']
            group['A']+=mu
            if kind=='RLT':
                _,_,s,sign,_=r['meta'];assert 0<=s<9 and sign in [-1,1];group['b'][s]+=sign*mu;group['unmerged'].append([s,sign,str(mu)])
            else:group['unmerged'].append([-1,0,str(mu)])
        assert energy_weight>0
        grouped=[];factors=[];unmerged=[];zero_margins=0
        for key,group in sorted(groups.items()):
            A,b=group['A'],group['b'];assert A>=sum(map(abs,b));zero_margins+=int(A==sum(map(abs,b)))
            old=model['rows'][19*group['old_id']];fr=factor_row(old,model['center'],model['radius'],A,b);grouped.append(fr)
            factors.append({'old_meta':group['meta'],'A':str(A),'b':[[s,str(v)] for s,v in enumerate(b) if v]})
            unmerged.append(group['unmerged'])
        energy_old=model['rows'][-len(case['energy_packets'])]
        energy_row={'coeff':{i:energy_weight*v for i,v in energy_old['coeff'].items()},'bound':energy_weight*energy_old['bound'],'meta':['weighted_energy',0]};grouped.append(energy_row)
        combined={'coeff':{},'bound':F(0)}
        for row in grouped:add_weighted(combined,row,1)
        assert all(combined['coeff'].get(i,F(0))==original['coeff'].get(i,F(0)) for i in range(exact.V)) and combined['bound']==original['bound']
        converted=[exact.integerize(r,model['bounds'],10**30) for r in grouped]
        checked=exact.verify_aggregate(converted,[(i,1) for i in range(len(converted))],model['bounds']);assert checked['strict_exclusion']
        active_slabs=sorted({f['old_meta'][1] for f in factors if f['old_meta'][0]=='slab'})
        saved_case={'path':case['path'],'scalar_affine_data':[[t,case['scalar_affine_data'][t]] for t in active_slabs],
          'factors':factors,'energy_packet':case['energy_packets'][0],'energy_weight':str(energy_weight),
          'integerization_denominator':str(10**30),'unrounded_full_464_row_sha256':digest_row(combined),
          'expected_strict_margin':str(checked['strict_margin']),'expected_box_minimum':str(checked['box_minimum']),
          'expected_aggregate_bound':str(checked['bound'])}
        rows.append(saved_case);audit.append({'path':case['path'],'unmerged_terms_by_factor':unmerged,
          'original_selected_rows':len(case['selected_integer_rows']),'original_energy_weight':str(energy_weight),
          'unrounded_original_464_row_sha256':digest_row(original),'unrounded_grouped_464_row_sha256':digest_row(combined)})
        summary={'path':case['path'],'old_product_rows':sum(r['meta'][0]=='RLT' for r in case['selected_integer_rows']),
          'old_base_rows':sum(r['meta'][0]=='base' for r in case['selected_integer_rows']),'affine_factor_groups':len(factors),
          'total_integer_rows_with_energy':len(grouped),'nonnegative_factors_checked':len(factors),'factors_with_zero_nonnegative_margin':zero_margins,
          'all_464_unrounded_coefficients_and_constant_equal':True,'active_scalar_slabs':len(active_slabs),
          'old_strict_margin':case['aggregate']['strict_margin'],'new_strict_margin':str(checked['strict_margin']),
          'new_normalized_margin_original_weight_sum':str(checked['strict_margin']/(10**30*original_weight_sum)),
          'old_weighted_rounding_payment':str(sum(int(s['weight'])*F(s['rounding_payment']) for s in case['selected_integer_rows'])),
          'new_group_rounding_payment':str(sum(r['rounding_payment'] for r in converted))}
        stats.append(summary);print(json.dumps({'path':case['path'],'old_RLT_rows':summary['old_product_rows'],'groups':len(factors),'strict':True,'seconds':time.monotonic()-start}),flush=True)
    wanted={r['path'] for r in rows};needed={p[:k] for p in wanted for k in range(1,len(p))};projection={k:source[k] for k in ['root','target','input_sha256']}
    for key in ['branches','OBBT','Newton']:projection[key]={p:r for p,r in source[key].items() if p in needed}
    projection['cases']=[{'path':c['path'],'before':c['before']} for c in source['cases'] if c['path'] in wanted]
    out={'schema':'quadratic-energy-affine-factor-certificate-v1','source':projection,'records':rows,
      'provenance':{'original_integer_certificate_sha256':sha(raw),'original_parent64_input_gzip_sha256':sha(parent_raw),
      'parameters_sha256':sha((ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes()),
      'derivative_table_sha256':sha((HERE/'cover_newjet.json').read_bytes())},'actual_Lean_exclusions':0,
      'complete_global_cover':False,'new_zero_proportion_proven':False}
    folder=HERE/'cover-cross-moment-factor-evidence';folder.mkdir(exist_ok=True);data=(json.dumps(out,separators=(',',':'))+'\n').encode();packed=gzip.compress(data,mtime=0);(folder/'proof.json.gz').write_bytes(packed)
    audit_data=(json.dumps({'schema':'affine-factor-original-multiplier-comparison-v1','proof_gzip_sha256':sha(packed),'records':audit},separators=(',',':'))+'\n').encode()
    audit_packed=gzip.compress(audit_data,mtime=0);(folder/'comparison.json.gz').write_bytes(audit_packed)
    receipt={'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'exact_rows_sha256':sha(Path(exact.__file__).read_bytes()),
      'original_integer_certificate_sha256':sha(raw),'original_integer_certificate_bytes':len(raw),
      'original_integer_certificate_gzip_bytes':len(gzip.compress(raw,mtime=0)),
      'proof_gzip_sha256':sha(packed),'proof_gzip_bytes':len(packed),'proof_uncompressed_sha256':sha(data),'proof_uncompressed_bytes':len(data),
      'comparison_gzip_sha256':sha(audit_packed),'comparison_gzip_bytes':len(audit_packed),'cases':stats,
      'all_unrounded_polynomials_equal':True,'strict_integer_systems':2,'independent_replay_passed':False,
      'new_cell_exclusions':0,'actual_Lean_exclusions':0,'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    (folder/'manifest.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf8');print(json.dumps({'proof_bytes':len(packed),'comparison_bytes':len(audit_packed),'original_bytes':len(raw),'seconds':receipt['seconds']}),flush=True)
if __name__=='__main__':main()
