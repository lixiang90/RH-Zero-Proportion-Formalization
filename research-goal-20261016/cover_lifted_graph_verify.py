"""Independent stdlib-only replay of lifted multi-facet KKT exclusions.

Recomputes every used 1/64 derivative grid interval from the frozen Taylor
coefficients and its rational order-24 remainder.  Rechecks every supporting
line over the entire clipped span, the old affine slabs, boundary KKT signs,
all nonnegative Farkas weights, actual DBM edge costs, flow divergence and
the strict residual-paid contradiction.  No discovery code is imported.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
from functools import lru_cache
import argparse,gzip,hashlib,json,time
import cover_compact_codec as codec
import cover_correlated_replay as scalar_module
import cover_sublevel_obbt_verify as obbt
import cover_sublevel_verify as energy
import cover_contractor_verify as newton
SC=scalar_module.SC;DS=scalar_module.DS;a=scalar_module.a;ceil=scalar_module.ceil
HERE=Path(__file__).parent;ROOT=HERE.parent
sha=lambda b:hashlib.sha256(b).hexdigest()


class GraphReplay:
    def __init__(self,doc):
        self.scalar=scalar_module.ScalarReplay(doc);self.width=self.scalar.width;self.grid=self.scalar.ranges;self.checked_grid=set()
        self.remainder=self.scalar.M*F(1,2)**23/factorial(23)
    @lru_cache(4096)
    def grid_interval(self,k):
        n=round(F(2*k+1,2*self.scalar.step));x=scalar_module.J(F(k,self.scalar.step)-n,F(k+1,self.scalar.step)-n)
        v=self.scalar.poly(n,x,0);l=(v.l-self.remainder)*DS;u=(v.u+self.remainder)*DS
        lower=l.numerator//l.denominator;upper=ceil(u);stored=self.grid[k]
        assert stored[0]<=lower and upper<=stored[1],('bad frozen derivative grid',k,stored,lower,upper)
        self.checked_grid.add(k);return stored
    def rectangles(self,l,u):
        if l<0 or u>32*SC:return [(l,u,-7*DS,7*DS)]
        first=l//self.width;last=(max(l+1,u)+self.width-1)//self.width
        return [(max(l,k*self.width),min(u,(k+1)*self.width),*self.grid_interval(k)) for k in range(first,last)]
    def slab(self,l,u,row):
        if row[4]=='interval':self.rectangles(l,u)
        return self.scalar.check(l,u,row)


def verify(state,cert,params,checker):
    a.closure_valid(state);D=params['denominator'];assert D==10**10;Q=2*SC*DS*D
    assert cert['kind']=='lifted_graph_KKT' and int(cert['row_denominator'])==Q
    terms=[tuple(r) for r in params['a_upper'] if r[2]];N=len(terms);bs=params['b_numerators'];sep=123*SC//128
    assert len(cert['scalar_affine_data'])==N;data=[]
    for (i,j,aw),raw in zip(terms,cert['scalar_affine_data']):
        z=a.INDEX[i,j];data.append(checker.slab(state[0][z],state[1][z],raw))
    Ag=[0]*9;Au=[0]*N;B=0;row_counts={};facet_grid_indices=set()
    for meta,weight in cert['weighted_rows']:
        mu=int(weight);assert mu>0 and str(mu)==weight;ag=[0]*9;au=[0]*N;kind=meta[0];row_counts[kind]=row_counts.get(kind,0)+1
        if kind=='DBM':
            _,z,sign=meta;assert isinstance(z,int) and 0<=z<45 and sign in [-1,1];i,j=a.PAIRS[z]
            ag=[sign*Q if i<=k<j else 0 for k in range(9)];b=sign*2*DS*D*state[1 if sign==1 else 0][z]
        elif kind=='KKT':
            _,k,sign=meta;assert isinstance(k,int) and 0<=k<9 and sign in [-1,1]
            assert sign==-1 or state[0][k]>sep
            au=[sign*2*SC*DS*aw if i<=k<j else 0 for i,j,aw in terms];b=-sign*2*SC*DS*bs[k]
        else:
            assert kind in ['slab','facet'];t=meta[1];sign=meta[2];assert isinstance(t,int) and 0<=t<N and sign in [-1,1]
            i,j,aw=terms[t];z=a.INDEX[i,j];l,u=state[0][z],state[1][z];au[t]=sign*Q
            if kind=='slab':
                P,m0,m1,err,_=data[t];ag=[-sign*2*SC*m1*D if i<=k<j else 0 for k in range(9)]
                b=D*(sign*(2*SC*m0-m1*P)+2*SC*err)
            else:
                S=int(meta[3]);C=int(meta[4]);rect=checker.rectangles(l,u)
                if sign==1:wanted=max(SC*U-S*(aa if S>=0 else bb) for aa,bb,L,U in rect)
                else:wanted=min(SC*L-S*(bb if S>=0 else aa) for aa,bb,L,U in rect)
                assert C==wanted;ag=[-sign*2*SC*S*D if i<=k<j else 0 for k in range(9)];b=sign*2*D*C
                if l>=0 and u<=32*SC:facet_grid_indices.update(range(l//checker.width,(max(l+1,u)+checker.width-1)//checker.width))
        Ag=[x+mu*y for x,y in zip(Ag,ag)];Au=[x+mu*y for x,y in zip(Au,au)];B+=mu*b
    assert Ag==list(map(int,cert['gap_coefficients'])) and Au==list(map(int,cert['scalar_coefficients'])) and B==int(cert['rhs'])
    minimum=newton.flow_bound(state,Ag,cert['flow']);payment=7*SC*sum(map(abs,Au));margin=minimum-payment-SC*B
    assert minimum==int(cert['minimum_numerator']) and payment==int(cert['scalar_residual_payment'])
    assert margin==int(cert['strict_margin'])>0
    return {'strict_margin':str(margin),'row_counts':row_counts,'facet_grid_indices':len(facet_grid_indices)}


def reconstruct(doc,selected,params,checker,target):
    bs=params['b_numerators'];sep=123*SC//128;cn=F(doc['target'])*10**10;assert cn.denominator==1
    budget=int(cn)*SC-sum(bs)*sep;up=[sep+ceil(F(budget,b)) for b in bs]
    root=[[(j-i)*sep for i,j in a.PAIRS],[min(sum(up[i:j]),(j-i)*sep+ceil(F(budget,min(bs[i:j])))) for i,j in a.PAIRS]]
    assert root==doc['root'];cases={r['path']:r for r in doc['cases']};needed={p[:k] for p in selected for k in range(1,len(p)+1)}
    todo=[('r',root)];before={};seen=set();bounds=steps=0
    while todo:
        p,state=todo.pop();assert p not in seen;seen.add(p)
        if p in selected:assert state==cases[p]['before'];before[p]=state;continue
        if p in doc['OBBT']:
            step=codec.unpack_obbt(state,doc['OBBT'][p],target,obbt.shared.w);obbt.verify({**step,'result':None},target,checker.scalar)
            bounds+=len(step['certificates']);state=step['new_cell']
        for packedstep in doc['Newton'].get(p,[]):
            step=codec.unpack_newton(state,packedstep,obbt.shared.w);state=newton.verify_step(state,step,params,checker.scalar);steps+=1
        assert state is not None;b=doc['branches'][p];assert state[0][b['axis']]<b['cut']<state[1][b['axis']]
        for bit in ['0','1']:
            if p+bit in needed:
                child=a.child(state,b['axis'],b['cut'],bit=='0');assert child is not None;todo.append((p+bit,child))
    assert seen==needed and set(before)==set(selected)
    return before,{'nodes':len(seen),'source_OBBT_bounds':bounds,'source_Newton_steps':steps}


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=HERE/'cover-lifted-graph8.json');ap.add_argument('--output',type=Path,default=HERE/'cover-lifted-graph8-replay.json');args=ap.parse_args()
    start=time.monotonic();raw=args.input.read_bytes();proof=json.loads(raw);packed=(HERE/'cover-curvature-parent64.input.json.gz').read_bytes();assert sha(packed)==proof['receipt']['input_sha256'];doc=json.loads(gzip.decompress(packed))
    for name,digest in doc['input_sha256'].items():assert sha((ROOT/name).read_bytes())==digest,name
    tabraw=(HERE/'cover_newjet.json').read_bytes();assert sha(tabraw)==proof['receipt']['table_sha256'];table=json.loads(tabraw)
    params=json.loads((ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes());assert table['receipt']['parameter_sha256']==sha((ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes())
    checker=GraphReplay(table);target=F(doc['target'])*energy.g.DEN;assert target.denominator==1;target=target.numerator
    selected={r['path'] for r in proof['rows']};assert len(selected)==len(proof['rows']) and not any(p!=q and p.startswith(q) for p in selected for q in selected)
    before,counts=reconstruct(doc,selected,params,checker,target);closed=[];details=[];savings={k:0 for k in doc['cases'][0]['recorded_old_work']};cases={r['path']:r for r in doc['cases']}
    for row in proof['rows']:
        for label in ['baseline','graph']:
            if row[label]:
                details.append({'path':row['path'],'label':label,**verify(before[row['path']],row[label],params,checker)})
        if row['graph'] and not row['baseline']:
            closed.append(row['path'])
            for k,v in cases[row['path']]['recorded_old_work'].items():savings[k]+=v
    counts['checked_farkas_certificates']=len(details)
    out={'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'input_sha256':sha(raw),'all_passed':True,'parents':len(selected),'counts':counts,
      'additional_over_single_slab':len(closed),'additional_paths':closed,'strict_certificates':details,'independently_recomputed_derivative_grid_cells':len(checker.checked_grid),
      'source_recorded_work_below_additional_parents':savings,'descendant_counts_are_source_projection_metrics':True,
      'LP_residual_values_are_discovery_metadata':True,'baseline_no_certificate_is_not_a_feasibility_theorem':True,
      'complete_global_cover':False,'actual_lifted_graph_Lean_consumer_complete':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
