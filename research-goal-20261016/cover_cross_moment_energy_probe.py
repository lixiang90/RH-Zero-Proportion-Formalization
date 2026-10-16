"""Uniform quadratic energy sublevel rows for the two-cell cross-moment test.

For each fixed feasible centre c, Taylor's integral remainder gives
 F(g) >= F(c)+grad F(c).(g-c)+sum_t a_t*L_t*(span_t(g-c))^2/2,
where L_t encloses w'' from below on the whole cell span. Point interval
uncertainty is paid uniformly. The resulting quadratic shares the position
moments already coupled to the multiplied KKT rows. All arithmetic packets
are rational; solver results remain floating diagnostics, not exclusions.
The immutable earlier model is reused by adapting only its LP call.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,gzip,hashlib,json,time
import numpy as np
from scipy.sparse import csr_matrix,vstack
import cover_cross_moment_probe as base
import window_interval_kernel as ik

HERE=Path(__file__).parent;g=base.g;SC=base.SC
sha=lambda b:hashlib.sha256(b).hexdigest()

def packet(state,point,second):
    assert len(point)==9
    assert all(F(l,SC)<=sum(point[i:j])<=F(u,SC) for (i,j),l,u in zip(g.ALL,*state))
    lo=list(map(lambda n:F(n,SC),state[0][:9]));hi=[F(n,SC) for n in state[1][:9]]
    mid=[(a+b)/2 for a,b in zip(lo,hi)];rad=[(b-a)/2 for a,b in zip(lo,hi)]
    f0=ik.I(sum(F(b,g.D)*x for b,x in zip(g.BS,point)))
    grad=[ik.I(F(b,g.D)) for b in g.BS];lower=[]
    for i,j,aw in g.TERMS:
        x=sum(point[i:j]);w0,w1=ik.w_jet(x,1);a=F(aw,g.D)
        f0+=a*w0
        for r in range(i,j):grad[r]+=a*w1
        axis=g.LOOK[i,j];L,U=second.query(state[0][axis],state[1][axis]);lower.append(F(L,base.old.DS))
    gm=[(v.l+v.u)/2 for v in grad]
    payment=sum((v.u-v.l)/2*max(abs(a-c),abs(b-c)) for v,a,b,c in zip(grad,lo,hi,point))
    constant=f0.l-payment+sum(v*(m-c) for v,m,c in zip(gm,mid,point))
    linear=[v*r for v,r in zip(gm,rad)];quad={pair:F(0) for pair in base.PAIRS}
    for (i,j,aw),L in zip(g.TERMS,lower):
        aL=F(aw,g.D)*L;delta=sum(mid[i:j])-sum(point[i:j]);constant+=aL*delta*delta/2
        for r in range(i,j):
            linear[r]+=aL*delta*rad[r]
            for s in range(r,j):quad[r,s]+=aL*rad[r]*rad[s]/(2 if r==s else 1)
    exact=[F(0)]*base.V
    for r in range(9):exact[r]=linear[r]/rad[r];constant-=linear[r]*mid[r]/rad[r]
    for (r,s),v in quad.items():exact[base.hindex(r,s)]=v
    bound=F(11,1250)-constant
    # A factorized point at c makes the lower polynomial equal F(c)'s
    # lower endpoint minus exactly the uniform gradient uncertainty payment.
    ys=[(c-m)/r for c,m,r in zip(point,mid,rad)]
    factor=[F(0)]*base.V;factor[:9]=point
    for r,s in base.PAIRS:factor[base.hindex(r,s)]=ys[r]*ys[s]
    assert constant+sum(a*x for a,x in zip(exact,factor))==f0.l-payment
    return {'centre':list(map(str,point)),'F_interval':[str(f0.l),str(f0.u)],
      'gradient_interval':[[str(v.l),str(v.u)] for v in grad],
      'uniform_gradient_error_payment':str(payment),'whole_span_second_lower':list(map(str,lower)),
      'quadratic_constant':str(constant),'row':[[k,str(v)] for k,v in enumerate(exact) if v],
      'bound':str(bound),'centre_factorization_exact':True}

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();assert not args.output.exists(),'Use a new output.'
    start=time.monotonic();source=HERE/'cover-curvature-parent64.input.json.gz';raw=source.read_bytes()
    cases={c['path']:c for c in json.loads(gzip.decompress(raw))['cases']}
    samplepath=HERE/'cover-gradient-mixture.json';sample_raw=samplepath.read_bytes();samples=json.loads(sample_raw)['rows']
    table=HERE/'cover_newjet.json';taylor=base.old.context.curvature.first.TaylorOracle(table)
    second=base.old.context.curvature.second.SecondOracle(taylor);graph=base.old.GraphOracle(table);results=[]
    for sample in samples:
        path=sample['path'];assert path in ['r001000001000001101011101','r001000001000001110011100']
        state=tuple(cases[path]['before']);assert [list(x) for x in state]==sample['cell']
        prefix=[F(0)]+[F(state[0][g.LOOK[0,j]]+state[1][g.LOOK[0,j]],2*SC) for j in range(1,10)]
        centres=[[prefix[j+1]-prefix[j] for j in range(9)]]
        k=int(np.argmin(sample['sample_energies_hint']))
        centres.append([F(x)/SC for x in sample['sample_points_gap_units'][k]])
        packets=[packet(state,c,second) for c in centres];erows=[];ebounds=[]
        for p in packets:
            row=np.zeros(base.V)
            for k,v in p['row']:row[k]=float(F(v))
            B=float(F(p['bound']));scale=max(1.,max(abs(row)),abs(B));erows.append(row/scale);ebounds.append(B/scale)
        original=base.linprog
        def augmented(c,**kw):
            kw['A_ub']=vstack([kw['A_ub'],csr_matrix(erows)],format='csr')
            kw['b_ub']=np.r_[kw['b_ub'],ebounds]
            return original(c,**kw)
        base.linprog=augmented
        try:result=base.solve(state,taylor,graph,3)
        finally:base.linprog=original
        if result['final_primal'] is not None:
            result['minimum_added_energy_row_slack_hint']=float(min(np.array(ebounds)-np.array(erows)@np.array(result['final_primal'])))
        results.append({'path':path,'energy_packets':packets,'added_energy_rows':len(packets),'position_PSD_cut_rounds':3,**result})
        print(json.dumps({'path':path,'history':result['history'],'seconds':time.monotonic()-start}),flush=True)
    receipt={'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'base_model_sha256':sha(Path(base.__file__).read_bytes()),
      'kernel_helper_sha256':sha(Path(ik.__file__).read_bytes()),'parent64_input_sha256':sha(raw),'sample_input_sha256':sha(sample_raw),
      'table_sha256':sha(table.read_bytes()),'strict_certificates':0,'floating_hints_only':True,'quadratic_energy_consumer_Lean_proven':False,
      'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps({'receipt':receipt,'rows':results},separators=(',',':'))+'\n',encoding='utf8')
    print(json.dumps(receipt),flush=True)
if __name__=='__main__':main()
