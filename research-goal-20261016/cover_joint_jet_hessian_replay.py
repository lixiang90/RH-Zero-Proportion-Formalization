"""Pure-stdlib replay of the new joint-jet facets and Hessian extension.

Recompute every same-grid w'' interval, every integer-normal support
payment, and the fixed old exact vector's per-edge v interval. Choose
each v at its allowed upper endpoint and verify a positive rational LDL
factorization of the full physical Hessian. The old 464-variable model's
43,306 rows and 41 residual cones are a separate, pinned frozen certificate;
this replay checks the added constraints, not those old checks again.
"""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
from math import factorial
import argparse,hashlib,json,sys,time

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;SC=32768;DS=10**15
OUT=HERE/'cover-joint-jet-hessian-replay.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def floor(x):return x.numerator//x.denominator
def ceil(x):return -floor(-x)
def mul(a,b):
    z=[x*y for x in a for y in b];return min(z),max(z)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write-receipt',action='store_true')
    args=parser.parse_args()
    if args.write_receipt:assert not OUT.exists(),'Use an absent receipt path; existing receipts are immutable.'
    started=time.monotonic()
    pilotpath=HERE/'cover-joint-jet-hessian-pilot.json'
    pointpath=HERE/'cover-residual-psd-rational-projection.json'
    oldreplaypath=HERE/'cover-residual-psd-rational-replay.json'
    oldsourcepath=HERE/'cover_residual_psd_rational_replay.py'
    parampath=ROOT/'research-20261016-followup/window_reweight_rational.json'
    tablepath=HERE/'cover_newjet.json'
    watched=[Path(__file__),pilotpath,pointpath,oldreplaypath,oldsourcepath,parampath,tablepath]
    initial={p.relative_to(ROOT).as_posix():sha(p) for p in watched}
    pilot=json.loads(pilotpath.read_bytes());point=json.loads(pointpath.read_bytes())
    oldreplay=json.loads(oldreplaypath.read_bytes());params=json.loads(parampath.read_bytes())
    table=json.loads(tablepath.read_bytes());state=pilot['cell'];step=table['receipt']['grid_step'];width=SC//step
    assert pilot['phase']=='completed_single_joint_jet_Hessian_test' and pilot['target']=='11/1250'
    assert point['path']==pilot['path']==oldreplay['path']
    assert oldreplay['status']=='strict_exact_feasible_outer_relaxation_verified'
    assert oldreplay['rational_rows_checked']==43306 and oldreplay['strict_positive_LDL_blocks_checked']==41
    assert oldreplay['inputs_unchanged']=='yes'
    for rel,h in pilot['input_sha256'].items():assert sha(ROOT/rel)==h
    for rel,h in oldreplay['input_sha256_start'].items():assert sha(ROOT/rel)==h
    assert table['receipt']['denominator']==DS and SC%step==0
    coeff={int(n):[(F(l),F(u)) for l,u in cs] for n,cs in table['integer_taylor_coefficients'].items()}
    remainder=F(44,7)**24*F(1,2)**22/factorial(22)
    @lru_cache(None)
    def second_grid(k):
        n=round(F(2*k+1,2*step));x=(F(k,step)-n,F(k+1,step)-n);value=(F(0),F(0))
        for j in range(len(coeff[n])-1,0,-1):
            a,b=mul(value,x);l,u=coeff[n][j];value=(a+j*l,b+j*u)
        return floor((value[0]-remainder)*DS),ceil((value[1]+remainder)*DS)
    terms=[tuple(row) for row in params['a_upper'] if row[2]];assert len(terms)==41
    positions=[(r,r+1) for r in range(9)]+[(i,j) for i in range(10) for j in range(i+2,10)]
    # Match the ledger's span ordering directly from the old fixed-cell file.
    # Its first nine entries are adjacent, followed by lexicographic longer spans.
    lookup={p:k for k,p in enumerate(positions)}
    x=list(map(F,point['projected_464_rational_moments']));assert len(x)==464
    all_v=[];extension=[];rectcount=facetcount=mixed=0
    for e,(data,(i,j,aw)) in enumerate(zip(pilot['joint_graph_edges'],terms)):
        assert data['edge']==e and data['ij']==[i,j]
        z=lookup[i,j];l=state[0][z];u=state[1][z]
        first=l//width;last=(max(l+1,u)+width-1)//width
        expected=[]
        for k in range(first,last):
            expected.append([max(l,k*width),min(u,(k+1)*width),*table['ranges'][k],*second_grid(k)])
        assert expected==data['rectangles'],(e,'rectangles')
        rectcount+=len(expected);s=sum(x[i:j]);uu=x[9+e];lo=up=None;li=ui=None
        for k,(n,C) in enumerate(data['facets']):
            ns,nu,nv=n;assert all(isinstance(t,int) for t in n) and any(n)
            paid=max(ns*(b if ns>=0 else a)*DS+SC*(nu*(U if nu>=0 else L)+nv*(K if nv>=0 else J))
                     for a,b,L,U,J,K in expected)
            assert paid==int(C),(e,k,'exact support payment')
            # Independent all-eight-corners replay of the same payment.
            assert paid==max(ns*xx*DS+SC*(nu*yy+nv*zz) for a,b,L,U,J,K in expected
                             for xx in (a,b) for yy in (L,U) for zz in (J,K))
            rhs=F(paid,SC*DS)-ns*s-nu*uu
            if nv>0:
                bound=rhs/nv
                if up is None or bound<up:up=bound;ui=k
            elif nv<0:
                bound=rhs/nv
                if lo is None or bound>lo:lo=bound;li=k
            else:assert rhs>=0,(e,k,'zero-v row')
            facetcount+=1;mixed+=bool(nu and nv)
        assert lo is not None and up is not None and lo<=up
        saved=pilot['frozen_exact_point_joint_graph_check']['edges'][e]
        assert lo==F(saved['v_lower']) and up==F(saved['v_upper'])
        for n,C in data['facets']:
            assert n[0]*s+n[1]*uu+n[2]*up<=F(int(C),SC*DS)
        all_v.append(up);extension.append({'edge':e,'v_lower':str(lo),'v_upper':str(up),
            'chosen_v':'upper endpoint','lower_facet':li,'upper_facet':ui})
    assert facetcount==pilot['joint_graph_facet_count']==6075 and mixed==4047
    den=params['denominator'];H=[[sum(F(aw,den)*all_v[e] for e,(l,u,aw) in enumerate(terms)
        if l<=i<u and l<=j<u) for j in range(9)] for i in range(9)]
    L=[[F(int(i==j)) for j in range(9)] for i in range(9)];D=[]
    for i in range(9):
        d=H[i][i]-sum(L[i][k]**2*D[k] for k in range(i));assert d>0;D.append(d)
        for j in range(i+1,9):L[j][i]=(H[j][i]-sum(L[j][k]*L[i][k]*D[k] for k in range(i)))/d
    assert all(H[i][j]==sum(L[i][k]*D[k]*L[j][k] for k in range(9)) for i in range(9) for j in range(9))
    assert not any(n.split('.')[0] in ['numpy','scipy','scs'] for n in sys.modules)
    final={p.relative_to(ROOT).as_posix():sha(p) for p in watched};assert initial==final
    result={'scope':__doc__,'status':'new_joint_facets_and_positive_Hessian_extension_exactly_verified',
        'path':pilot['path'],'target':'11/1250','input_sha256_start':initial,'input_sha256_end':final,
        'inputs_unchanged':True,'same_grid_rectangles_checked':rectcount,'facets_checked':facetcount,
        'mixed_u_v_facets_checked':mixed,'v_grid_intervals_recomputed':second_grid.cache_info().currsize,
        'extension':extension,'chosen_v':list(map(str,all_v)),
        'physical_Hessian_unit_lower':[[str(v) for v in row] for row in L],
        'physical_Hessian_positive_diagonal':list(map(str,D)),
        'positive_diagonal_display_only':list(map(float,D)),
        'old_baseline_reference':{'receipt_sha256':sha(oldreplaypath),'source_sha256':sha(oldsourcepath),
          'separate_prior_certificate_status':oldreplay['status'],'prior_rows':43306,'prior_residual_PSD_blocks':41},
        'new_constraints_exactly_feasible_at_old_outer_relaxation_point':True,
        'old_baseline_constraints_rechecked_here':False,'actual_Fw_sublevel_counterexample':False,
        'actual_new_cell_exclusion':False,'new_zero_proportion_proven':False,'pure_stdlib_replay':True,
        'elapsed_milliseconds':int(1000*(time.monotonic()-started))}
    if args.write_receipt:OUT.write_text(json.dumps(result,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({k:result[k] for k in ['status','facets_checked','mixed_u_v_facets_checked',
        'v_grid_intervals_recomputed','positive_diagonal_display_only','elapsed_milliseconds']}))

if __name__=='__main__':main()
