"""Two-cell position/gradient moment RLT diagnostic; floating hints only.

Keep the old actual derivative graph and original-orthant KKT rows. Lift
all products y_s*y_r and y_s*u_t, where y is the centred/scaled gap vector.
Multiply every old inequality by both 1+y_s and 1-y_s. At an actual KKT
point these are nonnegative factors; retaining cross-position KKT products
is stronger than the single radial complementarity trace. No floating LP
outcome is accepted as an exclusion proof. No phase or Lean run is used.
"""
from pathlib import Path
import argparse,gzip,hashlib,json,time
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix
import cover_lifted_graph_probe as old

HERE=Path(__file__).parent;g=old.g;SC=g.SC
sha=lambda b:hashlib.sha256(b).hexdigest()
PAIRS=[(s,r) for s in range(9) for r in range(s,9)]
HI={p:50+k for k,p in enumerate(PAIRS)}
def hindex(s,r):return HI[min(s,r),max(s,r)]
def qindex(s,t):return 95+41*s+t
V=95+9*41

def solve(state,taylor,graph,rounds):
    rr,bb,integer,meta,data,obj,stats=old.build(state,taylor,graph,True)
    assert len(g.TERMS)==41
    lower=np.array(state[0][:9],dtype=float)/SC
    upper=np.array(state[1][:9],dtype=float)/SC
    center=(lower+upper)/2;radius=(upper-lower)/2
    assert min(radius)>0
    rows=[];rhs=[];counts={};algebra_error=0.
    def add(row,B,kind):
        scale=max(1.,float(np.max(np.abs(row))),abs(float(B)))
        rows.append(row/scale);rhs.append(float(B)/scale)
        counts[kind]=counts.get(kind,0)+1
    def yadd(row,s,coefficient):
        row[s]+=coefficient/radius[s]
        return coefficient*center[s]/radius[s]
    probe=np.zeros(V);probe[:9]=center+radius*np.linspace(-.8,.8,9)
    probe[9:50]=np.linspace(-.3,.3,41);yp=(probe[:9]-center)/radius
    for s,r in PAIRS:probe[hindex(s,r)]=yp[s]*yp[r]
    for s in range(9):
        for t in range(41):probe[qindex(s,t)]=yp[s]*probe[9+t]
    for original,B,m in zip(rr,bb,meta):
        base=np.zeros(V);base[:50]=original[:50]
        add(base,B,'base_'+m[0])
        ag=base[:9];au=base[9:50];K=float(ag@center-B)
        for s in range(9):
            for sign in (-1,1):
                row=base.copy();bound=B+yadd(row,s,sign*K)
                for r in range(9):row[hindex(s,r)]+=sign*ag[r]*radius[r]
                for t in range(41):row[qindex(s,t)]+=sign*au[t]
                expected=(float(base@probe)-B)*(1+sign*yp[s])
                algebra_error=max(algebra_error,abs(float(row@probe)-bound-expected))
                add(row,bound,'RLT_'+m[0])
    assert algebra_error<1e-9,algebra_error
    bounds=[(None,None)]*V
    for s in range(9):bounds[s]=(lower[s],upper[s])
    for s,r in PAIRS:
        bounds[hindex(s,r)]=(0,1) if s==r else (-1,1)
        for a,b,sign in [(-1,-1,-1),(1,1,-1),(-1,1,1),(1,-1,1)]:
            # Standard McCormick row for h=y_s*y_r with both in [-1,1].
            row=np.zeros(V);row[hindex(s,r)]=sign
            bound=-sign*a*b
            bound+=yadd(row,s,-sign*b)+yadd(row,r,-sign*a)
            add(row,bound,'moment_McCormick')
    for t,(i,j,aw) in enumerate(g.TERMS):
        z=g.LOOK[i,j];facets,n=graph.facets(state[0][z],state[1][z])
        U=min(C/(SC*old.DS) for sign,S,C in facets if sign==1 and S==0)
        L=max(C/(SC*old.DS) for sign,S,C in facets if sign==-1 and S==0)
        assert L<=U
        bounds[9+t]=(L,U)
        for s in range(9):
            bounds[qindex(s,t)]=(-max(abs(L),abs(U)),max(abs(L),abs(U)))
            for a,b,sign in [(-1,L,-1),(1,U,-1),(-1,U,1),(1,L,1)]:
                row=np.zeros(V);row[qindex(s,t)]=sign;row[9+t]=-sign*a
                bound=-sign*a*b+yadd(row,s,-sign*b)
                add(row,bound,'cross_McCormick')
    history=[];cuts=[];primal=None
    for iteration in range(rounds+1):
        lp=linprog(np.zeros(V),A_ub=csr_matrix(np.asarray(rows)),b_ub=np.array(rhs),bounds=bounds,method='highs')
        record={'iteration':iteration,'LP_status':int(lp.status),'LP_success':bool(lp.success),'rows':len(rows)}
        if not lp.success:
            history.append(record);break
        x=lp.x;ys=(x[:9]-center)/radius
        matrix=np.eye(10);matrix[0,1:]=ys;matrix[1:,0]=ys
        for s,r in PAIRS:matrix[s+1,r+1]=matrix[r+1,s+1]=x[hindex(s,r)]
        eigen,vectors=np.linalg.eigh(matrix);record['minimum_moment_eigenvalue_hint']=float(eigen[0])
        record['minimum_row_slack_hint']=float(min(np.array(rhs)-np.asarray(rows)@x))
        record['factorized_cross_max_defect_hint']=max(abs(x[qindex(s,t)]-ys[s]*x[9+t]) for s in range(9) for t in range(41))
        history.append(record);primal=x.tolist()
        if eigen[0]>=-1e-8 or iteration==rounds:break
        for k,value in enumerate(eigen):
            if value>=-1e-8:break
            v=vectors[:,k];v=np.rint(v/max(abs(v))*32768).astype(np.int64)
            # v^T [[1,y^T],[y,H]] v >= 0; integer coefficients, float LP only.
            row=np.zeros(V);bound=int(v[0])**2
            for s in range(9):
                bound+=yadd(row,s,-2*int(v[0])*int(v[s+1]))
                for r in range(s,9):row[hindex(s,r)]=-(1 if s==r else 2)*int(v[s+1])*int(v[r+1])
            add(row,bound,'position_moment_PSD_cut');cuts.append(list(map(int,v)))
    return {'history':history,'statistics':counts,'variables':V,'strict_free_coordinates':[r for r in range(9) if state[0][r]>g.SEP],
      'algebra_factorization_check_max_error':algebra_error,'integer_PSD_cut_vectors':cuts,'final_primal':primal,
      'positive_or_infeasible_hint':history[-1]['LP_status']==2,'strict_certificate':None}

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--rounds',type=int,default=5);args=ap.parse_args();assert 0<=args.rounds<=5
    assert not args.output.exists(),'Use a new output; existing receipts are immutable.'
    start=time.monotonic();source=HERE/'cover-curvature-parent64.input.json.gz';raw=source.read_bytes()
    cases={c['path']:c for c in json.loads(gzip.decompress(raw))['cases']}
    paths=['r001000001000001101011101','r001000001000001110011100']
    table=HERE/'cover_newjet.json';taylor=old.context.curvature.first.TaylorOracle(table);graph=old.GraphOracle(table);rows=[]
    for path in paths:
        result=solve(tuple(cases[path]['before']),taylor,graph,args.rounds)
        rows.append({'path':path,**result});print(json.dumps({'path':path,'history':result['history'],'seconds':time.monotonic()-start}),flush=True)
    receipt={'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'source_sha256':sha(raw),
      'old_graph_sha256':sha(Path(old.__file__).read_bytes()),'table_sha256':sha(table.read_bytes()),'maximum_PSD_rounds':args.rounds,
      'floating_hints_only':True,'strict_certificates':0,'analytic_Lean_consumer_proven':False,'complete_global_cover':False,
      'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps({'receipt':receipt,'rows':rows},separators=(',',':'))+'\n',encoding='utf8')
    print(json.dumps(receipt),flush=True)
if __name__=='__main__':main()
