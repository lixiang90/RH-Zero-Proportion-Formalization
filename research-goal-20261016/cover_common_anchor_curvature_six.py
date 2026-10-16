"""Six frozen cells: fixed-direction shared cubic curvature upper bounds.

No branching, Newton contraction, direction scan, Lean, or SDP. Three
canonical DBM potentials (lower, mean, upper) are inspected per cell.
Actual positive-definite Hessian witnesses rule out a uniform negative
direction where possible. Otherwise one quantized mean-Hessian direction
is tested with one shared-gap degree-three Taylor/RLT LP. Rational scalar
remainders and rounded nonnegative LP-dual payment decide acceptance.
"""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations_with_replacement
from collections import Counter
from math import factorial,gcd
from functools import reduce
import hashlib,json,os,time
os.environ['OPENBLAS_NUM_THREADS']='1'
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix
import cover_correlated_curvature as old

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;SC=old.g.SC;DS=old.DS
OUT=HERE/'cover-common-anchor-curvature-six.json'
MON=[(i,) for i in range(9)]+list(combinations_with_replacement(range(9),2))+list(combinations_with_replacement(range(9),3))
INDEX={t:k for k,t in enumerate(MON)};N=len(MON)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def add(row,k,a):
    row[k]=row.get(k,F(0))+a
    if not row[k]:del row[k]
def product_range(bounds):
    z=[F(1)]
    for l,u in bounds:z=[a*b for a in z for b in (l,u)]
    return min(z),max(z)

class Jets:
    def __init__(self,taylor):self.taylor=taylor;self.width=SC//taylor.step
    @lru_cache(None)
    def point(self,P,derivative):
        x=F(P,2*SC);n=round(x);h=x-n
        v=self.taylor.poly(n,old.first.I(h),derivative-1)
        power=24-derivative;err=old.first.M24*abs(h)**power/factorial(power)
        return v.l-err,v.u+err
    @lru_cache(None)
    def sixth_grid(self,k):
        n=round(F(2*k+1,2*self.taylor.step))
        h=old.first.I(F(k,self.taylor.step)-n,F(k+1,self.taylor.step)-n)
        v=self.taylor.poly(n,h,5);err=old.first.M24*F(1,2)**18/factorial(18)
        return v.l-err,v.u+err
    def sixth_bound(self,l,u):
        first=l//self.width;last=(max(l+1,u)+self.width-1)//self.width
        return max(max(abs(a),abs(b)) for a,b in (self.sixth_grid(k) for k in range(first,last)))

def canonical(state,kind):
    if kind=='mean':p=[0]+[state[0][old.g.LOOK[0,j]]+state[1][old.g.LOOK[0,j]] for j in range(1,10)]
    else:p=[0]+[2*state[int(kind=='upper')][old.g.LOOK[0,j]] for j in range(1,10)]
    for z,(i,j) in enumerate(old.g.ALL):assert 2*state[0][z]<=p[j]-p[i]<=2*state[1][z]
    return p

def ldl(M):
    n=len(M);L=[[F(int(i==j)) for j in range(n)] for i in range(n)];D=[]
    for i in range(n):
        d=M[i][i]-sum(L[i][k]**2*D[k] for k in range(i))
        if d<=0:return None
        D.append(d)
        for j in range(i+1,n):L[j][i]=(M[j][i]-sum(L[j][k]*L[i][k]*D[k] for k in range(i)))/d
    assert all(M[i][j]==sum(L[i][k]*D[k]*L[j][k] for k in range(n)) for i in range(n) for j in range(n))
    return {'unit_lower':[[str(a) for a in r] for r in L],'positive_diagonal':list(map(str,D))}

def point_hessian(jets,p,free):
    vals=[jets.point(p[j]-p[i],2) for i,j,a in old.g.TERMS]
    mid=[[F(0) for _ in range(9)] for _ in range(9)];err=[[F(0) for _ in range(9)] for _ in range(9)]
    for (i,j,a),(l,u) in zip(old.g.TERMS,vals):
        for r in range(i,j):
            for s in range(i,j):mid[r][s]+=F(a,old.g.D)*(l+u)/2;err[r][s]+=F(a,old.g.D)*(u-l)/2
    pay=[sum(r) for r in err];lower=[[mid[i][j]-(pay[i] if i==j else 0) for j in range(9)] for i in range(9)]
    block=[[lower[i][j] for j in free] for i in free]
    return mid,{'prefix_twice_SC':p,'actual_w2_intervals':[[str(l),str(u)] for l,u in vals],
        'diagonal_error_payment':list(map(str,pay)),'strict_free_coordinates':free,'lower_Hessian_LDL':ldl(block),
        'minimum_midpoint_Hessian_eigenvalue_hint':float(np.linalg.eigvalsh(np.array(mid,dtype=float))[0])}

def rows_for(state,anchor,radius):
    bounds=[]
    y=[(F(state[0][i],SC)-anchor[i],F(state[1][i],SC)-anchor[i]) for i in range(9)]
    y=[(l/radius[i],u/radius[i]) for i,(l,u) in enumerate(y)]
    for m in MON:
        l,u=product_range([y[i] for i in m])
        if len(m)==2 and m[0]==m[1]:
            l=F(0) if y[m[0]][0]<=0<=y[m[0]][1] else min(z*z for z in y[m[0]])
        bounds.append((l,u))
    rows=[];rhs=[];kind=[]
    def put(row,b,k):rows.append({i:F(v) for i,v in row.items() if v});rhs.append(F(b));kind.append(k)
    base=[]
    for z,(i,j) in enumerate(old.g.ALL):
        r={k:radius[k] for k in range(i,j)};c=sum(anchor[i:j])
        base.extend([(r,F(state[1][z],SC)-c),({k:-v for k,v in r.items()},c-F(state[0][z],SC))])
    for r,b in base:
        put(r,b,'DBM')
        for s,(lo,hi) in enumerate(y):
            rr={}
            for k,a in r.items():add(rr,INDEX[tuple(sorted((k,s)))],a);add(rr,k,-lo*a)
            add(rr,s,-b);put(rr,-b*lo,'DBM_RLT_lower')
            rr={}
            for k,a in r.items():add(rr,INDEX[tuple(sorted((k,s)))],-a);add(rr,k,hi*a)
            add(rr,s,b);put(rr,b*hi,'DBM_RLT_upper')
    def mc(z,x,y):
        a,b=bounds[x];c,d=bounds[y]
        for sign,xx,yy,B in [(-1,c,a,a*c),(-1,d,b,b*d),(1,-c,-b,-b*c),(1,-d,-a,-a*d)]:
            rr={z:F(sign)};add(rr,x,-xx if sign==-1 else xx);add(rr,y,-yy if sign==-1 else yy)
            # Lower rows: -z+c*x+a*y <= a*c; upper rows: z-c*x-b*y <= -b*c.
            if sign==-1:
                rr={z:F(-1)};add(rr,x,xx);add(rr,y,yy)
            put(rr,B,'McCormick')
    for t in MON[9:54]:mc(INDEX[t],t[0],t[1])
    for t in MON[54:]:
        for s in sorted(set(t)):
            pair=list(t);pair.remove(s);mc(INDEX[t],INDEX[tuple(pair)],s)
    return rows,rhs,bounds,kind

def polynomial(jets,state,p,d):
    anchor=[F(p[i+1]-p[i],2*SC) for i in range(9)]
    radius=[max(anchor[i]-F(state[0][i],SC),F(state[1][i],SC)-anchor[i]) for i in range(9)];assert min(radius)>0
    norm=sum(a*a for a in d);C=E=F(0);coeff=[F(0)]*N;data=[]
    for i,j,aw in old.g.TERMS:
        rho=F(aw*sum(d[i:j])**2,old.g.D*norm);z=old.g.LOOK[i,j]
        P=p[j]-p[i];s0=F(P,2*SC);r=max(s0-F(state[0][z],SC),F(state[1][z],SC)-s0)
        vals=[jets.point(P,k) for k in (2,3,4,5)];m=[(l+u)/2 for l,u in vals];ee=[(u-l)/2 for l,u in vals]
        M=jets.sixth_bound(state[0][z],state[1][z]);payment=sum(ee[k]*r**k/factorial(k) for k in range(4))+M*r**4/24
        C+=rho*m[0];E+=rho*payment
        for degree in (1,2,3):
            for mon in combinations_with_replacement(range(i,j),degree):
                factor=F(factorial(degree),1)
                for mult in Counter(mon).values():factor/=factorial(mult)
                a=rho*m[degree]*factor/factorial(degree)
                for k in mon:a*=radius[k]
                coeff[INDEX[mon]]+=a
        data.append({'ij':[i,j],'rho':str(rho),'anchor_span':str(s0),'radius':str(r),
            'derivative_intervals':[[str(l),str(u)] for l,u in vals],'sixth_absolute_bound':str(M),'error_payment':str(payment)})
    return anchor,radius,C,E,coeff,data

def optimize_once(rows,rhs,bounds,c,C,E):
    scales=[max(F(1),abs(b),*(abs(v) for v in r.values())) for r,b in zip(rows,rhs)]
    rr=[];cc=[];vv=[]
    for j,(row,scale) in enumerate(zip(rows,scales)):
        for k,v in row.items():rr.append(j);cc.append(k);vv.append(float(v/scale))
    A=csr_matrix((vv,(rr,cc)),shape=(len(rows),N));b=np.array([float(v/s) for v,s in zip(rhs,scales)])
    lp=linprog(-np.array(c,dtype=float),A_ub=A,b_ub=b,bounds=[(float(l),float(u)) for l,u in bounds],method='highs',options={'time_limit':15})
    if not lp.success:return {'LP_status':int(lp.status),'message':lp.message,'strict_exclusion':False}
    quantum=10**12;dual=[max(0,round(F(str(float(-a)))*quantum/s)) for a,s in zip(lp.ineqlin.marginals,scales)]
    residual=c.copy();paid=F(0)
    for w,row,B in zip(dual,rows,rhs):
        lam=F(w,quantum);paid+=lam*B
        for k,a in row.items():residual[k]-=lam*a
    residualpay=sum(a*(u if a>=0 else l) for a,(l,u) in zip(residual,bounds))
    exact=C+E+paid+residualpay
    return {'LP_status':int(lp.status),'LP_upper_hint':float(C+E)-float(lp.fun),'LP_iterations':int(lp.nit),
        'exact_upper':str(exact),'exact_upper_hint':float(exact),'strict_exclusion':bool(exact<0),
        'dual_quantum':quantum,'nonzero_integer_dual':[[k,str(w)] for k,w in enumerate(dual) if w],
        'dual_payment':str(paid),'residual_box_payment':str(residualpay),
        'uncancelled_polynomial_coefficients':list(map(str,residual)),'raw_primal':lp.x.tolist()}

def main():
    assert not OUT.exists(),'Choose a new output; earlier packages are frozen.'
    start=time.monotonic();source=HERE/'cover-cross-moment-remaining-six.json';table=HERE/'cover_newjet.json'
    cells=json.loads(source.read_bytes())['rows'];assert len(cells)==6
    deps=[Path(__file__),source,table,Path(old.__file__),Path(old.first.__file__),
        ROOT/'research-20261016-followup/window_reweight_rational.json',ROOT/'StructuralGoal20261016/WindowSecondVariation.lean']
    guard={p.relative_to(ROOT).as_posix():sha(p) for p in deps}
    taylor=old.first.TaylorOracle(table);jets=Jets(taylor);oracle=old.CurvatureOracle(taylor)
    out={'scope':__doc__,'input_sha256':guard,'target':'11/1250','cases':[],'LP_calls':0,
        'new_cell_exclusions':0,'complete_global_cover':False,'actual_Lean_exclusion_proven':False,'new_zero_proportion_proven':False}
    for number,cell in enumerate(cells):
        state=tuple(cell['cell']);assert all(l>=old.g.SEP for l in state[0][:9])
        free=[i for i in range(9) if state[0][i]>old.g.SEP];assert free
        points=[];mats=[]
        for kind in ('mean','lower','upper'):
            M,receipt=point_hessian(jets,canonical(state,kind),free);receipt['kind']=kind;points.append(receipt);mats.append(M)
        row={'case':number,'path':cell['path'],'cell':state,'strict_free_coordinates':free,'canonical_points':points}
        blockers=[p['kind'] for p in points if p['lower_Hessian_LDL']]
        if blockers:
            row.update({'uniform_negative_direction_impossible':True,'positive_actual_Hessian_witnesses':blockers,'LP_calls':0,'strict_exclusion':False})
        else:
            eig,vec=np.linalg.eigh(np.array(mats[0],dtype=float)[np.ix_(free,free)]);v=vec[:,0]
            d=[0]*9
            for k,i in enumerate(free):d[i]=round(float(v[k]/max(abs(v)))*65536)
            common=reduce(gcd,map(abs,d));d=[a//common for a in d]
            if next(a for a in d if a)<0:d=[-a for a in d]
            norm=sum(a*a for a in d);qd=[]
            for point in points:
                lo=up=F(0)
                for (i,j,a),(l,u) in zip(old.g.TERMS,point['actual_w2_intervals']):
                    weight=F(a*sum(d[i:j])**2,old.g.D*norm);lo+=weight*F(l);up+=weight*F(u)
                qd.append([point['kind'],str(lo),str(up)])
            data=[oracle.affine(state[0][old.g.LOOK[i,j]],state[1][old.g.LOOK[i,j]]) for i,j,a in old.g.TERMS]
            oldupper,flow=old.exact_upper(state,data,d)
            anchor,radius,C,E,coeff,scalar=polynomial(jets,state,canonical(state,'mean'),d)
            constraints,rhs,bounds,kinds=rows_for(state,anchor,radius)
            result=optimize_once(constraints,rhs,bounds,coeff,C,E);out['LP_calls']+=1
            out['new_cell_exclusions']+=int(result.get('strict_exclusion',False))
            row.update({'uniform_negative_direction_impossible':False,'LP_calls':1,'direction':d,'direction_norm_squared':str(norm),
                'canonical_normalized_curvature_intervals':qd,'selected_direction_positive_at_canonical_point':any(F(l)>0 for kind,l,u in qd),
                'old_correlated_affine_upper':str(F(oldupper,2*SC*old.g.D*DS*norm)),
                'anchor_gaps':list(map(str,anchor)),'coordinate_normalization_radius':list(map(str,radius)),
                'polynomial_constant':str(C),'polynomial_error':str(E),'polynomial_coefficients':list(map(str,coeff)),
                'scalar_cubic_data':scalar,'LP_variables':N,'LP_rows':len(constraints),'LP_result':result,'strict_exclusion':result['strict_exclusion']})
        out['cases'].append(row)
        print(json.dumps({'case':number,'path':cell['path'],'SPD_blockers':blockers,
            'strict_exclusion':row['strict_exclusion'],'LP_result':{k:v for k,v in row.get('LP_result',{}).items() if k in ('LP_upper_hint','exact_upper_hint','LP_status')}}),flush=True)
    assert guard=={p.relative_to(ROOT).as_posix():sha(p) for p in deps}
    out['seconds']=time.monotonic()-start;out['sixth_grid_intervals_used']=jets.sixth_grid.cache_info().currsize
    OUT.write_text(json.dumps(out,separators=(',',':'),allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'LP_calls':out['LP_calls'],'new_cell_exclusions':out['new_cell_exclusions'],'seconds':out['seconds']}))

if __name__=='__main__':main()
