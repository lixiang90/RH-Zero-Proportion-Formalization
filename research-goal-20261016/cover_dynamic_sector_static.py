"""Exact dynamic secant-sector cones at the sealed rational relaxation point.

Static only: no optimization package, solver, new scalar position, or Lean.
Reuse the old common energy anchor and the same integer Taylor table.  The
bottom of each cone is gamma*E[(span-p)^2]+1025*epsilon0^2, not a radius max.
Actual-kernel analytic validity of the frozen Taylor input remains explicit.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import hashlib,json,sys,time

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
SC=32768;DS=10**15;V=464;TAU=F(1,1024)
ALL=[(i,i+1) for i in range(9)]+[(i,j) for i in range(9) for j in range(i+2,10)]
LOOK={e:k for k,e in enumerate(ALL)}
HP=[(i,j) for i in range(9) for j in range(i,9)]
HI={e:50+k for k,e in enumerate(HP)}
OUT=HERE/'cover-dynamic-sector-static.json'


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


class J:
    def __init__(self,l,u=None):self.l=F(l);self.u=F(l if u is None else u);assert self.l<=self.u
    def __add__(self,x):
        if not isinstance(x,J):x=J(x)
        return J(self.l+x.l,self.u+x.u)
    __radd__=__add__
    def __mul__(self,x):
        if not isinstance(x,J):x=J(x)
        values=[self.l*x.l,self.l*x.u,self.u*x.l,self.u*x.u]
        return J(min(values),max(values))
    __rmul__=__mul__


def floor(x):return x.numerator//x.denominator
def ceil(x):return -floor(-x)


class Table:
    """Small independent interval-Horner replay at existing anchors/cells."""
    def __init__(self,doc):
        self.cs={int(n):[J(l,u) for l,u in row] for n,row in doc['integer_taylor_coefficients'].items()}
        self.step=doc['receipt']['grid_step'];self.width=SC//self.step
        self.M=F(44,7)**24;self.second={}
        assert self.step==64 and doc['receipt']['order']==24
    def poly(self,n,x,derivative):
        value=J(0)
        for k in range(len(self.cs[n])-1,derivative-1,-1):
            value=value*x+self.cs[n][k]*F(factorial(k),factorial(k-derivative))
        return value
    def derivative_point(self,P):
        p=F(P,2*SC);n=round(p);x=p-n
        v=self.poly(n,J(x),0);rem=self.M*abs(x)**23/factorial(23)
        return J(v.l-rem,v.u+rem)
    def second_grid(self,k):
        if k not in self.second:
            n=round(F(2*k+1,2*self.step))
            x=J(F(k,self.step)-n,F(k+1,self.step)-n)
            value=self.poly(n,x,1);rem=self.M*F(1,2)**22/factorial(22)
            self.second[k]=(floor((value.l-rem)*DS),ceil((value.u+rem)*DS))
        return self.second[k]
    def second_range(self,l,u):
        assert 0<=l<=u<=32*SC
        rows=[self.second_grid(k) for k in range(l//self.width,(max(l+1,u)+self.width-1)//self.width)]
        return F(min(v[0] for v in rows),DS),F(max(v[1] for v in rows),DS)


def form(c=0,a=None):return [F(c),{} if a is None else {k:F(v) for k,v in a.items() if v}]
def add(A,B,scale=F(1)):
    c=A[0]+scale*B[0];a=A[1].copy()
    for k,v in B[1].items():
        z=a.get(k,F(0))+scale*v
        if z:a[k]=z
        else:a.pop(k,None)
    return [c,a]
def mul(A,v):return [A[0]*v,{k:c*v for k,c in A[1].items() if c*v}]
def val(A,x):return A[0]+sum(v*x[k] for k,v in A[1].items())
def pack(A):return {'constant':str(A[0]),'coefficients':[[k,str(v)] for k,v in sorted(A[1].items())]}
def dot(a,b):return sum(x*y for x,y in zip(a,b))


def ldl(A):
    n=len(A);L=[[F(i==j) for j in range(n)] for i in range(n)];D=[]
    for j in range(n):
        d=A[j][j]-sum(L[j][k]**2*D[k] for k in range(j));assert d>0
        D.append(d)
        for i in range(j+1,n):L[i][j]=(A[i][j]-sum(L[i][k]*D[k]*L[j][k] for k in range(j)))/d
    assert all(A[i][j]==sum(L[i][k]*D[k]*L[j][k] for k in range(n)) for i in range(n) for j in range(n))
    return L,D


def solve_ldl(L,D,b):
    n=len(D);q=[]
    for i in range(n):q.append(b[i]-sum(L[i][j]*q[j] for j in range(i)))
    q=[x/d for x,d in zip(q,D)];ans=[F(0)]*n
    for i in range(n-1,-1,-1):ans[i]=q[i]-sum(L[j][i]*ans[j] for j in range(i+1,n))
    return ans


def main():
    assert not OUT.exists(),'Preserve existing static receipts.'
    began=time.monotonic()
    proofpath=HERE/'cover-residual-psd-rational-projection.json'
    inputpath=HERE/'cover-residual-psd-rational-inputs.json'
    priorpath=HERE/'cover-cross-moment-remaining-six.json'
    reversepath=HERE/'cover-reverse-taylor-pilot.json'
    slabpath=HERE/'cover-residual-psd-pilot.json'
    tablepath=HERE/'cover_newjet.json'
    parampath=ROOT/'research-20261016-followup/window_reweight_rational.json'
    sealpath=HERE/'cover-residual-psd-rational-files.json'
    watched=[Path(__file__),proofpath,inputpath,priorpath,reversepath,slabpath,tablepath,parampath,sealpath]
    pins={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in watched}
    assert sha(sealpath)=='5995d2ba510e40e31edbd17d3337a4f39c89acc62e209c016b0d584464714c6b'
    proof=json.loads(proofpath.read_bytes());inputs=json.loads(inputpath.read_bytes())
    prior=json.loads(priorpath.read_bytes())['rows'][0];reverse=json.loads(reversepath.read_bytes())
    slabs=json.loads(slabpath.read_bytes());params=json.loads(parampath.read_bytes());table_doc=json.loads(tablepath.read_bytes())
    assert proof['status']=='strict_exact_feasible_relaxation_point'
    assert proof['path']==inputs['path']==prior['path']==reverse['path']==slabs['path']
    assert proof['retained_row_serialization_sha256']==inputs['retained_row_serialization_sha256']
    assert table_doc['receipt']['parameter_sha256']==sha(parampath)
    state=inputs['cell'];assert state==prior['cell']
    packet=prior['energy_packets'][0];anchor=list(map(F,packet['centre']))
    assert packet['centre']==reverse['energy_packets'][1]['centre']
    assert all(F(l,SC)<=sum(anchor[i:j])<=F(u,SC) for (i,j),l,u in zip(ALL,*state))
    terms=[tuple(t) for t in params['a_upper'] if t[2]];assert len(terms)==41
    x=list(map(F,proof['projected_464_rational_moments']));assert len(x)==V
    center=[F(l+u,2*SC) for l,u in zip(state[0][:9],state[1][:9])]
    radius=[F(u-l,2*SC) for l,u in zip(state[0][:9],state[1][:9])];assert all(r>0 for r in radius)
    X=[[form() for j in range(10)] for i in range(10)];X[0][0]=form(1)
    for r in range(9):X[0][r+1]=X[r+1][0]=form(-center[r]/radius[r],{r:1/radius[r]})
    for r,s in HP:X[r+1][s+1]=X[s+1][r+1]=form(0,{HI[r,s]:1})
    XV=[[val(v,x) for v in row] for row in X];LL,DD=ldl(XV)
    oracle=Table(table_doc);rows=[];violations=[]
    for e,(i,j,aw) in enumerate(terms):
        axis=LOOK[i,j];lo,hi=state[0][axis],state[1][axis]
        p=sum(anchor[i:j]);P=2*SC*p;assert P.denominator==1
        assert F(lo,SC)<=p<=F(hi,SC)
        u0=oracle.derivative_point(P.numerator)
        u0mid=(u0.l+u0.u)/2;eps=(u0.u-u0.l)/2;assert eps>=0
        actual_m,actual_M=oracle.second_range(lo,hi)
        m,M=map(F,reverse['energy_packets'][1]['whole_span_second_bounds'][e])
        assert m==F(packet['whole_span_second_lower'][e])
        assert m<=actual_m<=actual_M<=M
        k=(m+M)/2;halfwidth=(M-m)/2;gamma=(1+TAU)*halfwidth**2
        delta0=sum(center[i:j])-p
        beta=[u0mid+k*delta0]+[k*radius[r] if i<=r<j else F(0) for r in range(9)]
        z=[form(0,{9+e:1})]+[form(0,{95+41*r+e:1}) for r in range(9)]
        cross=[]
        for r in range(10):
            v=z[r]
            for s in range(10):v=add(v,X[r][s],-beta[s])
            cross.append(v)
        # Exact old-lift expression for E[d^2], retaining its actual moment.
        dvec=[delta0]+[radius[r] if i<=r<j else F(0) for r in range(9)]
        d2=form()
        for r in range(10):
            for s in range(10):d2=add(d2,X[r][s],dvec[r]*dvec[s])
        bottom=add(mul(d2,gamma),form((1+1/TAU)*eps**2))
        # Verify factorized identities at the old shared anchor and box center.
        factorization=[]
        for gpoint in [anchor,center]:
            yy=[(g-c)/r for g,c,r in zip(gpoint,center,radius)]
            actual=[F(0)]*V;actual[:9]=gpoint;actual[9+e]=F(3,17)
            for r,s in HP:actual[HI[r,s]]=yy[r]*yy[s]
            for r in range(9):actual[95+41*r+e]=yy[r]*actual[9+e]
            eta=actual[9+e]-u0mid-k*(sum(gpoint[i:j])-p)
            xx=[F(1)]+yy
            assert val(d2,actual)==(sum(gpoint[i:j])-p)**2
            assert [val(v,actual) for v in cross]==[a*eta for a in xx]
            assert val(bottom,actual)==gamma*(sum(gpoint[i:j])-p)**2+(1+1/TAU)*eps**2
            factorization.append(True)
        residual=[val(v,x) for v in cross];bottom_value=val(bottom,x)
        solution=solve_ldl(LL,DD,residual)
        assert [dot(row,solution) for row in XV]==residual
        schur=bottom_value-dot(residual,solution)
        oldeps=F(slabs['scalar_slabs'][e]['epsilon']);assert oldeps>0
        witness=[-v for v in solution]+[F(1)]
        N=[row+[residual[r]] for r,row in enumerate(XV)]+[residual+[bottom_value]]
        value=sum(witness[r]*N[r][s]*witness[s] for r in range(11) for s in range(11))
        assert value==schur
        normalized_schur=schur/oldeps**2
        row={'term':e,'edge':[i,j],'weight_numerator':aw,'span_axis':axis,
             'span_interval':[str(F(lo,SC)),str(F(hi,SC))],
             'anchor_span':str(p),'doubled_anchor_integer':P.numerator,
             'anchor_in_whole_span_interval':True,'anchor_derived_from_shared_old_point':True,
             'anchor_derivative_interval':[str(u0.l),str(u0.u)],
             'anchor_derivative_midpoint':str(u0mid),'anchor_derivative_error':str(eps),
             'whole_second_bounds':[str(m),str(M)],'independent_second_range':[str(actual_m),str(actual_M)],
             'k':str(k),'L':str(halfwidth),'tau':str(TAU),'gamma':str(gamma),
             'beta':list(map(str,beta)),'d_vector_in_1_y':list(map(str,dvec)),
             'dynamic_d2_form':pack(d2),'dynamic_bottom_form':pack(bottom),
             'cross_forms':[pack(v) for v in cross],
             'factorized_anchor_and_center_checks':factorization,
             'saved_point_d2_value':str(val(d2,x)),
             'saved_point_bottom_value':str(bottom_value),
             'saved_point_schur_complement':str(schur),
             'old_constant_error_normalization':str(oldeps),
             'saved_point_normalized_schur':str(normalized_schur),
             'saved_point_normalized_schur_hint':float(normalized_schur),
             'strictly_violated_at_old_exact_point':schur<0,
             'exact_schur_test_vector':list(map(str,witness)),
             'exact_test_vector_value':str(value)}
        rows.append(row)
        if schur<0:violations.append(e)
    assert not any(n.split('.')[0] in ['numpy','scipy','scs'] for n in sys.modules)
    final={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in watched};assert final==pins
    out={'scope':__doc__,'status':'all_41_exact_dynamic_cones_built_and_statically_checked',
         'path':prior['path'],'cell':state,'common_old_anchor':list(map(str,anchor)),
         'anchor_feasible_for_all_45_spans':True,'new_scalar_positions':0,
         'old_Taylor_table_reused_at_existing_common_anchor':True,'tau':str(TAU),
         'source_sha256_start':pins,'source_sha256_end':final,'all_sources_unchanged':True,
         'moment_dimension':V,'cone_size':11,'cones':rows,'violated_terms':violations,
         'exact_violated_cones':len(violations),'minimum_normalized_schur_hint':min(r['saved_point_normalized_schur_hint'] for r in rows),
         'shared_X_forms':[[i,j,pack(X[i][j])] for i in range(10) for j in range(i,10)],
         'shared_X_value':[[str(v) for v in row] for row in XV],
         'shared_X_unit_lower':[[str(v) for v in row] for row in LL],
         'shared_X_strict_positive_diagonal':list(map(str,DD)),
         'second_grid_cells_rebuilt':len(oracle.second),'optimization_calls':0,'Lean_invocations':0,
         'actual_kernel_analytic_inputs_proved_here':False,'whole_cell_exclusion_proven':False,
         'complete_global_cover':False,'new_zero_proportion_proven':False,
         'elapsed_milliseconds':int((time.monotonic()-began)*1000)}
    OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'status':out['status'],'cones':41,'exact_violated_cones':len(violations),
        'minimum_normalized_schur_hint':out['minimum_normalized_schur_hint'],
        'first_violated_edges':[rows[e]['edge'] for e in violations[:8]],
        'second_grid_cells_rebuilt':len(oracle.second),'elapsed_milliseconds':out['elapsed_milliseconds']},indent=2),flush=True)


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
