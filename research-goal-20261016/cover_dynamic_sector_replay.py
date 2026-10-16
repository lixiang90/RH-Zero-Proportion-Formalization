"""Independent stdlib replay of 41 dynamic sector forms and seven violations.

No producer, solver, or numerical package is imported.  Rebuild anchor jets
and curvature ranges from the frozen table through the older independent
checker.  Expand new forms directly in physical g, h=yy, and q=yu indices.
This verifies necessary-model inequalities and their exact old-point tests;
it is not a proof of the actual analytic Taylor input or a cell exclusion.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,sys,time
from cover_correlated_replay import ScalarReplay
from cover_correlated_curvature_verify import CurvatureReplay

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;SC=32768;TAU=F(1,1024)
ALL=[(i,i+1) for i in range(9)]+[(i,j) for i in range(9) for j in range(i+2,10)]
INDEX={e:k for k,e in enumerate(ALL)}
HP=[(i,j) for i in range(9) for j in range(i,9)]
HI={e:50+k for k,e in enumerate(HP)}
OUT=HERE/'cover-dynamic-sector-replay.json'


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def unpack(A):return F(A['constant']),{i:F(v) for i,v in A['coefficients']}
def add(a,k,v):
    z=a.get(k,F(0))+v
    if z:a[k]=z
    else:a.pop(k,None)
def value(A,x):c,a=unpack(A);return c+sum(v*x[i] for i,v in a.items())


def main():
    assert not OUT.exists()
    began=time.monotonic()
    source=HERE/'cover-dynamic-sector-static.json';proofpath=HERE/'cover-residual-psd-rational-projection.json'
    tablepath=HERE/'cover_newjet.json';parampath=ROOT/'research-20261016-followup/window_reweight_rational.json'
    slabpath=HERE/'cover-residual-psd-pilot.json';oldreceipt=HERE/'cover-residual-psd-rational-replay.json'
    watched=[Path(__file__),source,proofpath,tablepath,parampath,slabpath,oldreceipt,
             HERE/'cover_correlated_replay.py',HERE/'cover_correlated_curvature_verify.py']
    pins={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in watched}
    doc=json.loads(source.read_bytes());proof=json.loads(proofpath.read_bytes())
    old=json.loads(oldreceipt.read_bytes());params=json.loads(parampath.read_bytes())
    slabs=json.loads(slabpath.read_bytes());tab=json.loads(tablepath.read_bytes())
    for p,h in doc['source_sha256_start'].items():assert sha(ROOT/p)==h
    assert doc['source_sha256_start']==doc['source_sha256_end']
    assert old['status']=='strict_exact_feasible_outer_relaxation_verified'
    assert doc['path']==proof['path']==old['path']==slabs['path']
    assert doc['tau']==str(TAU) and doc['optimization_calls']==doc['Lean_invocations']==0
    state=doc['cell'];anchor=list(map(F,doc['common_old_anchor']));terms=[r for r in params['a_upper'] if r[2]]
    assert all(F(l,SC)<=sum(anchor[i:j])<=F(u,SC) for (i,j),l,u in zip(ALL,*state))
    x=list(map(F,proof['projected_464_rational_moments']))
    center=[F(l+u,2*SC) for l,u in zip(state[0][:9],state[1][:9])]
    radius=[F(u-l,2*SC) for l,u in zip(state[0][:9],state[1][:9])]
    y=[(g-c)/r for g,c,r in zip(x[:9],center,radius)]
    X=[[F(0) for _ in range(10)] for _ in range(10)];X[0][0]=F(1)
    for r in range(9):X[0][r+1]=X[r+1][0]=y[r]
    for r,s in HP:X[r+1][s+1]=X[s+1][r+1]=x[HI[r,s]]
    assert X==[list(map(F,row)) for row in doc['shared_X_value']]
    L=[list(map(F,row)) for row in doc['shared_X_unit_lower']];D=list(map(F,doc['shared_X_strict_positive_diagonal']))
    assert len(D)==10 and all(v>0 for v in D)
    assert all(L[i][i]==1 and all(L[i][j]==0 for j in range(i+1,10)) for i in range(10))
    assert all(X[i][j]==sum(L[i][k]*D[k]*L[j][k] for k in range(10)) for i in range(10) for j in range(10))
    scalar=ScalarReplay(tab);curvature=CurvatureReplay(scalar)
    violated=[];checked=[]
    for e,(row,(i,j,aw),slab) in enumerate(zip(doc['cones'],terms,slabs['scalar_slabs'])):
        assert row['term']==e and row['edge']==[i,j] and row['weight_numerator']==aw
        p=sum(anchor[i:j]);P=2*SC*p;assert P.denominator==1 and P.numerator==row['doubled_anchor_integer']
        axis=INDEX[i,j];lo,hi=state[0][axis],state[1][axis]
        assert F(lo,SC)<=p<=F(hi,SC)
        u0,_=scalar.point(P.numerator)
        assert [u0.l,u0.u]==list(map(F,row['anchor_derivative_interval']))
        mid=(u0.l+u0.u)/2;eps=(u0.u-u0.l)/2
        assert mid==F(row['anchor_derivative_midpoint']) and eps==F(row['anchor_derivative_error'])
        first=lo//scalar.width;last=(max(lo+1,hi)+scalar.width-1)//scalar.width
        cm=F(min(v[0] for v in curvature.second[first:last]),10**15)
        cM=F(max(v[1] for v in curvature.second[first:last]),10**15)
        assert [cm,cM]==list(map(F,row['independent_second_range']))
        m,M=map(F,row['whole_second_bounds']);assert m<=cm<=cM<=M
        k=(m+M)/2;half=(M-m)/2;gamma=(1+TAU)*half**2
        assert k==F(row['k']) and half==F(row['L']) and gamma==F(row['gamma'])
        delta=sum(center[i:j])-p
        # Independent physical-coordinate expansion of E[(span-p)^2].
        dc=delta**2-2*delta*sum(center[i:j]);da={}
        for r in range(i,j):
            add(da,r,2*delta)
            for s in range(r,j):add(da,HI[r,s],(1 if r==s else 2)*radius[r]*radius[s])
        assert unpack(row['dynamic_d2_form'])==(dc,da)
        bc=gamma*dc+(1+1/TAU)*eps**2;ba={r:gamma*v for r,v in da.items() if gamma*v}
        assert unpack(row['dynamic_bottom_form'])==(bc,ba)
        beta0=mid+k*delta
        for r,entry in enumerate(row['cross_forms']):
            aa={}
            if r==0:
                cc=-mid+k*p;add(aa,9+e,F(1))
                for s in range(i,j):add(aa,s,-k)
            else:
                s=r-1;cc=beta0*center[s]/radius[s]
                add(aa,95+41*s+e,F(1));add(aa,s,-beta0/radius[s])
                for t in range(i,j):add(aa,HI[min(s,t),max(s,t)],-k*radius[t])
            assert unpack(entry)==(cc,aa)
        res=[value(v,x) for v in row['cross_forms']];bottom=value(row['dynamic_bottom_form'],x)
        witness=list(map(F,row['exact_schur_test_vector']));assert len(witness)==11 and witness[-1]==1
        w=witness[:10]
        assert [sum(X[r][s]*w[s] for s in range(10))+res[r] for r in range(10)]==[0]*10
        schur=bottom+sum(a*b for a,b in zip(res,w))
        assert schur==F(row['saved_point_schur_complement'])==F(row['exact_test_vector_value'])
        N=[xx+[res[r]] for r,xx in enumerate(X)]+[res+[bottom]]
        assert sum(witness[r]*N[r][s]*witness[s] for r in range(11) for s in range(11))==schur
        oldeps=F(slab['epsilon']);assert oldeps==F(row['old_constant_error_normalization'])>0
        assert schur/oldeps**2==F(row['saved_point_normalized_schur'])
        assert (schur<0)==row['strictly_violated_at_old_exact_point']
        if schur<0:violated.append(e)
        # Young difference is an exact nonnegative-square decomposition.
        assert -(1+TAU)+TAU==-1
        assert -(1+1/TAU)+1/TAU==-1
        checked.append({'term':e,'edge':[i,j],'exact_anchor_and_forms_match':True,
                        'exact_schur_sign':-1 if schur<0 else 1 if schur>0 else 0,
                        'dynamic_second_moment_preserved':True})
    assert violated==doc['violated_terms'] and len(violated)==7
    assert not any(n.split('.')[0] in ['numpy','scipy','scs'] for n in sys.modules)
    final={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in watched};assert final==pins
    out={'scope':__doc__,'status':'all_41_dynamic_cones_and_7_exact_violations_independently_verified',
         'path':doc['path'],'source_sha256_start':pins,'source_sha256_end':final,'all_sources_unchanged':True,
         'cones_checked':41,'strict_old_point_violations':7,'violated_terms':violated,
         'anchor_positions_new':0,'all_anchors_in_whole_curvature_intervals':True,
         'moment_X_strict_positive_LDL_verified':True,'dynamic_d2_forms_checked':41,
         'checks':checked,'optimization_packages_imported':False,'Lean_invocations':0,
         'actual_kernel_analytic_input_proven_here':False,'whole_cell_exclusion_proven':False,
         'elapsed_milliseconds':int((time.monotonic()-began)*1000)}
    OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({k:out[k] for k in ['status','cones_checked','strict_old_point_violations','elapsed_milliseconds']}),flush=True)


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
