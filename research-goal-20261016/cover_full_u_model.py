"""Exact 1325-variable full derivative-moment model, before one conic pilot.

Add all 861 derivative cross moments, box-product RLT, and 369 free-KKT
products.  A full 51x51 joint PSD and 82 residual-square upper rows imply
both frozen families of 41 independent cones.  Cross moments are retained;
the minimal Gram extension is used only for an explicitly limited diagnostic.
No solver, actual scalar evaluation, or Lean invocation occurs here.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,sys,time
import cover_cross_moment_exact_rows as exact
from cover_dynamic_sector_static import form,add,mul,pack,val,dot,ldl,solve_ldl

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
OLDV=464;V=1325;SC=32768
UP=[(i,j) for i in range(41) for j in range(i,41)]
UI={p:OLDV+k for k,p in enumerate(UP)}
OUT=HERE/'cover-full-u-model.json'


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def unpack(A):return [F(A['constant']),{i:F(v) for i,v in A['coefficients']}]
def unit(k):return form(0,{k:1})
def windex(e,t):return UI[min(e,t),max(e,t)]


def main():
    assert not OUT.exists()
    began=time.monotonic()
    inputpath=HERE/'cover-residual-psd-rational-inputs.json'
    proofpath=HERE/'cover-residual-psd-rational-projection.json'
    slabpath=HERE/'cover-residual-psd-pilot.json';dynamicpath=HERE/'cover-dynamic-sector-static.json'
    parampath=ROOT/'research-20261016-followup/window_reweight_rational.json'
    sealpath=HERE/'cover-dynamic-sector-files.json'
    paths=[Path(__file__),inputpath,proofpath,slabpath,dynamicpath,parampath,sealpath,
           Path(exact.__file__),HERE/'cover_dynamic_sector_static.py']
    pins={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in paths}
    assert sha(sealpath)=='7ae3208f705a7fec9ca0796ff47f7c23426356c7b140e6920933be8048e28922'
    inputs=json.loads(inputpath.read_bytes());proof=json.loads(proofpath.read_bytes())
    slabs=json.loads(slabpath.read_bytes());dynamic=json.loads(dynamicpath.read_bytes());params=json.loads(parampath.read_bytes())
    assert inputs['path']==proof['path']==slabs['path']==dynamic['path']
    state=inputs['cell'];assert all(l>123*SC//128 for l in state[0][:9])
    terms=[tuple(t) for t in params['a_upper'] if t[2]];assert len(terms)==41 and len(UP)==861
    b=[F(v,params['denominator']) for v in params['b_numerators']]
    aw=[F(v,params['denominator']) for _,_,v in terms]
    ubounds=[tuple(map(F,v)) for v in inputs['u_bounds']]
    mu=[(l+u)/2 for l,u in ubounds];rad=[(u-l)/2 for l,u in ubounds];assert all(a>0 for a in rad)
    mv=[form(-m/a,{9+e:1/a}) for e,(m,a) in enumerate(zip(mu,rad))]
    X=[[form() for j in range(10)] for i in range(10)]
    for i,j,entry in dynamic['shared_X_forms']:X[i][j]=X[j][i]=unpack(entry)
    z=[[unit(9+e)]+[unit(95+41*r+e) for r in range(9)] for e in range(41)]
    def physical_U(e,t):
        ans=form(-mu[e]*mu[t],{windex(e,t):rad[e]*rad[t]})
        return add(add(ans,unit(9+t),mu[e]),unit(9+e),mu[t])
    def residual_square(e,beta):
        ans=physical_U(e,e)
        for i in range(10):
            ans=add(ans,z[e][i],-2*beta[i])
            for j in range(10):ans=add(ans,X[i][j],beta[i]*beta[j])
        return ans
    rows=[]
    def append(lhs,kind):
        cc,aa=lhs;bound=-cc
        scale=max([abs(bound)]+list(map(abs,aa.values())))
        if not scale:scale=F(1)
        rows.append({'coefficients':[[k,str(v)] for k,v in sorted(aa.items())],
                     'bound':str(bound),'scale':str(scale),'meta':kind})
    for e,(slab,cone) in enumerate(zip(slabs['scalar_slabs'],dynamic['cones'])):
        append(add(residual_square(e,list(map(F,slab['beta']))),form(F(slab['epsilon'])**2),F(-1)),['old_slab_square',e])
        append(add(residual_square(e,list(map(F,cone['beta']))),unpack(cone['dynamic_bottom_form']),F(-1)),['dynamic_sector_square',e])
    # Every four box-product RLT inequalities are retained, including diagonal.
    for e,t in UP:
        for s1 in [-1,1]:
            for s2 in [-1,1]:
                lhs=form(-1,{windex(e,t):-s1*s2})
                lhs=add(add(lhs,mv[e],-s1),mv[t],-s2)
                append(lhs,['u_u_box_RLT',e,t,s1,s2])
    kkt_forms=[]
    for r in range(9):
        inc=[e for e,(i,j,_) in enumerate(terms) if i<=r<j]
        for t in range(41):
            lhs=mul(unit(9+t),b[r])
            for e in inc:lhs=add(lhs,physical_U(t,e),aw[e])
            kkt_forms.append((r,t,lhs))
            append(lhs,['u_multiplied_free_KKT',r,t,1]);append(mul(lhs,F(-1)),['u_multiplied_free_KKT',r,t,-1])
    assert len(rows)==82+4*861+2*369
    # Full joint PSD of (1,y,v), v=(u-mu)/rad; W is E[v v^T].
    joint=[]
    for j in range(51):
        for i in range(j,51):
            if i<10:entry=X[i][j]
            elif j>=10:entry=unit(windex(i-10,j-10))
            else:
                e=i-10
                entry=mul(add(z[e][j],X[j][0],-mu[e]),1/rad[e])
            joint.append([i,j,pack(entry)])
    assert len(joint)==1326
    old=exact.inputs(state,inputs['old_integer_rows'],inputs['old_meta'],inputs['u_bounds'],inputs['energy_packets'])
    digest=hashlib.sha256()
    for row in old['rows']:
        digest.update(json.dumps([sorted((i,str(v)) for i,v in row['coeff'].items()),str(row['bound']),row['meta']],separators=(',',':')).encode())
    assert digest.hexdigest()==inputs['retained_row_serialization_sha256']==proof['retained_row_serialization_sha256']
    # Actual-point polynomial factorization checks, including all new U products.
    center=old['center'];radius=old['radius'];identities=0
    for yy in [[F(0)]*9,[F((3*r)%7-3,5) for r in range(9)]]:
        actual=[F(0)]*V;actual[:9]=[c+a*y for c,a,y in zip(center,radius,yy)]
        vv=[F((5*e)%17-8,10) for e in range(41)]
        actual[9:50]=[m+a*v for m,a,v in zip(mu,rad,vv)]
        for r,s in exact.PAIRS:actual[exact.hindex(r,s)]=yy[r]*yy[s]
        for r in range(9):
            for e in range(41):actual[exact.qindex(r,e)]=yy[r]*actual[9+e]
        for e,t in UP:actual[windex(e,t)]=vv[e]*vv[t]
        feat=[F(1)]+yy+vv
        for i,j,entry in joint:assert val(unpack(entry),actual)==feat[i]*feat[j];identities+=1
        for e,t in UP:assert val(physical_U(e,t),actual)==actual[9+e]*actual[9+t];identities+=1
        for r,t,lhs in kkt_forms:
            H=b[r]+sum(aw[e]*actual[9+e] for e,(i,j,_) in enumerate(terms) if i<=r<j)
            assert val(lhs,actual)==actual[9+t]*H;identities+=1
    # Strict algebraic toy beyond independent residual cones plus y-u RLT.
    toyX=[[F(1),F(0)],[F(0),F(1,4)]];toyZ=[[F(1,2),F(2,5)],[F(1,2),F(-2,5)]]
    assert all(1-z[0]**2-4*z[1]**2==F(11,100) for z in toyZ)
    assert all(1+s1*z[0]+s2*z[1]>=F(1,10) for z in toyZ for s1 in [-1,1] for s2 in [-1,1])
    toy_lower=F(64,25);toy_upper=F(2);assert toy_lower>toy_upper
    # Limited diagnostic: exact old 464 point under OLD 41 slab cones only.
    # Dynamic sector already excludes this point, so no extension is claimed.
    px=list(map(F,proof['projected_464_rational_moments']));XV=[[val(a,px) for a in row] for row in X]
    LL,DD=ldl(XV);C=[];sol=[]
    for e in range(41):
        col=[val(mul(add(z[e][r],X[r][0],-mu[e]),1/rad[e]),px) for r in range(10)]
        C.append(col);sol.append(solve_ldl(LL,DD,col))
    Wmin=[[dot(C[e],sol[t]) for t in range(41)] for e in range(41)]
    cap=[];means=[val(a,px) for a in mv]
    for e,slab in enumerate(slabs['scalar_slabs']):
        beta=list(map(F,slab['beta']));zz=[val(v,px) for v in z[e]]
        ucap=F(slab['epsilon'])**2+2*dot(beta,zz)-sum(beta[r]*XV[r][s]*beta[s] for r in range(10) for s in range(10))
        wc=(ucap-2*mu[e]*px[9+e]+mu[e]**2)/rad[e]**2
        cap.append(min(F(1),wc));assert cap[-1]>=Wmin[e][e]
    minimal_violations=[];pair_obstructions=[]
    for e,t in UP:
        lower=abs(means[e]+means[t])-1;upper=1-abs(means[e]-means[t]);q=Wmin[e][t]
        if not lower<=q<=upper:minimal_violations.append([e,t,str(q),str(lower),str(upper)])
        gap=lower-q if q<lower else q-upper if q>upper else F(0)
        room=(cap[e]-Wmin[e][e])*(cap[t]-Wmin[t][t])
        if gap>0 and gap**2>room:
            pair_obstructions.append({'edges':[e,t],'signed_gap':str(gap),'squared_gap':str(gap**2),'maximum_room_product':str(room)})
    final={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in paths};assert final==pins
    result={'scope':__doc__,'status':'exact_full_U_model_built_no_solver','path':inputs['path'],'cell':state,
        'source_sha256_start':pins,'source_sha256_end':final,'all_sources_unchanged':True,
        'old_variables':OLDV,'new_derivative_cross_variables':861,'variables':V,'joint_PSD_size':51,
        'all_nine_KKT_coordinates_free':True,'derivative_normalization':[
            {'term':e,'lower':str(l),'upper':str(u),'midpoint':str(mu[e]),'radius':str(rad[e])}
            for e,(l,u) in enumerate(ubounds)],
        'U_from_normalized_W_formula':'U_e,t=rad_e*rad_t*W_e,t+mu_e*u_t+mu_t*u_e-mu_e*mu_t',
        'W_variable_pairs':[[e,t,windex(e,t)] for e,t in UP],
        'new_variable_bounds':[[windex(e,t),'0' if e==t else '-1','1'] for e,t in UP],
        'new_linear_rows':rows,'joint_PSD_affine_entries':joint,
        'old_row_count':len(old['rows']),'old_row_serialization_sha256':digest.hexdigest(),
        'row_counts':{'old_slab_square':41,'dynamic_sector_square':41,'u_u_box_RLT':3444,'u_multiplied_KKT_equalities':369,'u_multiplied_KKT_inequality_rows':738},
        'old_82_cones_logically_implied_by_joint_PSD_and_square_rows':True,
        'actual_point_factorization_identities_checked':identities,
        'strict_toy':{'X':[[str(v) for v in row] for row in toyX],'z':[[str(v) for v in row] for row in toyZ],
            'individual_cone_bottom':'1','individual_Schur':'11/100','minimum_box_RLT_slack':'1/10',
            'joint_PSD_difference_square_lower':str(toy_lower),'UU_RLT_difference_square_upper':str(toy_upper),
            'strict_contradiction_margin':str(toy_lower-toy_upper),
            'minimal_Gram_offdiagonal':'-39/100','required_UU_RLT_lower':'0'},
        'old_point_diagnostic':{'scope':'old41 only; dynamic cones already exclude this old point. No U extension claimed.',
            'minimal_Gram_RLT_violations':minimal_violations,'pairwise_Cauchy_completion_obstructions':pair_obstructions,
            'minimum_Gram_diagonal_room':str(min(cap[e]-Wmin[e][e] for e in range(41)))},
        'solver_calls':0,'Lean_invocations':0,'cell_exclusion_proven':False,'new_zero_proportion_proven':False,
        'elapsed_milliseconds':int((time.monotonic()-began)*1000)}
    assert not any(n.split('.')[0] in ['numpy','scipy','scs'] for n in sys.modules)
    OUT.write_text(json.dumps(result,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'variables':V,'new_rows':len(rows),'joint_PSD_size':51,'strict_toy_margin':str(toy_lower-toy_upper),
        'old_point_minimal_Gram_RLT_violations':len(minimal_violations),'old_point_pair_completion_obstructions':len(pair_obstructions),
        'elapsed_milliseconds':result['elapsed_milliseconds']}),flush=True)


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
