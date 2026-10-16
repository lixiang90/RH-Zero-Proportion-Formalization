"""Independent stdlib polynomial replay of the full-U model and strict toy.

Reconstruct every one of 4264 added rows and 1326 joint PSD entries by
expanding degree-two polynomials in actual y and u, then substituting the
declared moment coordinates.  No producer or optimizer is imported.
This checks the algebraic model; analytic scalar inputs remain frozen inputs.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,sys,time

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
SC=32768;V=1325
HP=[(i,j) for i in range(9) for j in range(i,9)];HI={p:50+k for k,p in enumerate(HP)}
UP=[(i,j) for i in range(41) for j in range(i,41)];UI={p:464+k for k,p in enumerate(UP)}
OUT=HERE/'cover-full-u-replay.json'


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def put(p,k,v):
    z=p.get(k,F(0))+v
    if z:p[k]=z
    else:p.pop(k,None)
def plus(p,q,s=F(1)):
    p=p.copy()
    for k,v in q.items():put(p,k,s*v)
    return p
def times(p,q):
    out={}
    for i,a in p.items():
        for j,b in q.items():put(out,tuple(sorted(i+j)),a*b)
    return out
def unpack(A):return F(A['constant']),{i:F(v) for i,v in A['coefficients']}
def formsum(a,b,s=F(1)):
    c=a[0]+s*b[0];d=a[1].copy()
    for k,v in b[1].items():put(d,k,s*v)
    return c,d
def formscale(a,s):return a[0]*s,{k:v*s for k,v in a[1].items() if v*s}


def main():
    assert not OUT.exists();began=time.monotonic()
    source=HERE/'cover-full-u-model.json';inputpath=HERE/'cover-residual-psd-rational-inputs.json'
    slabpath=HERE/'cover-residual-psd-pilot.json';dynpath=HERE/'cover-dynamic-sector-static.json'
    parampath=ROOT/'research-20261016-followup/window_reweight_rational.json'
    paths=[Path(__file__),source,inputpath,slabpath,dynpath,parampath]
    pins={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in paths}
    model=json.loads(source.read_bytes());inputs=json.loads(inputpath.read_bytes())
    slabs=json.loads(slabpath.read_bytes());dynamic=json.loads(dynpath.read_bytes());params=json.loads(parampath.read_bytes())
    for p,h in model['source_sha256_start'].items():assert sha(ROOT/p)==h
    assert model['source_sha256_start']==model['source_sha256_end'] and model['all_sources_unchanged']
    assert model['variables']==V and model['joint_PSD_size']==51 and model['all_nine_KKT_coordinates_free']
    state=inputs['cell'];assert all(l>123*SC//128 for l in state[0][:9])
    center=[F(l+u,2*SC) for l,u in zip(state[0][:9],state[1][:9])]
    radius=[F(u-l,2*SC) for l,u in zip(state[0][:9],state[1][:9])]
    ubounds=[tuple(map(F,v)) for v in inputs['u_bounds']]
    mu=[(l+u)/2 for l,u in ubounds];rad=[(u-l)/2 for l,u in ubounds];assert all(r>0 for r in rad)
    assert model['new_variable_bounds']==[[UI[e,t],'0' if e==t else '-1','1'] for e,t in UP]
    assert model['W_variable_pairs']==[[e,t,UI[e,t]] for e,t in UP]
    for e,row in enumerate(model['derivative_normalization']):
        assert list(map(F,[row['lower'],row['upper'],row['midpoint'],row['radius']]))==[ubounds[e][0],ubounds[e][1],mu[e],rad[e]]
    # Polynomial variables 0..8 are normalized y; 9..49 are physical u.
    def convert(poly):
        c=F(0);a={}
        for mon,v in poly.items():
            if not mon:c+=v
            elif len(mon)==1:
                k=mon[0]
                if k<9:c-=v*center[k]/radius[k];put(a,k,v/radius[k])
                else:put(a,k,v)
            else:
                assert len(mon)==2;k,l=mon
                if l<9:put(a,HI[k,l],v)
                elif k<9:put(a,95+41*k+(l-9),v)
                else:
                    e,t=k-9,l-9
                    put(a,UI[e,t],v*rad[e]*rad[t])
                    put(a,9+t,v*mu[e]);put(a,9+e,v*mu[t]);c-=v*mu[e]*mu[t]
        return c,a
    one={():F(1)};yp=[{(r,):F(1)} for r in range(9)]
    up=[{(9+e,):F(1)} for e in range(41)]
    vp=[{():-mu[e]/rad[e],(9+e,):1/rad[e]} for e in range(41)]
    expected=[]
    def append(A,meta):
        c,a=A;bound=-c;scale=max([abs(bound)]+list(map(abs,a.values()))) or F(1)
        expected.append({'coefficients':[[k,str(v)] for k,v in sorted(a.items())],
                         'bound':str(bound),'scale':str(scale),'meta':meta})
    for e,(slab,cone) in enumerate(zip(slabs['scalar_slabs'],dynamic['cones'])):
        for beta,upper,kind in [(list(map(F,slab['beta'])),(F(slab['epsilon'])**2,{}),'old_slab_square'),
                                (list(map(F,cone['beta'])),unpack(cone['dynamic_bottom_form']),'dynamic_sector_square')]:
            residual=up[e].copy();put(residual,(),-beta[0])
            for r in range(9):put(residual,(r,),-beta[r+1])
            append(formsum(convert(times(residual,residual)),upper,F(-1)),[kind,e])
    for e,t in UP:
        for s1 in [-1,1]:
            for s2 in [-1,1]:
                positive=times(plus(one,vp[e],F(s1)),plus(one,vp[t],F(s2)))
                append(formscale(convert(positive),F(-1)),['u_u_box_RLT',e,t,s1,s2])
    terms=[tuple(t) for t in params['a_upper'] if t[2]];den=params['denominator']
    for r in range(9):
        H={():F(params['b_numerators'][r],den)}
        for e,(i,j,aw) in enumerate(terms):
            if i<=r<j:put(H,(9+e,),F(aw,den))
        for t in range(41):
            product=convert(times(up[t],H))
            append(product,['u_multiplied_free_KKT',r,t,1]);append(formscale(product,F(-1)),['u_multiplied_free_KKT',r,t,-1])
    assert expected==model['new_linear_rows'] and len(expected)==4264
    feature=[one]+yp+vp;entries=[]
    for j in range(51):
        for i in range(j,51):
            c,a=convert(times(feature[i],feature[j]))
            entries.append([i,j,{'constant':str(c),'coefficients':[[k,str(v)] for k,v in sorted(a.items())]}])
    assert entries==model['joint_PSD_affine_entries'] and len(entries)==1326
    # Verify the strict toy using exact Schur and a separating PSD quadratic.
    toy=model['strict_toy'];assert toy['individual_Schur']=='11/100'
    z=[[F(1,2),F(2,5)],[F(1,2),F(-2,5)]]
    assert all(1-a*a-4*b*b==F(11,100) for a,b in z)
    assert min(1+s1*a+s2*b for a,b in z for s1 in [-1,1] for s2 in [-1,1])==F(1,10)
    C=F(16,5);cov=F(4,5);position_variance=F(1,4)
    lower=2*C*cov-C*C*position_variance
    assert lower==F(64,25)>2 and lower-2==F(toy['strict_contradiction_margin'])==F(14,25)
    # The Gram-minimal completion passes multiplied KKT but fails UU RLT.
    U=[[F(89,100),F(-39,100)],[F(-39,100),F(89,100)]]
    assert all(sum(U[t])-F(1,2)==0 for t in range(2)) and U[0][1]<0
    assert model['old_row_count']==43306 and model['old_row_serialization_sha256']==inputs['retained_row_serialization_sha256']
    assert not any(n.split('.')[0] in ['numpy','scipy','scs'] for n in sys.modules)
    final={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in paths};assert final==pins
    result={'scope':__doc__,'status':'full_U_polynomial_model_and_strict_toy_independently_verified',
        'path':model['path'],'source_sha256_start':pins,'source_sha256_end':final,'all_sources_unchanged':True,
        'variables':V,'new_rows_reconstructed':len(expected),'joint_PSD_entries_reconstructed':len(entries),
        'UU_box_RLT_rows':3444,'u_multiplied_KKT_equalities':369,'residual_square_upper_rows':82,
        'strict_toy_margin':'14/25','Gram_minimal_extension_not_accepted_as_UU_feasible':True,
        'optimization_packages_imported':False,'Lean_invocations':0,'cell_exclusion_proven':False,
        'elapsed_milliseconds':int((time.monotonic()-began)*1000)}
    OUT.write_text(json.dumps(result,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({k:result[k] for k in ['status','new_rows_reconstructed','joint_PSD_entries_reconstructed','elapsed_milliseconds']}),flush=True)


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
