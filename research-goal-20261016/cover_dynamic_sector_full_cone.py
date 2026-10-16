"""One fixed-cell SCS test: old residual PSD plus dynamic secant-sector PSD.

Retain the 43,304 old linear rows, two original energy packets, all boxes,
and all 41 old residual blocks.  Add exactly 41 dynamic 11x11 blocks using
the same 464 moments, old common anchor, and fixed tau=1/1024.  One solve,
<=45 seconds and <=10,000 iterations; no cuts/cases/scale or sample loop.
Solver output is discovery only, never a rational feasibility certificate.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,math,os,time,traceback
os.environ['OPENBLAS_NUM_THREADS']='1'
import cover_residual_psd_bregman_full_cone as old

np=old.np;scs=old.scs;base=old.base
csr_matrix=old.csr_matrix;csc_matrix=old.csc_matrix;hstack=old.hstack;vstack=old.vstack
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;V=464;SC=32768
OUT=HERE/'cover-dynamic-sector-full-cone.json'


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def unpackform(A):return F(A['constant']),{i:F(v) for i,v in A['coefficients']}
def sanitize(v):
    if isinstance(v,float) and not math.isfinite(v):return 'NaN' if math.isnan(v) else 'Infinity' if v>0 else '-Infinity'
    if isinstance(v,dict):return {k:sanitize(w) for k,w in v.items()}
    if isinstance(v,list):return [sanitize(w) for w in v]
    return v


def main():
    assert not OUT.exists()
    began=time.monotonic()
    priorpath=HERE/'cover-cross-moment-remaining-six.json';slabpath=HERE/'cover-residual-psd-pilot.json'
    closedpath=HERE/'cover-bregman-closed-energy-pilot.json';dynamicpath=HERE/'cover-dynamic-sector-static.json'
    proofpath=HERE/'cover-residual-psd-rational-projection.json'
    prior=json.loads(priorpath.read_bytes())['rows'][0];slabs=json.loads(slabpath.read_bytes())
    closed=json.loads(closedpath.read_bytes());dynamic=json.loads(dynamicpath.read_bytes());proof=json.loads(proofpath.read_bytes())
    assert prior['path']==slabs['path']==closed['path']==dynamic['path']==proof['path']
    assert prior['cell']==slabs['cell']==dynamic['cell']
    assert dynamic['exact_violated_cones']==7 and len(dynamic['cones'])==41
    state=prior['cell'];center=[F(l+u,2*SC) for l,u in zip(state[0][:9],state[1][:9])]
    radius=[F(u-l,2*SC) for l,u in zip(state[0][:9],state[1][:9])]
    packets=[prior['energy_packets'][0],closed['energy_packets'][1]]
    deps=[Path(__file__),priorpath,slabpath,closedpath,dynamicpath,proofpath,
          HERE/'cover_newjet.json',Path(old.__file__),Path(base.__file__),Path(base.old.__file__),
          ROOT/'research-20261016-followup/window_reweight_rational.json']
    guard={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in deps}
    out={'scope':__doc__,'path':prior['path'],'target':'11/1250','scalar_variables':V,
         'old_residual_blocks':41,'new_dynamic_sector_blocks':41,'PSD_block_sizes':[11]*82,
         'energy_packets':2,'new_scalar_positions':0,'cut_rounds':0,'SCS_calls_authorized':1,
         'solver':'SCS','solver_version':scs.__version__,'numpy_version':np.__version__,
         'scipy_version':old.scipy.__version__,'time_limit_seconds':45,'maximum_iterations':10000,
         'input_sha256_start':guard,'strict_certificate':None,'actual_Lean_exclusion':False,
         'complete_global_cover':False,'new_zero_proportion_proven':False}
    def save():
        final={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in deps};assert final==guard
        out['input_sha256_end']=final;out['all_sources_unchanged']=True
        out['seconds_hint']=time.monotonic()-began
        OUT.write_text(json.dumps(sanitize(out),separators=(',',':'),allow_nan=False)+'\n',encoding='utf8')
    out['phase']='building_original_base';save();capture={};original=base.linprog
    def intercept(c,**kw):
        capture.update(kw)
        return old.OptimizeResult(success=False,status=4,message='model capture only; no LP solve')
    base.linprog=intercept
    try:
        taylor=base.old.context.curvature.first.TaylorOracle(HERE/'cover_newjet.json')
        graph=base.old.GraphOracle(HERE/'cover_newjet.json');base.solve(state,taylor,graph,0)
    finally:base.linprog=original
    A=capture['A_ub'];b=capture['b_ub'];nr=A.shape[0];assert nr==43304
    A=hstack([A,csr_matrix((nr,1))],format='csr')
    for packet in packets:
        rr=np.zeros(V)
        for k,v in packet['row']:rr[k]=float(F(v))
        B=float(F(packet['bound']));scale=max(1.,abs(B),max(abs(rr)))
        A=vstack([A,csr_matrix(np.r_[rr/scale,-.001/scale][None,:])],format='csr');b=np.r_[b,B/scale]
    br=[];bb=[]
    for k,(l,u) in enumerate(capture['bounds']+[(0,None)]):
        if l is not None:
            rr=np.zeros(V+1);rr[k]=-1;br.append(rr);bb.append(-l)
        if u is not None:
            rr=np.zeros(V+1);rr[k]=1;br.append(rr);bb.append(u)
    A=vstack([A,csr_matrix(br)],format='csr');b=np.r_[b,bb];linearrows=len(b)
    psdrows=[];psdrhs=[];exacthash=hashlib.sha256();scales=[]
    def append(block,i,j,c,coeff,scale):
        exacthash.update(json.dumps([block,i,j,str(c),[[k,str(v)] for k,v in sorted(coeff.items())],str(scale)],separators=(',',':')).encode())
        factor=1 if i==j else np.sqrt(2);rr=np.zeros(V+1)
        for k,v in coeff.items():rr[k]=-factor*float(v*scale)
        psdrows.append(rr);psdrhs.append(factor*float(c*scale))
    for e,slab in enumerate(slabs['scalar_slabs']):
        beta=list(map(F,slab['beta']));eps=F(slab['epsilon'])
        for i,j,c,coeff in old.block_entries(e,beta,eps,center,radius):append(e,i,j,c,coeff,F(1))
    shared={(i,j):unpackform(v) for i,j,v in dynamic['shared_X_forms']}
    for e,cone in enumerate(dynamic['cones']):
        eps=F(cone['old_constant_error_normalization']);assert eps==F(slabs['scalar_slabs'][e]['epsilon'])>0
        scales.append({'term':e,'congruence_diagonal':['1']*10+[str(1/eps)],
                       'cross_multiplier':str(1/eps),'bottom_multiplier':str(1/eps**2)})
        for j in range(11):
            for i in range(j,11):
                if i<10:c,coeff=shared[j,i];scale=F(1)
                elif j==10:c,coeff=unpackform(cone['dynamic_bottom_form']);scale=1/eps**2
                else:c,coeff=unpackform(cone['cross_forms'][j]);scale=1/eps
                append(41+e,i,j,c,coeff,scale)
    AP=csr_matrix(psdrows);bp=np.array(psdrhs);assert AP.shape==(82*66,V+1)
    # Check the entire new packed map on the exact known point before solving.
    xx=np.r_[np.array(list(map(lambda v:float(F(v)),proof['projected_464_rational_moments']))),0.]
    packed=bp-AP@xx;error=0.;old_min=1e100;new_min=1e100
    X=np.array([[float(F(v)) for v in row] for row in dynamic['shared_X_value']])
    for e,cone in enumerate(dynamic['cones']):
        eps=float(F(cone['old_constant_error_normalization']))
        residual=np.array([float(F(cone['cross_forms'][r]['constant']))+
            sum(float(F(v))*xx[k] for k,v in cone['cross_forms'][r]['coefficients']) for r in range(10)])
        bottom=float(F(cone['saved_point_bottom_value']))
        expected=np.block([[X,(residual/eps)[:,None]],[(residual/eps)[None,:],np.array([[bottom/eps**2]])]])
        actual=old.unpack(packed[66*(41+e):66*(42+e)])
        error=max(error,float(np.max(abs(expected-actual))))
        old_min=min(old_min,float(np.linalg.eigvalsh(old.unpack(packed[66*e:66*(e+1)]))[0]))
        new_min=min(new_min,float(np.linalg.eigvalsh(actual)[0]))
    assert error<1e-7,error
    out.update({'old_rows':nr,'linear_rows_with_energy_and_boxes':linearrows,
         'exact_PSD_affine_map_serialization_sha256':exacthash.hexdigest(),
         'new_congruence_normalizations':scales,'old_point_packed_map_max_error_hint':error,
         'old_point_minimum_old_cone_eigenvalue_hint':old_min,'old_point_minimum_new_cone_eigenvalue_hint':new_min})
    A=csc_matrix(vstack([A,AP],format='csc'));b=np.r_[b,bp];c=np.r_[np.zeros(V),1.]
    out['phase']='single_82_cone_SCS_running';save();tick=time.monotonic()
    try:
        result=scs.solve({'A':A,'b':b,'c':c},{'l':linearrows,'s':[11]*82},
            verbose=False,time_limit_secs=45,max_iters=10000,eps_abs=1e-7,eps_rel=1e-7)
        out['solver_info']=result['info'];out['solver_seconds_hint']=time.monotonic()-tick
        out['raw_primal_hint']=result['x'].tolist();out['raw_dual_hint']=result['y'].tolist();out['raw_conic_slack_hint']=result['s'].tolist()
        xx=result['x'];out['raw_energy_slack_hint']=float(xx[-1]*.001)
        out['minimum_linear_slack_hint']=float(np.min(b[:linearrows]-A[:linearrows]@xx))
        matrices=bp-AP@xx
        eig=[float(np.linalg.eigvalsh(old.unpack(matrices[66*e:66*(e+1)]))[0]) for e in range(82)]
        out['minimum_old_cone_eigenvalue_hint']=min(eig[:41]);out['minimum_dynamic_cone_eigenvalue_hint']=min(eig[41:])
        out['all_82_minimum_eigenvalues_hint']=eig
        out['positive_energy_slack_hint']=out['raw_energy_slack_hint']>1e-7
        out['phase']='completed_single_dynamic_sector_SCS';save()
    except BaseException as exc:
        out['phase']='exception_stopped';out['exception']=repr(exc);out['traceback']=traceback.format_exc();save();raise
    print(json.dumps(sanitize({k:out[k] for k in ['phase','solver_info','solver_seconds_hint','raw_energy_slack_hint',
        'minimum_linear_slack_hint','minimum_old_cone_eigenvalue_hint','minimum_dynamic_cone_eigenvalue_hint','positive_energy_slack_hint']})),flush=True)


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
