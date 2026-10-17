"""One bounded shared-quartic cone with the complete eight swap rows.

714 shared gap moments plus one energy slack.  Geometry, cubic-Taylor KKT
and the old quadratic sublevel localizer remain unsoftened. The eight
global-competitor rows are also unsoftened. Original rows/PSD unchanged.
One call to
SCS, <=45 seconds/10000 iterations; no case/parameter expansion or retry.
The output records primal and infeasibility-dual hints separately.
"""
from pathlib import Path
from fractions import Fraction as F
import gzip,hashlib,json,math,os,sys,time,traceback
os.environ['OPENBLAS_NUM_THREADS']='1'
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
sys.path.insert(0,str(ROOT/'tmp/goal-20261016/python-sdp'))
import numpy as np
import scipy
from scipy.sparse import coo_matrix
import scs

V=714;OUT=HERE/'swap-family-cone.json'
PARENT=ROOT/'research-goal-20261017-quartic'
GATE=ROOT/'research-goal-20261017-swap-family-audit/independent-replay.json'


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def sanitize(v):
    if isinstance(v,float) and not math.isfinite(v):return 'NaN' if math.isnan(v) else 'Infinity' if v>0 else '-Infinity'
    if isinstance(v,dict):return {k:sanitize(w) for k,w in v.items()}
    if isinstance(v,list):return [sanitize(w) for w in v]
    return v
def unpack_matrix(v,n):
    ans=np.empty((n,n));p=0
    for j in range(n):
        for i in range(j,n):ans[i,j]=ans[j,i]=v[p]/(1 if i==j else np.sqrt(2));p+=1
    assert p==len(v)
    return ans
def polyvalue(p,values):return sum(F(q)*values[k] for k,q in p)


def main():
    assert not OUT.exists();began=time.monotonic()
    modelpath=PARENT/'quartic-model.json.gz';buildpath=PARENT/'quartic-build.json';replaypath=PARENT/'quartic-replay.json'
    packetpath=HERE/'swap-family-normalized.json.gz';packetbuildpath=HERE/'swap-family-normalized-build.json'
    paths=[Path(__file__),modelpath,buildpath,replaypath,PARENT/'quartic_static.py',PARENT/'quartic_replay.py',
        PARENT/'quartic_cone.py',packetpath,packetbuildpath,HERE/'swap_family_normalized_static.py',GATE,
        GATE.parent/'independent_replay.py']
    pins={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in paths}
    raw=gzip.decompress(modelpath.read_bytes());model=json.loads(raw);build=json.loads(buildpath.read_bytes());replay=json.loads(replaypath.read_bytes())
    assert sha(modelpath)==build['model_compressed_sha256'] and hashlib.sha256(raw).hexdigest()==build['model_uncompressed_sha256']
    assert replay['status']=='shared_quartic_coefficients_rows_and_localizers_independently_verified'
    assert replay['source_sha256_start']['research-goal-20261017-quartic/quartic-model.json.gz']==sha(modelpath)
    assert model['nonconstant_moment_variables']==V and model['slack_index']==V and model['unsoftened_sublevel_localizer']
    familyraw=gzip.decompress(packetpath.read_bytes());family=json.loads(familyraw);fb=json.loads(packetbuildpath.read_bytes());gate=json.loads(GATE.read_bytes())
    assert fb['packet_compressed_sha256']==sha(packetpath) and fb['packet_uncompressed_sha256']==hashlib.sha256(familyraw).hexdigest()
    assert gate['passed'] and gate['source_sha256_start']==gate['source_sha256_end'] and gate['all_sources_unchanged']
    for name,h in gate['source_sha256_start'].items():assert sha(ROOT/name)==h
    assert gate['source_sha256_start'][packetpath.relative_to(ROOT).as_posix()]==sha(packetpath)
    assert family['path']==model['path'] and family['parent_model_sha256']==sha(modelpath)
    assert family['target']==model['target']=='11/1250' and family['monomials']==model['monomials']
    assert family['scalar_variables_including_energy_slack']==715 and family['slack_index']==714
    extra=family['additional_linear_rows'];assert len(extra)==8 and family['all_eight_conditions_simultaneous']
    for r,row in enumerate(extra):
        assert row['meta']==['unsoftened_global_adjacent_swap_necessary',r,r+1]
        assert all(0<=k<714 for k,_ in row['coefficients']) and F(row['scale'])>0
    sizes=model['PSD_sizes'];assert sizes==[55]+[10]*46
    out={'scope':__doc__,'phase':'building_shared_quartic_eight_swap_sparse_map','path':model['path'],'target':model['target'],
        'scalar_variables':V+1,'shared_nonconstant_gap_moments':V,'energy_slack_index':V,'PSD_sizes':sizes,
        'solver_calls_authorized':1,'time_limit_seconds':45,'maximum_iterations':10000,
        'solver':'SCS','solver_version':scs.__version__,'numpy_version':np.__version__,'scipy_version':scipy.__version__,
        'input_sha256_start':pins,'strict_certificate':None,'actual_Lean_exclusion':False,
        'complete_global_cover':False,'new_zero_proportion_proven':False,
        'actual_analytic_inputs_Lean_proved_here':False,'unsoftened_old_energy_sublevel_localizer':True,
        'independent_new_rows_replay_passed':True,'old_rows_PSD_and_objective_unchanged':True,
        'unsoftened_global_competitor_rows':8,'new_row_old_wprime_coefficients_used':False,
        'original_base_analytic_premises_still_explicit':True,'all_eight_conditions_simultaneous':True}
    def save():
        final={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in paths};assert final==pins
        out['input_sha256_end']=final;out['all_sources_unchanged']=True;out['seconds_hint']=time.monotonic()-began
        OUT.write_text(json.dumps(sanitize(out),separators=(',',':'),allow_nan=False)+'\n',encoding='utf8')
    save()
    try:
        ri=[];ci=[];vv=[];bb=[]
        for row,entry in enumerate(model['linear_rows']+extra):
            scale=F(entry['scale']);assert scale>0
            for k,q in entry['coefficients']:ri.append(row);ci.append(k);vv.append(float(F(q)/scale))
            bb.append(float(F(entry['bound'])/scale))
        linearrows=len(bb);assert len(model['linear_rows'])==5795 and linearrows==5803
        # Positive rational uniform congruence factor per block: B -> B/s.
        # This is equivalent to congruence by I/sqrt(s), and changes no PSD set.
        block_scales=[];block_offsets=[]
        for block in model['PSD_blocks']:
            scale=max([F(1)]+[abs(F(f['constant'])) for _,_,f in block['entries']]+
                [abs(F(q)) for _,_,f in block['entries'] for _,q in f['coefficients']])
            block_scales.append(str(scale));block_offsets.append(len(bb))
            for i,j,form in block['entries']:
                factor=1. if i==j else np.sqrt(2);row=len(bb)
                bb.append(float(F(form['constant'])/scale)*factor)
                for k,q in form['coefficients']:ri.append(row);ci.append(k);vv.append(-float(F(q)/scale)*factor)
        assert len(bb)==9873
        A=coo_matrix((vv,(ri,ci)),shape=(len(bb),V+1)).tocsc();b=np.array(bb);c=np.r_[np.zeros(V),1.]
        # Check the conic packing against exact rank-one polynomial evaluation.
        # No positivity assertion at this arbitrary point, which need not have F<c.
        y=[F((-1)**r*(r+1),19) for r in range(9)];moments=[]
        for monomial in model['monomials']:
            z=F(1)
            for r in monomial:z*=y[r]
            moments.append(z)
        xx=np.array([float(z) for z in moments[1:]]+[0.]);packed=b-A@xx;maxerror=0.
        for block,offset,scale in zip(model['PSD_blocks'],block_offsets,block_scales):
            n=block['size'];mat=unpack_matrix(packed[offset:offset+n*(n+1)//2],n)
            multiplier=polyvalue(block['multiplier_polynomial'],moments)/F(scale)
            basis=moments[:n];exact=np.array([[float(multiplier*q*r) for r in basis] for q in basis])
            maxerror=max(maxerror,float(np.max(np.abs(mat-exact))))
        assert maxerror<1e-10
        # Independent affine-row packing sanity at a fixed rational rank-one
        # vector. This is polynomial identity only, not a minimizer claim.
        swap_row_error=0.
        for r,(row,item) in enumerate(zip(extra,family['maps'])):
            exact=polyvalue(item['difference_upper_quartic'],moments)/F(row['scale'])
            swap_row_error=max(swap_row_error,abs(float(exact)-packed[5795+r]))
        assert swap_row_error<1e-10
        out.update({'linear_rows':linearrows,'total_conic_rows':len(bb),'matrix_nonzero_count':int(A.nnz),
            'positive_rational_PSD_block_divisors':block_scales,'PSD_block_offsets':block_offsets,
            'factorized_packing_max_absolute_error_hint':maxerror,
            'factorized_packing_test_asserts_energy_localizer_PSD':False,
            'swap_row_packing_max_absolute_error_hint':swap_row_error})
        out['phase']='single_shared_quartic_eight_swap_SCS_running';save();tick=time.monotonic()
        result=scs.solve({'A':A,'b':b,'c':c},{'l':linearrows,'s':sizes},verbose=False,
            time_limit_secs=45,max_iters=10000,eps_abs=1e-7,eps_rel=1e-7)
        out['solver_info']=result['info'];out['solver_seconds_hint']=time.monotonic()-tick
        out['raw_primal_hint']=result['x'].tolist();out['raw_dual_hint']=result['y'].tolist();out['raw_conic_slack_hint']=result['s'].tolist()
        xx=result['x'];dual=result['y'];status=str(result['info'].get('status','')).lower()
        out['infeasible_dual_ray_hint']='infeasible' in status and bool(np.all(np.isfinite(dual)))
        if np.all(np.isfinite(xx)):
            out['raw_energy_slack_hint']=float(xx[-1]*.001)
            out['minimum_normalized_linear_slack_hint']=float(np.min(b[:linearrows]-A[:linearrows]@xx))
            packed=b-A@xx;eigenvalues=[]
            for block,offset in zip(model['PSD_blocks'],block_offsets):
                n=block['size'];eigenvalues.append(float(np.linalg.eigvalsh(unpack_matrix(packed[offset:offset+n*(n+1)//2],n))[0]))
            out['PSD_minimum_eigenvalues_hint']=eigenvalues
            out['minimum_normalized_PSD_eigenvalue_hint']=min(eigenvalues)
            out['positive_energy_slack_hint']=out['raw_energy_slack_hint']>1e-7
        else:out['positive_energy_slack_hint']=False
        if np.all(np.isfinite(dual)):
            out['dual_b_dot_hint']=float(b@dual);out['dual_stationarity_norm_hint']=float(np.linalg.norm(A.T@dual-c,np.inf))
            out['infeasible_ray_Atranspose_norm_hint']=float(np.linalg.norm(A.T@dual,np.inf))
        out['any_positive_hint']=out['positive_energy_slack_hint'] or out['infeasible_dual_ray_hint']
        if np.all(np.isfinite(xx)):
            out['new_swap_row_normalized_slacks_hint']=(b[5795:5803]-A[5795:5803]@xx).tolist()
        out['phase']='completed_single_shared_quartic_eight_swap_SCS';save()
    except BaseException as exc:
        out['phase']='exception_stopped';out['exception']=repr(exc);out['traceback']=traceback.format_exc();save();raise
    print(json.dumps(sanitize({k:out[k] for k in ['phase','solver_info','solver_seconds_hint','raw_energy_slack_hint',
        'minimum_normalized_linear_slack_hint','minimum_normalized_PSD_eigenvalue_hint','positive_energy_slack_hint',
        'infeasible_dual_ray_hint','any_positive_hint'] if k in out})),flush=True)


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
