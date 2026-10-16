"""One exact-face-reduced SCS representation of the frozen full-U model.

902 moment variables plus the same energy slack, a 42x42 PSD block, and
46,347 exact normalized pulled-back rows.  No new mathematical constraint.
One solve <=45 seconds/10000 iterations; no repeated full51 experiment.
The output is floating discovery, not an exact feasible or exclusion proof.
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

V=902;OUT=HERE/'cover-full-u-face-cone.json'


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def sanitize(v):
    if isinstance(v,float) and not math.isfinite(v):return 'NaN' if math.isnan(v) else 'Infinity' if v>0 else '-Infinity'
    if isinstance(v,dict):return {k:sanitize(w) for k,w in v.items()}
    if isinstance(v,list):return [sanitize(w) for w in v]
    return v
def matrix(v):
    ans=np.empty((42,42));p=0
    for j in range(42):
        for i in range(j,42):ans[i,j]=ans[j,i]=v[p]/(1 if i==j else np.sqrt(2));p+=1
    assert p==len(v)
    return ans


def main():
    assert not OUT.exists();began=time.monotonic()
    modelpath=HERE/'cover-full-u-face-model.json.gz';buildpath=HERE/'cover-full-u-face-build.json'
    paths=[Path(__file__),modelpath,buildpath,HERE/'cover_full_u_face_model.py',HERE/'cover-full-u-files.json']
    pins={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in paths}
    raw=gzip.decompress(modelpath.read_bytes());model=json.loads(raw);build=json.loads(buildpath.read_bytes())
    assert sha(modelpath)==build['compressed_model_sha256'] and hashlib.sha256(raw).hexdigest()==build['uncompressed_model_sha256']
    assert model['same_mathematical_model'] and model['reduced_variables']==V and model['reduced_PSD_size']==42
    out={'scope':__doc__,'phase':'building_reduced_sparse_map','path':model['path'],'target':'11/1250',
        'scalar_variables':V,'slack_index':V,'joint_PSD_size':42,'original_variables':1325,'original_PSD_size':51,
        'mathematical_constraint_changes':0,'eliminated_moment_variables':423,
        'exact_tautology_rows_removed':model['exact_tautology_rows_removed'],
        'positive_proportional_duplicates_removed':model['positive_proportional_duplicates_removed'],
        'solver_calls_authorized':1,'time_limit_seconds':45,'maximum_iterations':10000,
        'solver':'SCS','solver_version':scs.__version__,'numpy_version':np.__version__,'scipy_version':scipy.__version__,
        'input_sha256_start':pins,'strict_certificate':None,'actual_Lean_exclusion':False,
        'complete_global_cover':False,'new_zero_proportion_proven':False}
    def save():
        final={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in paths};assert final==pins
        out['input_sha256_end']=final;out['all_sources_unchanged']=True;out['seconds_hint']=time.monotonic()-began
        OUT.write_text(json.dumps(sanitize(out),separators=(',',':'),allow_nan=False)+'\n',encoding='utf8')
    save()
    try:
        ri=[];ci=[];vv=[];bb=[]
        for row,(coeff,bound) in enumerate(model['reduced_distinct_linear_rows']):
            for k,v in coeff:ri.append(row);ci.append(k);vv.append(float(F(v)))
            bb.append(float(F(bound)))
        linearrows=len(bb);assert linearrows==46347
        indices={(min(i,j),max(i,j)):k for i,j,k in model['reduced_Gram_entry_variables']}
        for j in range(42):
            for i in range(j,42):
                row=len(bb)
                if i==j==0:bb.append(1.)
                else:
                    ri.append(row);ci.append(indices[j,i]);vv.append(-1. if i==j else -np.sqrt(2));bb.append(0.)
        A=coo_matrix((vv,(ri,ci)),shape=(len(bb),V+1)).tocsc();b=np.array(bb);c=np.r_[np.zeros(V),1.]
        out.update({'linear_rows':linearrows,'total_conic_rows':len(bb),'matrix_nonzero_count':int(A.nnz)})
        out['phase']='single_reduced42_SCS_running';save();tick=time.monotonic()
        result=scs.solve({'A':A,'b':b,'c':c},{'l':linearrows,'s':[42]},
            verbose=False,time_limit_secs=45,max_iters=10000,eps_abs=1e-7,eps_rel=1e-7)
        out['solver_info']=result['info'];out['solver_seconds_hint']=time.monotonic()-tick
        out['raw_reduced_primal_hint']=result['x'].tolist();out['raw_dual_hint']=result['y'].tolist();out['raw_conic_slack_hint']=result['s'].tolist()
        xx=result['x']
        if np.all(np.isfinite(xx)):
            out['raw_energy_slack_hint']=float(xx[-1]*.001)
            out['minimum_reduced_linear_slack_hint']=float(np.min(b[:linearrows]-A[:linearrows]@xx))
            Q=matrix(b[linearrows:]-A[linearrows:]@xx);eigen=np.linalg.eigvalsh(Q)
            out['minimum_reduced_PSD_eigenvalue_hint']=float(eigen[0]);out['reduced_PSD_eigenvalues_hint']=eigen.tolist()
            full=[]
            for entry in model['original_1325_variable_maps']:
                full.append(float(F(entry['constant']))+sum(float(F(v))*xx[k] for k,v in entry['coefficients']))
            out['reconstructed_full_1325_primal_hint']=full
            out['positive_energy_slack_hint']=out['raw_energy_slack_hint']>1e-7
        else:out['positive_energy_slack_hint']=False
        out['phase']='completed_single_reduced42_SCS';save()
    except BaseException as exc:
        out['phase']='exception_stopped';out['exception']=repr(exc);out['traceback']=traceback.format_exc();save();raise
    print(json.dumps(sanitize({k:out[k] for k in ['phase','solver_info','solver_seconds_hint','raw_energy_slack_hint',
        'minimum_reduced_linear_slack_hint','minimum_reduced_PSD_eigenvalue_hint','positive_energy_slack_hint'] if k in out})),flush=True)


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
