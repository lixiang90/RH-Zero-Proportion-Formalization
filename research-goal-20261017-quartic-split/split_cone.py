"""At most one SCS discovery call for each side of one exact disjunction.

Keep all frozen parent rows/47 PSD blocks, and add exactly the three
halfspace localizers.  No recursive split, new direction, Taylor anchor,
or actual scalar sample.  This driver refuses any existing branch output.
Primal and infeasible-dual hints are separate; neither alone is a proof.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,gzip,hashlib,json,math,os,sys,time,traceback
os.environ['OPENBLAS_NUM_THREADS']='1'
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;PARENT=ROOT/'research-goal-20261017-quartic'
sys.path.insert(0,str(ROOT/'tmp/goal-20261016/python-sdp'))
import numpy as np
import scipy
from scipy.sparse import coo_matrix
import scs


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def clean(v):
    if isinstance(v,float) and not math.isfinite(v):return 'NaN' if math.isnan(v) else 'Infinity' if v>0 else '-Infinity'
    if isinstance(v,dict):return {k:clean(w) for k,w in v.items()}
    if isinstance(v,list):return [clean(w) for w in v]
    return v
def matrix(v,n):
    out=np.empty((n,n));k=0
    for j in range(n):
        for i in range(j,n):out[i,j]=out[j,i]=v[k]/(1 if i==j else np.sqrt(2));k+=1
    assert k==len(v)
    return out


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--sigma',type=int,choices=[-1,1],required=True);args=parser.parse_args()
    sigma=args.sigma;OUT=HERE/('split-cone-minus.json' if sigma==-1 else 'split-cone-plus.json');assert not OUT.exists();began=time.monotonic()
    paths=[Path(__file__),HERE/'split-model.json',HERE/'split-replay.json',HERE/'split_replay.py',
        PARENT/'quartic-files.json',PARENT/'quartic-model.json.gz',PARENT/'quartic-build.json']
    pins={p.relative_to(ROOT).as_posix():sha(p) for p in paths}
    split=json.loads(paths[1].read_bytes());replay=json.loads(paths[2].read_bytes());raw=gzip.decompress(paths[5].read_bytes());model=json.loads(raw);build=json.loads(paths[6].read_bytes())
    assert replay['status']=='exact_halfspace_cover_localizers_and_two_negative_witnesses_verified'
    assert replay['source_sha256_start']['research-goal-20261017-quartic-split/split-model.json']==sha(paths[1])
    assert hashlib.sha256(raw).hexdigest()==build['model_uncompressed_sha256'] and sha(paths[5])==build['model_compressed_sha256']
    assert split['parent_manifest_sha256']==sha(paths[4]) and model['nonconstant_moment_variables']==714
    branch=next(b for b in split['branches'] if b['sigma']==sigma);blocks=model['PSD_blocks']+branch['extra_PSD_blocks'];sizes=[b['size'] for b in blocks]
    assert sizes==[55]+[10]*49
    out={'scope':__doc__,'phase':'building_split_conic_map','path':model['path'],'sigma':sigma,'halfspace':branch['halfspace'],
        'alpha':split['alpha'],'threshold':split['threshold'],'target':model['target'],'scalar_variables':715,
        'PSD_sizes':sizes,'parent_rows_unchanged':True,'parent_47_PSD_blocks_unchanged':True,
        'additional_localizers':3,'solver_calls_authorized_for_this_branch':1,'time_limit_seconds':45,'maximum_iterations':10000,
        'solver':'SCS','solver_version':scs.__version__,'numpy_version':np.__version__,'scipy_version':scipy.__version__,
        'source_sha256_start':pins,'strict_certificate':None,'actual_Lean_exclusion':False,'complete_global_cover':False,
        'new_zero_proportion_proven':False,'new_actual_scalar_positions':0}
    def save():
        final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert final==pins
        out.update({'source_sha256_end':final,'all_sources_unchanged':True,'seconds_hint':time.monotonic()-began})
        OUT.write_text(json.dumps(clean(out),separators=(',',':'),allow_nan=False)+'\n',encoding='utf8')
    save()
    try:
        ri=[];ci=[];vv=[];bb=[]
        for row,data in enumerate(model['linear_rows']):
            scale=F(data['scale']);assert scale>0
            bb.append(float(F(data['bound'])/scale))
            for k,v in data['coefficients']:ri.append(row);ci.append(k);vv.append(float(F(v)/scale))
        linear=len(bb);assert linear==5795
        divisors=[];offsets=[]
        for block in blocks:
            divisor=max([F(1)]+[abs(F(f['constant'])) for _,_,f in block['entries']]+
                [abs(F(v)) for _,_,f in block['entries'] for _,v in f['coefficients']])
            divisors.append(str(divisor));offsets.append(len(bb))
            for i,j,form in block['entries']:
                row=len(bb);factor=1. if i==j else np.sqrt(2)
                bb.append(float(F(form['constant'])/divisor)*factor)
                for k,v in form['coefficients']:ri.append(row);ci.append(k);vv.append(-float(F(v)/divisor)*factor)
        assert len(bb)==10030
        A=coo_matrix((vv,(ri,ci)),shape=(len(bb),715)).tocsc();b=np.array(bb);c=np.r_[np.zeros(714),1.]
        out.update({'linear_rows':linear,'total_conic_rows':len(bb),'matrix_nonzero_count':int(A.nnz),
            'positive_rational_PSD_block_divisors':divisors,'PSD_block_offsets':offsets})
        out['phase']='single_branch_SCS_running';save();tick=time.monotonic()
        result=scs.solve({'A':A,'b':b,'c':c},{'l':linear,'s':sizes},verbose=False,
            time_limit_secs=45,max_iters=10000,eps_abs=1e-7,eps_rel=1e-7)
        out['solver_info']=result['info'];out['solver_seconds_hint']=time.monotonic()-tick
        out['raw_primal_hint']=result['x'].tolist();out['raw_dual_hint']=result['y'].tolist();out['raw_conic_slack_hint']=result['s'].tolist()
        x=result['x'];dual=result['y'];status=str(result['info'].get('status','')).lower()
        out['infeasible_dual_ray_hint']='infeasible' in status and bool(np.all(np.isfinite(dual)))
        if np.all(np.isfinite(x)):
            out['raw_energy_slack_hint']=float(x[-1]*.001);slack=b-A@x
            out['minimum_normalized_linear_slack_hint']=float(np.min(slack[:linear]));eigen=[]
            for block,offset in zip(blocks,offsets):
                n=block['size'];eigen.append(float(np.linalg.eigvalsh(matrix(slack[offset:offset+n*(n+1)//2],n))[0]))
            out['PSD_minimum_eigenvalues_hint']=eigen;out['minimum_normalized_PSD_eigenvalue_hint']=min(eigen)
            out['positive_energy_slack_hint']=out['raw_energy_slack_hint']>1e-7
            out['mean_phi_minus_threshold_hint']=float(sum(float(F(a))*x[r] for r,a in enumerate(split['alpha']))-float(F(split['threshold'])))
        else:out['positive_energy_slack_hint']=False
        if np.all(np.isfinite(dual)):
            out['dual_b_dot_hint']=float(b@dual);out['standard_dual_stationarity_norm_hint']=float(np.linalg.norm(A.T@dual+c,np.inf))
            out['infeasible_ray_Atranspose_norm_hint']=float(np.linalg.norm(A.T@dual,np.inf))
        out['any_positive_hint']=out['positive_energy_slack_hint'] or out['infeasible_dual_ray_hint']
        out['phase']='completed_single_branch_SCS';save()
    except BaseException as exc:
        out['phase']='exception_stopped';out['exception']=repr(exc);out['traceback']=traceback.format_exc();save();raise
    print(json.dumps(clean({k:out[k] for k in ['phase','sigma','solver_info','solver_seconds_hint','raw_energy_slack_hint',
        'minimum_normalized_linear_slack_hint','minimum_normalized_PSD_eigenvalue_hint','positive_energy_slack_hint',
        'infeasible_dual_ray_hint','any_positive_hint'] if k in out})),flush=True)


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
