"""One SCS test of the exact full-U cross-derivative model on the first cell.

1325 scalar variables plus the original energy slack; all old rows and boxes,
82 scalar residual-square bounds, full 51x51 joint PSD, all 861 UU boxes and
3444 UU RLT rows, and 369 derivative-multiplied free-KKT equalities.
One solve <=45s/10000 iterations.  No cell, scale, point, or cut loop.
Floating discovery only: this file never asserts exact model feasibility.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,math,os,sys,time,traceback
os.environ['OPENBLAS_NUM_THREADS']='1'
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
sys.path.insert(0,str(ROOT/'tmp/goal-20261016/python-sdp'))
import numpy as np
import scipy
from scipy.sparse import coo_matrix
import scs
import cover_cross_moment_exact_rows as exact

V=1325;OUT=HERE/'cover-full-u-joint-cone.json'


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def sanitize(v):
    if isinstance(v,float) and not math.isfinite(v):return 'NaN' if math.isnan(v) else 'Infinity' if v>0 else '-Infinity'
    if isinstance(v,dict):return {k:sanitize(w) for k,w in v.items()}
    if isinstance(v,list):return [sanitize(w) for w in v]
    return v
def matrix(v):
    ans=np.empty((51,51));p=0
    for j in range(51):
        for i in range(j,51):ans[i,j]=ans[j,i]=v[p]/(1 if i==j else np.sqrt(2));p+=1
    assert p==len(v)
    return ans


def main():
    assert not OUT.exists()
    began=time.monotonic();modelpath=HERE/'cover-full-u-model.json';inputpath=HERE/'cover-residual-psd-rational-inputs.json'
    model=json.loads(modelpath.read_bytes());inputs=json.loads(inputpath.read_bytes())
    assert model['path']==inputs['path'] and model['variables']==V and model['joint_PSD_size']==51
    paths=[Path(__file__),modelpath,inputpath,Path(exact.__file__),HERE/'cover_full_u_model.py',
           HERE/'cover-dynamic-sector-static.json',HERE/'cover-residual-psd-pilot.json',
           ROOT/'research-20261016-followup/window_reweight_rational.json']
    pins={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in paths}
    out={'scope':__doc__,'phase':'building_exact_row_model','path':model['path'],'target':'11/1250',
         'scalar_variables':V,'slack_index':V,'joint_PSD_size':51,'new_U_variables':861,
         'energy_packets':2,'old82_cones_retained_via_joint_PSD_and_residual_square_rows':True,
         'new_scalar_positions':0,'new_table_queries':0,'solver_calls_authorized':1,
         'time_limit_seconds':45,'maximum_iterations':10000,'solver':'SCS','solver_version':scs.__version__,
         'numpy_version':np.__version__,'scipy_version':scipy.__version__,
         'input_sha256_start':pins,'strict_certificate':None,'actual_Lean_exclusion':False,
         'complete_global_cover':False,'new_zero_proportion_proven':False}
    def save():
        final={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in paths};assert final==pins
        out['input_sha256_end']=final;out['all_sources_unchanged']=True;out['seconds_hint']=time.monotonic()-began
        OUT.write_text(json.dumps(sanitize(out),separators=(',',':'),allow_nan=False)+'\n',encoding='utf8')
    save()
    try:
        old=exact.inputs(inputs['cell'],inputs['old_integer_rows'],inputs['old_meta'],inputs['u_bounds'],inputs['energy_packets'])
        check=hashlib.sha256()
        for row in old['rows']:check.update(json.dumps([sorted((i,str(v)) for i,v in row['coeff'].items()),str(row['bound']),row['meta']],separators=(',',':')).encode())
        assert check.hexdigest()==model['old_row_serialization_sha256'] and len(old['rows'])==43306
        ri=[];ci=[];vv=[];bb=[];labels=[];exacthash=hashlib.sha256()
        def append(coeff,bound,scale,label):
            row=len(bb);assert scale>0
            exacthash.update(json.dumps([label,str(bound),str(scale),[[k,str(v)] for k,v in sorted(coeff.items())]],separators=(',',':')).encode())
            for k,v in coeff.items():
                if v:ri.append(row);ci.append(k);vv.append(float(v/scale))
            bb.append(float(bound/scale));labels.append(label)
        for n,row in enumerate(old['rows']):
            coeff=row['coeff'].copy()
            if row['meta'][0]=='energy':coeff[V]=F(-1,1000)
            append(coeff,row['bound'],row['scale'],['old',n,row['meta']])
        for n,row in enumerate(model['new_linear_rows']):
            append({k:F(v) for k,v in row['coefficients']},F(row['bound']),F(row['scale']),['new',n,row['meta']])
        bounds=old['bounds']+[(F(l),F(u)) for _,l,u in model['new_variable_bounds']]
        assert len(bounds)==V and [k for k,_,_ in model['new_variable_bounds']]==list(range(464,V))
        for k,(l,u) in enumerate(bounds):
            append({k:F(-1)},-l,F(1),['box',k,-1]);append({k:F(1)},u,F(1),['box',k,1])
        append({V:F(-1)},F(0),F(1),['slack_nonnegative'])
        linearrows=len(bb);assert linearrows==50221
        packedhash=hashlib.sha256()
        for i,j,entry in model['joint_PSD_affine_entries']:
            c=F(entry['constant']);a={k:F(v) for k,v in entry['coefficients']}
            packedhash.update(json.dumps([i,j,str(c),[[k,str(v)] for k,v in sorted(a.items())]],separators=(',',':')).encode())
            factor=1 if i==j else np.sqrt(2);row=len(bb)
            for k,v in a.items():ri.append(row);ci.append(k);vv.append(-factor*float(v))
            bb.append(factor*float(c))
        A=coo_matrix((vv,(ri,ci)),shape=(len(bb),V+1)).tocsc();b=np.array(bb);c=np.r_[np.zeros(V),1.]
        # A rank-one serialization test at y=0, normalized v=0.
        factor=np.zeros(V+1);factor[:9]=list(map(float,old['center']))
        factor[9:50]=[float(F(v['midpoint'])) for v in model['derivative_normalization']]
        M=matrix(b[linearrows:]-A[linearrows:]@factor);expected=np.zeros((51,51));expected[0,0]=1
        err=float(np.max(abs(M-expected)));assert err<1e-8,err
        out.update({'old_linear_rows_with_energy':43306,'new_linear_rows':4264,'linear_rows_with_boxes':linearrows,
            'total_conic_rows':len(bb),'matrix_nonzero_count':int(A.nnz),
            'exact_linear_row_serialization_sha256':exacthash.hexdigest(),
            'exact_joint_PSD_map_serialization_sha256':packedhash.hexdigest(),
            'rank_one_packed_map_max_error_hint':err,
            'expected_exact_KKT_null_directions':9})
        out['phase']='single_full_U_SCS_running';save();tick=time.monotonic()
        result=scs.solve({'A':A,'b':b,'c':c},{'l':linearrows,'s':[51]},
            verbose=False,time_limit_secs=45,max_iters=10000,eps_abs=1e-7,eps_rel=1e-7)
        out['solver_info']=result['info'];out['solver_seconds_hint']=time.monotonic()-tick
        out['raw_primal_hint']=result['x'].tolist();out['raw_dual_hint']=result['y'].tolist();out['raw_conic_slack_hint']=result['s'].tolist()
        xx=result['x']
        if np.all(np.isfinite(xx)):
            out['raw_energy_slack_hint']=float(xx[-1]*.001)
            slack=b[:linearrows]-A[:linearrows]@xx
            out['minimum_linear_slack_hint']=float(np.min(slack))
            out['minimum_new_linear_slack_hint']=float(np.min(slack[43306:43306+4264]))
            PSD=matrix(b[linearrows:]-A[linearrows:]@xx);eigen=np.linalg.eigvalsh(PSD)
            out['minimum_joint_PSD_eigenvalue_hint']=float(eigen[0]);out['joint_PSD_eigenvalues_hint']=eigen.tolist()
            out['positive_energy_slack_hint']=out['raw_energy_slack_hint']>1e-7
        else:out['positive_energy_slack_hint']=False
        out['phase']='completed_single_full_U_SCS';save()
    except BaseException as exc:
        out['phase']='exception_stopped';out['exception']=repr(exc);out['traceback']=traceback.format_exc();save();raise
    print(json.dumps(sanitize({k:out[k] for k in ['phase','solver_info','solver_seconds_hint','raw_energy_slack_hint',
        'minimum_linear_slack_hint','minimum_new_linear_slack_hint','minimum_joint_PSD_eigenvalue_hint','positive_energy_slack_hint'] if k in out})),flush=True)


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
