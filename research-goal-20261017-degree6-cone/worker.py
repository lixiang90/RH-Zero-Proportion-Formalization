"""One cold CPU-indirect SCS attempt on the complete frozen degree6 model.

This is numerical discovery only. All scalar rows and every PSD entry
are retained. A separate parent monitors this PID and its peak RSS.
Exactly one solver construction/solve, no fallback, warm start or retry.
"""
from pathlib import Path
from fractions import Fraction as F
from array import array
import ctypes,gzip,hashlib,json,math,os,sys,time,traceback
for key in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:os.environ[key]='1'
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;STATIC=ROOT/'research-goal-20261017-degree6-static'
sys.path.insert(0,str(ROOT/'tmp/goal-20261016/python-sdp'))
import numpy as np
import scipy
from scipy.sparse import coo_matrix
import scs
OUT=HERE/'worker-receipt.json';HINTS=HERE/'degree6-hints.json.gz';LIMIT=1536*1024**2
SCALAR=14383;N=5005;SLACK=5004;EXPECTED_NNZ=2247687

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def memory():
    from ctypes import wintypes as W
    class PMC(ctypes.Structure):
        _fields_=[('cb',W.DWORD),('PageFaultCount',W.DWORD)]+[(s,ctypes.c_size_t) for s in
            ['PeakWorkingSetSize','WorkingSetSize','QuotaPeakPagedPoolUsage','QuotaPagedPoolUsage','QuotaPeakNonPagedPoolUsage','QuotaNonPagedPoolUsage','PagefileUsage','PeakPagefileUsage']]
    kernel=ctypes.WinDLL('kernel32',use_last_error=True);kernel.GetCurrentProcess.restype=W.HANDLE
    psapi=ctypes.WinDLL('psapi',use_last_error=True);psapi.GetProcessMemoryInfo.argtypes=[W.HANDLE,ctypes.POINTER(PMC),W.DWORD]
    q=PMC();q.cb=ctypes.sizeof(q);assert psapi.GetProcessMemoryInfo(kernel.GetCurrentProcess(),ctypes.byref(q),q.cb)
    return {'working_set_bytes':q.WorkingSetSize,'peak_working_set_bytes':q.PeakWorkingSetSize,'private_commit_bytes':q.PagefileUsage}
def clean(v):
    if isinstance(v,float) and not math.isfinite(v):return 'NaN' if math.isnan(v) else 'Infinity' if v>0 else '-Infinity'
    if isinstance(v,dict):return {k:clean(w) for k,w in v.items()}
    if isinstance(v,list):return [clean(w) for w in v]
    return v
def unpack_matrix(v,n):
    out=np.zeros((n,n));p=0
    for j in range(n):
        for i in range(j,n):out[i,j]=out[j,i]=v[p]/(1. if i==j else np.sqrt(2));p+=1
    assert p==len(v);return out

def main():
    assert not OUT.exists() and not HINTS.exists();began=time.monotonic()
    paths=[Path(__file__),HERE/'run_once.py',STATIC/'degree6-files.json',STATIC/'degree6-build.json',
        STATIC/'degree6-model.json.gz',STATIC/'degree6-targets.bin',STATIC/'degree6-entryplans.bin',
        ROOT/'research-goal-20261017-degree6-audit/independent-replay.json',Path(scs.__file__),
        Path(scs.__file__).parent/'_scs_indirect.cp314-win_amd64.pyd']
    initial={str(p.relative_to(ROOT)).replace('\\','/') if p.is_relative_to(ROOT) else str(p):sha(p) for p in paths}
    out={'scope':__doc__,'phase':'checking_frozen_inputs','PID':os.getpid(),'input_sha256_start':initial,
        'numpy_version':np.__version__,'scipy_version':scipy.__version__,'scs_version':scs.__version__,
        'underlying_real_variables':9,'optimization_variables':N,'energy_slack_column':SLACK,
        'time_limit_seconds':45,'maximum_iterations':1000,'eps_abs':1e-6,'eps_rel':1e-6,
        'linear_solver':'cpu_indirect','cold_solve':True,'warm_start':False,'BLAS_threads':1,
        'memory_limit_bytes':LIMIT,'memory_snapshots':[],'SCS_invocations_started':0,'SCS_solve_calls':0,
        'actual_certificate':None,'actual_analytic_instances_Lean_proved':False,'new_actual_kernel_inputs':0,
        'Lean_invocations':0,'cell_exclusion_proven':False,'new_zero_proportion_proven':False}
    def save(phase):
        out['phase']=phase;m=memory();m['phase']=phase;m['elapsed_milliseconds']=int((time.monotonic()-began)*1000);out['memory_snapshots'].append(m)
        final={str(p.relative_to(ROOT)).replace('\\','/') if p.is_relative_to(ROOT) else str(p):sha(p) for p in paths};assert final==initial
        out.update({'input_sha256_end':final,'all_inputs_unchanged':True,'elapsed_milliseconds':m['elapsed_milliseconds']})
        tmp=OUT.with_suffix('.json.partial');tmp.write_text(json.dumps(clean(out),separators=(',',':'),allow_nan=False)+'\n',encoding='utf8');tmp.replace(OUT)
        if m['peak_working_set_bytes']>LIMIT:raise MemoryError('worker1.5GiB peak-working-set guard')
    save('checking_frozen_inputs')
    try:
        manifest=json.loads(paths[2].read_bytes())
        for r in manifest['package_files']+manifest['dependency_files']:assert sha(ROOT/r['path'])==r['sha256']
        build=json.loads(paths[3].read_bytes());raw=gzip.decompress(paths[4].read_bytes());model=json.loads(raw)
        assert hashlib.sha256(raw).hexdigest()==build['model_uncompressed_sha256'];del raw
        gate=json.loads(paths[7].read_bytes());assert gate['status']=='complete_factored_degree6_representation_independently_decoded' and gate['all_inputs_unchanged']
        assert model['nonconstant_moment_columns']==5004 and model['energy_slack_column']==SLACK
        assert [b['size'] for b in model['blocks']]==[220]+[55]*46+[10]*26
        mon=[tuple(m) for m in model['monomials']];assert len(mon)==5005
        target=array('H');target.frombytes(paths[5].read_bytes());entry=array('I');entry.frombytes(paths[6].read_bytes())
        if sys.byteorder!='little':target.byteswap();entry.byteswap()
        assert len(target)==1416525 and len(entry)==96580
        assert sha(paths[5])==model['target_indices']['sha256'] and sha(paths[6])==model['block_entry_plan_indices']['sha256']
        source=ROOT/model['old_row_adapter']['sources'][0];old=json.loads(gzip.decompress(source.read_bytes()))
        source=ROOT/model['old_row_adapter']['sources'][1];family=json.loads(gzip.decompress(source.read_bytes()))
        rows=old['linear_rows']+family['additional_linear_rows'];assert len(rows)==5803
        save('frozen_model_and_all_row_sources_loaded')
        # Fixed rational point for packing identities only. It is never a
        # warm seed and need not satisfy any minimizer or sublevel premise.
        y=[F((-1)**r*(r+1),19) for r in range(9)];values=[]
        for m in mon:
            z=F(1)
            for r in m:z*=y[r]
            values.append(z)
        multipliers=model['multipliers'];plans=model['entry_plans'];qfrac=[];qfloat=[];qvalue=[];divisors=[]
        for q in multipliers:
            coeff=[F(a) for _,a in q['terms']];divisor=max([F(1)]+[abs(a) for a in coeff])
            qfrac.append(coeff);qfloat.append([float(a/divisor) for a in coeff]);divisors.append(divisor)
            qvalue.append(sum(a*values[k] for (k,_),a in zip(q['terms'],coeff)))
        # Exact termwise distribution proves the entire rational b-Ax=qvv
        # identity without expanding millions of repeated huge Fractions.
        term_identity_checks=0
        for qid,shift,offset,count in plans:
            terms=multipliers[qid]['terms'];assert len(terms)==count
            for j,(k,_) in enumerate(terms):
                assert values[target[offset+j]]==values[k]*values[shift];term_identity_checks+=1
        assert term_identity_checks==1416525
        rr=np.empty(EXPECTED_NNZ,dtype=np.int32);cc=np.empty(EXPECTED_NNZ,dtype=np.int32);vv=np.empty(EXPECTED_NNZ,dtype=np.float64)
        bb=np.zeros(SCALAR+96580);used=0;rowid=0;linear_exact=[]
        for row in rows:
            divisor=F(row['scale']);assert divisor>0;bb[rowid]=float(F(row['bound'])/divisor);exact=F(row['bound'])
            for col,a in row['coefficients']:
                col=SLACK if col==714 else col;value=F(a)
                rr[used]=rowid;cc[used]=col;vv[used]=float(value/divisor);used+=1
                if col!=SLACK:exact-=value*values[col+1]
            linear_exact.append(exact/divisor);rowid+=1
        assert rowid==5803
        for col,lo,hi in model['new_moment_boxes']:
            for a,bound in [(-1,-lo),(1,hi)]:
                rr[used]=rowid;cc[used]=col;vv[used]=a;used+=1;bb[rowid]=bound
                linear_exact.append(F(bound)-a*values[col+1]);rowid+=1
        assert rowid==SCALAR
        offsets=[];positions=[]
        for block in model['blocks']:
            n=block['size'];qid=block['multiplier_id'];offsets.append(rowid);start=block['entry_plan_offset']
            assert start==rowid-SCALAR
            local=0
            for j in range(n):
                for i in range(j,n):
                    pid=entry[start+local];pq,shift,offset,count=plans[pid];assert pq==qid
                    factor=1. if i==j else np.sqrt(2)
                    for k in range(count):
                        targetid=target[offset+k];a=qfloat[qid][k]*factor
                        if targetid==0:bb[rowid]=a
                        else:
                            rr[used]=rowid;cc[used]=targetid-1;vv[used]=-a;used+=1
                    positions.append((qid,i,j));rowid+=1;local+=1
            assert local==n*(n+1)//2
        assert rowid==len(bb)==110963 and used==EXPECTED_NNZ
        save('complete_COO_assembly_before_CSC')
        A=coo_matrix((vv,(rr,cc)),shape=(len(bb),N)).tocsc();del rr,cc,vv
        assert A.nnz==EXPECTED_NNZ;xx=np.array([float(v) for v in values[1:]]+[0.]);packed=bb-A@xx
        linear_error=float(np.max(np.abs(packed[:SCALAR]-np.array([float(v) for v in linear_exact]))))
        psd_error=0.
        for k,(qid,i,j) in enumerate(positions):
            factor=1. if i==j else np.sqrt(2);exact=qvalue[qid]*values[i]*values[j]/divisors[qid]
            psd_error=max(psd_error,abs(packed[SCALAR+k]-float(exact)*factor))
        assert linear_error<1e-9 and psd_error<1e-9
        # No rank-one feasible claim is made: the test is only an identity.
        out.update({'linear_rows':SCALAR,'PSD_blocks':73,'PSD_lower_triangle_entries':96580,
            'matrix_shape':[110963,N],'matrix_nonzero_count':int(A.nnz),'exact_rank1_term_identities_checked':term_identity_checks,
            'fixed_rank1_test_y':list(map(str,y)),'rank1_linear_packing_max_absolute_error_hint':linear_error,
            'rank1_PSD_packing_max_absolute_error_hint':psd_error,'rank1_PSD_or_model_feasibility_asserted':False,
            'positive_rational_uniform_PSD_divisors':list(map(str,divisors)),'PSD_offsets':offsets,
            'full_model_no_constraints_dropped':True,'objective':'min diagnostic energy slack column5004; old soft-energy coefficient unchanged'})
        del xx,packed,linear_exact,positions
        save('assembly_and_fixed_rational_rank1_identity_passed_before_solver')
        c=np.zeros(N);c[SLACK]=1.
        # One object, one solve, no call to another backend or fallback.
        out['SCS_invocations_started']=1;save('one_CPU_indirect_SCS_initialization_starting');tick=time.monotonic()
        engine=scs.SCS({'A':A,'b':bb,'c':c},{'l':SCALAR,'s':[b['size'] for b in model['blocks']]},
            linear_solver=scs.LinearSolver.CPU_INDIRECT,verbose=False,time_limit_secs=45,max_iters=1000,eps_abs=1e-6,eps_rel=1e-6)
        out['SCS_solve_calls']=1;save('one_cold_CPU_indirect_SCS_solve_running')
        result=engine.solve(warm_start=False);out['solver_seconds_including_setup_hint']=time.monotonic()-tick
        out['solver_info']=result['info'];x=result['x'];dual=result['y'];slack=result['s']
        save('one_SCS_returned_before_hint_serialization')
        hints={'scope':'Numerical discovery x/y/s only; not an exact certificate.','source_receipt':'worker-receipt.json',
            'raw_primal_hint':x.tolist(),'raw_dual_hint':dual.tolist(),'raw_conic_slack_hint':slack.tolist()}
        encoded=json.dumps(clean(hints),separators=(',',':'),allow_nan=False).encode();compressed=gzip.compress(encoded,compresslevel=9,mtime=0);HINTS.write_bytes(compressed)
        out['full_hints']={'path':HINTS.relative_to(ROOT).as_posix(),'bytes':len(compressed),'sha256':sha(HINTS),
            'uncompressed_bytes':len(encoded),'uncompressed_sha256':hashlib.sha256(encoded).hexdigest(),'lengths':[len(x),len(dual),len(slack)]}
        if len(compressed)>4*1024**2:
            parts=[]
            for k,start in enumerate(range(0,len(compressed),3*1024**2)):
                p=HERE/(HINTS.name+f'.part{k:03d}');assert not p.exists();b=compressed[start:start+3*1024**2];p.write_bytes(b)
                parts.append({'name':p.name,'bytes':len(b),'sha256':sha(p)})
            out['full_hints']['lossless_parts']=parts
        status=str(result['info'].get('status','')).lower();out['infeasible_dual_ray_hint']='infeasible' in status and bool(np.all(np.isfinite(dual)))
        out['positive_energy_slack_hint']=False
        if np.all(np.isfinite(x)):
            r=bb-A@x;out['raw_energy_slack_hint']=float(x[SLACK]*.001)
            out['minimum_normalized_linear_slack_hint']=float(np.min(r[:SCALAR]));mins=[]
            for block,offset in zip(model['blocks'],offsets):
                n=block['size'];mins.append(float(np.linalg.eigvalsh(unpack_matrix(r[offset:offset+n*(n+1)//2],n))[0]))
            out['PSD_minimum_eigenvalues_hint']=mins;out['minimum_normalized_PSD_eigenvalue_hint']=min(mins)
            out['positive_energy_slack_hint']=out['raw_energy_slack_hint']>1e-7
            if np.all(np.isfinite(slack)):out['packed_primal_residual_infinity_hint']=float(np.linalg.norm(r-slack,np.inf))
        if np.all(np.isfinite(dual)):
            out['dual_b_dot_hint']=float(bb@dual);out['dual_stationarity_infinity_hint']=float(np.linalg.norm(A.T@dual+c,np.inf))
            out['infeasible_ray_Atranspose_infinity_hint']=float(np.linalg.norm(A.T@dual,np.inf))
        out['any_positive_hint']=out['positive_energy_slack_hint'] or out['infeasible_dual_ray_hint']
        save('completed_one_cold_CPU_indirect_SCS_attempt')
    except BaseException as exc:
        out['exception']=repr(exc);out['traceback']=traceback.format_exc();save('worker_stopped_without_retry');raise
    print(json.dumps(clean({k:out.get(k) for k in ['phase','solver_info','solver_seconds_including_setup_hint',
        'raw_energy_slack_hint','minimum_normalized_linear_slack_hint','minimum_normalized_PSD_eigenvalue_hint','any_positive_hint']})),flush=True)
if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
