"""Fixed one-pass rationalization of the frozen numerical infeasibility ray.

No optimizer is invoked. Each PSD block has exactly one eigh; every
positive eigenvalue is retained. Its square-root factor is rounded once
to the prescribed common denominator10^12. The saved integer factors
prove PSD algebraically, independently of any numerical eigenvalue claim.
"""
from pathlib import Path
from fractions import Fraction as F
import ctypes,gzip,hashlib,json,math,os,sys,time
for key in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:os.environ[key]='1'
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
sys.path.insert(0,str(ROOT/'tmp/goal-20261016/python-sdp'))
import numpy as np
OUT=HERE/'quantized-ray.json.gz';RECEIPT=HERE/'quantization.json'
DEN=10**12;LIMIT=1536*1024**2;FILELIMIT=40*1024**2
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def mem():
    from ctypes import wintypes as W
    class PMC(ctypes.Structure):
        _fields_=[('cb',W.DWORD),('PageFaultCount',W.DWORD)]+[(s,ctypes.c_size_t) for s in
            ['PeakWorkingSetSize','WorkingSetSize','QuotaPeakPagedPoolUsage','QuotaPagedPoolUsage','QuotaPeakNonPagedPoolUsage','QuotaNonPagedPoolUsage','PagefileUsage','PeakPagefileUsage']]
    k=ctypes.WinDLL('kernel32');k.GetCurrentProcess.restype=W.HANDLE;p=ctypes.WinDLL('psapi');p.GetProcessMemoryInfo.argtypes=[W.HANDLE,ctypes.POINTER(PMC),W.DWORD]
    m=PMC();m.cb=ctypes.sizeof(m);assert p.GetProcessMemoryInfo(k.GetCurrentProcess(),ctypes.byref(m),m.cb)
    return {'working_set_bytes':m.WorkingSetSize,'peak_working_set_bytes':m.PeakWorkingSetSize,'private_commit_bytes':m.PagefileUsage}
def main():
    assert not OUT.exists() and not RECEIPT.exists();began=time.monotonic()
    paths=[Path(__file__),ROOT/'AGENTS.md',ROOT/'research-goal-20261016/DIRECTION.zh.md',
        ROOT/'research-goal-20261016/direction-state.json',
        ROOT/'research-goal-20261017-actual-sextic-cone/actual-sextic-cone-files.json',
        ROOT/'research-goal-20261017-actual-sextic-cone/actual-sextic-hints.json.gz',
        ROOT/'research-goal-20261017-actual-sextic-cone/worker-receipt.json',
        ROOT/'research-goal-20261017-degree6-static/degree6-model.json.gz']
    initial={p.relative_to(ROOT).as_posix():sha(p) for p in paths}
    assert initial[paths[4].relative_to(ROOT).as_posix()]=='4094f05bf934e083aebd99ed548836b1487681a963f53fe2fa95d930b8ecffd8'
    report={'scope':__doc__,'phase':'loading_frozen_ray','source_sha256_start':initial,
        'denominator':DEN,'eigh_calls':0,'optimizer_calls':0,'Lean_invocations':0,'memory_snapshots':[],
        'actual_certificate':False,'cell_exclusion_proven':False,'new_zero_proportion_proven':False}
    def save(phase):
        m=mem();m.update({'phase':phase,'elapsed_milliseconds':int((time.monotonic()-began)*1000)});report['memory_snapshots'].append(m)
        final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert final==initial
        report.update({'phase':phase,'source_sha256_end':final,'all_inputs_unchanged':True,'elapsed_milliseconds':m['elapsed_milliseconds']})
        RECEIPT.write_text(json.dumps(report,indent=2,allow_nan=False)+'\n',encoding='utf8')
        if m['peak_working_set_bytes']>LIMIT:raise MemoryError('exact-ray1.5GiB RSS guard')
    save('loading_frozen_ray')
    manifest=json.loads(paths[4].read_bytes())
    for field in ['package_files','dependency_files','reconstructed_dependency_files','runtime_dependency_files']:
        for r in manifest[field]:assert (ROOT/r['path']).stat().st_size==r['bytes'] and sha(ROOT/r['path'])==r['sha256']
    native=json.loads(gzip.decompress(paths[5].read_bytes()));worker=json.loads(paths[6].read_bytes());model=json.loads(gzip.decompress(paths[7].read_bytes()))
    dual=np.array(native['raw_dual_hint'],dtype=float);assert len(dual)==111144 and np.all(np.isfinite(dual))
    assert worker['infeasible_dual_ray_hint'] and worker['SCS_solve_calls']==1
    lam=[max(0,int(round(DEN*float(v)))) for v in dual[:14564]]
    deleted=[lam[5793],lam[5794]];lam[5793]=lam[5794]=0
    factors=[];offset=14564;divs=worker['positive_rational_uniform_PSD_divisors']
    assert len(divs)==len(model['blocks'])==73
    for bid,block in enumerate(model['blocks']):
        n=block['size'];matrix=np.zeros((n,n));at=offset
        for j in range(n):
            for i in range(j,n):
                value=dual[at]/(1. if i==j else math.sqrt(2));matrix[i,j]=matrix[j,i]=value;at+=1
        q=model['multipliers'][block['multiplier_id']]
        assert F(divs[bid])==max([F(1)]+[abs(F(v)) for _,v in q['terms']])
        values,vectors=np.linalg.eigh(matrix);report['eigh_calls']+=1
        positive=values>0;L=vectors[:,positive]*np.sqrt(values[positive])
        integers=[[int(round(DEN*float(v))) for v in row] for row in L]
        assert len(integers)==n and all(len(row)==int(np.sum(positive)) for row in integers)
        factors.append({'block_id':bid,'size':n,'multiplier_id':block['multiplier_id'],
            'column_count':int(np.sum(positive)),'factor_denominator':DEN,'factor_numerators_by_row':integers,
            'positive_rational_block_divisor':divs[bid],
            'discovery_eigenvalues_positive':int(np.sum(positive)),
            'discovery_eigenvalues_nonpositive':int(np.sum(~positive))})
        offset=at
        if (bid+1)%10==0:save('quantized_Gram_factors_'+str(bid+1))
    assert offset==111144 and report['eigh_calls']==73
    packet={'schema':'fixed-rounded-scalar-and-integer-Gram-ray-v1','scope':__doc__,
        'scalar_row_count':14564,'moment_column_count':5004,'unbounded_slack_column':5004,
        'scalar_weight_denominator':DEN,'scalar_weight_numerators':lam,
        'forced_zero_scalar_rows':[5793,5794],'rounded_weights_before_forced_zero':deleted,
        'PSD_block_count':73,'PSD_factors':factors,
        'native_scalar_sign':'max(0,round(10^12*y_i))/10^12',
        'trace_semantics':'trace((L*L^T)*M_b(m)/positive_rational_block_divisor); offdiagonal factor2, no sqrt2 in exact expression',
        'source_sha256':initial,'eigh_calls':73,'optimizer_calls':0,'exact_contradiction_checked':False}
    encoded=json.dumps(packet,separators=(',',':'),allow_nan=False).encode();assert len(encoded)<FILELIMIT
    compressed=gzip.compress(encoded,compresslevel=9,mtime=0);assert len(compressed)<FILELIMIT
    tmp=OUT.with_suffix('.partial');tmp.write_bytes(compressed);tmp.replace(OUT)
    report.update({'quantized_packet':{'path':OUT.relative_to(ROOT).as_posix(),'bytes':len(compressed),'sha256':sha(OUT),
        'uncompressed_bytes':len(encoded),'uncompressed_sha256':hashlib.sha256(encoded).hexdigest()},
        'nonzero_scalar_weights':sum(v!=0 for v in lam),
        'nonzero_old_5803_scalar_weights':sum(v!=0 for v in lam[:5803]),
        'nonzero_added_moment_box_weights':sum(v!=0 for v in lam[5803:14383]),
        'nonzero_new_actual_sextic_weights':sum(v!=0 for v in lam[14383:]),
        'positive_eigenvalues_retained':sum(p['column_count'] for p in factors),
        'PSD_factors_with_nonzero_integer_entry':sum(any(any(row) for row in p['factor_numerators_by_row']) for p in factors),
        'forced_zero_soft_rows':[5793,5794],'rounded_weights_before_forced_zero':deleted})
    save('one_fixed_ray_quantization_complete_no_exact_combination_yet')
    print(json.dumps({k:report.get(k) for k in ['phase','elapsed_milliseconds','nonzero_scalar_weights',
        'nonzero_new_actual_sextic_weights','positive_eigenvalues_retained','quantized_packet']}),flush=True)
if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
