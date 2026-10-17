"""Exact aggregation of the181 new unsoftened actual-sextic scalar rows.

Store one canonical exact row hash per row and its exact fixed-rational
rank1 slack. Store the corresponding rounded numerical CSR arrays in NPZ.
The factored exact source stays authoritative; no huge repeated Fraction
matrix is serialized. This prepares no solver, warm seed or point fit.
"""
from pathlib import Path
from fractions import Fraction as F
import ctypes,gzip,hashlib,json,os,sys,time
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;PACK=ROOT/'research-goal-20261017-actual-sextic-static'
sys.path.insert(0,str(ROOT/'tmp/goal-20261016/python-sdp'))
import numpy as np
OUT=HERE/'aggregation.json';ROWS=HERE/'new-row-hashes.json';FLOAT=HERE/'new-rows-float.npz';LIMIT=1536*1024**2
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def memory():
    from ctypes import wintypes as W
    class PMC(ctypes.Structure):
        _fields_=[('cb',W.DWORD),('PageFaultCount',W.DWORD)]+[(s,ctypes.c_size_t) for s in
            ['PeakWorkingSetSize','WorkingSetSize','QuotaPeakPagedPoolUsage','QuotaPagedPoolUsage','QuotaPeakNonPagedPoolUsage','QuotaNonPagedPoolUsage','PagefileUsage','PeakPagefileUsage']]
    k=ctypes.WinDLL('kernel32');k.GetCurrentProcess.restype=W.HANDLE;p=ctypes.WinDLL('psapi');p.GetProcessMemoryInfo.argtypes=[W.HANDLE,ctypes.POINTER(PMC),W.DWORD]
    m=PMC();m.cb=ctypes.sizeof(m);assert p.GetProcessMemoryInfo(k.GetCurrentProcess(),ctypes.byref(m),m.cb)
    return {'working_set_bytes':m.WorkingSetSize,'peak_working_set_bytes':m.PeakWorkingSetSize,'private_commit_bytes':m.PagefileUsage}
def add(p,q,c=F(1)):
    for m,a in q.items():
        v=p.get(m,F(0))+c*a
        if v:p[m]=v
        else:p.pop(m,None)
    return p

def main():
    assert not any(p.exists() for p in [OUT,ROWS,FLOAT]);began=time.monotonic()
    paths=[Path(__file__),PACK/'actual-sextic-files.json',PACK/'actual-sextic.json.gz',PACK/'sextic-build.json',
        ROOT/'research-goal-20261017-degree6-static/degree6-model.json.gz',
        ROOT/'research-goal-20261017-actual-sextic-audit/independent-replay.json']
    pins={p.relative_to(ROOT).as_posix():sha(p) for p in paths};manifest=json.loads(paths[1].read_bytes())
    for r in manifest['package_files']+manifest['dependency_files']:assert sha(ROOT/r['path'])==r['sha256']
    report={'scope':__doc__,'phase':'loading_exact_source','source_sha256_start':pins,'memory_snapshots':[],
        'solver_calls':0,'new_points_or_fits':0,'Lean_invocations':0,'strict_feasibility_or_exclusion_claimed':False}
    def save(phase):
        m=memory();m['phase']=phase;m['elapsed_milliseconds']=int((time.monotonic()-began)*1000);report['memory_snapshots'].append(m)
        final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert final==pins
        report.update({'phase':phase,'source_sha256_end':final,'all_inputs_unchanged':True,'elapsed_milliseconds':m['elapsed_milliseconds']})
        OUT.write_text(json.dumps(report,indent=2,allow_nan=False)+'\n',encoding='utf8')
        if m['peak_working_set_bytes']>LIMIT:raise MemoryError('aggregation1.5GiB RSS guard')
    save('loading_exact_source')
    raw=gzip.decompress(paths[2].read_bytes());packet=json.loads(raw);build=json.loads(paths[3].read_bytes())
    assert hashlib.sha256(raw).hexdigest()==build['packet_uncompressed_sha256'];del raw
    base=json.loads(gzip.decompress(paths[4].read_bytes()));mon=[tuple(m) for m in packet['monomials']];mi={m:k for k,m in enumerate(mon)}
    assert len(mon)==5005 and packet['monomials']==base['monomials'] and packet['energy_slack_column']==5004
    assert packet['new_scalar_row_count']==181 and packet['unsoftened_absolute_energy_row'] and packet['new_PSD_blocks']==0
    powers=[{mon[k]:F(v) for k,v in p['terms']} for p in packet['span_powers']]
    edges=packet['edges'];incident=packet['coordinate_incident_edges'];pressure={mon[k]:F(v) for k,v in packet['pressure_polynomial']}
    y=[F((-1)**r*(r+1),19) for r in range(9)];point=[]
    for m in mon:
        value=F(1)
        for r in m:value*=y[r]
        point.append(value)
    def evalpoly(p):return sum(a*point[mi[m]] for m,a in p.items())
    edge_L=[];edge_U=[];edge_E=[]
    for e in edges:
        atoms=[]
        for field in ['absolute_L6_coefficients_in_d','derivative_U5_coefficients_in_d','derivative_E6_coefficients_in_d']:
            poly={}
            for k,value in enumerate(e[field]):add(poly,powers[e['power_ids'][k]],F(value)*F(e['weight']))
            atoms.append(poly)
        edge_L.append(atoms[0]);edge_U.append(atoms[1]);edge_E.append(atoms[2])
    L=pressure.copy()
    for p in edge_L:add(L,p)
    P=[];E=[];b=list(map(F,packet['pressure_coefficients_b']))
    for r in range(9):
        pr={():b[r]};er={}
        for eid in incident[r]:add(pr,edge_U[eid]);add(er,edge_E[eid])
        P.append(pr);E.append(er)
    save('exact_L6_P5_E6_aggregated_same5005_monomials')
    # Factored evaluations are computed separately from row aggregation.
    edgevalues=[]
    for e in edges:
        d=sum(F(v)*point[k] for k,v in e['d_polynomial']);vals=[]
        for field in ['absolute_L6_coefficients_in_d','derivative_U5_coefficients_in_d','derivative_E6_coefficients_in_d']:
            vals.append(F(e['weight'])*sum(F(v)*d**k for k,v in enumerate(e[field])))
        edgevalues.append(vals)
    Lvalue=evalpoly(pressure)+sum(v[0] for v in edgevalues)
    Pvalues=[b[r]+sum(edgevalues[eid][1] for eid in incident[r]) for r in range(9)]
    Evalues=[sum(edgevalues[eid][2] for eid in incident[r]) for r in range(9)]
    data=[];indices=[];indptr=[0];bounds=[];records=[];streamhash=hashlib.sha256()
    for descriptor in packet['new_scalar_rows']:
        if descriptor['kind']=='absolute_energy_L6':
            polynomial=L;const=F(descriptor['bound'])-L.get((),F(0));coef={mi[m]-1:a for m,a in polynomial.items() if m};exact_expected=F(descriptor['bound'])-Lvalue
            meta=['actual_sextic_absolute_energy_unsoftened']
        else:
            r=descriptor['coordinate'];test=descriptor['test_monomial_id'];sign=descriptor['sign'];suffix=mon[test]
            q=E[r].copy();shift={tuple(sorted(m+suffix)):a for m,a in P[r].items()};add(q,shift,F(sign))
            assert all(len(m)<=6 for m in q)
            const=q.get((),F(0));coef={mi[m]-1:-a for m,a in q.items() if m}
            exact_expected=Evalues[r]+sign*point[test]*Pvalues[r];meta=['actual_sextic_free_KKT',r,test,sign]
        scale=max([F(1,1000),abs(const)]+[abs(a) for a in coef.values()]);assert scale>0
        assert all(0<=k<5004 for k in coef)
        canonical={'coefficients':[[k,str(a)] for k,a in sorted(coef.items())],'bound':str(const),'scale':str(scale),'meta':meta}
        exact=const-sum(a*point[k+1] for k,a in coef.items());assert exact==exact_expected
        raw=json.dumps(canonical,sort_keys=True,separators=(',',':')).encode();streamhash.update(raw+b'\n')
        records.append({'row':descriptor['id'],'meta':meta,'nonzero_coefficients':len(coef),'bound':str(const),'scale':str(scale),
            'exact_canonical_row_sha256':hashlib.sha256(raw).hexdigest(),'fixed_rational_rank1_exact_slack':str(exact),
            'fixed_rational_rank1_normalized_slack':str(exact/scale),'energy_slack_coefficient_absent':True})
        for k,a in sorted(coef.items()):indices.append(k);data.append(float(a/scale))
        indptr.append(len(data));bounds.append(float(const/scale))
        if len(records)%30==0:save('exact_rows_aggregated_'+str(len(records)))
    assert len(records)==181 and all(r['energy_slack_coefficient_absent'] for r in records)
    np.savez_compressed(FLOAT,data=np.array(data,dtype=np.float64),indices=np.array(indices,dtype=np.int32),
        indptr=np.array(indptr,dtype=np.int32),b=np.array(bounds,dtype=np.float64),shape=np.array([181,5005],dtype=np.int32))
    rowdoc={'scope':__doc__,'canonical_row_schema':'sort_keys=True,separators=(comma,colon),UTF8; exact Fraction strings; JSONL newline',
        'exact_canonical_rows_JSONL_sha256':streamhash.hexdigest(),'rows':records,'fixed_rank1_y':list(map(str,y)),
        'fixed_rank1_is_only_packing_test_not_warm_seed_or_feasibility_claim':True}
    ROWS.write_text(json.dumps(rowdoc,indent=2,allow_nan=False)+'\n',encoding='utf8')
    report.update({'new_unsoftened_rows':181,'nonzero_numeric_coefficients':len(data),'shape':[181,5005],
        'exact_canonical_rows_JSONL_sha256':streamhash.hexdigest(),'all_new_rows_have_no_energy_slack':True,
        'all181_exact_rank1_row_vs_factored_identities_checked':True,
        'row_hashes_file':{'path':ROWS.relative_to(ROOT).as_posix(),'bytes':ROWS.stat().st_size,'sha256':sha(ROWS)},
        'numeric_CSR_file':{'path':FLOAT.relative_to(ROOT).as_posix(),'bytes':FLOAT.stat().st_size,'sha256':sha(FLOAT)},
        'new_energy_row_unsoftened':True,'aggregate_full_Fraction_rows_not_serialized':True})
    save('all181_new_exact_rows_prepared_no_solver')
    print(json.dumps({'phase':report['phase'],'newrows':181,'nnz':len(data),'NPZ_bytes':FLOAT.stat().st_size,
        'elapsed_milliseconds':report['elapsed_milliseconds'],'peak_working_set_bytes':max(m['peak_working_set_bytes'] for m in report['memory_snapshots'])}),flush=True)
if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
