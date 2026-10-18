"""Prepared N2 storage-only resumption change, same frozen pooled mathematics.

No mathematics at import. A separate root gate is required. No old LP index is
ever called again. Progress publication is append-only fsync, no os.replace.
"""
from pathlib import Path
from hashlib import sha256
from fractions import Fraction as F
from collections import Counter
import argparse
import gzip
import importlib.util
import json
import os
import struct
import sys
import time
import traceback
import zlib
sys.dont_write_bytecode=True
sys.set_int_max_str_digits(0)
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
OLD=ROOT/'research-goal-20261018-stageN-complete-component-preparation'
H=ROOT/'research-goal-20261018-stageH-ordered-transport'
M=ROOT/'research-goal-20261018-stageM-component-envelope-preparation'
PINS={
 'research-goal-20261018-stageN-complete-component-preparation/files.json':'181473343e98152ab01e622b6346cd37516bb9724477ac26ade56e15dc9b7377',
 'research-goal-20261018-stageN-static-review/files.json':'1cfce252137aa979ad4aa0d2b5f1e5bc9091b1977fd5c36fc069cc1a38d36be2'
}
EXPECTED=15378
OLD_PUBLISHED=675
OLD_DURABLE_CASES=676
OLD_LP_CALLS=675
MAX_NEW_LP_CALLS=14701

def pin(p):
    h=sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def rel(p):return p.relative_to(ROOT).as_posix()
def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':'),allow_nan=False).encode('ascii')+b'\n'
def write(p,x):
    with p.open('xb') as f:f.write(canonical(x));f.flush();os.fsync(f.fileno())
def checked(name):
    p=(ROOT/name).resolve();assert p.is_relative_to(ROOT);return p
def import_frozen(p,name):
    spec=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
def pin_package(p,expected,refs):
    assert pin(p)==expected;refs[rel(p)]=expected;package=load(p)
    for field in ['files','read_only_dependencies','dependencies','read_only_existing_references']:
        for item in package.get(field,[]):
            q=checked(item['path']);assert pin(q)==item['sha256']
            if 'bytes' in item:assert q.stat().st_size==item['bytes']
            if rel(q) in refs:assert refs[rel(q)]==item['sha256']
            refs[rel(q)]=item['sha256']
def size():return sum(p.stat().st_size for p in HERE.iterdir() if p.is_file())
class WorkLimit(Exception):pass
def limit(start,g):
    if time.monotonic()-start>g['work_limits']['elapsed_seconds']:raise WorkLimit('soft_elapsed_limit')
    if size()>g['work_limits']['closed_output_bytes']:raise WorkLimit('soft_output_limit')

def old_members(path):
    """Frozen six-MB attempt only: exact gzip-member offsets, hashes and EOF."""
    data=path.read_bytes();offset=0
    while offset<len(data):
        dec=zlib.decompressobj(31);raw=dec.decompress(data[offset:])
        assert dec.eof and not dec.unconsumed_tail
        n=len(data)-offset-len(dec.unused_data);assert n>0
        value=json.loads(raw);assert canonical(value)==raw
        desc={'path':rel(path),'offset':offset,'bytes':n,'decoded_sha256':sha256(raw).hexdigest(),
            'compressed_member_sha256':sha256(data[offset:offset+n]).hexdigest()}
        yield value,desc
        offset+=n
    assert offset==len(data)

def published_boundary_members(path):
    """Also prove the frozen published byte limit ends at its claimed member."""
    expected=load(OLD/'prefix.json')['streams'][path.name];count=0;matched=expected['records']==0
    for value,desc in old_members(path):
        count+=1
        if count==expected['records']:
            assert desc['offset']+desc['bytes']==expected['bytes'];matched=True
        yield value,desc
    assert matched and count>=expected['records']

class Stream:
    def __init__(self,path):
        self.path=path;self.f=path.open('xb');self.h=sha256();self.records=0
    def append(self,value):
        raw=canonical(value);member=gzip.compress(raw,compresslevel=6,mtime=0);off=self.f.tell()
        self.f.write(member);self.f.flush();os.fsync(self.f.fileno());self.h.update(member);self.records+=1
        return {'path':rel(self.path),'offset':off,'bytes':len(member),'decoded_sha256':sha256(raw).hexdigest(),
            'compressed_member_sha256':sha256(member).hexdigest()}
    def descriptor(self):return {'path':rel(self.path),'bytes':self.f.tell(),'sha256':self.h.hexdigest(),'records':self.records}
    def close(self):self.f.close()

class Commits:
    """Only complete newline records with a valid prior-chain hash publish."""
    def __init__(self,path,indices,streams):
        self.f=path.open('xb');self.path=path;self.indices=indices;self.streams=streams
        self.count=0;self.head='0'*64;self.indexhash=sha256();self.counts=Counter()
    def append(self,index,outcome,old_calls,new_calls,proof_ref):
        assert index==self.indices[self.count]
        self.indexhash.update(struct.pack('<I',index));self.count+=1;self.counts[outcome]+=1
        body={'schema':'N2-append-only-durable-commit-v1','ordinal':self.count,'G_index':index,'outcome':outcome,
            'previous_commit_sha256':self.head,'counts':dict(self.counts),'old_LP_calls':old_calls,
            'new_LP_calls':new_calls,'total_LP_calls':old_calls+new_calls,'proof_record':proof_ref,
            'committed_index_sequence_sha256':self.indexhash.hexdigest(),
            'streams':{s.path.name:s.descriptor() for s in self.streams},
            'unprocessed_suffix_is_not_classified':True}
        digest=sha256(canonical(body)).hexdigest();line=canonical({'body':body,'commit_sha256':digest})
        self.f.write(line);self.f.flush();os.fsync(self.f.fileno());self.head=digest
    def summary(self):return {'committed_records':self.count,'counts':dict(self.counts),
        'commit_head_sha256':self.head,'journal_path':rel(self.path),'journal_bytes':self.f.tell(),
        'committed_index_sequence_sha256':self.indexhash.hexdigest()}
    def close(self):self.f.close()

def inputs(gate_path,gate_sha):
    assert pin(gate_path)==gate_sha;g=load(gate_path)
    assert g['same_model_infrastructure_resumption_passes_authorized']==1
    assert g['old_package_sha256']==PINS[rel(OLD/'files.json')]
    assert g['old_published_records']==OLD_PUBLISHED and g['old_durable_candidate_records']==OLD_DURABLE_CASES
    assert g['old_linprog_calls']==OLD_LP_CALLS and g['maximum_new_linprog_calls']==MAX_NEW_LP_CALLS
    assert g['same_pooled_model_helpers_required'] is True and g['repeated_old_LP_calls_authorized']==0
    assert g['per_new_case_maximum_linprog_calls']==1 and g['maximum_total_linprog_calls']==15376
    assert g['stop_at_first_exact_Below'] is True
    assert g['auxiliary_calls_math_support_precision_parameter_retries_authorized']==0
    assert g['new_FS_anchors_kernel_points_or_Lean_authorized']==0
    assert g['progress_protocol']=='append_only_fsync_commit_chain_no_replace'
    for key in ['elapsed_seconds','closed_output_bytes']:
        assert 0<g['work_limits'][key]<g['resource_limits'][key]
    refs={rel(gate_path):gate_sha}
    for name,expected in PINS.items():pin_package(checked(name),expected,refs)
    pin_package(HERE/'prepared-files.json',g['prepared_manifest_sha256'],refs)
    old=import_frozen(OLD/'discover_complete.py','N2_frozen_N_utilities')
    assert g['solver_method']==old.METHOD and g['solver_options']==old.OPTIONS
    assert int(g['target_c_numerator'])==893766123055294719 and int(g['denominator'])==10**20
    runtime=load(M/'external-runtime.json');external=old.runtime_hashes(runtime)
    assert str(Path(sys.executable))==runtime['python_executable']
    data=(H/'remaining-indices.u32.bin').read_bytes();indices=[v[0] for v in struct.iter_unpack('<I',data)]
    assert len(indices)==EXPECTED and indices==sorted(set(indices))
    p=load(OLD/'prefix.json');failure=load(OLD/'failure.json');terminal=load(OLD/'terminal.json')
    assert p['committed_records']==OLD_PUBLISHED and failure['linprog_calls_started']==OLD_LP_CALLS
    assert failure['committed_records']==OLD_DURABLE_CASES and terminal['exit_code']==1
    assert terminal['inputs_unchanged_after_terminal'] and terminal['external_runtime_unchanged_after_terminal']
    for name,desc in p['streams'].items():
        q=checked(desc['path']);h=sha256()
        with q.open('rb') as f:
            left=desc['bytes']
            while left:
                b=f.read(min(left,1048576));assert b;h.update(b);left-=len(b)
        assert h.hexdigest()==desc['sha256']
    return g,refs,old,runtime,external,indices

def execute(gate_path,gate_sha):
    assert __debug__
    for name in ['started.json','result.json','failure.json','progress-commits.jsonl','recovery.json']:
        assert not (HERE/name).exists(),('existing_attempt_no_retry',name)
    start=time.monotonic();stage='inputs';refs={};external={};streams=[];commits=None;intents=None;new_calls=0
    try:
        g,refs,old,runtime,external,indices=inputs(gate_path,gate_sha)
        write(HERE/'started.json',{'schema':'N2-same-pooled-model-storage-resumption-start-v1','pid':os.getpid(),
            'inputs_sha256':refs,'external_runtime_sha256_start':external,'old_actual_LP_calls':OLD_LP_CALLS,
            'new_LP_calls':0,'repeated_old_LP_calls_authorized':0,'progress_protocol':g['progress_protocol'],
            'process_runtime_cache_starts_empty':True,'mathematical_support_policy_unchanged':True})
        alg=import_frozen(OLD/'component_model.py','N2_frozen_pooled_math')
        recon=import_frozen(OLD/'reconstruct_support.py','N2_frozen_support_policy')
        check=import_frozen(OLD/'check_raw_certificate.py','N2_frozen_raw_certificate_check')
        stage='original_source_and_cache_identity';limit(start,g)
        source,mathmod,core,cells,traces,jcache=old.initialize_originals(refs)
        cache={};cache_refs={}
        for w,desc in published_boundary_members(OLD/'original-components.jsonl.gz'):
            cid=w['cell_id'];assert cid not in cache
            jc=jcache[cid];assert w['canonical_Cstar']==jc['canonical_Cstar'] and w['canonical_J']==jc['canonical_J']
            assert sha256(canonical(w['terms'])).hexdigest()==jc['original_term_components_sha256']
            assert w['state_sha256']==cells[cid]['state_sha256']==jc['state_sha256']
            assert w['witness']==cells[cid]['witness']==jc['witness']
            cache[cid]=w;cache_refs[cid]=desc
        old_intents=[json.loads(line) for line in (OLD/'call-intents.jsonl').read_bytes().splitlines()]
        assert len(old_intents)==OLD_LP_CALLS
        called=set();intent_by_index={}
        for ordinal,item in enumerate(old_intents,1):
            assert item['linprog_call_number']==ordinal and item['G_index'] not in called
            called.add(item['G_index']);intent_by_index[item['G_index']]=item
            assert item['method']==old.METHOD and item['options']==old.OPTIONS
        old_native={}
        for value,desc in published_boundary_members(OLD/'native-results.jsonl.gz'):
            index=value['G_index'];assert index not in old_native and index in called
            assert value['call_number']==intent_by_index[index]['linprog_call_number']
            assert value['native_row_ids']==intent_by_index[index]['native_row_ids']
            old_native[index]=(value,desc)
        assert set(old_native)==called
        old_cases=list(published_boundary_members(OLD/'case-records.jsonl.gz'))
        assert len(old_cases)==OLD_DURABLE_CASES
        assert [v['G_index'] for v,_ in old_cases]==indices[:OLD_DURABLE_CASES]
        originals=Stream(HERE/'new-original-components.jsonl.gz')
        native=Stream(HERE/'new-native-results.jsonl.gz');records=Stream(HERE/'case-records.jsonl.gz')
        streams=[originals,native,records];commits=Commits(HERE/'progress-commits.jsonl',indices,streams)
        intents=(HERE/'new-call-intents.jsonl').open('xb')
        def model_for(index):
            pair,chart=divmod(index,4);i,j=divmod(pair,old.N);windows=[]
            for cid in (i,j):
                if cid not in cache:
                    w,_=core.extract_original_affine(cells[cid],source,mathmod,traces);jc=jcache[cid]
                    assert w['canonical_Cstar']==jc['canonical_Cstar'] and w['canonical_J']==jc['canonical_J']
                    assert sha256(canonical(w['terms'])).hexdigest()==jc['original_term_components_sha256']
                    assert w['state_sha256']==jc['state_sha256'] and w['witness']==jc['witness']
                    cache_refs[cid]=originals.append(w);cache[cid]=w
                windows.append(cache[cid])
            model=alg.assemble(windows,cells,source,mathmod.ALL,chart)
            assert model['group_count']==42 and model['columns_count']==51 and model['full_balance_coordinates']==52
            return model,i,j,chart
        stage='recover_all_frozen_complete_members_no_LP'
        for ordinal,(record,desc) in enumerate(old_cases,1):
            limit(start,g);index=record['G_index']
            if record['outcome']=='deduction_Lower':
                assert index in old.DEDUCTIONS and record['dependency']==old.DEDUCTIONS[index]
                verification={'Lower':True,'Below':False,'deduction':record['dependency']}
            else:
                assert index in called
                model,_,_,_=model_for(index);digest=sha256(canonical(model)).hexdigest()
                assert digest==record['model_sha256']==intent_by_index[index]['model_sha256']
                nv,nd=old_native[index]
                for key in ['offset','bytes','decoded_sha256','compressed_member_sha256']:
                    assert record['native_record'][key]==nd[key]
                verification=check.verify(model,record['normalized_exact_reconstruction'])
                assert verification==record['separate_raw_verification']
                for primal in [record['normalized_exact_reconstruction'].get('exact_primal')]:
                    if primal is not None:
                        assert alg.sparse_primal_check(model,list(map(F,primal['raw_primal'])),cells)==primal['checks']
                expected='Lower' if verification['Lower'] else 'Below' if verification['Below'] else 'unresolved'
                assert record['outcome']==expected
            proof=records.append({'G_index':index,'outcome':record['outcome'],'recovered_original_record':desc,
                'was_originally_published':ordinal<=OLD_PUBLISHED,'separate_raw_replay':verification,
                'LP_calls_during_recovery':0})
            commits.append(index,record['outcome'],OLD_LP_CALLS,new_calls,proof)
            if record['outcome']=='Below':break
        write(HERE/'recovery.json',{'schema':'N2-original-durable-members-recovery-v1','old_published':OLD_PUBLISHED,
            'old_complete_candidate_members':OLD_DURABLE_CASES,'accepted_recovered_records':commits.count,
            'old_LP_calls_bound_to_native_and_intents':len(called),'repeated_LP_calls':0,
            'recovered_unpublished_tail_accepted_only_after_exact_raw_replay':commits.count>OLD_PUBLISHED,
            'commit_head_sha256':commits.head,'whole_original_gzip_members_and_EOF_verified':True})
        if not commits.counts['Below']:
            stage='new_runtime_import'
            import numpy as np
            import scipy
            from scipy.optimize import linprog
            assert np.__version__=='2.5.2' and scipy.__version__=='1.18.1'
            assert old.runtime_hashes(runtime)==external
            for index in indices[commits.count:]:
                limit(start,g);stage='new_case_'+str(index)
                if index in old.DEDUCTIONS:
                    proof=records.append({'G_index':index,'outcome':'deduction_Lower','dependency':old.DEDUCTIONS[index]})
                    commits.append(index,'deduction_Lower',OLD_LP_CALLS,new_calls,proof);continue
                assert index not in called,'no_old_or_duplicate_LP_call'
                model,i,j,chart=model_for(index);digest=sha256(canonical(model)).hexdigest()
                c,A,b,selected=alg.native_arrays(model,np);limit(start,g)
                assert new_calls<MAX_NEW_LP_CALLS;new_calls+=1;called.add(index)
                intent={'G_index':index,'new_call_number':new_calls,'total_call_number':OLD_LP_CALLS+new_calls,
                    'model_sha256':digest,'method':old.METHOD,'options':old.OPTIONS,'native_row_ids':selected}
                intents.write(canonical(intent));intents.flush();os.fsync(intents.fileno())
                result=linprog(c,A_ub=A,b_ub=b,bounds=[(None,None)]*model['columns_count'],method=old.METHOD,options=old.OPTIONS)
                raw=old.safe_native(dict(result));nr=native.append({'G_index':index,'new_call_number':new_calls,
                    'native_row_ids':selected,'result':raw})
                hint=dict(raw);ineq=dict(raw.get('ineqlin',{}));marg=ineq.get('marginals')
                if isinstance(marg,list) and len(marg)==len(selected):
                    fullmarg=[0.0]*len(model['rows'])
                    for rid,value in zip(selected,marg):fullmarg[rid]=value
                    ineq['marginals']=fullmarg
                hint['ineqlin']=ineq
                exact=recon.reconstruct(hint,model,alg,cells);verification=check.verify(model,exact)
                outcome='Lower' if verification['Lower'] else 'Below' if verification['Below'] else 'unresolved'
                proof=records.append({'G_index':index,'pair':[i,j],'chart':old.CHARTS[chart],'outcome':outcome,
                    'native_record':nr,'model_sha256':digest,'original_components':{str(cid):cache_refs[cid] for cid in (i,j)},
                    'normalized_exact_reconstruction':exact,'separate_raw_verification':verification,
                    'native_status_not_mathematical_evidence':raw.get('status'),
                    'Below_is_not_actual_F_counterexample':True,'unresolved_is_not_nonempty':True})
                commits.append(index,outcome,OLD_LP_CALLS,new_calls,proof)
                print(json.dumps({**commits.summary(),'new_LP_calls':new_calls,'total_LP_calls':OLD_LP_CALLS+new_calls,
                    'last_G_index':index,'seconds':time.monotonic()-start}),flush=True)
                if outcome=='Below':break
        stage='final_hashes';after={name:pin(ROOT/name) for name in refs};assert after==refs
        assert old.runtime_hashes(runtime)==external
        complete=commits.count==EXPECTED;all_lower=complete and not commits.counts['unresolved'] and not commits.counts['Below']
        write(HERE/'result.json',{'schema':'N2-same-pooled-model-result-v1','pid':os.getpid(),'seconds':time.monotonic()-start,
            **commits.summary(),'complete_original_H_range':complete,'all_range_Lower_candidate':all_lower,
            'first_exact_Below_found':commits.counts['Below']==1,'old_LP_calls':OLD_LP_CALLS,
            'new_LP_calls':new_calls,'total_LP_calls':OLD_LP_CALLS+new_calls,'repeated_old_LP_calls':0,
            'inputs_sha256_start':refs,'inputs_sha256_end':after,'external_runtime_sha256_start':external,
            'external_runtime_sha256_end':old.runtime_hashes(runtime),'independent_mathematical_replay_pending':True,
            'actual_Lean_or_unconditional_global_floor_proven':False,'website_source_runtime_payload_budget':'unknown',
            'automatic_retry':False,'storage_protocol_only_changed':True})
    except WorkLimit as exc:
        write(HERE/'inconclusive.json',{'stage':stage,'reason':str(exc),'seconds':time.monotonic()-start,
            'progress':commits.summary() if commits else None,'new_LP_calls_started':new_calls,
            'old_LP_calls':OLD_LP_CALLS,'unprocessed_suffix_not_classified':True,'automatic_retry':False})
    except BaseException as exc:
        write(HERE/'failure.json',{'stage':stage,'error':repr(exc),'traceback':traceback.format_exc(),
            'pid':os.getpid(),'seconds':time.monotonic()-start,'progress':commits.summary() if commits else None,
            'new_LP_calls_started':new_calls,'old_LP_calls':OLD_LP_CALLS,'automatic_retry':False})
        raise
    finally:
        if commits:commits.close()
        if intents:intents.close()
        for stream in streams:stream.close()

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--execute-authorized-same-model-N2',action='store_true')
    ap.add_argument('--gate');ap.add_argument('--gate-sha256');args=ap.parse_args()
    if not args.execute_authorized_same_model_N2:
        print(json.dumps({'prepared_only':True,'mathematical_runs':0,'solver_calls':0}));return
    assert args.gate and args.gate_sha256
    execute(checked(args.gate),args.gate_sha256)
if __name__=='__main__':main()
