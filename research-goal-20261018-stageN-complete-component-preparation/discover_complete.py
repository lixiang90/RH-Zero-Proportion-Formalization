"""Prepared N pooled complete-domain discovery. No mathematics at import.

Execution requires a separate immutable root gate. One HiGHS call per original
H index not already Lower by J or M; no retry, support search, new anchors,
kernel queries or Lean. Every native result is durable before reconstruction.
"""
from pathlib import Path
from fractions import Fraction as F
from hashlib import sha256
from collections import Counter
import argparse
import gzip
import importlib.util
import json
import math
import os
import struct
import sys
import time
import traceback

sys.dont_write_bytecode=True
sys.set_int_max_str_digits(0)
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
BASE=ROOT/'research-goal-20261018-record-baseline-replay'
B=ROOT/'research-goal-20261018-stageB-classification'
J=ROOT/'research-goal-20261018-stageJ-fixed-basis-preparation'
H=ROOT/'research-goal-20261018-stageH-ordered-transport'
M=ROOT/'research-goal-20261018-stageM-component-envelope-preparation'
I=ROOT/'research-goal-20261018-stageI-original-affine-point'
N=1187
EXPECTED=15378
DEDUCTIONS={2417:'verified_M_unpooled_Lower_implies_pooled_Lower',5331088:'verified_J_Lower'}
CHARTS=('id/id','id/rev','rev/id','rev/rev')
METHOD='highs-ds'
OPTIONS={'presolve':True,'time_limit':180.0,'maxiter':100000,
    'primal_feasibility_tolerance':1e-7,'dual_feasibility_tolerance':1e-7,'threads':1}
PINS={
 'research-goal-20261018-record-source-audit/snapshot/Solution.lean':'f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf',
 'research-goal-20261018-record-baseline-replay/files.json':'03f3426e29ab7355ed76729dcaa3a3ba754154ae39ff5e9632bae2c57eff069f',
 'research-goal-20261018-stageB-classification/files.json':'3f9408f2cf1ceae12339456da034d9e8f175f828cf2d53a652339ee79eec89ad',
 'research-goal-20261018-stageH-ordered-transport/remaining-indices.u32.bin':'c740852a5757983f462f3a78eb05d1aca5410ffb4077682e3afa48d6f7943559',
 'research-goal-20261018-stageH-independent/audit-files.json':'a0018aa4ce33e4cb6cea2019739e857fa3a1b58cc8b48f001e17d651e1dcbb3a',
 'research-goal-20261018-stageJ-fixed-basis-preparation/files.json':'90726f8987fd69820f70a63cc55c22f279a872263ced314fa41a452d4f1b09cd',
 'research-goal-20261018-stageJ-independent/audit-files.json':'32de2e9381d1c103209c89b8f007d29815746a398c5c3d197f7762a727f55005',
 'research-goal-20261018-stageM-component-envelope-preparation/files.json':'129c706dcab0aff47ef54a0f249e5d0a49e8f718476faaf453681e73858526d8',
 'research-goal-20261018-stageM-independent/audit-files.json':'2887e7527180ca2b77d7779cd5c25ada853d040e82d0380a125f7f821c907be4',
 'research-goal-20261018-component-flow-normalization-static/files.json':'3b322277203c58be7885b73bf2301024f00bf1e48ac33ae6cfe54aa5daec79ad',
 'research-goal-20261018-component-flow-normalization-independent/audit-files.json':'bcf78974d087ff0ba1d1d570261be9fa1fe41faed7a8fe7b414d480f3f208cbb',
 'research-goal-20261018-pooled-component-static/files.json':'62f4ba187ed59aa8e10aee0e772cfcbb602ba86d07e6f634ad6c9630cd12ab5d'
}

def pin(p):
    h=sha256()
    with p.open('rb') as f:
        for block in iter(lambda:f.read(1048576),b''):h.update(block)
    return h.hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def rel(p):return p.relative_to(ROOT).as_posix()
def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':'),allow_nan=False).encode('ascii')+b'\n'
def write(p,x):
    with p.open('xb') as f:f.write(canonical(x));f.flush();os.fsync(f.fileno())
def atomic(p,x):
    tmp=p.with_name(p.name+'.tmp')
    with tmp.open('wb') as f:f.write(canonical(x));f.flush();os.fsync(f.fileno())
    os.replace(tmp,p)
def checked(name):
    p=(ROOT/name).resolve();assert p.is_relative_to(ROOT);return p
def import_frozen(p,name):
    spec=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
def pin_package(p,expected,refs):
    assert pin(p)==expected;refs[rel(p)]=expected;data=load(p)
    for field in ['files','read_only_dependencies','read_only_existing_references','dependencies']:
        for row in data.get(field,[]):
            q=checked(row['path']);assert pin(q)==row['sha256']
            if 'bytes' in row:assert q.stat().st_size==row['bytes']
            if rel(q) in refs:assert refs[rel(q)]==row['sha256']
            refs[rel(q)]=row['sha256']
def runtime_hashes(runtime):
    out={}
    for row in runtime['files']:
        p=Path(row['path']);assert p.is_absolute() and p.stat().st_size==row['bytes']
        out[str(p)]=pin(p);assert out[str(p)]==row['sha256']
    return out
def package_size():return sum(p.stat().st_size for p in HERE.iterdir() if p.is_file())
class WorkLimit(Exception):pass
def limit(start,gate):
    if time.monotonic()-start>gate['work_limits']['elapsed_seconds']:raise WorkLimit('soft_elapsed_limit')
    if package_size()>gate['work_limits']['closed_output_bytes']:raise WorkLimit('soft_output_limit')

class GzipJournal:
    """One lossless gzip member per record; fsync precedes prefix publication."""
    def __init__(self,path):
        self.path=path;self.raw=path.open('xb');self.hash=sha256();self.records=0
    def append(self,record):
        data=canonical(record);member=gzip.compress(data,compresslevel=6,mtime=0)
        offset=self.raw.tell();self.raw.write(member);self.raw.flush();os.fsync(self.raw.fileno())
        self.hash.update(member);self.records+=1
        return {'offset':offset,'bytes':len(member),'decoded_sha256':sha256(data).hexdigest(),
            'compressed_member_sha256':sha256(member).hexdigest()}
    def descriptor(self):return {'path':rel(self.path),'bytes':self.raw.tell(),
        'sha256':self.hash.hexdigest(),'records':self.records}
    def close(self):self.raw.close()

def safe_native(value):
    if isinstance(value,dict):return {str(k):safe_native(v) for k,v in value.items()}
    if isinstance(value,(list,tuple)):return [safe_native(v) for v in value]
    if hasattr(value,'tolist'):return safe_native(value.tolist())
    if isinstance(value,float):return value if math.isfinite(value) else str(value)
    if value is None or isinstance(value,(str,bool,int)):return value
    if hasattr(value,'item'):return safe_native(value.item())
    return repr(value)

def read_uleb(f):
    n=shift=0;data=bytearray()
    while True:
        b=f.read(1);assert b;v=b[0];data+=b;n|=(v&127)<<shift
        if v<128:break
        shift+=7;assert shift<100000
    if len(data)>1:assert data[-1]!=0
    return n

def inputs(gate_path,gate_sha):
    assert pin(gate_path)==gate_sha;g=load(gate_path)
    assert g['complete_component_discovery_passes_authorized']==1
    assert g['physical_span_pooling'] is True and g['per_case_maximum_linprog_calls']==1
    assert g['expected_H_remaining']==EXPECTED and g['maximum_linprog_calls']==EXPECTED-len(DEDUCTIONS)
    assert g['explicit_deduction_indices']==sorted(DEDUCTIONS)
    assert g['chart_order']==list(CHARTS) and g['index_formula']=='((i*1187+j)*4+chart)'
    assert int(g['target_c_numerator'])==893766123055294719 and int(g['denominator'])==10**20
    assert g['solver_method']==METHOD and g['solver_options']==OPTIONS
    assert g['auxiliary_calls_retries_new_FS_anchors_kernel_or_Lean_authorized']==0
    assert g['stop_at_first_exact_Below'] is True and g['reflection_orbit_LP_reuse'] is False
    assert g['native_same_S_max_E_pruning'] is True
    for field in ['resource_limits','work_limits']:
        assert g[field]['elapsed_seconds']>0 and g[field]['closed_output_bytes']>0
    assert g['work_limits']['elapsed_seconds']<g['resource_limits']['elapsed_seconds']
    assert g['work_limits']['closed_output_bytes']<g['resource_limits']['closed_output_bytes']
    refs={rel(gate_path):gate_sha}
    for name,expected in PINS.items():
        p=checked(name);assert pin(p)==expected;refs[name]=expected
        if p.name in ['files.json','audit-files.json']:pin_package(p,expected,refs)
    pin_package(HERE/'prepared-files.json',g['prepared_manifest_sha256'],refs)
    runtime=load(M/'external-runtime.json');external=runtime_hashes(runtime)
    assert str(Path(sys.executable))==runtime['python_executable']
    h=load(ROOT/'research-goal-20261018-stageH-independent/independent-review.json')
    j=load(ROOT/'research-goal-20261018-stageJ-independent/independent-review.json')
    m=load(ROOT/'research-goal-20261018-stageM-independent/independent-review.json')
    assert h['passed'] and h['counts']=={'Empty':4460,'unresolved':EXPECTED}
    assert j['passed'] and j['records']==EXPECTED and j['all_effective_N_over_d_checked_including_below_target']
    assert m['passed'] and m['valid_local_Lower'] is True and load(M/'result.json')['outcome']=='Lower'
    old_model=load(M/'model.json')
    assert old_model['fixed_cells']==[0,604] and old_model['chart']=='id/rev'
    assert ((0*N+604)*4+1)==2417 and old_model['target']==4*(32768*1024*10**10)*893766123055294719
    data=(H/'remaining-indices.u32.bin').read_bytes();assert len(data)==4*EXPECTED
    indices=[v[0] for v in struct.iter_unpack('<I',data)]
    assert indices==sorted(set(indices)) and set(DEDUCTIONS)<=set(indices)
    jremaining={v[0] for v in struct.iter_unpack('<I',(J/'remaining-indices.u32.bin').read_bytes())}
    assert set(indices)-jremaining=={5331088} and jremaining<=set(indices)
    # Existing J records only, no FS or model evaluation. Bind the deduction.
    with (J/'classifications.bin').open('rb') as f:
        assert f.read(5)==b'JLB2\n';lowers=[]
        for index in indices:
            assert struct.unpack('<I',f.read(4))[0]==index;tag=f.read(1)[0];assert tag in (0,1,2,3)
            if tag in (1,2):
                u=read_uleb(f);numerator=(u>>1)^-(u&1)
                if tag==1:lowers.append(index)
        assert not f.read(1) and lowers==[5331088]
    return g,refs,runtime,external,indices

def initialize_originals(refs):
    parser=import_frozen(BASE/'packing_parser_v3.py','N_frozen_parser')
    mathmod=import_frozen(BASE/'record_math.py','N_frozen_math')
    original=import_frozen(I/'evaluate_once.py','N_frozen_locator')
    core=import_frozen(J/'original_affine_core.py','N_frozen_generic_core')
    core.ORIGINAL_LOCATOR=original.locate_original_payload
    source=parser.load_model();mathmod.configure(source)
    assert source['CN']==893616123055294719 and len(source['TS'])==34
    cells={}
    with gzip.open(B/'exception-cells.jsonl.gz','rt',encoding='ascii') as f:
        for line in f:
            c=json.loads(line);cells[c['exception_id']]=c
    assert set(cells)==set(range(N))
    traces={}
    with gzip.open(BASE/'baseline-events.jsonl.gz','rt',encoding='ascii') as f:
        for line in f:
            e=json.loads(line);traces[e['root'],e['pos']]=e
    jcache={}
    with (J/'affine-cache.jsonl').open('r',encoding='ascii') as f:
        for line in f:
            c=json.loads(line);jcache[c['cell_id']]=c
    return source,mathmod,core,cells,traces,jcache

def execute(gate_path,gate_sha):
    assert __debug__
    for name in ['started.json','result.json','prefix.json','failure.json','native-results.jsonl.gz','case-records.jsonl.gz']:
        assert not (HERE/name).exists(),('existing_attempt_no_retry',name)
    start=time.monotonic();stage='gate_and_hashes';refs={};external={};runtime=None;calls=0
    committed=0;counts=Counter();streams=[];g=None;cache={};cache_offsets={};call_intents=None
    try:
        g,refs,runtime,external,indices=inputs(gate_path,gate_sha)
        write(HERE/'started.json',{'schema':'N-pooled-complete-discovery-start-v1','pid':os.getpid(),
            'inputs_sha256':refs,'external_runtime_sha256_start':external,'expected_H_remaining':EXPECTED,
            'deductions':DEDUCTIONS,'process_cache_initially_empty':True,'mathematical_state_resumed':False,
            'maximum_linprog_calls':EXPECTED-len(DEDUCTIONS),'new_source_gate_required':True})
        alg=import_frozen(HERE/'component_model.py','N_pooled_components')
        recon=import_frozen(HERE/'reconstruct_support.py','N_fixed_support')
        check=import_frozen(HERE/'check_raw_certificate.py','N_raw_check_independent_of_discovery')
        stage='original_source_parser_and_runtime_imports';limit(start,g)
        source,mathmod,core,cells,traces,jcache=initialize_originals(refs)
        import numpy as np
        import scipy
        from scipy.optimize import linprog
        assert np.__version__=='2.5.2' and scipy.__version__=='1.18.1'
        assert runtime_hashes(runtime)==external
        originals=GzipJournal(HERE/'original-components.jsonl.gz')
        native=GzipJournal(HERE/'native-results.jsonl.gz');records=GzipJournal(HERE/'case-records.jsonl.gz')
        streams=[originals,native,records];call_intents=(HERE/'call-intents.jsonl').open('xb')
        def publish():
            atomic(HERE/'prefix.json',{'schema':'N-durable-complete-record-prefix-v1','committed_records':committed,
                'expected_records':EXPECTED,'counts':dict(counts),'linprog_calls_started':calls,
                'last_G_index':indices[committed-1] if committed else None,
                'input_index_sequence_sha256':pin(H/'remaining-indices.u32.bin'),
                'committed_index_sequence_sha256':sha256(b''.join(struct.pack('<I',v) for v in indices[:committed])).hexdigest(),
                'streams':{p.path.name:p.descriptor() for p in streams},
                'unprocessed_suffix_is_not_classified':True,'independent_math_replay_pending':True})
        publish()
        for index in indices:
            limit(start,g);stage='case_'+str(index)
            if index in DEDUCTIONS:
                records.append({'G_index':index,'outcome':'deduction_Lower','dependency':DEDUCTIONS[index],
                    'no_new_FS_model_or_solver_for_this_case':True})
                counts['deduction_Lower']+=1;committed+=1;publish();continue
            pair,chart=divmod(index,4);i,j=divmod(pair,N)
            windows=[]
            for cid in (i,j):
                if cid not in cache:
                    w,_state=core.extract_original_affine(cells[cid],source,mathmod,traces)
                    jc=jcache[cid]
                    assert w['canonical_Cstar']==jc['canonical_Cstar'] and w['canonical_J']==jc['canonical_J']
                    assert sha256(canonical(w['terms'])).hexdigest()==jc['original_term_components_sha256']
                    assert w['state_sha256']==jc['state_sha256'] and w['witness']==jc['witness']
                    cache_offsets[cid]=originals.append(w);cache[cid]=w
                windows.append(cache[cid])
            model=alg.assemble(windows,cells,source,mathmod.ALL,chart)
            assert model['group_count']==42 and model['columns_count']==51 and model['full_balance_coordinates']==52
            model_bytes=canonical(model);model_sha=sha256(model_bytes).hexdigest()
            c,A,b,selected=alg.native_arrays(model,np);limit(start,g)
            assert calls<EXPECTED-len(DEDUCTIONS);calls+=1
            intent={'G_index':index,'linprog_call_number':calls,'model_sha256':model_sha,
                'method':METHOD,'options':OPTIONS,'raw_columns':51,'raw_rows':len(model['rows']),
                'native_row_ids':selected,'native_same_S_max_E_pruning':True}
            call_intents.write(canonical(intent));call_intents.flush();os.fsync(call_intents.fileno())
            # There is exactly one call in this loop and no retry branch.
            result=linprog(c,A_ub=A,b_ub=b,bounds=[(None,None)]*model['columns_count'],method=METHOD,options=OPTIONS)
            raw=safe_native(dict(result));rawref=native.append({'G_index':index,'call_number':calls,
                'native_row_ids':selected,'result':raw})
            hint=dict(raw);ineq=dict(raw.get('ineqlin',{}));marg=ineq.get('marginals')
            if isinstance(marg,list) and len(marg)==len(selected):
                fullmarg=[0.0]*len(model['rows'])
                for rid,value in zip(selected,marg):fullmarg[rid]=value
                ineq['marginals']=fullmarg
            hint['ineqlin']=ineq
            exact=recon.reconstruct(hint,model,alg,cells)
            verification=check.verify(model,exact)
            outcome='Lower' if verification['Lower'] else 'Below' if verification['Below'] else 'unresolved'
            record={'G_index':index,'pair':[i,j],'chart':CHARTS[chart],'outcome':outcome,
                'native_record':rawref,'model_sha256':model_sha,'original_components':{str(cid):cache_offsets[cid] for cid in (i,j)},
                'original_cell_state_sha256':[cells[cid]['state_sha256'] for cid in (i,j)],
                'row_count':len(model['rows']),'group_count':42,'raw_column_count':51,'full_balance_coordinates':52,
                'normalized_exact_reconstruction':exact,'separate_raw_verification':verification,
                'native_status_not_mathematical_evidence':raw.get('status'),
                'unresolved_does_not_claim_nonempty':True,'Below_is_not_actual_F_counterexample':True}
            records.append(record);counts[outcome]+=1;committed+=1;publish()
            print(json.dumps({'committed':committed,'expected':EXPECTED,'last_index':index,
                'counts':dict(counts),'linprog_calls':calls,'seconds':time.monotonic()-start}),flush=True)
            if outcome=='Below':break
        stage='final_input_guards'
        after={name:pin(ROOT/name) for name in refs};assert after==refs
        assert runtime_hashes(runtime)==external
        complete=committed==EXPECTED;all_lower=complete and counts['unresolved']==counts['Below']==0
        write(HERE/'result.json',{'schema':'N-pooled-complete-component-discovery-result-v1','pid':os.getpid(),
            'seconds':time.monotonic()-start,'complete_original_H_range':complete,'all_range_Lower_candidate':all_lower,
            'first_exact_Below_found':counts['Below']==1,'committed_records':committed,'counts':dict(counts),
            'linprog_calls':calls,'auxiliary_calls':0,'retries':0,'prefix_sha256':pin(HERE/'prefix.json'),
            'inputs_sha256_start':refs,'inputs_sha256_end':after,
            'external_runtime_sha256_start':external,'external_runtime_sha256_end':runtime_hashes(runtime),
            'physical_span_pooling':True,'independent_full_replay_pending':True,
            'unresolved_is_not_nonempty':True,'Below_scope':'Only the pooled original-component polyhedral envelope, not actual F.',
            'actual_Lean_or_unconditional_global_floor_proven':False,'website_source_runtime_payload_budget':'unknown',
            'website_submission_ready':False,'automatic_retry':False})
    except WorkLimit as exc:
        write(HERE/'inconclusive.json',{'stage':stage,'reason':str(exc),'seconds':time.monotonic()-start,
            'committed_records':committed,'counts':dict(counts),'linprog_calls_started':calls,
            'published_prefix_only':True,'unprocessed_suffix_unclassified':True,'automatic_retry':False})
    except BaseException as exc:
        write(HERE/'failure.json',{'stage':stage,'error':repr(exc),'traceback':traceback.format_exc(),
            'pid':os.getpid(),'seconds':time.monotonic()-start,'committed_records':committed,
            'linprog_calls_started':calls,'automatic_retry':False})
        raise
    finally:
        if call_intents is not None:call_intents.close()
        for stream in streams:stream.close()

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--execute-authorized-complete-N',action='store_true')
    ap.add_argument('--gate');ap.add_argument('--gate-sha256');args=ap.parse_args()
    if not args.execute_authorized_complete_N:
        print(json.dumps({'prepared_only':True,'FS_extractions':0,'matrix_or_LP_runs':0}));return
    assert args.gate and args.gate_sha256
    execute(checked(args.gate),args.gate_sha256)
if __name__=='__main__':main()
