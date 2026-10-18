"""Prepared single fixed N2 Below audit plus complete commit/reference metadata.

No mathematics at import. After a separate root gate, imports only our own
frozen v1 audit helpers and our own A parser. Never imports N/N2/M/I/J producers.
Other Lower records receive metadata/reference checks, not mathematical replay.
"""
import argparse
from collections import Counter
from hashlib import sha256
import importlib.util
import json
import os
from pathlib import Path
import struct
import sys
import time
import traceback

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
PROD=ROOT/'research-goal-20261018-stageN2-pooled-component-resumption'
OLD=ROOT/'research-goal-20261018-stageN-complete-component-preparation'
OWN=ROOT/'research-goal-20261018-stageN-independent-v1/audit_once.py'
OWN_A=ROOT/'research-goal-20261018-record-baseline-independent/replay_independent.py'
H=ROOT/'research-goal-20261018-stageH-ordered-transport'
INDEX,COUNT=1322606,2375
SCOPE='single_N2_exact_Below_1322606_source_math_plus_complete_commit_reference_metadata'
PRODUCER_SHA='327db7c23c63aeb0ad49236b59303d04fea93a9fcde524caa5998bcd3637369f'

def canonical(x):return (json.dumps(x,sort_keys=True,separators=(',',':'),allow_nan=False)+'\n').encode('ascii')
def load(p):return json.loads(p.read_text(encoding='utf8'))
def digest(p):
    h=sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def path_checked(name):
    p=(ROOT/name).resolve();assert p.is_relative_to(ROOT);return p
def save(n,x):
    with (HERE/n).open('xb') as f:f.write(canonical(x));f.flush();os.fsync(f.fileno())
def append_pin(refs,row):
    p=path_checked(row['path']);assert digest(p)==row['sha256']
    if 'bytes' in row:assert p.stat().st_size==row['bytes']
    if row['path'] in refs:assert refs[row['path']]==row['sha256']
    refs[row['path']]=row['sha256']
def inventory(refs,row):
    append_pin(refs,row);m=load(path_checked(row['path']))
    for field in ['files','package_files','read_only_dependencies','dependencies']:
        for r in m.get(field,[]):append_pin(refs,r)
    return m
def import_own(p,name):
    spec=importlib.util.spec_from_file_location(name,p);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module

def identity(args):
    refs={};append_pin(refs,{'path':args.gate,'sha256':args.gate_sha256});g=load(path_checked(args.gate))
    assert type(g['independent_N2_fixed_Below_audits_authorized']) is int and g['independent_N2_fixed_Below_audits_authorized']==1
    assert g['scope']==SCOPE and g['fixed_G_index']==INDEX and g['combined_committed_records']==COUNT
    assert g['other_Lower_mathematical_replay_authorized'] is False and g['automatic_retry_allowed'] is False
    assert type(g['new_solver_RREF_point_kernel_Lean_authorized']) is int and g['new_solver_RREF_point_kernel_Lean_authorized']==0
    assert g['resource_limits']['elapsed_seconds']>0 and g['resource_limits']['closed_output_bytes']>0
    prep=inventory(refs,{'path':HERE.relative_to(ROOT).as_posix()+'/prepared-files.json','sha256':g['prepared_manifest_sha256']})
    rt=prep['runtime'];assert Path(sys.executable).resolve()==Path(rt['executable']).resolve()
    assert digest(Path(sys.executable))==rt['sha256'] and sys.version==rt['version'] and sys.flags.optimize==0
    for r in rt['additional_files']:assert digest(Path(r['path']))==r['sha256']
    assert g['producer_manifest']=={'path':PROD.relative_to(ROOT).as_posix()+'/files.json','sha256':PRODUCER_SHA}
    inventory(refs,g['producer_manifest'])
    for r in g['producer_endpoints']:append_pin(refs,r)
    return g,refs

def prefix_hashes(commits,boundaries):
    """Linear bytes read across all commits; each member boundary checked."""
    states={}
    try:
        for commit in commits:
            for name,desc in commit['streams'].items():
                if name not in states:
                    states[name]={'f':path_checked(desc['path']).open('rb'),'bytes':0,'h':sha256(),'path':desc['path']}
                s=states[name];assert desc['path']==s['path'] and desc['bytes']>=s['bytes']
                left=desc['bytes']-s['bytes']
                while left:
                    data=s['f'].read(min(left,65536));assert data;s['h'].update(data);left-=len(data)
                s['bytes']=desc['bytes'];assert s['h'].hexdigest()==desc['sha256']
                assert boundaries[name][desc['bytes']]==desc['records']
        for s in states.values():assert not s['f'].read(1)
    finally:
        for s in states.values():s['f'].close()

def metadata(own):
    result=load(PROD/'result.json');terminal=load(PROD/'terminal.json');recovery=load(PROD/'recovery.json')
    assert terminal['exit_code']==0 and terminal['limit_stop'] is None
    assert result['committed_records']==COUNT and result['first_exact_Below_found'] is True
    assert result['complete_original_H_range'] is False and result['all_range_Lower_candidate'] is False
    assert result['old_LP_calls']==675 and result['new_LP_calls']==1699 and result['total_LP_calls']==2374
    assert result['repeated_old_LP_calls']==0 and recovery['repeated_LP_calls']==0
    assert recovery['accepted_recovered_records']==676 and recovery['old_published']==675
    indices_raw=(H/'remaining-indices.u32.bin').read_bytes();indices=[v[0] for v in struct.iter_unpack('<I',indices_raw)]
    assert len(indices)==15378 and indices==sorted(set(indices)) and indices[COUNT-1]==INDEX
    commits=[];head='0'*64;counts=Counter();ih=sha256()
    with (PROD/'progress-commits.jsonl').open('rb') as f:
        for line in f:
            r=json.loads(line);assert line==canonical(r);body=r['body'];ordinal=len(commits)+1
            assert body['ordinal']==ordinal and body['G_index']==indices[ordinal-1]
            assert body['previous_commit_sha256']==head and r['commit_sha256']==sha256(canonical(body)).hexdigest()
            kind=body['outcome'];assert kind in ['Lower','Below','unresolved','deduction_Lower']
            counts[kind]+=1;assert dict(counts)==body['counts']
            if kind=='Below':assert ordinal==COUNT and body['G_index']==INDEX
            assert body['old_LP_calls']==675 and body['total_LP_calls']==675+body['new_LP_calls']
            ih.update(struct.pack('<I',body['G_index']));assert body['committed_index_sequence_sha256']==ih.hexdigest()
            assert body['unprocessed_suffix_is_not_classified'] is True
            commits.append(body);head=r['commit_sha256']
    assert len(commits)==COUNT and dict(counts)=={'Lower':2373,'deduction_Lower':1,'Below':1}
    assert result['counts']==dict(counts) and result['commit_head_sha256']==head
    assert result['committed_index_sequence_sha256']==ih.hexdigest()
    last=commits[-1];assert last['new_LP_calls']==1699
    streams=last['streams'];boundaries={};member_refs={};records={};native={};cache={};target=None
    for name,desc in streams.items():
        assert name in ['new-original-components.jsonl.gz','new-native-results.jsonl.gz','case-records.jsonl.gz']
        bounds={0:0};refs_by_offset={};number=0
        for rec,ref in own.journal(desc,True):
            number+=1;bounds[ref['offset']+ref['bytes']]=number
            full={'path':desc['path'],**ref};refs_by_offset[ref['offset']]=(full,rec)
        boundaries[name]=bounds;member_refs[name]=refs_by_offset
    prefix_hashes(commits,boundaries)
    for offset,(ref,rec) in member_refs['case-records.jsonl.gz'].items():
        ix=rec['G_index'];assert ix not in records;records[ix]=(ref,rec)
        if ix==INDEX:target=rec
    for ref,rec in member_refs['new-native-results.jsonl.gz'].values():
        ix=rec['G_index'];assert ix not in native;native[ix]=(ref,rec)
    for ref,rec in member_refs['new-original-components.jsonl.gz'].values():
        cid=rec['cell_id'];assert cid not in cache;cache[cid]=(ref,rec)
    assert len(records)==COUNT and target is not None and target['outcome']=='Below'
    # Prior durable members are dependencies, with no repeated Lower mathematics.
    old_prefix=load(OLD/'prefix.json.tmp');old_refs={};old_cache={};old_native={}
    for rec,ref in own.journal(old_prefix['streams']['case-records.jsonl.gz'],True):
        ix=rec['G_index'];assert ix not in old_refs;old_refs[ix]=({'path':str((OLD/'case-records.jsonl.gz').relative_to(ROOT)).replace('\\','/'),**ref},rec)
    for rec,ref in own.journal(old_prefix['streams']['original-components.jsonl.gz'],True):
        old_cache[rec['cell_id']]=({'path':str((OLD/'original-components.jsonl.gz').relative_to(ROOT)).replace('\\','/'),**ref},rec)
    for rec,ref in own.journal(old_prefix['streams']['native-results.jsonl.gz'],True):old_native[rec['G_index']]=(ref,rec)
    assert len(old_refs)==676 and len(old_native)==675 and list(old_refs)==indices[:676]
    new_intents=[]
    with (PROD/'new-call-intents.jsonl').open('rb') as f:
        for line in f:
            rec=json.loads(line);assert line==canonical(rec);new_intents.append(rec)
    old_intents=[]
    with (OLD/'call-intents.jsonl').open('rb') as f:
        for line in f:
            rec=json.loads(line);assert line==canonical(rec);old_intents.append(rec)
    assert len(old_intents)==675 and len(new_intents)==len(native)==1699
    old_called={r['G_index'] for r in old_intents};assert len(old_called)==675 and set(old_native)==old_called
    assert [r['linprog_call_number'] for r in old_intents]==list(range(1,676))
    new_called=[r['G_index'] for r in new_intents];assert len(set(new_called))==1699 and not(old_called&set(new_called))
    assert new_called==[r['G_index'] for r in commits[676:] if r['outcome']!='deduction_Lower']
    for k,intent in enumerate(new_intents,1):
        ix=intent['G_index'];ref,native_rec=native[ix]
        assert intent['new_call_number']==k and intent['total_call_number']==675+k
        assert native_rec['new_call_number']==k and native_rec['native_row_ids']==intent['native_row_ids']
        assert records[ix][1]['native_record']==ref and records[ix][1]['model_sha256']==intent['model_sha256']
    for ordinal,commit in enumerate(commits,1):
        ix=commit['G_index'];ref,rec=records[ix]
        assert commit['proof_record']==ref and rec['outcome']==commit['outcome']
        if ordinal<=676:
            old_ref,old_record=old_refs[ix]
            assert rec['recovered_original_record']==old_ref and rec['was_originally_published']==(ordinal<=675)
            assert rec['LP_calls_during_recovery']==0 and old_record['outcome']==rec['outcome']
            if rec['outcome']=='deduction_Lower':assert ix==2417
            else:
                assert old_record['native_record']==old_native[ix][0]
                assert rec['separate_raw_replay']==old_record['separate_raw_verification']
            assert commit['new_LP_calls']==0
        else:
            assert ix not in old_called and commit['new_LP_calls']==ordinal-676
            pair,chart=divmod(ix,4);i,j=divmod(pair,1187)
            assert rec['pair']==[i,j] and rec['chart']==['id/id','id/rev','rev/id','rev/rev'][chart]
            for cid in [i,j]:
                supplied=rec['original_components'][str(cid)]
                source_cache=old_cache if supplied['path'].startswith(OLD.relative_to(ROOT).as_posix()+'/') else cache
                assert supplied==source_cache[cid][0]
    assert target['pair']==[278,665] and target['chart']=='rev/id'
    selected={}
    for cid in target['pair']:
        ref=target['original_components'][str(cid)]
        store=old_cache if ref['path'].startswith(OLD.relative_to(ROOT).as_posix()+'/') else cache
        assert ref==store[cid][0];selected[cid]=store[cid][1]
    return target,selected,{'commit_records':COUNT,'counts':dict(counts),'commit_chain_sha256':head,
        'all_stream_members_hash_CRC_canonical_JSON_EOF_verified':True,'all_commit_stream_prefix_hashes_and_member_boundaries_verified':True,
        'old_new_member_and_intent_references_verified':True,'old_repeated_LP_indices':0,
        'old_LP_calls':675,'new_LP_calls':1699,'combined_LP_calls':2374,'other_Lower_mathematical_replay_claimed':False}

def execute(args):
    for n in ['started.json','independent-review.json','failure.json']:assert not (HERE/n).exists()
    start=time.monotonic();stage='identity';refs={}
    try:
        g,refs=identity(args);save('started.json',{'pid':os.getpid(),'scope':SCOPE,'inputs_sha256':refs})
        own=import_own(OWN,'N2_own_frozen_v1_helpers')
        stage='whole_commit_stream_reference_metadata';target,saved,meta=metadata(own)
        assert time.monotonic()-start<g['resource_limits']['elapsed_seconds']
        stage='fixed_original_source_FS_guards'
        a=import_own(OWN_A,'N2_own_frozen_A_parser');source=a.load_source();all_cells=own.load_cells()
        cells=[all_cells[cid] for cid in [278,665]];history=own.load_history({r['root'] for r in cells})
        windows=[own.original(a,source,row,history,saved[row['exception_id']]) for row in cells]
        assert sum(len(term['active_mokI_guards']) for window in windows for term,_lines in window)==82
        rows,pressure,weights,members=own.model_from_source(source,cells,windows,2)
        assert len(rows)==305 and len(weights)==42 and len(pressure)==10
        stage='fixed_raw_primal_and_optional_dual'
        math_review=own.certificates(target,rows,pressure,weights,members,cells,source,2)
        assert math_review['outcome']=='Below' and math_review['primal_rechecked']['valid'] is True
        assert own.scalar(math_review['primal_rechecked']['raw_minus_target'])<0
        after={name:digest(path_checked(name)) for name in refs};assert after==refs
        assert time.monotonic()-start<g['resource_limits']['elapsed_seconds']
        save('independent-review.json',{'schema':'N2-independent-fixed-Below-source-and-metadata-review-v1','passed':True,
            'pid':os.getpid(),'seconds':time.monotonic()-start,'scope':SCOPE,'fixed_G_index':INDEX,
            'pair':[278,665],'chart':'rev/id','inputs_sha256_start':refs,'inputs_sha256_end':after,
            'commit_and_reference_metadata':meta,'fixed_case_math':math_review,
            'all_305_original_rows_primal_checked':True,'full_balance_coordinates':52,'original_source_FS_cells_rebuilt':2,
            'original_positive_mass_anchor_guards_checked':82,
            'only_pooled_component_model_insufficiency_proven':True,'actual_F_counterexample_claimed':False,
            'other_Lower_mathematical_replay_claimed':False,'all_domain_floor_proven':False,
            'N_N2_M_I_J_producer_imports':0,'RREF_solver_new_point_kernel_Lean_runs':0})
        print(json.dumps({'passed':True,'fixed_G_index':INDEX,'outcome':'Below','other_Lower_mathematics_replayed':False}),flush=True)
    except BaseException as exc:
        save('failure.json',{'stage':stage,'error':repr(exc),'traceback':traceback.format_exc(),'seconds':time.monotonic()-start,
            'scope':SCOPE,'automatic_retry':False});raise

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--execute-authorized-audit-once',action='store_true')
    p.add_argument('--gate');p.add_argument('--gate-sha256');a=p.parse_args()
    assert a.execute_authorized_audit_once and a.gate and a.gate_sha256;execute(a)
if __name__=='__main__':main()
