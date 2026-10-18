"""N2 byte/commit-metadata freeze only, not an independent math audit."""
from pathlib import Path
from hashlib import sha256
from collections import Counter
import json
import os
import struct
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
PREPARED='e83e14f92e4471189c4f558807dec830baed560fe682fc3a9ef70ddb3d89e297'
GATE='research-goal-20261016/gates/stageN2-same-model-resumption-20261018.json'
GATE_SHA='286427f9f3c78f39fefbf7080d6ae13c1ec70494d548b1b0418c255dc5607f3d'
def pin(p):
    h=sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def row(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':pin(p)}
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':'),allow_nan=False).encode('ascii')+b'\n'
def write(p,x):
    with p.open('x',encoding='utf-8',newline='\n') as f:
        json.dump(x,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
def main():
    assert not (HERE/'files.json').exists() and not (HERE/'freeze-receipt.json').exists()
    assert pin(HERE/'prepared-files.json')==PREPARED and pin(ROOT/GATE)==GATE_SHA
    prep=load(HERE/'prepared-files.json')
    for item in prep['files']:
        q=ROOT/item['path'];assert pin(q)==item['sha256'] and q.stat().st_size==item['bytes']
    result=load(HERE/'result.json');terminal=load(HERE/'terminal.json');recovery=load(HERE/'recovery.json')
    assert terminal['exit_code']==0 and terminal['child_launches']==1 and terminal['limit_stop'] is None
    assert terminal['inputs_unchanged_after_terminal'] and terminal['external_runtime_unchanged_after_terminal']
    assert result['first_exact_Below_found'] and result['counts']=={'Below':1,'Lower':2373,'deduction_Lower':1}
    assert result['committed_records']==2375 and result['old_LP_calls']==675 and result['new_LP_calls']==1699
    assert result['total_LP_calls']==2374 and result['repeated_old_LP_calls']==0
    assert recovery['accepted_recovered_records']==676 and recovery['repeated_LP_calls']==0
    indices=[v[0] for v in struct.iter_unpack('<I',(ROOT/'research-goal-20261018-stageH-ordered-transport/remaining-indices.u32.bin').read_bytes())]
    head='0'*64;counts=Counter();indexhash=sha256();last=None;ordinal=0
    with (HERE/'progress-commits.jsonl').open('rb') as f:
        for line in f:
            assert line.endswith(b'\n');envelope=json.loads(line);assert canonical(envelope)==line
            body=envelope['body'];ordinal+=1
            assert body['ordinal']==ordinal and body['G_index']==indices[ordinal-1]
            assert body['previous_commit_sha256']==head
            head=sha256(canonical(body)).hexdigest();assert head==envelope['commit_sha256']
            counts[body['outcome']]+=1;assert dict(counts)==body['counts']
            indexhash.update(struct.pack('<I',body['G_index']))
            assert indexhash.hexdigest()==body['committed_index_sequence_sha256'];last=body
    assert ordinal==result['committed_records'] and head==result['commit_head_sha256']
    assert dict(counts)==result['counts'] and last['G_index']==1322606
    assert (HERE/'progress-commits.jsonl').stat().st_size==result['journal_bytes']
    for name,desc in last['streams'].items():
        q=ROOT/desc['path'];assert q.name==name and q.stat().st_size==desc['bytes'] and pin(q)==desc['sha256']
    readout=load(HERE/'first-Below-readout.json')
    assert readout['G_index']==1322606 and readout['pair']==[278,665] and readout['chart']=='rev/id'
    assert readout['primal_checks']['valid'] and readout['primal_checks']['all_raw_rows_checked']==305
    receipt={'schema':'N2-terminal-byte-and-commit-metadata-freeze-v1','passed_byte_identity_checks':True,
        'parent_pid':6844,'child_pid':25804,'session_id':19667,'actual_child_exit_code':0,
        'committed_records':2375,'counts':dict(counts),'unprocessed_H_suffix':len(indices)-ordinal,
        'old_calls':675,'new_calls':1699,'total_calls':2374,'repeated_old_calls':0,
        'first_Below_index':1322606,'commit_head_sha256':head,
        'complete_commit_lines_and_EOF':True,'final_stream_bytes_and_hashes_match_committed':True,
        'mathematical_replay_executions':0,'kernel_FS_matrix_solver_or_Lean_runs':0,
        'independent_source_and_mathematics_replay_pending':True,'whole_range_complete':False,
        'prepared_manifest_sha256':PREPARED,'gate_path':GATE,'gate_sha256':GATE_SHA,
        'unconditional_floor_or_website_acceptance_proven':False}
    write(HERE/'freeze-receipt.json',receipt)
    owned=[p for p in sorted(HERE.iterdir()) if p.is_file() and p.name!='files.json']
    manifest={'schema':'N2-same-model-first-Below-complete-evidence-v1','files':[row(p) for p in owned],
        'read_only_dependencies':prep['read_only_dependencies']+[row(ROOT/GATE)],
        'external_read_only_runtime_files':prep['external_read_only_runtime_files'],
        'prepared_manifest_sha256':PREPARED,'whole_range_complete':False,'unprocessed_H_suffix':13003,
        'first_Below_index':1322606,'retries':0,'new_math_in_freezer':False,
        'scope':'Frozen internal exact model Below and successful Lower prefix; external independent audit pending, not actual F counterexample.'}
    write(HERE/'files.json',manifest)
    print(json.dumps({'frozen':row(HERE/'files.json'),'owned_files':len(owned),
        'owned_bytes':sum(p.stat().st_size for p in owned),'first_Below':1322606,'unprocessed_H_suffix':13003}))
if __name__=='__main__':main()
