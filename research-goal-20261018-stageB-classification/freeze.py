"""Freeze closed Stage B outputs; archive integrity only, no new math replay."""
from pathlib import Path
from hashlib import sha256
import gzip
import json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent

def pin(p):return sha256(p.read_bytes()).hexdigest()
def row(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':pin(p)}
def read(p):return json.loads(p.read_text(encoding='utf-8'))

def main():
    out=HERE/'files.json';assert not out.exists()
    a=read(HERE/'classification.json');terminal=read(HERE/'terminal.json')
    assert a['passed'] and terminal['exit_code']==0 and terminal['limit_stop'] is None
    assert terminal['child_launches']==a['classification_passes']==1
    assert not (HERE/'failure.json').exists()
    assert a['inputs_sha256_start']==a['inputs_sha256_end']
    refs=[]
    for name,expected in a['inputs_sha256_start'].items():
        p=ROOT/name;assert pin(p)==expected
        if p.parent!=HERE:refs.append(row(p))
    integrity={}
    for name,expected_count in [('trace',27234),('numeric',13046),('exceptions',1187)]:
        obj=a['outputs'][name];p=ROOT/obj['path'];assert pin(p)==obj['sha256']
        h=sha256();count=0;nbytes=0
        with gzip.open(p,'rb') as f:
            for line in f:
                assert line.endswith(b'\n');h.update(line);count+=1;nbytes+=len(line)
        assert count==expected_count and h.hexdigest()==obj['uncompressed_canonical_jsonl_sha256']
        integrity[name]={'rows':count,'uncompressed_bytes':nbytes,'uncompressed_sha256':h.hexdigest()}
    files=[row(p) for p in sorted(HERE.iterdir()) if p.is_file() and p.name!='files.json']
    assert sum(r['bytes'] for r in files)<32000000
    result={'schema':'fixed-new-record-StageB-producer-package-v1',
        'files':files,'total_bytes':sum(r['bytes'] for r in files),
        'read_only_dependencies':sorted(refs,key=lambda r:r['path']),
        'archive_integrity':integrity,'classification_passes':1,
        'independent_StageB_mathematical_review_pending':True,
        'scope':'One fixed original-witness debit classification and complete conservative closed outercover of arbitrary separated sublevel. Not a pair test, new floor, or formal kernel acceptance.',
        'numeric_closed':11859,'numeric_exceptions':1187,'ordered_reflection_exclusions':595,
        'whole_source_and_original_witnesses_unchanged':True,
        'unknown_complete_consumer_source_and_runtime_budget':True,
        'complete_source_gate_passed':False,'exception_pairs_scanned':0,
        'new_kernel_queries':0,'Lean_runs':0,'optimizer_calls':0,
        'new_joint_floor_proven':False,'new_unconditional_zero_proportion_proven':False,
        'website_submission_ready':False,'mutable_governance_dependency':False}
    with out.open('x',encoding='utf-8',newline='\n') as f:
        json.dump(result,f,indent=2);f.write('\n')
    print(json.dumps({'path':out.relative_to(ROOT).as_posix(),'sha256':pin(out),
        'files':len(files),'total_bytes':result['total_bytes'],'archive_integrity':integrity}))

if __name__=='__main__':main()
