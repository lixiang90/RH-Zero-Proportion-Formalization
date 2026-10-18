"""Hash existing metadata outputs only; no archive or mathematical replay."""
from hashlib import sha256
import json
import os
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
def digest(p):return sha256(p.read_bytes()).hexdigest()
def row(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':digest(p)}
def load(p):return json.loads(p.read_text(encoding='utf8'))
def main():
    assert not (HERE/'audit-files.json').exists()
    r=load(HERE/'independent-review.json');assert r['passed'] is True
    assert r['numeric_count']==13046 and r['other_numeric_debit_nonnegative']==13045
    assert r['unique_failed_numeric_leaf']==462 and r['candidate_strictly_exceeds_fresh_current'] is True
    assert r['new_leaf_decode_FS_kernel_LP_Lean_runs']==0 and r['metadata_read_passes']==2
    assert load(HERE/'first-attempt-terminal.json')['exit_code']==1 and load(HERE/'v1-terminal.json')['exit_code']==0
    assert r['inputs_sha256_start']==r['inputs_sha256_end']
    deps=[]
    for name,h in sorted(r['inputs_sha256_start'].items()):
        p=(ROOT/name).resolve();assert p.is_relative_to(ROOT) and digest(p)==h;deps.append(row(p))
    out={'schema':'tiny-overlap-independent-existing-metadata-files-v1',
        'files':[row(p) for p in sorted(HERE.iterdir()) if p.is_file() and p.name!='audit-files.json'],
        'read_only_dependencies':deps,'passed':True,'new_Lean_global_proof_claimed':False,
        'scope':'full13046already_proved_margins_and_unique_exception_four_chart_geometry_only'}
    with (HERE/'audit-files.json').open('x',encoding='utf8') as f:json.dump(out,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
    print(json.dumps({'manifest':row(HERE/'audit-files.json'),'receipt':row(HERE/'independent-review.json'),
        'files':len(out['files']),'closed_bytes':sum(v['bytes'] for v in out['files'])}))
if __name__=='__main__':main()
