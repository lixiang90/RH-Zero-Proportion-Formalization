"""AST + existing bytehash metadata only; no producer or audit imports."""
import ast
from hashlib import sha256
import json
import os
from pathlib import Path
import sys
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
def row(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':sha256(p.read_bytes()).hexdigest()}
def save(n,x):
    with (HERE/n).open('x',encoding='utf8') as f:json.dump(x,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
def main():
    for n in ['prepared-files.json','started.json','launch.json','independent-review.json']:assert not (HERE/n).exists()
    scripts=['audit_once.py','run_once.py','prepare_static.py']
    for n in scripts:ast.parse((HERE/n).read_text(encoding='utf8'),filename=n)
    paths=['research-goal-20261018-stageN-independent-v1/audit-files.json',
        'research-goal-20261018-stageN-independent-v1/audit_once.py',
        'research-goal-20261018-stageN-independent-v1/independent-review.json',
        'research-goal-20261018-record-baseline-independent/replay_independent.py',
        'research-goal-20261018-record-baseline-independent/audit-files.json',
        'research-goal-20261018-record-packing-independent/decode_packing.py',
        'research-goal-20261018-record-source-audit/snapshot/Solution.lean',
        'research-goal-20261018-record-baseline-replay/baseline-events.jsonl.gz',
        'research-goal-20261018-stageB-classification/exception-cells.jsonl.gz',
        'research-goal-20261018-stageB-independent/audit-files.json',
        'research-goal-20261018-stageH-ordered-transport/remaining-indices.u32.bin',
        'research-goal-20261018-stageH-independent/audit-files.json',
        'research-goal-20261018-stageN-complete-component-preparation/files.json',
        'research-goal-20261018-stageN2-pooled-component-resumption/files.json',
        'research-goal-20261018-pooled-component-static/files.json']
    deps={n:row(ROOT/n) for n in paths}
    assert deps['research-goal-20261018-stageN2-pooled-component-resumption/files.json']['sha256']=='327db7c23c63aeb0ad49236b59303d04fea93a9fcde524caa5998bcd3637369f'
    for name in paths:
        if name.endswith('audit-files.json') or name.endswith('files.json'):
            doc=json.loads((ROOT/name).read_text(encoding='utf8'))
            for field in ['files','read_only_dependencies','dependencies']:
                for dep in doc.get(field,[]):
                    p=(ROOT/dep['path']).resolve();assert p.is_relative_to(ROOT);r=row(p)
                    assert r['sha256']==dep['sha256']
                    if 'bytes' in dep:assert r['bytes']==dep['bytes']
                    deps[r['path']]=r
    exe=Path(sys.executable);dll=exe.parent/'python314.dll'
    runtime={'executable':str(exe),'sha256':sha256(exe.read_bytes()).hexdigest(),'version':sys.version,
        'additional_files':[{'path':str(dll),'bytes':dll.stat().st_size,'sha256':sha256(dll.read_bytes()).hexdigest()}]}
    out={'schema':'N2-independent-fixed-Below-audit-prepared-only-v1','files':[row(HERE/n) for n in scripts+['SPEC.zh.md','required-gate-fields.json']],
        'read_only_dependencies':[deps[p] for p in sorted(deps)],'runtime':runtime,'AST_parse_only':True,
        'audit_or_producer_imports':0,'mathematical_executions':0,'execution_gate_required':True,
        'scope':'One fixed Below source proof; all commit/reference metadata only, no other Lower mathematics'}
    save('prepared-files.json',out)
    print(json.dumps({'prepared_only':True,'manifest':row(HERE/'prepared-files.json'),'mathematical_executions':0}))
if __name__=='__main__':main()
