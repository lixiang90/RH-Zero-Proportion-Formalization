"""AST and existing bytes only. Never imports any mathematical module."""
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
    scripts=['audit_once.py','source_cell.py','run_once.py','prepare_static.py']
    for n in scripts:ast.parse((HERE/n).read_text(encoding='utf8'),filename=n)
    paths=[
        'research-goal-20261018-stageN-independent-v1/audit-files.json',
        'research-goal-20261018-stageN-independent-v1/audit_once.py',
        'research-goal-20261018-record-baseline-independent/audit-files.json',
        'research-goal-20261018-record-baseline-independent/replay_independent.py',
        'research-goal-20261018-record-packing-independent/decode_packing.py',
        'research-goal-20261018-record-source-audit/snapshot/Solution.lean',
        'research-goal-20261018-record-baseline-replay/baseline-events.jsonl.gz',
        'research-goal-20261018-stageB-classification/exception-cells.jsonl.gz',
        'research-goal-20261018-stageN2-independent-below/audit-files.json',
        'research-goal-20261018-stageN2-independent-below/independent-review.json',
        'research-goal-20261018-stageN2-pooled-component-resumption/files.json',
        'research-goal-20261018-stageO-cellA-static-review/files.json',
        'research-goal-20261018-stageO-fixed-curvature-preparation/files.json',
        'research-goal-20261018-stageO-fixed-curvature-preparation/curvature-packet.json']
    deps={n:row(ROOT/n) for n in paths}
    expected={
        'research-goal-20261018-stageO-fixed-curvature-preparation/files.json':'9eeb39270ad6853ee7ad3472c0446237ad21b64be0db442815e2566bfe97191b',
        'research-goal-20261018-stageO-fixed-curvature-preparation/curvature-packet.json':'a952a8bd239bddaa0c8d1f24b45a5096cb3a3b6ff19f067baaba46686eb11cbf',
        'research-goal-20261018-stageN2-independent-below/independent-review.json':'ed007f28ad6544935f76af982d09f93dbbce339ac648368ea3a7d21454cd2a5a'}
    for name,h in expected.items():assert deps[name]['sha256']==h
    for name in paths:
        if name.endswith('files.json'):
            doc=json.loads((ROOT/name).read_text(encoding='utf8'))
            for field in ['files','package_files','read_only_dependencies','dependencies']:
                for dep in doc.get(field,[]):
                    p=(ROOT/dep['path']).resolve();assert p.is_relative_to(ROOT);r=row(p)
                    assert r['sha256']==dep['sha256']
                    if 'bytes' in dep:assert r['bytes']==dep['bytes']
                    if r['path'] in deps:assert deps[r['path']]==r
                    deps[r['path']]=r
    exe=Path(sys.executable);dll=exe.parent/'python314.dll'
    runtime={'executable':str(exe),'sha256':sha256(exe.read_bytes()).hexdigest(),'version':sys.version,
        'additional_files':[{'path':str(dll),'bytes':dll.stat().st_size,'sha256':sha256(dll.read_bytes()).hexdigest()}]}
    out={'schema':'O-independent-fixed-curvature-prepared-only-v1',
        'files':[row(HERE/n) for n in scripts+['SPEC.zh.md','required-gate-fields.json']],
        'read_only_dependencies':[deps[p] for p in sorted(deps)],'runtime':runtime,
        'AST_parse_only':True,'mathematical_module_imports':0,'mathematical_executions':0,
        'execution_gate_required':True,'scope':'fixed23CellA49anchors42spans_saved_full10_stationarity_no_solve'}
    save('prepared-files.json',out)
    print(json.dumps({'prepared_only':True,'manifest':row(HERE/'prepared-files.json'),
        'dependency_count':len(deps),'mathematical_executions':0}))
if __name__=='__main__':main()
