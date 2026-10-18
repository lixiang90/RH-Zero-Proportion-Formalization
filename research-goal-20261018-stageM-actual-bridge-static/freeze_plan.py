"""Freeze a static source/API plan; no model, certificate or Lean evaluation."""
from pathlib import Path
from hashlib import sha256
import json
import os

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
PINS={
 'research-goal-20261018-record-source-audit/snapshot/Solution.lean':'f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf',
 'research-goal-20261018-stageM-component-envelope-preparation/files.json':'129c706dcab0aff47ef54a0f249e5d0a49e8f718476faaf453681e73858526d8',
 'research-goal-20261018-stageM-independent/audit-files.json':'2887e7527180ca2b77d7779cd5c25ada853d040e82d0380a125f7f821c907be4',
 'research-goal-20261018-stageM-independent/independent-review.json':'13d73403029aa10b1f6e598919f1ce5c231a541516854601773f1f796c3f52a0',
 'research-goal-20261018-nonlinear-remainder-static/NOTE.zh.md':'206d5b3fb2c2bee2790caf77f4225f7b095c44e0c0bf53b9100b5be643e7c7d4',
 'StructuralGoal20261016/AffineFlowCertificate.lean':'94b8aa67e553fe5f026e40ee78669309fac09090223e01c03de02aeb93ffbfc1'
}
def pin(p):return sha256(p.read_bytes()).hexdigest()
def row(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':pin(p)}
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def write(p,x):
    with p.open('x',encoding='utf-8',newline='\n') as f:
        json.dump(x,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
def main():
    assert not (HERE/'files.json').exists() and not (HERE/'source-layout.json').exists()
    deps=[]
    for name,expected in PINS.items():
        p=ROOT/name;assert pin(p)==expected;deps.append(row(p))
    producer=load(ROOT/'research-goal-20261018-stageM-component-envelope-preparation/files.json')
    wanted={'model.json','certificate.json','envelope_model.py','discover_once.py','original-components.json','exact-reconstruction.json'}
    selected={Path(item['path']).name:item for item in producer['files'] if Path(item['path']).name in wanted}
    assert set(selected)==wanted
    for item in selected.values():
        p=ROOT/item['path'];assert pin(p)==item['sha256'] and p.stat().st_size==item['bytes'];deps.append(row(p))
    source=ROOT/'research-goal-20261018-record-source-audit/snapshot/Solution.lean';raw=source.read_bytes()
    lines=raw.splitlines(keepends=True);prefix=b''.join(lines[:12407])
    review=load(ROOT/'research-goal-20261018-stageM-independent/independent-review.json')
    layout={'schema':'M-static-existing-source-byte-layout-v1','source':row(source),
        'prefix_through_ptS':{'last_line':12407,'bytes':len(prefix),'sha256':sha256(prefix).hexdigest(),
            'new_Lean_prefix_created':False,'closure_suffix_needed':'end AMW.Cert.PC9QB6MData; end'},
        'existing_artifact_bytes':{name:item['bytes'] for name,item in selected.items()},
        'observed_independent_receipt_fields':{name:review[name] for name in
            ['passed','rows','variables','full_dual_coordinates','original_FS_terms_reconstructed','valid_local_Lower']},
        'statistical_scope':'Byte/line layout and existing receipt metadata only, no FS, row or certificate arithmetic recomputation.',
        'new_mathematical_evaluations_or_Lean_runs':0}
    write(HERE/'source-layout.json',layout)
    files=[HERE/name for name in ['PLAN.zh.md','interfaces.json','freeze_plan.py','source-layout.json']]
    manifest={'schema':'M-current-s1R-actual-bridge-static-plan-v1','files':[row(p) for p in files],
        'read_only_dependencies':deps,'new_Lean_source_created':False,'compiler_runs':0,
        'FS_kernel_point_matrix_solver_or_new_certificate_evaluations':0,
        'local_pair_bridge_plan_only':True,'actual_local_Lean_theorem_proven':False,
        'global_cover_and_leaf_reachability_deferred':True,'new_unconditional_kappa_proven':False,
        'source_size_and_total_runtime_measured_for_final_submission':False,
        'live_governance_documents_are_not_immutable_mathematical_dependencies':True}
    write(HERE/'files.json',manifest)
    print(json.dumps({'static_only':True,'manifest':row(HERE/'files.json'),
        'current_prefix_bytes':len(prefix),'owned_bytes':sum(p.stat().st_size for p in files),
        'new_Lean_or_math_executions':0}))

if __name__=='__main__':main()
