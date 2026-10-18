"""AST and byte-hash preparation only; never imports/extracts/evaluates I."""
from pathlib import Path
from hashlib import sha256
import ast
import json
import os
import sys

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
def pin(p):return sha256(p.read_bytes()).hexdigest()
def row(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':pin(p)}
def write_new(p,x):
    with p.open('x',encoding='utf-8',newline='\n') as f:json.dump(x,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
def main():
    assert not (HERE/'preparation.json').exists() and not (HERE/'prepared-files.json').exists()
    for name in ['started.json','result.json','launch.json','terminal.json','failure.json','inconclusive.json']:
        assert not (HERE/name).exists(),('mathematical_execution_artifact_present_during_preparation',name)
    scripts=[HERE/'evaluate_once.py',HERE/'run_once.py',Path(__file__)]
    parsed=[];producer_tree=None
    for p in scripts:
        tree=ast.parse(p.read_text(encoding='utf-8'),filename=str(p));parsed.append({**row(p),'AST_parse_passed':True})
        if p.name=='evaluate_once.py':producer_tree=tree
    found=[node for node in producer_tree.body if isinstance(node,ast.Assign)
           and any(isinstance(t,ast.Name) and t.id=='PINS' for t in node.targets)]
    assert len(found)==1
    dependencies=[]
    for name,expected in ast.literal_eval(found[0].value).items():
        p=ROOT/name;assert pin(p)==expected;dependencies.append(row(p))
    load_json(HERE/'required-gate-fields.json')
    runtime={'path':str(Path(sys.executable)),'sha256':pin(Path(sys.executable)),
        'bytes':Path(sys.executable).stat().st_size,'version':sys.version,'read_only_external_identity':True,'copied':False}
    command=[str(Path(sys.executable)),'research-goal-20261018-stageI-original-affine-point/run_once.py',
        '--launch-authorized-I-point','--gate','<ROOT_IMMUTABLE_GATE_RELATIVE_PATH>','--gate-sha256','<ROOT_GATE_SHA256>']
    preparation={'schema':'I-Phase1-AST-bytehash-only-preparation-v1','passed':True,'scripts':parsed,
        'read_only_dependencies':dependencies,'external_read_only_runtime':runtime,'command_template':command,
        'command_template_sha256':sha256(json.dumps(command,separators=(',',':')).encode()).hexdigest(),
        'producer_imports':0,'inputs_calls':0,'source_model_configure_calls':0,'FS_extractions':0,
        'point_evaluations':0,'matrix_LP_kernel_or_Lean_runs':0,'new_immutable_root_gate_required':True,
        'independent_checker_not_a_producer_math_dependency':True,'independent_audit_requires_separate_gate':True,
        'scope':'AST and read-only byte hashes only. Neither producer nor parser/math functions executed.'}
    write_new(HERE/'preparation.json',preparation)
    files=[HERE/name for name in ['evaluate_once.py','run_once.py','SPEC.zh.md','required-gate-fields.json','prepare_freeze.py','preparation.json']]
    manifest={'schema':'I-Phase1-prepared-only-source-package-v1','files':[row(p) for p in files],
        'read_only_dependencies':dependencies,'external_read_only_runtime':runtime,'arithmetic_executions':0,
        'FS_extractions':0,'point_evaluations':0,'independent_arithmetic_replays':0,
        'independent_checker_not_a_producer_math_dependency':True,'independent_audit_requires_separate_gate':True,
        'immutable_execution_gate_pending':True,'new_global_floor_or_kappa_proven':False,
        'website_source_and_runtime_budget':'unknown','scope':'Implementation preparation, not authorization or result.'}
    write_new(HERE/'prepared-files.json',manifest)
    print(json.dumps({'prepared_only':True,'manifest':row(HERE/'prepared-files.json'),
        'owned_source_bytes':sum(p.stat().st_size for p in files),'mathematical_executions':0}))
def load_json(p):return json.loads(p.read_text(encoding='utf-8'))

if __name__=='__main__':main()
