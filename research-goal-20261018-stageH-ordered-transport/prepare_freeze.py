"""Only AST parsing and read-only byte hashes; never imports the H producer."""
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
    scripts=[HERE/'classify_once.py',HERE/'run_once.py',Path(__file__)]
    parsed=[];producer_tree=None
    for p in scripts:
        tree=ast.parse(p.read_text(encoding='utf-8'),filename=str(p))
        parsed.append({**row(p),'AST_parse_passed':True,'top_level_nodes':len(tree.body)})
        if p.name=='classify_once.py':producer_tree=tree
    constants=[node for node in producer_tree.body if isinstance(node,ast.Assign)
               and any(isinstance(t,ast.Name) and t.id=='PINS' for t in node.targets)]
    assert len(constants)==1
    pins=ast.literal_eval(constants[0].value)
    dependencies=[]
    for name,expected in pins.items():
        p=ROOT/name;assert pin(p)==expected;dependencies.append(row(p))
    checker=ROOT/'research-goal-20261018-stageH-independent/audit_h.py'
    checker_package=checker.parent/'prepared-files.json'
    assert pin(checker)=='45396edbb2ca0162451ebbb19ce00ed853818b7f59a4362af9b899a85d922ac9'
    assert pin(checker_package)=='379ddbe5d72a0bcdf8552a76976989fe644064138188476d51fdd8da8abf5e40'
    dependencies.extend([row(checker),row(checker_package)])
    executable=Path(sys.executable)
    runtime={'path':str(executable),'bytes':executable.stat().st_size,'sha256':pin(executable),
             'version':sys.version,'read_only_external_identity':True,'copied':False}
    command=[str(executable),'research-goal-20261018-stageH-ordered-transport/run_once.py',
             '--launch-authorized-H','--gate','<ROOT_IMMUTABLE_GATE_RELATIVE_PATH>',
             '--gate-sha256','<ROOT_GATE_SHA256>']
    preparation={'schema':'H-preparation-AST-and-hash-only-v1','passed':True,'scripts':parsed,
        'read_only_dependencies':dependencies,'external_read_only_runtime':runtime,'command_template':command,
        'command_template_sha256':sha256(json.dumps(command,separators=(',',':')).encode()).hexdigest(),
        'classification_runs':0,'producer_imports':0,'inputs_calls':0,'Floyd_calls':0,
        'assignment_or_catalog_enumerations':0,'LP_calls':0,'kernel_FS_or_Lean_runs':0,
        'new_immutable_root_gate_required':True,
        'scope':'Only AST and byte/hash checks. No runtime producer function or mathematical classification executed.'}
    write_new(HERE/'preparation.json',preparation)
    files=[HERE/name for name in ['classify_once.py','run_once.py','SPEC.zh.md','required-gate-fields.json',
                                 'prepare_freeze.py','preparation.json']]
    manifest={'schema':'H-prepared-only-source-package-v1','files':[row(p) for p in files],
        'read_only_dependencies':dependencies,'external_read_only_runtime':runtime,
        'classification_executions':0,'mathematical_replay_executions':0,
        'immutable_execution_gate_pending':True,'website_source_and_runtime_budget':'unknown',
        'scope':'Prepared one fixed H pass; not authorization, execution, Empty result, or global floor.'}
    write_new(HERE/'prepared-files.json',manifest)
    print(json.dumps({'prepared_only':True,'manifest':row(HERE/'prepared-files.json'),
                      'owned_source_bytes':sum(p.stat().st_size for p in files),'mathematical_runs':0}))

if __name__=='__main__':main()
