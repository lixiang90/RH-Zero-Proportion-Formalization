"""N AST/read-only bytehash/old-index metadata only. No producer imports."""
from pathlib import Path
from hashlib import sha256
import ast
import json
import os
import struct
import sys
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
def pin(p):
    h=sha256()
    with p.open('rb') as f:
        for block in iter(lambda:f.read(1048576),b''):h.update(block)
    return h.hexdigest()
def row(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':pin(p)}
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def write(p,x):
    with p.open('x',encoding='utf-8',newline='\n') as f:
        json.dump(x,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
def literal(tree,name):
    nodes=[n for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id==name for t in n.targets)]
    assert len(nodes)==1;return ast.literal_eval(nodes[0].value)
def main():
    for name in ['preparation.json','prepared-files.json','started.json','launch.json','result.json','prefix.json',
        'failure.json','native-results.jsonl.gz','case-records.jsonl.gz','original-components.jsonl.gz']:
        assert not (HERE/name).exists(),('prepare_before_any_execution',name)
    scripts=['component_model.py','reconstruct_support.py','check_raw_certificate.py','discover_complete.py',
        'run_once.py','prepare_freeze.py']
    trees={name:ast.parse((HERE/name).read_text(encoding='utf-8'),filename=str(HERE/name)) for name in scripts}
    deps={}
    def add(name,expected=None,size=None):
        p=(ROOT/name).resolve();assert p.is_relative_to(ROOT);actual=pin(p)
        if expected is not None:assert actual==expected,(name,actual,expected)
        if size is not None:assert p.stat().st_size==size
        if name in deps:assert deps[name]['sha256']==actual
        deps[name]=row(p)
    pins=literal(trees['discover_complete.py'],'PINS')
    for name,expected in pins.items():
        add(name,expected)
        if Path(name).name in ['files.json','audit-files.json']:
            package=load(ROOT/name)
            for field in ['files','read_only_dependencies','read_only_existing_references','dependencies']:
                for item in package.get(field,[]):add(item['path'],item['sha256'],item.get('bytes'))
    # No model/FS calls: these are the existing frozen uint32 index lists only.
    h=(ROOT/'research-goal-20261018-stageH-ordered-transport/remaining-indices.u32.bin').read_bytes()
    j=(ROOT/'research-goal-20261018-stageJ-fixed-basis-preparation/remaining-indices.u32.bin').read_bytes()
    hi=[v[0] for v in struct.iter_unpack('<I',h)];ji=[v[0] for v in struct.iter_unpack('<I',j)]
    assert hi==sorted(set(hi)) and ji==sorted(set(ji))
    assert len(hi)==15378 and len(ji)==15377 and set(hi)-set(ji)=={5331088}
    assert set(ji)<=set(hi) and 2417 in hi and 2417!=5331088
    runtime_path=ROOT/'research-goal-20261018-stageM-component-envelope-preparation/external-runtime.json'
    add(runtime_path.relative_to(ROOT).as_posix())
    runtime=load(runtime_path);external=[]
    for item in runtime['files']:
        p=Path(item['path']);assert pin(p)==item['sha256'] and p.stat().st_size==item['bytes']
        external.append(item)
    assert str(Path(sys.executable))==runtime['python_executable']
    gate=load(HERE/'required-gate-fields.json')
    assert gate['physical_span_pooling'] and gate['explicit_deduction_indices']==[2417,5331088]
    assert gate['maximum_linprog_calls']==15376 and not gate['execution_authorized_by_this_template']
    cli=[runtime['python_executable'],'-B','-X','utf8',
        'research-goal-20261018-stageN-complete-component-preparation/run_once.py','--launch-authorized-complete-N',
        '--gate','<ROOT_GATE_RELATIVE_PATH>','--gate-sha256','<ROOT_GATE_SHA256>']
    preparation={'schema':'N-static-AST-identity-only-preparation-v1','passed':True,
        'scripts':[{**row(HERE/name),'AST_parse_passed':True} for name in scripts],
        'read_only_dependencies':[deps[n] for n in sorted(deps)],'external_read_only_runtime_files':external,
        'existing_index_metadata':{'H_count':15378,'J_remaining_count':15377,'J_only_Lower_index':5331088,
            'M_already_verified_Lower_index':2417,'possible_new_solver_cases':15376},
        'command_template':cli,'producer_imports':0,'FS_extractions':0,'matrix_rank_or_inverse_evaluations':0,
        'point_or_kernel_evaluations':0,'LP_or_Lean_runs':0,'immutable_execution_gate_pending':True,
        'resource_limits_not_yet_chosen':True,'source_runtime_and_payload_budget':'unknown'}
    write(HERE/'preparation.json',preparation)
    owned=scripts+['SPEC.zh.md','required-gate-fields.json','preparation.json']
    manifest={'schema':'N-pooled-component-complete-domain-prepared-only-v1','files':[row(HERE/n) for n in owned],
        'read_only_dependencies':[deps[n] for n in sorted(deps)],'external_read_only_runtime_files':external,
        'FS_extractions':0,'matrix_rank_or_inverse_evaluations':0,'point_or_kernel_evaluations':0,'LP_or_Lean_runs':0,
        'immutable_execution_gate_required':True,'source_runtime_payload_budget':'unknown',
        'new_global_floor_or_unconditional_kappa_proven':False,'website_submission_ready':False}
    write(HERE/'prepared-files.json',manifest)
    print(json.dumps({'prepared_only':True,'manifest':row(HERE/'prepared-files.json'),
        'source_files':{n:pin(HERE/n) for n in scripts},'read_only_dependencies':len(deps),
        'mathematical_executions':0,'existing_index_metadata_only':True}))
if __name__=='__main__':main()
