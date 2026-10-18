"""AST and immutable-byte review only. Never imports a mathematical producer."""
from pathlib import Path
from hashlib import sha256
import ast
import json
import os
import sys

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
RUNTIME_SHA='3adbbf2af609e206e3ca18cd55fc7c4b52f5c8bb8218dd99fd5a9e50d7a193cd'
def pin(p):return sha256(p.read_bytes()).hexdigest()
def row(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':pin(p)}
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def write(p,x):
    with p.open('x',encoding='utf-8',newline='\n') as f:
        json.dump(x,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
def literal(tree,name):
    found=[n for n in tree.body if isinstance(n,ast.Assign)
        and any(isinstance(t,ast.Name) and t.id==name for t in n.targets)]
    assert len(found)==1;return ast.literal_eval(found[0].value)
def main():
    for name in ['preparation.json','prepared-files.json','started.json','result.json','launch.json','child.json',
        'terminal.json','failure.json','inconclusive.json','basis.json','affine-cache.jsonl','cache-index.json',
        'prefix.json','classifications.bin','remaining-indices.u32.bin','stdout.log','stderr.log','files.json']:
        assert not (HERE/name).exists(),('preparation_must_precede_execution',name)
    scripts=['classify_once.py','run_once.py','generate_shared_core.py','original_affine_core.py','freeze_result.py','prepare_freeze.py']
    trees={};parsed=[]
    for name in scripts:
        p=HERE/name;trees[name]=ast.parse(p.read_text(encoding='utf-8'),filename=str(p))
        parsed.append({**row(p),'AST_parse_passed':True})
    expected=literal(trees['classify_once.py'],'PINS');deps={}
    def add(name,expected_sha,expected_bytes=None):
        p=(ROOT/name).resolve();assert p.is_relative_to(ROOT) and pin(p)==expected_sha
        if expected_bytes is not None:assert p.stat().st_size==expected_bytes
        if name in deps:assert deps[name]['sha256']==expected_sha
        deps[name]=row(p)
    for name,expected_sha in expected.items():add(name,expected_sha)
    # The I package fixes the original source, parser/math, A cursor traces, B
    # witness packet, and historical mathematical audits, without executing them.
    original=load(ROOT/'research-goal-20261018-stageI-original-affine-point/files.json')
    for field in ['files','read_only_dependencies']:
        for item in original.get(field,[]):add(item['path'],item['sha256'],item.get('bytes'))
    # Verify the only function-body adaptation as text, without imports/calls.
    source=(ROOT/'research-goal-20261018-stageI-original-affine-point/evaluate_once.py').read_text(encoding='utf-8')
    body=source[source.index('def extract_original_affine('):source.index('def embed_and_evaluate(')]
    old="FIXED_CELLS[cid]['payload_bits']";new="cell['witness']['consumed_payload_bits']"
    assert body.count(old)==1
    generated=(HERE/'original_affine_core.py').read_text(encoding='utf-8')
    assert generated[generated.index('def extract_original_affine('):]==body.replace(old,new)
    gate=load(HERE/'required-gate-fields.json')
    assert gate['expected_H_remaining']==15378 and gate['basis_row_ids']==[9,29,36,74,84,110,130,153,154]
    assert gate['new_FS_kernel_points_LP_or_Lean_authorized']==0
    executable=Path(sys.executable);assert pin(executable)==RUNTIME_SHA
    runtime={'path':str(executable),'sha256':pin(executable),'bytes':executable.stat().st_size,
        'version':sys.version,'read_only_external_identity':True,'copied':False}
    command=[str(executable),'-B','-X','utf8',
        'research-goal-20261018-stageJ-fixed-basis-preparation/run_once.py','--launch-authorized-fixed-J',
        '--gate','<ROOT_IMMUTABLE_GATE_RELATIVE_PATH>','--gate-sha256','<ROOT_GATE_SHA256>']
    receipt={'schema':'J-AST-bytehash-only-preparation-v1','passed':True,'scripts':parsed,
        'read_only_dependencies':[deps[name] for name in sorted(deps)],'external_read_only_runtime':runtime,
        'command_template':command,'command_template_sha256':sha256(json.dumps(command,separators=(',',':')).encode()).hexdigest(),
        'shared_core_body_equals_frozen_I_except_one_payload_lookup':True,
        'static_source_text_generator_calls':1,'producer_imports':0,'inputs_calls':0,
        'source_model_configure_calls':0,'FS_extractions':0,'matrix_rank_or_inverse_evaluations':0,
        'point_or_kernel_evaluations':0,'LP_or_Lean_runs':0,'stageI_independent_pass_required_at_future_gate':True,
        'new_immutable_root_execution_gate_required':True,'independent_J_checker_is_not_a_producer_math_dependency':True,
        'scope':'AST, exact source-body comparison and byte hashes only; no classification executed.'}
    write(HERE/'preparation.json',receipt)
    files=[HERE/name for name in scripts+['SPEC.zh.md','required-gate-fields.json','preparation.json']]
    manifest={'schema':'J-fixed-basis-prepared-only-source-package-v1','files':[row(p) for p in files],
        'read_only_dependencies':[deps[name] for name in sorted(deps)],'external_read_only_runtime':runtime,
        'arithmetic_classification_executions':0,'FS_extractions':0,'matrix_rank_or_inverse_evaluations':0,
        'point_or_kernel_evaluations':0,'LP_or_Lean_runs':0,'future_stageI_independent_gate_pending':True,
        'independent_J_checker_not_a_producer_mathematical_input':True,'immutable_execution_gate_pending':True,
        'below_target_valid_exact_bounds_will_be_retained':True,'new_global_floor_or_kappa_proven':False,
        'website_source_and_total_runtime_budget':'unknown','scope':'Preparation, not authorization or mathematical result.'}
    write(HERE/'prepared-files.json',manifest)
    print(json.dumps({'prepared_only':True,'manifest':row(HERE/'prepared-files.json'),
        'owned_package_bytes':sum(p.stat().st_size for p in files),'read_only_dependencies':len(deps),
        'mathematical_executions':0}))

if __name__=='__main__':main()
