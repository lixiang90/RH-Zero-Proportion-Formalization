"""Static source/diff/hash checks only; no Lean or mathematical evaluations."""
from pathlib import Path
from hashlib import sha256
import ast
import json
import os
import re

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
ORIGINAL=ROOT/'research-goal-20261018-record-source-audit/snapshot/Solution.lean'
CORE=ROOT/'StructuralS1RTiny20261018/Core.lean'
PINS={
 'research-goal-20261018-record-source-audit/snapshot/Solution.lean':'f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf',
 'research-goal-20261018-tiny-overlap-independent/unique-exception.json':'3904ff3b5b0e4867fdb9354c6b8232ede49cde102036f513a10467ac96f0327a',
 'research-goal-20261018-tiny-counting-preparation/prepared-files.json':'36d9ac75c35009cdf0a4280dddabb408a9dfa3ebd4f8de75e9850d256a2aa67b',
}
def row(path):
    data=path.read_bytes();return {'path':path.relative_to(ROOT).as_posix(),'bytes':len(data),'sha256':sha256(data).hexdigest()}
def load(path):return json.loads(path.read_text(encoding='utf-8'))
def write(path,value):
    with path.open('x',encoding='utf-8',newline='\n') as handle:
        json.dump(value,handle,indent=2);handle.write('\n');handle.flush();os.fsync(handle.fileno())
def part(text,start,end):
    assert text.count(start)==text.count(end)==1
    return text[text.index(start):text.index(end)]
def main():
    assert not (HERE/'prepared-files.json').exists() and not (HERE/'static-checks.json').exists()
    dependencies=[]
    for name,expected in PINS.items():
        item=row(ROOT/name);assert item['sha256']==expected;dependencies.append(item)
    counting_package=load(ROOT/'research-goal-20261018-tiny-counting-preparation/prepared-files.json')
    for item in counting_package['files']:
        actual=row(ROOT/item['path']);assert actual==item;dependencies.append(actual)
    original=ORIGINAL.read_text(encoding='utf-8');core=CORE.read_text(encoding='utf-8');generation=load(HERE/'generation.json')
    assert row(CORE)==generation['generated_Core']
    assert generation['source_sha256_start']==generation['source_sha256_end']==PINS[ORIGINAL.relative_to(ROOT).as_posix()]
    old_packed=[line for line in original.splitlines() if ' := zfNat64 ' in line]
    new_packed=[line for line in core.splitlines() if ' := zfNat64 ' in line]
    assert old_packed==new_packed and len(old_packed)==137
    cursor=lambda text:[line for line in text.splitlines() if re.match(r'theorem ready.*_(?:cursor|parent_cursor)\s*:',line)]
    assert cursor(original)==cursor(core)
    old_check=part(original,'noncomputable def mcheckP (top : ℕ)','theorem mcheckP_ok ')
    new_check=part(core,'noncomputable def mcheckP (goalN : ℕ)','theorem mcheckP_ok ')
    restored=new_check.replace('def mcheckP (goalN : ℕ) (top : ℕ)','def mcheckP (top : ℕ)',1)
    restored=re.sub(r'\bgoalN\b','cN',restored)
    assert restored==old_check
    assert core.count('abbrev Covered : Cl → Prop := CovBy 8 PR TinyGoal')==1
    assert 'cov_splitB (P := Pg cN 8 BS TS)' not in core
    assert core.count('cov_splitB (P := TinyGoal)')==1
    assert core.count('noncomputable def stEq (a b : St)')==1
    assert core.count('theorem St_eq ')==1
    assert '(h : mleafP (tinyTarget s) top bk tD bD pb R w s ≠ 0)' in core
    assert 'hwin W hW (fun idx hi g hg => tiny_forget (hrun idx hi g hg))' in core
    assert not re.search(r'\b(?:sorry|admit|native_decide)\b',core)
    assert not re.search(r'^\s*axiom\s',core,re.M)
    sources=['generate_core.py','generate_core_v1.py','freeze_prepared.py']
    for filename in sources:ast.parse((HERE/filename).read_text(encoding='utf-8'),filename=filename)
    assert row(HERE/'generate_core.py')['sha256']=='75d9ea6aa8f3276fb9641ffa40cc5229e4cc55cce0006cc2e4456a10c8314ca0'
    assert row(HERE/'generate_core_v1.py')['sha256']=='cca08423d63632aa7f196148cf070f3a62f4a670af0b9d1768f6ce940562969d'
    counting=row(ROOT/'StructuralS1RTiny20261018/Counting.lean')
    static={'schema':'tiny-Core-source-only-static-shape-checks-v1','passed_source_checks':True,
        'Core':row(CORE),'all137_packed_declaration_lines_identical':True,
        'all_original_ready_cursor_lines_identical':True,
        'single_target_checker_restores_original_text_exactly':True,
        'Covered_and_split_use_TinyGoal':True,'stEq_and_St_eq_each_single_definition':True,
        'cert_of_forgets_strong_goal_before_original_root_cover':True,
        'forbidden_proof_shortcuts_absent':True,'three_Python_AST_checks':True,
        'current_Core_plus_prepared_Counting_data_bytes':CORE.stat().st_size+counting['bytes'],
        'this_sum_excludes_missing_pair_root_and_final_instance':True,
        'actual_text_generator_calls':2,'first_failed_second_root_authorized_versioned_anchor_fix':True,
        'leaf_Finite_math_kernel_solver_or_Lean_executions':0,
        'new_Core_typechecks_or_ordinary_axioms_export_Nano_source_runtime_gate_passed':False}
    write(HERE/'static-checks.json',static)
    owned=[row(path) for path in sorted(HERE.iterdir()) if path.is_file() and path.name!='prepared-files.json']+[row(CORE)]
    manifest={'schema':'tiny-Core-source-conversion-prepared-files-v1','files':owned,'read_only_dependencies':dependencies,
        'generation_scope':'two source-text generator attempts; first no outputs, explicitly versioned newline fix then success',
        'proof_status':'new Core has never been Lean parsed/elaborated; pair/root-outside/final-instance absent, not stubbed',
        'whole_floor_or_record_or_submission_proven':False,'source_only_preparation_no_mathematical_execution':True}
    write(HERE/'prepared-files.json',manifest)
    print(json.dumps({'prepared_manifest':row(HERE/'prepared-files.json'),'Core':row(CORE),
        'owned_rows':len(owned),'current_Core_plus_Counting_bytes':static['current_Core_plus_prepared_Counting_data_bytes'],
        'new_mathematical_or_Lean_runs':0}))
if __name__=='__main__':main()
