"""Existing bytehashes only; no proof or generator execution."""
from hashlib import sha256
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
def row(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':sha256(p.read_bytes()).hexdigest()}
def main():
    assert not (HERE/'files.json').exists()
    review=json.loads((HERE/'text-review.json').read_text(encoding='utf8'))
    assert review['passed_text_identity'] is True and review['new_Lean_or_mathematical_runs']==0
    deps=[
        'research-goal-20261018-record-source-audit/snapshot/Solution.lean',
        'StructuralS1RTiny20261018/Core.lean',
        'research-goal-20261018-tiny-core-preparation/generate_core.py',
        'research-goal-20261018-tiny-core-preparation/generate_core_v1.py',
        'research-goal-20261018-tiny-core-preparation/generator-v1-fix.diff',
        'research-goal-20261018-tiny-core-preparation/Core.diff',
        'research-goal-20261018-tiny-core-preparation/generation.json',
        'research-goal-20261018-tiny-core-preparation/first-generation-terminal.json',
        'research-goal-20261018-tiny-core-preparation/v1-generation-terminal.json',
        'research-goal-20261018-tiny-overlap-independent/unique-exception.json',
        'research-goal-20261018-tiny-core-independent-static/files.json']
    out={'schema':'actual-tiny-Core-independent-static-files-v1',
        'files':[row(p) for p in sorted(HERE.iterdir()) if p.is_file() and p.name!='files.json'],
        'read_only_dependencies':[row(ROOT/p) for p in deps],'static_only':True,
        'generator_Lean_or_mathematical_execution_runs':0,'no_concrete_static_error_found':True,
        'full_Core_global_floor_or_final_candidate_proven':False}
    with (HERE/'files.json').open('x',encoding='utf8') as f:json.dump(out,f,indent=2);f.write('\n')
    print(json.dumps({'manifest':row(HERE/'files.json'),'receipt':row(HERE/'text-review.json')}))
if __name__=='__main__':main()
