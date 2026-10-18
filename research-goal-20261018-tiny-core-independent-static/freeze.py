"""Static file hashes only. Does not import or execute the conversion script."""
from hashlib import sha256
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
def row(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':sha256(p.read_bytes()).hexdigest()}
def main():
    assert not (HERE/'files.json').exists()
    deps=[
        ROOT/'research-goal-20261018-tiny-core-preparation/generate_core.py',
        ROOT/'research-goal-20261018-record-source-audit/snapshot/Solution.lean',
        ROOT/'research-goal-20261018-tiny-overlap-independent/unique-exception.json',
        ROOT/'research-goal-20261018-tiny-overlap-independent/audit-files.json',
        ROOT/'research-goal-20261016/macro-reviews/006-20261018.zh.md',
        ROOT/'StructuralS1RTiny20261018/Counting.lean']
    assert row(deps[0])['sha256']=='75d9ea6aa8f3276fb9641ffa40cc5229e4cc55cce0006cc2e4456a10c8314ca0'
    out={'schema':'tiny-core-script-independent-static-review-v1',
        'files':[row(HERE/'REVIEW.zh.md'),row(Path(__file__))],
        'read_only_dependencies':[row(p) for p in deps],
        'source_conversion_executed':False,'mathematical_or_Lean_runs':0,
        'no_concrete_static_mathematical_or_identity_error_found':True,
        'generated_diff_identity_and_actual_compilation_pending':True}
    with (HERE/'files.json').open('x',encoding='utf8') as f:json.dump(out,f,indent=2);f.write('\n')
    print(json.dumps({'manifest':row(HERE/'files.json'),'static_only':True}))
if __name__=='__main__':main()
