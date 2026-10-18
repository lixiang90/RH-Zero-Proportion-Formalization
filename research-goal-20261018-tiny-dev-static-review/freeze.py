"""Minimal existing source hashes only, no Lean or mathematical execution."""
from hashlib import sha256
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
def row(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':sha256(p.read_bytes()).hexdigest()}
def main():
    assert not (HERE/'files.json').exists()
    pins={
        'research-goal-20261018-tiny-runtime-preparation/dev-source-files.json':'6d166f1640d8ad175329ef9587eb6df1ebfd34e1363c15f40017094d5b74943e',
        'research-goal-20261018-tiny-localization-preparation/prepared-files.json':'bd842466cffb01ec870b7aaa8d9b416b9c566f8eb79b8a90733ab88d5f3002e8',
        'research-goal-20261018-tiny-runtime-preparation/compiler-prepared.json':'4533c2fedb5d6f891da5c496e34aec58ece146fe839121a29d5ea46014ff5071',
        'StructuralS1RTiny20261018/Dev/Core.lean':'1e144c848b39c85277af45c590cb0e54e93b2f098d44f5eb40bcb2e1b8d216ac',
        'StructuralS1RTiny20261018/Dev/Localization.lean':'8d02de83edfced0a98a9b717a4b6c9de65d9ccc392d914084a59fda7b958f179',
        'StructuralS1RTiny20261018/Dev/Counting.lean':'e1629a96ac6239ae0d216c608c99f6d929c779b8201f4835aa72b125b2923f87',
        'StructuralS1RTiny20261018/Dev/Final.lean':'f4d398bc846415d6e428c07055ea799f2d70318aafeee69ab3a4864baf05b3de',
        'StructuralS1RM20261018/CurrentPrefix.lean':'ea8e01118d19158ba8313504910645ad467ea86eb2ea65a897859ae98101df21'}
    deps=[]
    for name,h in pins.items():
        r=row(ROOT/name);assert r['sha256']==h;deps.append(r)
    out={'schema':'tiny-Dev-four-module-independent-static-review-v1',
        'files':[row(HERE/'REVIEW.zh.md'),row(Path(__file__))],
        'read_only_dependencies':deps,'no_concrete_static_mathematical_or_interface_gap_found':True,
        'independent_Lean_math_network_execution_runs':0,'compile_inputs_changed':False,
        'ordinary_Nano_official_submission_acceptance_not_asserted':True}
    with (HERE/'files.json').open('x',encoding='utf8') as f:json.dump(out,f,indent=2);f.write('\n')
    print(json.dumps({'manifest':row(HERE/'files.json'),'static_only':True}))
if __name__=='__main__':main()
