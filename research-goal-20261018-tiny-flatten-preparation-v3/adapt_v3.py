"""Static Phase4 source binding only; never runs the generator."""
import difflib
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
OLD = ROOT / 'research-goal-20261018-tiny-flatten-preparation-v2'

def sha(data):
    return hashlib.sha256(data).hexdigest()

def main():
    prior = OLD / 'prepared-files.json'
    assert sha(prior.read_bytes()) == '9844ae7a2266a87f5aaa0e561befc5ebdb7aa00fefc82682bb2c3749f516956b'
    for row in json.loads(prior.read_text(encoding='utf-8'))['files']:
        assert sha((ROOT / row['path']).read_bytes()) == row['sha256']
    receipt_path = ROOT / 'tmp/current-s1r-tiny-20261018/phase4-v0/Final.receipt.json'
    receipt = json.loads(receipt_path.read_text(encoding='utf-8'))
    assert receipt['source_sha256'] == 'd477fd3181e0d4d5a3c89bcbcb987dd6cad00fbdde1946d01c26ac0c279489ed'
    assert receipt['exit_code'] == 0 and receipt['ordinary_compile_passed'] and receipt['axiom_audit_passed']
    outputs = {}
    outputs['generate_draft.py'] = (OLD / 'generate_draft.py').read_text(encoding='utf-8').replace(
        'StructuralS1RTiny20261018.Phase3.Final', 'StructuralS1RTiny20261018.Phase4.Final').replace(
        'StructuralS1RTiny20261018/Phase3/Final.lean', 'StructuralS1RTiny20261018/Phase4/Final.lean')
    prep = (OLD / 'prepare_only.py').read_text(encoding='utf-8')
    replacements = {
        'StructuralS1RTiny20261018/Phase3/Final.lean': 'StructuralS1RTiny20261018/Phase4/Final.lean',
        '356be48d1326022cc8148be1023d42a160a7562faa8c2f13af32ffb807de36ab': 'd477fd3181e0d4d5a3c89bcbcb987dd6cad00fbdde1946d01c26ac0c279489ed',
        'assert module_bytes == 1_977_056': 'assert module_bytes == 1_977_052',
        "'schema':'tiny-flatten-generator-prepared-v3'": "'schema':'tiny-flatten-generator-prepared-v4'",
        "'schema':'tiny-flatten-static-preparation-v3'": "'schema':'tiny-flatten-static-preparation-v4'",
        "'adapt_v2.py','v1-to-v2.diff'": "'adapt_v3.py','v2-to-v3.diff'",
    }
    for a, b in replacements.items():
        assert prep.count(a) == 1, a
        prep = prep.replace(a, b)
    marker = " 'research-goal-20261018-tiny-runtime-preparation/phase3-prepared.json',"
    assert prep.count(marker) == 1
    prep = prep.replace(marker, marker + "\n 'research-goal-20261018-tiny-runtime-preparation/phase4-prepared.json',\n 'tmp/current-s1r-tiny-20261018/phase4-v0/Final.receipt.json',\n 'tmp/current-s1r-tiny-20261018/phase4-v0/terminal.json',\n 'research-goal-20261018-tiny-flatten-preparation-v2/prepared-files.json',\n 'research-goal-20261018-tiny-flatten-preparation-v2/generate_draft.py',")
    outputs['prepare_only.py'] = prep
    outputs['official-wrapper.lean.txt'] = (OLD / 'official-wrapper.lean.txt').read_text(encoding='utf-8')
    spec = (OLD / 'SPEC.zh.md').read_text(encoding='utf-8').replace('Phase3.Final', 'Phase4.Final')
    spec = spec.replace('1,977,056 bytes', '1,977,052 bytes')
    spec = spec.replace('research-goal-20261018-tiny-flatten-preparation-v2/generate_draft.py',
                        'research-goal-20261018-tiny-flatten-preparation-v3/generate_draft.py')
    spec += '\n本 v3仅将最后输入更新为普通内核和六个传递根公理审计已通过的 Phase4.Final；绑定该次 receipt/terminal，不复用其用户 olean 做最终单源检查。本文仍是准备，generator 零执行。\n'
    outputs['SPEC.zh.md'] = spec
    outputs['v2-to-v3.diff'] = ''.join(''.join(difflib.unified_diff(
        (OLD / n).read_text(encoding='utf-8').splitlines(keepends=True), d.splitlines(keepends=True),
        fromfile='v2/' + n, tofile='v3/' + n)) for n, d in outputs.items())
    for n in outputs:
        assert not (HERE / n).exists()
    for n, d in outputs.items():
        with (HERE / n).open('x', encoding='utf-8', newline='\n') as f:
            f.write(d)
    with (HERE / 'version-delta.json').open('x', encoding='utf-8', newline='\n') as f:
        json.dump({'schema': 'tiny-flatten-static-adaptation-v3',
                   'prior_prepared_sha256': sha(prior.read_bytes()),
                   'Phase4_final_receipt_sha256': sha(receipt_path.read_bytes()),
                   'generator_algorithm_changed': False, 'wrapper_bytes_changed': False,
                   'old_files_modified': False, 'generator_executions': 0}, f, indent=2); f.write('\n')
    print(json.dumps({'static_adaptation_written': True, 'generator_executions': 0}))

if __name__ == '__main__':
    main()
