"""Versioned static adaptation only: never executes the flatten generator."""
import difflib
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
OLD = ROOT / 'research-goal-20261018-tiny-flatten-preparation-v1'

def sha(data):
    return hashlib.sha256(data).hexdigest()

def main():
    manifest = OLD / 'prepared-files.json'
    assert sha(manifest.read_bytes()) == '17ef8ed6f5e19911ecee399ed5898a25808b7cd700300c766117860a2980a0f4'
    previous = json.loads(manifest.read_text(encoding='utf-8'))
    for row in previous['files']:
        assert sha((ROOT / row['path']).read_bytes()) == row['sha256'], row['path']
    phase = ROOT / 'research-goal-20261018-tiny-runtime-preparation/phase3-prepared.json'
    assert sha(phase.read_bytes()) == '73a0c2b6fb124fe363fd060908d66f3988ffac481627a80287b221d66a9a797f'
    outputs = {}
    gen = (OLD / 'generate_draft.py').read_text(encoding='utf-8')
    gen = gen.replace('StructuralS1RTiny20261018.Dev.Counting', 'StructuralS1RTiny20261018.Phase2.Counting')
    gen = gen.replace('StructuralS1RTiny20261018/Dev/Counting.lean', 'StructuralS1RTiny20261018/Phase2/Counting.lean')
    gen = gen.replace('StructuralS1RTiny20261018.Phase1.Final', 'StructuralS1RTiny20261018.Phase3.Final')
    gen = gen.replace('StructuralS1RTiny20261018/Phase1/Final.lean', 'StructuralS1RTiny20261018/Phase3/Final.lean')
    outputs['generate_draft.py'] = gen
    prep = (OLD / 'prepare_only.py').read_text(encoding='utf-8')
    replacements = {
        'StructuralS1RTiny20261018/Dev/Counting.lean': 'StructuralS1RTiny20261018/Phase2/Counting.lean',
        'e1629a96ac6239ae0d216c608c99f6d929c779b8201f4835aa72b125b2923f87': '2bda5c9df708b4568f8f08447894cb73a3c6ecb9d2c77be67e2eb46387be868e',
        'StructuralS1RTiny20261018/Phase1/Final.lean': 'StructuralS1RTiny20261018/Phase3/Final.lean',
        'f99f0bafbc724b657f7321cf262d3550711a9c303c18a93ac03c3b15104ec497': '356be48d1326022cc8148be1023d42a160a7562faa8c2f13af32ffb807de36ab',
        'assert module_bytes == 1_976_894': 'assert module_bytes == 1_977_056',
        "'schema':'tiny-flatten-generator-prepared-v2'": "'schema':'tiny-flatten-generator-prepared-v3'",
        "'schema':'tiny-flatten-static-preparation-v2'": "'schema':'tiny-flatten-static-preparation-v3'",
        "'adapt_v1.py','v0-to-v1.diff'": "'adapt_v2.py','v1-to-v2.diff'",
    }
    for before, after in replacements.items():
        assert prep.count(before) == 1, before
        prep = prep.replace(before, after)
    marker = " 'research-goal-20261018-tiny-runtime-preparation/phase1-prepared.json',"
    assert prep.count(marker) == 1
    prep = prep.replace(marker, marker + "\n 'research-goal-20261018-tiny-runtime-preparation/phase2-prepared.json',\n 'research-goal-20261018-tiny-runtime-preparation/phase3-prepared.json',\n 'research-goal-20261018-tiny-flatten-preparation-v1/prepared-files.json',\n 'research-goal-20261018-tiny-flatten-preparation-v1/generate_draft.py',")
    outputs['prepare_only.py'] = prep
    outputs['official-wrapper.lean.txt'] = (OLD / 'official-wrapper.lean.txt').read_text(encoding='utf-8')
    spec = (OLD / 'SPEC.zh.md').read_text(encoding='utf-8')
    spec = spec.replace('Dev.Counting、Phase1.Final', 'Phase2.Counting、Phase3.Final')
    spec = spec.replace('1,976,894 bytes', '1,977,056 bytes')
    spec = spec.replace('research-goal-20261018-tiny-flatten-preparation-v1/generate_draft.py', 'research-goal-20261018-tiny-flatten-preparation-v2/generate_draft.py')
    spec += '\n本 v2 仅绑定 Phase2.Counting 的 let/Nat cast 归一化和 Phase3.Final 的函数别名/根计数名修复。算法、wrapper、阈值、数学命题均保持；输入版本是已冻结准备，不代表 ordinary 通过。generator 仍须在统一生产 t0 之后执行一次。\n'
    outputs['SPEC.zh.md'] = spec
    outputs['v1-to-v2.diff'] = ''.join(''.join(difflib.unified_diff(
        (OLD / name).read_text(encoding='utf-8').splitlines(keepends=True), data.splitlines(keepends=True),
        fromfile='v1/' + name, tofile='v2/' + name)) for name, data in outputs.items())
    for name in outputs:
        assert not (HERE / name).exists(), name
    for name, data in outputs.items():
        with (HERE / name).open('x', encoding='utf-8', newline='\n') as f:
            f.write(data)
    delta = {'schema': 'tiny-flatten-static-adaptation-v2', 'prior_prepared_sha256': sha(manifest.read_bytes()),
             'phase3_prepared_sha256': sha(phase.read_bytes()), 'generator_algorithm_changed': False,
             'wrapper_bytes_changed': False, 'namespace_names_changed': False,
             'old_files_modified': False, 'generator_executions': 0, 'Lean_runs': 0,
             'changed_module_paths': ['Phase2.Counting', 'Phase3.Final']}
    with (HERE / 'version-delta.json').open('x', encoding='utf-8', newline='\n') as f:
        json.dump(delta, f, ensure_ascii=False, indent=2); f.write('\n')
    print(json.dumps({'static_adaptation_written': True, 'generator_executions': 0}))

if __name__ == '__main__':
    main()
