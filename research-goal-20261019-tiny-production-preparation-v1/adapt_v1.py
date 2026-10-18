"""Versioned cold-runner preparation only. Never runs generation or verification."""
import ast
import difflib
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
OLD = ROOT / 'research-goal-20261018-tiny-production-preparation'
FLATTEN = ROOT / 'research-goal-20261019-tiny-flatten-preparation-v4'
FLATTEN_PIN = '2b77159157e500b0177c3c2294860830a495248ce3e3b216a813524032509d72'
SOURCE_PIN = '98a9dfe125cfdb4febc24fb8666bb73228e4f27fcbac9fe66506c1c7720f99d6'

def sha(blob):
    return hashlib.sha256(blob).hexdigest()

def main():
    oldmanifest = OLD / 'prepared-files.json'
    assert sha(oldmanifest.read_bytes()) == '8de6adf94411254d8aef96e625faa1dc869069848049e99eab31e38a06e957c1'
    assert sha((FLATTEN / 'prepared-files.json').read_bytes()) == FLATTEN_PIN
    for r in json.loads(oldmanifest.read_text(encoding='utf-8'))['files']:
        assert sha((ROOT / r['path']).read_bytes()) == r['sha256']
    runner = (OLD / 'run_production.py').read_text(encoding='utf-8')
    runner = runner.replace('/var/tmp/rh-zero-20261015/tiny-production-v0', '/var/tmp/rh-zero-20261015/tiny-production-v1')
    runner = runner.replace('tmp/current-s1r-tiny-20261018/production-v0', 'tmp/current-s1r-tiny-20261018/production-v1')
    runner = runner.replace("'schema': 'tiny-cold-production-result-v1'", "'schema': 'tiny-cold-production-result-v2'")
    runner = runner.replace("gate['ordinary_final_all_six_roots_passed']", "gate['original_ordinary_final_all_six_roots_passed']")
    before = "        assert gate['latest_record_receipt_sha256'] == config['latest_record_receipt_sha256']"
    assert runner.count(before) == 1
    runner = runner.replace(before, """        assert gate['production_source_prepared_sha256'] == config['production_source_prepared_sha256']
        recheck = gate['fresh_record_recheck']
        recheck_path = (ROOT / recheck['path']).resolve()
        assert recheck_path.is_relative_to(ROOT)
        self.bind(recheck_path, recheck['sha256'])
        fresh_recheck = load(recheck_path)
        assert fresh_recheck['status'] == 200
        assert fresh_recheck['current']['exactRational'] == config['expected_current_record']
        previous_failure = load(ROOT / config['previous_failure_receipt'])
        assert previous_failure['failed'] is True and previous_failure['local_single_file_verified'] is False
        assert previous_failure['stage'] == 'nanoda'
        self.receipt['fresh_record_recheck'] = recheck
        self.receipt['previous_failed_attempt_sha256'] = config['previous_failure_receipt_sha256']
        self.receipt['deduplicated_production_source_prepared_sha256'] = config['production_source_prepared_sha256']
        self.receipt['local_nanoda_threads'] = 4
        self.receipt['locked_official_Comparator_default_nanoda_is_serial'] = True
        self.receipt['official_runtime_equivalence_claimed'] = False""")
    helper = (OLD / 'windows_generate.py').read_text(encoding='utf-8')
    helper = helper.replace('research-goal-20261018-tiny-flatten-preparation-v3', 'research-goal-20261019-tiny-flatten-preparation-v4')
    helper = helper.replace('tmp/current-s1r-tiny-20261018/production-v0', 'tmp/current-s1r-tiny-20261018/production-v1')
    helper = helper.replace('8d866f77503210091280574f6a14fcead5461f07c156f383f1b67f78ee52ab32', FLATTEN_PIN)
    freezer = (OLD / 'freeze_static.py').read_text(encoding='utf-8')
    freezer = freezer.replace('research-goal-20261018-tiny-flatten-preparation-v3', 'research-goal-20261019-tiny-flatten-preparation-v4')
    freezer = freezer.replace('8d866f77503210091280574f6a14fcead5461f07c156f383f1b67f78ee52ab32', FLATTEN_PIN)
    freezer = freezer.replace("'schema': 'tiny-production-configuration-v1'", "'schema': 'tiny-production-configuration-v2'")
    freezer = freezer.replace("'schema': 'tiny-cold-production-prepared-v1'", "'schema': 'tiny-cold-production-prepared-v2'")
    marker = "    depnames = {"
    freezer = freezer.replace(marker, marker + "\n        'research-goal-20261018-tiny-production-preparation/prepared-files.json',\n        'research-goal-20261018-tiny-production-preparation/run_production.py',\n        'research-goal-20261019-tiny-dedup-source-preparation/prepared-files.json',\n        'research-goal-20261019-tiny-dedup-source-preparation/prepare_sources.py',\n        'research-goal-20261019-tiny-dedup-static-review/report-files.json',\n        'research-goal-20261019-nanoda-thread-static-review/files.json',\n        'research-goal-20261019-nanoda-thread-static-review/REVIEW.zh.md',\n        'tmp/current-s1r-tiny-20261018/production-v0/failure.json',")
    config_marker = "        'flatten_directory': FLATTEN.relative_to(ROOT).as_posix(),"
    freezer = freezer.replace(config_marker, config_marker + "\n        'production_source_prepared_sha256': '" + SOURCE_PIN + "',\n        'previous_failure_receipt': 'tmp/current-s1r-tiny-20261018/production-v0/failure.json',\n        'previous_failure_receipt_sha256': '3dcf11c64bebda5b543a52edc43041664d314ddc9855a8330240843ccf875747',\n        'local_nanoda_threads': 4,\n        'locked_official_Comparator_default_nanoda_is_serial': True,\n        'official_runtime_equivalence_claimed': False,")
    outputs = {'run_production.py': runner, 'windows_generate.py': helper, 'freeze_static.py': freezer}
    for n, text in outputs.items():
        ast.parse(text, filename=n)
        assert not (HERE / n).exists()
    for n, text in outputs.items():
        with (HERE / n).open('x', encoding='utf-8', newline='\n') as f:
            f.write(text)
    diff = ''.join(''.join(difflib.unified_diff((OLD / n).read_text(encoding='utf-8').splitlines(keepends=True),
        t.splitlines(keepends=True), fromfile='production-v0/' + n, tofile='production-v1/' + n))
        for n, t in outputs.items())
    with (HERE / 'v0-to-v1.diff').open('x', encoding='utf-8', newline='\n') as f:
        f.write(diff)
    with (HERE / 'version-delta.json').open('x', encoding='utf-8', newline='\n') as f:
        json.dump({'schema': 'tiny-deduplicated-cold-v1-static-adaptation',
            'old_prepared_sha256': sha(oldmanifest.read_bytes()), 'flatten_prepared_sha256': FLATTEN_PIN,
            'production_source_prepared_sha256': SOURCE_PIN,
            'new_exclusive_linux_directory': '/var/tmp/rh-zero-20261015/tiny-production-v1',
            'new_exclusive_mirror_directory': 'tmp/current-s1r-tiny-20261018/production-v1',
            'total_budget_seconds': 3200, 'automatic_retries': 0, 'num_threads_unchanged': 4,
            'permitted_axioms_and_complete_replay_unchanged': True,
            'new_fresh_exact_record_receipt_required_in_root_gate': True,
            'generator_executions': 0, 'Lean_export_Comparator_nanoda_runs': 0,
            'old_inputs_modified': False, 'official_runtime_equivalence_claimed': False}, f, indent=2); f.write('\n')
    print(json.dumps({'runner_statically_adapted': True, 'verification_executions': 0}))

if __name__ == '__main__':
    main()
