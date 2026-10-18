"""AST/hash-only static freezing; never imports or executes collect_once."""
import ast
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent

def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as handle:
        for block in iter(lambda: handle.read(1048576), b''):
            h.update(block)
    return h.hexdigest()

def row(path):
    return {'path': path.relative_to(ROOT).as_posix(), 'bytes': path.stat().st_size, 'sha256': sha(path)}

def main():
    assert sys.argv[1:] == ['--freeze-static-only']
    assert not (HERE / 'prepared-files.json').exists()
    for name in ['collect_once.py', 'freeze_static.py']:
        ast.parse((HERE / name).read_text(encoding='utf-8'), filename=name)
    expected = {
        'research-goal-20261016/gates/tiny-native-production-cold-v2-20261019.json':
            '3cd2bc378f815b53d5c31233d89662c090b04bcdabc489c115f3a4d66924631a',
        'research-goal-20261019-tiny-production-preparation-v2/prepared-files.json':
            'f2ab9d281bf39769da08280f40d9369e9b9ffc2f51c57acccbb116999daa9d74',
        'research-goal-20261019-tiny-flatten-preparation-v4/prepared-files.json':
            '2b77159157e500b0177c3c2294860830a495248ce3e3b216a813524032509d72',
        'research-goal-20261019-tiny-dedup-source-preparation/prepared-files.json':
            '98a9dfe125cfdb4febc24fb8666bb73228e4f27fcbac9fe66506c1c7720f99d6',
        'research-goal-20261019-native-tools-preparation-v2/prepared-files.json':
            'b7fd183217077da32688e8c23b399ac9f25713e79b107a13466b57fcf33caac2',
        'research-goal-20261018-tiny-flatten-preparation-v3/draft/Solution.lean':
            '024902a7ef01ccba2a6c71e54682a31712417e5d3c0b4ead5f6f80ad25fd1a81'}
    for name, digest in expected.items():
        assert sha(ROOT / name) == digest, name
    deps = [ROOT / name for name in expected]
    deps += [ROOT / name for name in [
        'research-goal-20261019-tiny-production-preparation-v2/run_production.py',
        'research-goal-20261019-tiny-production-preparation-v2/configuration.json',
        'research-goal-20261019-tiny-production-preparation-v2/native_binding_method.py.txt',
        'research-goal-20261019-tiny-flatten-preparation-v4/generate_draft.py',
        'research-goal-20261019-tiny-flatten-preparation-v4/candidate-parameters.json',
        'research-goal-20261019-tiny-flatten-preparation-v4/official-wrapper.lean.txt',
        'research-goal-20261019-tiny-materials-preparation/prepared-files.json',
        'research-goal-20261019-tiny-materials-preparation/collect_once.py']]
    # Immutable mathematical/status snapshots and older user-facing materials.
    for dirname in ['submission/single-exception-overlap-20261019', 'submission/tiny-overlap-20261018']:
        deps += [path for path in sorted((ROOT / dirname).rglob('*')) if path.is_file()]
    assert len(deps) == len(set(deps))
    before = [row(path) for path in deps]
    owned = [row(path) for path in sorted(HERE.iterdir()) if path.is_file()]
    assert before == [row(path) for path in deps]
    result = {'schema': 'native-v4-post-PASS-materials-collector-static-prepared-v1',
        'prepared_at_utc': datetime.now(timezone.utc).isoformat(),
        'scope': 'Static preparation only; active production results are not read or represented as complete',
        'files': owned, 'dependencies': before, 'AST_parse_passed': True,
        'production_session_id': 84529, 'production_job': '/var/tmp/rh-zero-20261015/tiny-production-v2',
        'production_gate_sha256': expected['research-goal-20261016/gates/tiny-native-production-cold-v2-20261019.json'],
        'collector_executions': 0, 'live_production_artifact_reads': 0,
        'Lean_export_Comparator_nanoda_generator_network_Git_runs': 0,
        'old_drafts_and_bound_inputs_changed': False, 'root_terminal_confirmation_required': True,
        'source_sha256_obtained_only_from_future_actual_metadata': True,
        'destination': 'submission/single-exception-overlap-native-v4-20261019',
        'submitted': False, 'official_website_acceptance': False}
    with (HERE / 'prepared-files.json').open('x', encoding='utf-8', newline='\n') as handle:
        json.dump(result, handle, ensure_ascii=False, indent=2); handle.write('\n')
    print(json.dumps({'prepared_sha256': sha(HERE / 'prepared-files.json'),
        'owned_files': len(owned), 'dependencies': len(before), 'collector_executions': 0}))

if __name__ == '__main__':
    main()
