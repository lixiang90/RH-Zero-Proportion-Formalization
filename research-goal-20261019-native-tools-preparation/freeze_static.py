"""AST/TOML/hash-only native-tool preparation. Never imports/runs setup code."""
import ast
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import tomllib

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent

def row(name):
    p = ROOT / name
    h = hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda: f.read(1048576), b''):
            h.update(b)
    return {'path': name, 'bytes': p.stat().st_size, 'sha256': h.hexdigest()}

def main():
    assert not (HERE/'prepared-files.json').exists()
    for p in HERE.glob('*.py'):
        ast.parse(p.read_text(encoding='utf-8'), filename=p.name)
    cfg = tomllib.loads((HERE/'lakefile.toml.in').read_text(encoding='utf-8'))
    assert 'require' not in cfg and cfg['defaultTargets'] == ['lean4export','coreaudit']
    assert [e['supportInterpreter'] for e in cfg['lean_exe']] == [True, False]
    deps = [
        'research-goal-20261019-native-verifier-source-audit/files.json',
        'research-goal-20261019-native-verifier-source-audit/install-verifier-tools.sh',
        'research-goal-20261019-native-verifier-source-audit/run-comparator-sandbox.sh',
        'tmp/setup-20261015/runtime.json', 'tmp/setup-20261015/sources.json',
        'tmp/setup-20261015/lean4export.tar.gz', 'tmp/setup-20261015/Comparator.tar.gz',
        'tmp/setup-20261015/packages/lean4export/lakefile.toml',
        'tmp/setup-20261015/packages/lean4export/lake-manifest.json',
        'tmp/setup-20261015/packages/lean4export/Main.lean',
        'tmp/setup-20261015/packages/lean4export/Export.lean',
        'tmp/setup-20261015/packages/lean4export/Export/Parse.lean',
        'tmp/setup-20261015/packages/Comparator/lakefile.toml',
        'tmp/setup-20261015/packages/Comparator/lake-manifest.json',
        'tmp/setup-20261015/packages/Comparator/Main.lean',
        'tmp/setup-20261015/packages/Comparator/Comparator.lean',
        'tmp/setup-20261015/packages/Comparator/Comparator/Axioms.lean',
        'tmp/setup-20261015/packages/Comparator/Comparator/Compare.lean',
        'tmp/setup-20261015/packages/Comparator/Comparator/Util.lean',
        'tools/ComparatorCoreAudit.lean',
        'research-goal-20261018-tiny-production-preparation/prepared-files.json',
        'research-goal-20261018-tiny-production-preparation/run_production.py',
        'research-goal-20261019-nanoda-thread-static-review/files.json',
        'scripts/setup_record_20261015/prepare_linux_runtime.py',
        'scripts/setup_record_20261015/fetch_compiler.py',
    ]
    before = [row(p) for p in deps]
    assert before[0]['sha256'] == 'b9c7d0821afe53a5e38990ce46cf8bc53212f024443b4960bf232cbc514b5067'
    assert before[1]['sha256'] == '80abf99bac5109a209cef864c3077cab068005c75a00884bdee6ee4bb850561c'
    archive = row('tmp/setup-20261015/lean-4.33.0-rc2-linux.tar.zst')
    assert archive['sha256'] == '48010c7d6264dc992574e9b0e09ece1f9c648e8f5106066b2cdb6834a6a60a6c'
    assert before == [row(p) for p in deps]
    result = {'schema': 'native-trusted-tool-setup-static-prepared-v1',
        'prepared_at_utc': datetime.now(timezone.utc).isoformat(),
        'scope': 'Only static plan/script and read-only SDK metadata; no native build or candidate check',
        'files': [row(p.relative_to(ROOT).as_posix()) for p in sorted(HERE.iterdir()) if p.is_file()],
        'dependencies': before, 'external_read_dependencies_not_for_Git': [archive],
        'AST_and_TOML_parse_passed': True,
        'SDK_metadata_only_processes': [{'session_id':66513,'exit_code':0}, {'session_id':33815,'exit_code':0}],
        'tool_native_builds': 0, 'candidate_compilations': 0, 'exports': 0,
        'kernel_replays': 0, 'network_requests_by_this_preparation': 0,
        'all_inputs_unchanged': True, 'root_new_gate_required': True,
        'old_prepared_packages_modified': False, 'official_website_acceptance': False}
    p = HERE/'prepared-files.json'
    with p.open('x', encoding='utf-8', newline='\n') as f:
        json.dump(result, f, ensure_ascii=False, indent=2); f.write('\n')
    print(json.dumps({'prepared_sha256': row(p.relative_to(ROOT).as_posix())['sha256'],
                     'files':len(result['files']), 'dependencies':len(before), 'native_builds':0}))

if __name__ == '__main__':
    main()
