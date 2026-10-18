"""Metadata/AST-only freezer; does not import or execute the production runner."""
import ast
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
FLATTEN = ROOT / 'research-goal-20261019-tiny-flatten-preparation-v4'

def sha(p):
    h = hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda: f.read(1048576), b''):
            h.update(b)
    return h.hexdigest()

def load(p):
    return json.loads(Path(p).read_text(encoding='utf-8'))

def row(p):
    p = Path(p)
    return {'path': p.relative_to(ROOT).as_posix(), 'bytes': p.stat().st_size, 'sha256': sha(p)}

def write(name, obj):
    with (HERE / name).open('x', encoding='utf-8', newline='\n') as f:
        json.dump(obj, f, ensure_ascii=False, indent=2); f.write('\n')

def main():
    assert len(sys.argv) == 2 and sys.argv[1] == '--freeze-static-only'
    assert sha(ROOT / 'research-goal-20261018-tiny-production-plan/files.json') == '6125796a0989935ad723f6961f93891f07210be34fc5b4109c5eecc36dd08cfa'
    assert sha(FLATTEN / 'prepared-files.json') == '2b77159157e500b0177c3c2294860830a495248ce3e3b216a813524032509d72'
    assert not (FLATTEN / 'draft').exists()
    for name in ['run_production.py', 'windows_generate.py', 'freeze_static.py']:
        ast.parse((HERE / name).read_text(encoding='utf-8'), filename=name)
    depnames = {
        'research-goal-20261018-tiny-production-preparation/prepared-files.json',
        'research-goal-20261018-tiny-production-preparation/run_production.py',
        'research-goal-20261019-tiny-dedup-source-preparation/prepared-files.json',
        'research-goal-20261019-tiny-dedup-source-preparation/prepare_sources.py',
        'research-goal-20261019-tiny-dedup-static-review/report-files.json',
        'research-goal-20261019-nanoda-thread-static-review/files.json',
        'research-goal-20261019-nanoda-thread-static-review/REVIEW.zh.md',
        'tmp/current-s1r-tiny-20261018/production-v0/failure.json',
        'research-goal-20261018-tiny-production-plan/files.json',
        'research-goal-20261018-tiny-production-plan/PRODUCTION-PLAN.zh.md',
        'research-goal-20261018-tiny-production-plan/COMMANDS.txt',
        'research-goal-20261018-tiny-production-plan/tool-provenance.json',
        'research-goal-20261019-tiny-flatten-preparation-v4/prepared-files.json',
        'research-goal-20261018-tiny-runtime-preparation/phase4-prepared.json',
        'tmp/current-s1r-tiny-20261018/phase4-v0/Final.receipt.json',
        'tmp/current-s1r-tiny-20261018/phase4-v0/terminal.json',
        'tmp/setup-20261015/runtime.json', 'tmp/setup-20261015/sources.json',
        'tmp/setup-20261015/dependencies.json', 'lake-manifest.json',
        'scripts/verify_record_20261015.py', 'scripts/verify_single_solution.py',
        'tools/ComparatorCoreAudit.lean',
        'verification/gram-defect-20261015/setup/nanoda-build.json',
        'verification/gram-defect-20261015/lean/single/verification.json',
        'research-goal-20261018-record-fresh-independent-1152/files.json',
        'research-goal-20261018-record-fresh-independent-1152/main-records.body',
        'research-goal-20261018-record-fresh-independent-1152/main-records.receipt.json',
        'tmp/goal-20261016/macro006-precompile-fresh-record.json',
    }
    flatten = load(FLATTEN / 'prepared-files.json')
    for r in flatten['files'] + flatten['read_dependencies']:
        assert sha(ROOT / r['path']) == r['sha256'], r['path']
        depnames.add(r['path'])
    runtime = load(ROOT / 'tmp/setup-20261015/runtime.json')
    for entry in runtime['source_archives']:
        p = 'tmp/setup-20261015/' + entry['name'] + '.tar.gz'
        assert sha(ROOT / p) == entry['archive_sha256']
        depnames.add(p)
    dependencies = load(ROOT / 'tmp/setup-20261015/dependencies.json')
    assert dependencies['passed'] and dependencies['runtime_manifest_sha256'] == sha(ROOT / 'tmp/setup-20261015/runtime.json')
    cachepins = []
    for r in dependencies['compiled_modules']:
        assert r['exit_code'] == 0 and r['source_unchanged']
        cachepins += [{'path': r['source'], 'sha256': r['source_sha256']},
                      {'path': r['olean'], 'sha256': r['olean_sha256']}]
    params = load(FLATTEN / 'candidate-parameters.json')
    nano = load(ROOT / 'verification/gram-defect-20261015/setup/nanoda-build.json')
    freshpath = 'tmp/goal-20261016/macro006-precompile-fresh-record.json'
    fresh = load(ROOT / freshpath)
    assert fresh['current']['exactRational'] == params['expected_current_record']
    config = {
        'schema': 'tiny-production-configuration-v2',
        'flatten_directory': FLATTEN.relative_to(ROOT).as_posix(),
        'production_source_prepared_sha256': '98a9dfe125cfdb4febc24fb8666bb73228e4f27fcbac9fe66506c1c7720f99d6',
        'previous_failure_receipt': 'tmp/current-s1r-tiny-20261018/production-v0/failure.json',
        'previous_failure_receipt_sha256': '3dcf11c64bebda5b543a52edc43041664d314ddc9855a8330240843ccf875747',
        'local_nanoda_threads': 4,
        'locked_official_Comparator_default_nanoda_is_serial': True,
        'official_runtime_equivalence_claimed': False,
        'flatten_prepared_sha256': sha(FLATTEN / 'prepared-files.json'),
        'latest_record_receipt': freshpath, 'latest_record_receipt_sha256': sha(ROOT / freshpath),
        'current_record_ledger': 'research-goal-20261018-record-fresh-independent-1152/main-records.body',
        'score': params['score'], 'expected_current_record': params['expected_current_record'],
        'candidate_template': 'research-20261016-w10-cert/website-snapshot/challenge/templates/CandidateSpec.lean.tmpl',
        'challenge_template': 'research-20261016-w10-cert/website-snapshot/challenge/templates/Challenge.Candidate.lean',
        'lean': runtime['lean'], 'lean_sha256': runtime['lean_sha256'], 'lean_version': runtime['lean_version'],
        'nanoda': nano['binary'], 'nanoda_sha256': nano['binary_sha256'],
        'Windows_Python_Linux_path': '/mnt/c/Python314/python.exe',
        'Windows_Python_sha256': sha(Path('C:/Python314/python.exe')),
        'Windows_Python_DLL_Linux_path': '/mnt/c/Python314/python314.dll',
        'Windows_Python_DLL_sha256': sha(Path('C:/Python314/python314.dll')),
        'Windows_helper_path': str(HERE / 'windows_generate.py'),
        'external_dependency_cache_pins': cachepins,
        'cache_basis': 'Runtime-named Mathlib cache plus completed source-bound Zeta23 dependency receipt; both proof replayers still required',
        'user_oleans_reused': False, 'official_website_acceptance': False,
    }
    write('configuration.json', config)
    old = load(ROOT / 'verification/gram-defect-20261015/lean/single/verification.json')
    summary = {'scope': 'Historical different candidate only; not a tiny performance result',
        'ordinary_seconds': sum(r['elapsed_seconds'] for r in old['compiled_modules']),
        'tool_seconds': sum(r['elapsed_seconds'] for r in old['tool_compiled_modules']),
        'exports': {k: {'elapsed_seconds': r['elapsed_seconds'], 'bytes': r['export_bytes']} for k, r in old['exports'].items()},
        'Comparator_default_kernel_seconds': old['comparator_default_kernel']['elapsed_seconds'],
        'nanoda_seconds': old['nanoda']['elapsed_seconds'],
        'uniform_total_timer_proven_for_old_receipt': False,
        'tiny_timing_inferred': False}
    summary['sum_of_logged_child_seconds'] = summary['ordinary_seconds'] + summary['tool_seconds'] + sum(r['elapsed_seconds'] for r in old['exports'].values()) + summary['Comparator_default_kernel_seconds'] + summary['nanoda_seconds']
    write('prior-recipe-timings.json', summary)
    before = [row(ROOT / n) for n in sorted(depnames)]
    write('static-checks.json', {'prepared_at_utc': datetime.now(timezone.utc).isoformat(),
        'AST_parse_passed': True, 'flatten_prepared_sha256': config['flatten_prepared_sha256'],
        'predicted_solution_bytes': load(FLATTEN / 'preparation.json')['predicted_solution_bytes'],
        'generator_executions': 0, 'Lean_runs': 0, 'export_runs': 0,
        'Comparator_runs': 0, 'nanoda_runs': 0, 'network_requests': 0,
        'production_runs': 0, 'upload_ready': False, 'new_gate_required': True})
    assert before == [row(ROOT / n) for n in sorted(depnames)]
    owned = [row(p) for p in sorted(HERE.iterdir()) if p.is_file()]
    write('prepared-files.json', {'schema': 'tiny-cold-production-prepared-v2',
        'scope': 'Static executable preparation only; not an execution gate or verification result',
        'files': owned, 'dependencies': before, 'fresh_generation_required': True,
        'all_bound_dependencies_unchanged': True, 'production_executions': 0,
        'generator_executions': 0, 'total_budget_seconds': 3200,
        'official_website_acceptance': False})
    print(json.dumps({'prepared_sha256': sha(HERE / 'prepared-files.json'),
        'flatten_prepared_sha256': config['flatten_prepared_sha256'],
        'files': len(owned), 'dependencies': len(before), 'executions': 0}))

if __name__ == '__main__':
    main()
