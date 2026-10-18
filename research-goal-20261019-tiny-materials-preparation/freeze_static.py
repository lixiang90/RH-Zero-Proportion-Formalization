"""AST/hash-only material-collector preparation. Never imports the collector."""
import ast
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent

def sha(p):
    h = hashlib.sha256()
    with Path(p).open('rb') as f:
        for block in iter(lambda: f.read(1048576), b''):
            h.update(block)
    return h.hexdigest()

def row(p):
    p = Path(p)
    return {'path': p.relative_to(ROOT).as_posix(), 'bytes': p.stat().st_size, 'sha256': sha(p)}

def main():
    assert sys.argv[1:] == ['--freeze-static-only']
    assert not (HERE / 'prepared-files.json').exists()
    for name in ['collect_once.py', 'freeze_static.py']:
        ast.parse((HERE / name).read_text(encoding='utf-8'), filename=name)
    prod = ROOT / 'research-goal-20261018-tiny-production-preparation/prepared-files.json'
    flat = ROOT / 'research-goal-20261018-tiny-flatten-preparation-v3/prepared-files.json'
    assert sha(prod) == '8de6adf94411254d8aef96e625faa1dc869069848049e99eab31e38a06e957c1'
    assert sha(flat) == '8d866f77503210091280574f6a14fcead5461f07c156f383f1b67f78ee52ab32'
    deps = [
        prod, flat,
        ROOT / 'research-goal-20261018-tiny-production-preparation/run_production.py',
        ROOT / 'research-goal-20261018-tiny-production-preparation/configuration.json',
        ROOT / 'research-goal-20261018-tiny-flatten-preparation-v3/generate_draft.py',
        ROOT / 'research-goal-20261018-tiny-flatten-preparation-v3/candidate-parameters.json',
        ROOT / 'research-goal-20261018-tiny-flatten-preparation-v3/official-wrapper.lean.txt',
        ROOT / 'research-goal-20261016/gates/tiny-production-cold-v0-20261018.json',
        ROOT / 'submission/tiny-overlap-20261018/README.zh.md',
        ROOT / 'submission/tiny-overlap-20261018/submission-fields.draft.json',
    ]
    before = [row(p) for p in deps]
    owned = [row(p) for p in sorted(HERE.iterdir()) if p.is_file()]
    assert before == [row(p) for p in deps]
    result = {'schema': 'tiny-success-materials-collector-static-prepared-v1',
        'prepared_at_utc': datetime.now(timezone.utc).isoformat(),
        'scope': 'Static script preparation only; production is not observed or represented as complete',
        'files': owned, 'dependencies': before, 'AST_parse_passed': True,
        'collector_executions': 0, 'production_results_read_as_complete': False,
        'Lean_export_Comparator_nanoda_network_Git_runs': 0,
        'old_drafts_and_bound_inputs_changed': False, 'root_terminal_confirmation_required': True,
        'submitted': False, 'official_website_acceptance': False}
    with (HERE / 'prepared-files.json').open('x', encoding='utf-8', newline='\n') as f:
        json.dump(result, f, ensure_ascii=False, indent=2); f.write('\n')
    print(json.dumps({'prepared_sha256': sha(HERE / 'prepared-files.json'),
        'files': len(owned), 'dependencies': len(before), 'collector_executions': 0}))

if __name__ == '__main__':
    main()
