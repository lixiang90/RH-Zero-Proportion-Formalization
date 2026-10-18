"""Hash/AST freeze only; does not execute or import the audit."""
import ast
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def row(p):
    b = p.read_bytes()
    return {'path': p.relative_to(ROOT).as_posix(), 'bytes': len(b),
            'sha256': hashlib.sha256(b).hexdigest()}


def main():
    dest = HERE / 'audit-files.json'
    assert not dest.exists()
    names = ['audit_once.py', 'REVIEW.zh.md', 'execution.json', 'independent-review.json', 'freeze_review.py']
    for name in ['audit_once.py', 'freeze_review.py']:
        ast.parse((HERE/name).read_text(encoding='utf-8'), filename=name)
    report = json.loads((HERE/'independent-review.json').read_bytes())
    assert report['passed'] is True
    result = {'schema': 'independent-accepted-v3-final-materials-review-files-v1',
              'files': [row(HERE/name) for name in names],
              'read_dependencies': report['read_dependencies'],
              'passed': True, 'audit_executions': 1,
              'network_compiler_kernel_collector_runs': 0,
              'final_cloud_audit_owner': '/root'}
    with dest.open('x', encoding='utf-8', newline='\n') as f:
        json.dump(result, f, ensure_ascii=False, indent=2)
        f.write('\n')
    print(json.dumps({'audit_files_sha256': row(dest)['sha256'], 'owned_files': len(names)}))


if __name__ == '__main__':
    main()
