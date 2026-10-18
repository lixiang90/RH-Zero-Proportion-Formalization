"""AST/hash only; never imports or runs the accepted materials builder."""
import ast
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def row(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)}

def main():
    assert not (HERE/'prepared-files.json').exists()
    assert not (ROOT/'submission/single-exception-overlap-accepted-20261019').exists()
    for name in ['build_accepted.py','freeze_static.py']:
        ast.parse((HERE/name).read_text(encoding='utf-8'),filename=name)
    official=ROOT/'research-goal-20261019-record-accepted-independent-1753/files.json'
    assert sha(official)=='71f1ba7aaf1ba70b0edf1526103bdf0f1684a4b9c06fbcde3ac5e8a3edb0ebf2'
    paths=[official]
    for r in json.loads(official.read_text(encoding='utf-8'))['files']:
        p=ROOT/r['path'];assert row(p)==r;paths.append(p)
    paths += [ROOT/'research-goal-20261018-tiny-flatten-preparation-v3/draft/Solution.lean',
      ROOT/'research-goal-20261019-tiny-kernel-evidence/checks.json']
    old=ROOT/'submission/single-exception-overlap-20261019'
    paths += [p for p in old.iterdir() if p.is_file()]
    before=[row(p) for p in paths]
    assert before==[row(p) for p in paths]
    with (HERE/'prepared-files.json').open('x',encoding='utf-8',newline='\n') as f:
        json.dump({'schema':'accepted-v3-materials-builder-static-preparation-v1',
          'files':[row(HERE/n) for n in ['build_accepted.py','SPEC.zh.md','freeze_static.py']],
          'dependencies':before,'builder_executions':0,'Lean_network_math_or_collector_runs':0,
          'destination_not_created':True,'old_materials_unchanged':True,
          'official_acceptance_evidence_received_but_materials_not_yet_generated':True},f,
          ensure_ascii=False,indent=2);f.write('\n')
    print(json.dumps({'prepared_sha256':sha(HERE/'prepared-files.json'),'builder_executions':0}))

if __name__=='__main__':main()
