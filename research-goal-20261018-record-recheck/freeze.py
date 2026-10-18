"""Hash-only seal of fresh public metadata recheck, with technical failure retained."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
def rec(p):
 b=p.read_bytes();return {'path':p.relative_to(ROOT).as_posix(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
j=json.loads((HERE/'receipt.json').read_text(encoding='utf-8'))
assert rec(HERE/'recheck.py')['sha256']==j['script_sha256']
assert j['site_equals_repository_current'] and j['current_equals_local_baseline']
assert j['public_source_matches_local_snapshot']
files=[rec(HERE/n) for n in ['recheck.py','receipt.json','attempt1-failure.json','NOTE.zh.md','freeze.py']]
deps=[rec(ROOT/p) for p in ['research-goal-20261018-record-source-audit/source-audit-files.json',
 'research-goal-20261018-record-source-audit/snapshot/Solution.lean']]
obj={'scope':'Fresh public website/GitHub metadata and local source identity recheck, not kernel replay.',
 'files':files,'dependencies':deps,'checked_through_UTC':j['finished_UTC'],
 'technical_metadata_attempts':2,'successful_metadata_attempts':1,
 'higher_public_accepted_record_observed':False,'same_record_and_source_as_local_baseline':True,
 'large_source_redownloaded':False,'Lean_invocations':0,'LP_calls':0,'leaf_decoding_runs':0}
p=HERE/'files.json'
with p.open('x',encoding='utf-8',newline='\n') as f:json.dump(obj,f,ensure_ascii=False,indent=2);f.write('\n')
print(json.dumps({'manifest':p.relative_to(ROOT).as_posix(),'sha256':rec(p)['sha256'],
 'owned_files':len(files),'owned_bytes':sum(r['bytes'] for r in files)},ensure_ascii=False))
