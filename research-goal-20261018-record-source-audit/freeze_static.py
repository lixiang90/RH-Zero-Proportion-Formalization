"""Hash-only seal for the immutable source acquisition and static inventory."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
def rec(p):
 b=p.read_bytes();return {'path':p.relative_to(ROOT).as_posix(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
fetch=json.loads((HERE/'fetch-receipt.json').read_text())
inventory=json.loads((HERE/'static-inventory.json').read_text())
assert rec(HERE/'snapshot/Solution.lean')['sha256']==fetch['sha256']==inventory['source']['sha256']
assert rec(HERE/'fetch_source.py')['sha256']==fetch['fetcher_sha256']
assert rec(HERE/'extract_static.py')['sha256']==inventory['extractor_sha256']
files=[rec(HERE/n)for n in ['snapshot/Solution.lean','fetch_source.py','fetch-receipt.json',
                           'extract_static.py','static-inventory.json','NOTE.zh.txt','freeze_static.py']]
obj={'scope':'Fixed canonical public record source, intact bytes/licensing and static source API extraction only.',
     'upstream_commit':fetch['commit'],'source_url':fetch['url'],'files':files,
     'dependencies':[rec(ROOT/n) for n in ['GramDefect20261015/Core.lean',
                      'scripts/finite_margin_20261015.py',
                      'scripts/review_finite_margin_20261015.py']],
     'source_copyright_and_license_preserved':True,'source_bytes_normalized':False,
     'source_executed':False,'Lean_invocations':0,'optimizer_calls':0,
     'leaf_payload_decoded':False,'reported_leaf_count':13046,'leaf_count_locally_confirmed':False,
     'website_acceptance':'reported by parent/site, not locally replayed in this package',
     'local_ordinary_kernel_passed':False,'local_Comparator_passed':False,'local_Nanoda_passed':False,
     'new_derived_zero_proportion_proven':False}
p=HERE/'source-audit-files.json'
with p.open('x',encoding='utf-8',newline='\n')as f:json.dump(obj,f,ensure_ascii=False,indent=2);f.write('\n')
print(json.dumps({'manifest':p.relative_to(ROOT).as_posix(),'sha256':rec(p)['sha256'],
                  'owned_files':len(files),'owned_bytes':sum(x['bytes']for x in files)},ensure_ascii=False))
