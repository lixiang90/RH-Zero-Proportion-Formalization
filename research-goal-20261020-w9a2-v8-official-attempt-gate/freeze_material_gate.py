"""Freeze an honest attempt-material gate. No proof or website action."""
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parents[1]
here=Path(__file__).resolve().parent
def sha(b): return hashlib.sha256(b).hexdigest()
pins=[
 ('research-goal-20261016/macro-reviews/012-20261020.zh.md','fb7516e57e8fe56802d16b088178c29215d10161a10060a1e007e2b7a9274347'),
 ('research-goal-20261020-w9a2-submission-attempt-v8/files.json','1f608acb37baa3a5d03c01c1d504e19a4eb172877f850b63120fa8d283f8de21'),
 ('research-goal-20261020-w9a2-attempt-v8-generator-static-independent/files.json','3fd6537fbebcbc0d9bad762c57269a38ea63db8e5b9e938e51dcab86f3243efd')]
for name,expected in pins:
 p=root/name
 assert sha(p.read_bytes())==expected,name
 if p.name=='files.json':
  for row in json.loads(p.read_bytes())['files']:
   q=p.parent/row['path']
   b=q.read_bytes()
   assert len(b)==row['bytes'] and sha(b)==row['sha256'],str(q)
s=json.loads((root/'research-goal-20261016/direction-state.json').read_bytes())
assert s['last_review_number']==12 and s['main_rounds_since_review']==0
assert s['v8_RSS_resource_route']['passed'] is False
runner=root/'research-goal-20261020-w9a2-submission-attempt-v8/prepare_attempt_v8.py'
assert sha(runner.read_bytes())=='0011c4732accb90350cbbd18e0e296a85e045cc07c71de5153dfeb8b608b8b4e'
t=json.loads((runner.parent/'gate-template.json').read_bytes())
assert t['allow_attempt_material_generation'] is False and t['proposal_only'] is True
t.update({'allow_attempt_material_generation':True,'proposal_only':False,
 'generator_sha256':sha(runner.read_bytes()),'root_small_review_evidence':[{'path':n,'sha256':h} for n,h in pins],
 'website_click_authorized_by_this_material_gate':False})
out=here/'material-generation-gate.json'
assert not out.exists()
out.write_bytes((json.dumps(t,ensure_ascii=False,indent=2)+'\n').encode())
print(json.dumps({'gate_sha256':sha(out.read_bytes()),'generator_sha256':sha(runner.read_bytes()),'local_resource_pass':False}))
