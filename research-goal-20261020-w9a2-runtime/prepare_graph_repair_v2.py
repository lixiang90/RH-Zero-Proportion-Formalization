"""Explicit root-reviewed tolerance for an already-normal Fin case."""
from pathlib import Path
import hashlib
import json
import difflib

ROOT=Path(__file__).resolve().parents[1]
oldpkg=ROOT/'research-goal-20261020-w9a2-graph-repair-v1'
out=ROOT/'research-goal-20261020-w9a2-graph-repair-v2'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(oldpkg/'files.json')=='a7a9b9090f51919d3f07276a758e333fed135f98a7b854dbe84f755bc4f0de19'
old=oldpkg/'StructuralW9A220261020/Graph.lean'
before=b'<;> simp only [Fin.reduceFinMk] <;> ring'
after=b'<;> (try simp only [Fin.reduceFinMk]) <;> ring'
raw=old.read_bytes()
assert raw.count(before)==1
new=raw.replace(before,after)
assert new.replace(after,before)==raw and len(new)==len(raw)+6
job=ROOT/'tmp/w9a2-20261020/candidate-ordinary-v2'
receipt=json.loads((job/'StructuralW9A220261020_Graph.receipt.json').read_text())
assert receipt['exit_code']==1 and receipt['source_sha256']==sha(old)
assert not json.loads((job/'terminal.json').read_text())['passed']
log=(job/'StructuralW9A220261020_Graph.log').read_text()
assert log.count('error:')==1 and '`simp` made no progress' in log
out.mkdir(exist_ok=False)
dest=out/'StructuralW9A220261020/Graph.lean'
dest.parent.mkdir()
dest.write_bytes(new)
(out/'Graph-v1-to-v2.diff').write_bytes(''.join(difflib.unified_diff(
    raw.decode().splitlines(keepends=True),new.decode().splitlines(keepends=True),
    fromfile='graph-repair-v1/Graph.lean',tofile='graph-repair-v2/Graph.lean')).encode())
evidence=out/'failed-v1-evidence'
evidence.mkdir()
for name in ['started.json','terminal.json']+[f'StructuralW9A220261020_Graph.{s}' for s in ['command.json','child.json','log','receipt.json']]:
    (evidence/name).write_bytes((job/name).read_bytes())
(out/'prepare_graph_repair_v2.py').write_bytes(Path(__file__).read_bytes())
note={'status':'PREPARED_PROOF_ONLY_REPAIR_NOT_COMPILED',
      'root_observed_previous_parent_session':42867,'actual_parent_exit_code':1,
      'previous_graph_elapsed_seconds':receipt['elapsed_seconds'],
      'old_source_sha256':sha(old),'new_source_sha256':sha(dest),
      'old_bytes':len(raw),'new_bytes':len(new),
      'change':'Parenthesized try around the existing explicit Fin.reduceFinMk simp only; original ring always follows.',
      'same_theorem_statement':True,'all_bytes_outside_one_proof_line_identical':True,
      'exact_forward_and_reverse_projection':True,'numerical_changes':0,
      'new_assumptions_or_axioms':0,'compiler_invocations':0,
      'round_counter_changed':False,'ordinary_passed':False}
(out/'repair.json').write_bytes((json.dumps(note,indent=2)+'\n').encode())
rows=[]
for p in sorted(out.rglob('*')):
    if p.is_file(): rows.append({'path':p.relative_to(out).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)})
(out/'files.json').write_bytes((json.dumps({'scope':'Single same-theorem tactic control repair, no mathematical input changes','files':rows},indent=2)+'\n').encode())
print(json.dumps({'manifest_sha256':sha(out/'files.json'),'source_sha256':sha(dest),'source_bytes':len(new)}))
