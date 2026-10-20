"""One reviewed Graph Fin normalization repair, with exact passing Core reuse."""
from pathlib import Path
import hashlib
import json

ROOT=Path(__file__).resolve().parents[1]
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p): return json.loads(Path(p).read_text(encoding='utf-8'))
def pin(p): return {'path':p.relative_to(ROOT).as_posix(),'sha256':sha(p)}
oldgate=ROOT/'research-goal-20261016/gates/w9a2-ordinary-v1b-20261020.json'
assert sha(oldgate)=='92def59e80c77b461e3cc301bff748f65e44d53b4c031d745098b156882a3bc5'
gate=load(oldgate)
repair=ROOT/'research-goal-20261020-w9a2-graph-repair-v1'
manifest=repair/'files.json'
for row in load(manifest)['files']:
    p=repair/row['path']
    assert p.is_relative_to(repair) and sha(p)==row['sha256'], row['path']
old=ROOT/'StructuralW9A220261020/Graph.lean'
new=repair/'StructuralW9A220261020/Graph.lean'
before=b'  all_goals norm_num [gsum_range, natGaps, reverse8, Finset.sum_range_succ] <;> ring'
after=b'  all_goals norm_num [gsum_range, natGaps, reverse8, Finset.sum_range_succ] <;> simp only [Fin.reduceFinMk] <;> ring'
raw=old.read_bytes()
assert raw.count(before)==1 and raw.replace(before,after)==new.read_bytes()
job=ROOT/'tmp/w9a2-20261020/candidate-ordinary-v1'
assert load(job/'terminal.json')['passed'] is False
assert load(job/'StructuralW9A220261020_Graph.receipt.json')['exit_code']==1
core=load(job/'StructuralW9A220261020_Core.receipt.json')
assert core['exit_code']==0 and core['ordinary_compile_passed'] and core['source_unchanged']
coreolean=job/'lib/StructuralW9A220261020/Core.olean'
assert sha(coreolean)==core['olean_sha256']=='4e24ca2145281fb866d4b24f4db11da74aa87cb4728796fc856e5e4f0ab3fc07'
gate['reused_oleans'].append({**pin(coreolean),'module_path':'StructuralW9A220261020/Core.olean'})
gate['targets']=gate['targets'][1:]
gate['targets'][0].update(source=new.relative_to(ROOT).as_posix(),source_root=repair.relative_to(ROOT).as_posix())
gate['source_files'] += [pin(p) for p in [oldgate,manifest,new,
    job/'terminal.json',job/'StructuralW9A220261020_Core.receipt.json',
    job/'StructuralW9A220261020_Graph.receipt.json',job/'StructuralW9A220261020_Graph.log',Path(__file__)]]
gate.update(work_directory='tmp/w9a2-20261020/candidate-ordinary-v2',
    scope='One explicitly reviewed same-theorem Fin normalization in Graph reverse_span, then Graph/Localization/Counting/Final ordinary verification.',
    candidate_compiler_runs_before_this_gate=2,
    root_observed_previous_parent_session=93720,root_observed_previous_parent_exit_code=1,
    repair_changes='Only explicit simp only [Fin.reduceFinMk] added between existing norm_num and ring; no statement, numerical graph, state, cost, potential, witness or axiom changes.',
    unchanged_passing_development_Core_reused=True,
    known_limits=['Exact passing Prefix/Core and trusted ChallengeDeps reused only for development; no fullchain/cold/Comparator/Nano/website claim.',
                  'First error stops this new batch, no automatic retries.'])
for row in gate['source_files']+gate['reused_oleans']:
    assert sha(ROOT/row['path'])==row['sha256'],row['path']
out=ROOT/'research-goal-20261016/gates/w9a2-ordinary-v2-20261020.json'
with out.open('x',encoding='utf-8',newline='\n') as f:
    json.dump(gate,f,indent=2);f.write('\n')
print(json.dumps({'gate':out.relative_to(ROOT).as_posix(),'sha256':sha(out),
                  'Graph_sha256':sha(new),'source_and_reused_pins':len(gate['source_files'])+len(gate['reused_oleans'])}))
