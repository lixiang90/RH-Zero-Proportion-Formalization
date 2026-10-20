"""Independent literal substitution and interface audit; never invokes Lean.

This deliberately does not import prepare.py or reconstruct any DBM/graph.
Every excluded pair is checked only at its already selected literal span.
"""
from pathlib import Path
import ast
import gzip
import hashlib
import json
import re

ROOT=Path(__file__).resolve().parent.parent
HERE=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
graph_path=ROOT/'StructuralW9A220261020/Graph.lean'
core_path=ROOT/'StructuralW9A220261020/Core.lean'
weighted_path=ROOT/'research-goal-20261019-w9a2-weighted-graph/weighted-graph.json'
part_path=ROOT/('research-goal-20261019-w9a2-record/transport/'
  'research-goal-20261019-w9a2-certificate-analysis--geometry-audit.json.gzip.part000')
paths=[graph_path,core_path,weighted_path,part_path,HERE/'lean/Graph.lean']
before={str(p.relative_to(ROOT)):sha(p) for p in paths}
text=graph_path.read_text(encoding='utf-8')
assert graph_path.read_bytes()==(HERE/'lean/Graph.lean').read_bytes()
assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',re.sub(r'/-[\s\S]*?-/', '', text))
def literal(name,typ):
    return ast.literal_eval(text.split(f'def {name} : {typ} := ',1)[1].split('\ndef ',1)[0].strip())
edges=literal('badEdges','List (ℕ × ℕ)')
spans=literal('sharedSpans','List (ℕ × ℕ)')
rows=literal('witnessRows','List (List ℕ)')
pots=literal('potentialValues','List ℤ')
# originalCosts is last literal, immediately followed by the generic function.
costs=literal('originalCosts','List ℕ')
geometry=json.loads(gzip.decompress(part_path.read_bytes()))
weighted=json.loads(weighted_path.read_bytes())
assert hashlib.sha256(gzip.decompress(part_path.read_bytes())).hexdigest()=='7d860bb023594ecc4dc84308435acbdcdeb5da7d8d81991220045955575b9c67'
src=core_path.read_text(encoding='utf-8')
states={int(k):list(map(int,re.findall(r'\d+',values))) for k,values in
  re.findall(r'\| (\d+) => ⟨([^⟩]+)⟩',src.split('def qState',1)[1].split('def qCost',1)[0])}
qc={int(k):int(v) for k,v in re.findall(r'\| (\d+) => (\d+)',src.split('def qCost',1)[1].split('def qCell',1)[0])}
assert len(states)==len(qc)==24
for k in range(24):
    assert states[k]==geometry['first24'][k]['state']
    assert qc[k]==geometry['first24'][k]['margin']//335544320000000000
assert costs==[qc[v//2] for v in range(48)]+[10**12]
assert pots==weighted['finite_potential_certificate']['potential_numerators']
assert spans==[(i,j) for i in range(1,8) for j in range(i+1,9)]
assert len(rows)==48 and all(len(r)==48 for r in rows)
assert set(edges)==set(map(tuple,geometry['graphs']['24']['retained_edges']))
assert len(edges)==len(set(edges))==37
def interval(v,i,j):
    if v%2:i,j=8-j,8-i
    assert 0<=i<j<=8
    if j==i+1:k=i
    else:k=8+i*(15-i)//2+(j-i-2)
    assert 0<=k<36
    return states[v//2][2*k:2*k+2]
count=0
differences=[]
for u in range(48):
    for v in range(48):
        w=rows[u][v]
        if (u,v) in edges:
            assert w==56
            continue
        assert 0<=w<56
        i,j=spans[w//2]
        a,b=interval(u,i,j),interval(v,i-1,j-1)
        difference=b[0]-a[1] if w%2==0 else a[0]-b[1]
        assert difference>0
        differences.append(difference)
        count+=1
all_edges=set(edges)|{(u,48) for u in range(49)}|{(48,v) for v in range(49)}
assert len(all_edges)==134 and count==2267
assert all(622387738726+pots[v]-pots[u]<=5*costs[u] for u,v in all_edges)
assert min(pots)==0 and max(pots)==2504722000690 and pots[48]==0
assert all(cost>=0 for cost in costs)
after={str(p.relative_to(ROOT)):sha(p) for p in paths}
assert before==after
out=dict(status='PASS_static_exact_literal_substitution_not_Lean',input_hashes=before,
  source_bytes=graph_path.stat().st_size,state_literals_equal_original_first24=True,
  qCost_literals_equal_original_margin_floor=True,strict_conflicts_checked=count,
  minimum_strict_difference=min(differences),bad_edges=37,all_edges=134,
  potential_inequalities_checked=134,potential_min=0,potential_max=2504722000690,
  actual_kernel_or_counting_theorem_checked=False,Lean_execution_count=0,
  scope='All fixed selected strict integer witnesses and fixed finite potential substituted independently against prepared Core qState/qCost and original packet. Generic actual real-variable Lean proofs remain uncompiled.')
(HERE/'static-audit.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:out[k] for k in ['status','source_bytes','strict_conflicts_checked','minimum_strict_difference','potential_inequalities_checked']},ensure_ascii=False))
