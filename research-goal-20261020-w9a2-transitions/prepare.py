"""Extract already-published finite witnesses. No geometry search or optimizer.

The first contradiction of each old row is selected without adding any new
span. The closed Lean check rechecks only those integer literal witnesses.
"""
from pathlib import Path
import gzip
import hashlib
import json

ROOT = Path(__file__).resolve().parent.parent
HERE = Path(__file__).resolve().parent
SHA = lambda b: hashlib.sha256(b).hexdigest()
SOURCE = ROOT / 'research-goal-20261019-w9a2-record/official/proof/Solution.lean'
PART = ROOT / ('research-goal-20261019-w9a2-record/transport/'
    'research-goal-20261019-w9a2-certificate-analysis--geometry-audit.json.gzip.part000')
WEIGHTED = ROOT / 'research-goal-20261019-w9a2-weighted-graph/weighted-graph.json'
raw = gzip.decompress(PART.read_bytes())
assert SHA(raw) == '7d860bb023594ecc4dc84308435acbdcdeb5da7d8d81991220045955575b9c67'
data = json.loads(raw)
weighted = json.loads(WEIGHTED.read_bytes())
assert SHA(SOURCE.read_bytes()) == data['source_sha256'] == weighted['source_sha256']
assert weighted['input_sha256'] == SHA(raw)
assert SHA(WEIGHTED.read_bytes()) == '7748d5a35b33931dfc66a83d089ca6ad7f9f707fdbb59af75c0a3c2a7cfa3414'
leaves = data['first24']
spans = [(i, j) for i in range(1, 8) for j in range(i+1, 9)]
pr = [(i, j) for i in range(9) for j in range(i+2, 9)]
span_order = [(i, i+1) for i in range(8)] + pr
assert len(spans) == 28

def bounds(v, i, j):
    if v % 2:
        i, j = 8-j, 8-i
    k = span_order.index((i, j))
    return leaves[v//2]['state'][2*k:2*k+2]

rows = [[56]*48 for _ in range(48)]
retained = set(map(tuple, data['graphs']['24']['retained_edges']))
exclusions = []
assert len(retained) == 37
for old in data['graphs']['24']['rows']:
    u = 2*old['prefix_rank'] + int(old['prefix_reversed'])
    v = 2*old['suffix_rank'] + int(old['suffix_reversed'])
    if old['DBM_feasible']:
        assert (u, v) in retained and not old['literal_contradictions']
        continue
    assert (u, v) not in retained
    c = old['literal_contradictions'][0]  # only extract existing witness
    i, j = c['shared_span']
    a, b = bounds(u, i, j), bounds(v, i-1, j-1)
    assert a == c['prefix'] and b == c['suffix']
    direction = 0 if a[1] < b[0] else 1
    assert (a[1] < b[0]) if direction == 0 else (b[1] < a[0])
    w = 2*spans.index((i, j)) + direction
    rows[u][v] = w
    exclusions.append(dict(source=u, target=v, witness=w, span=[i,j],
        prefix=a, suffix=b, strict_difference=(b[0]-a[1] if direction==0 else a[0]-b[1])))
assert len(exclusions) == 2267 and all(x['strict_difference'] > 0 for x in exclusions)
assert {(u,v) for u in range(48) for v in range(48) if rows[u][v] == 56} == retained
edges = [(e['from'], e['to']) for e in weighted['finite_potential_certificate']['all_134_edges']]
cost = [v['cost'] for v in weighted['vertices']]
pot = weighted['finite_potential_certificate']['potential_numerators']
assert len(edges) == 134 and len(set(edges)) == 134
assert set(edges) == retained | {(u,48) for u in range(49)} | {(48,v) for v in range(49)}
assert len(pot) == len(cost) == 49 and pot[48] == 0
assert all(5*cost[u] >= 622387738726 + pot[v]-pot[u] for u,v in edges)
assert min(pot) == 0 and max(pot) == 2504722000690

literal = '\n'.join([
    '-- Frozen literal packet: first published direct exclusion in each old row.',
    'def badEdges : List (ℕ × ℕ) := ' + repr(sorted(retained)),
    'def sharedSpans : List (ℕ × ℕ) := ' + repr(spans),
    'def witnessRows : List (List ℕ) := [\n' + ',\n'.join('  '+repr(r) for r in rows) + '\n]',
    'def potentialValues : List ℤ := ' + repr(pot),
    'def originalCosts : List ℕ := ' + repr(cost),
]) + '\n'
(HERE/'lean/Literals.txt').write_text(literal, encoding='utf-8')
detail = dict(scope='Extraction of existing first direct strict conflict per excluded row; exact replay of fixed published potential only. No new geometry search, Karp, LP, kernel, or Lean execution.',
    source_sha256=SHA(SOURCE.read_bytes()),geometry_sha256=SHA(raw),weighted_sha256=SHA(WEIGHTED.read_bytes()),
    bad_vertices=48,excluded_pairs=2267,retained_bad_edges=37,total_vertices=49,total_edges=134,
    shared_spans=spans,minimum_strict_difference=min(x['strict_difference'] for x in exclusions),
    witness_count=len(exclusions),closed_boundaries_preserved=True,orientation_encoding='2*rank+reverse',
    exclusions=exclusions)
(HERE/'extracted-witnesses.json').write_text(json.dumps(detail,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
template = (HERE/'lean/Graph.template.lean').read_text(encoding='utf-8')
assert template.count('-- @LITERALS@') == 1
graph = template.replace('-- @LITERALS@', literal.rstrip())
(HERE/'lean/Graph.lean').write_text(graph, encoding='utf-8')
(ROOT/'StructuralW9A220261020/Graph.lean').write_text(graph, encoding='utf-8')
print(json.dumps({k:detail[k] for k in ['bad_vertices','excluded_pairs','retained_bad_edges','total_vertices','total_edges','minimum_strict_difference']},ensure_ascii=False))
