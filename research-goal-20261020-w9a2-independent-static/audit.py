"""Read-only independent review of frozen W9A2 literals and scalar interfaces.

Only Python's standard library is used. This file never invokes a compiler,
solver, graph optimizer, kernel evaluator, or producer script. Every geometric
check below substitutes the already selected witness; it searches no new span.
"""
from pathlib import Path
from fractions import Fraction
import ast
import gzip
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
inputs = [
    'StructuralW9A220261020/Core.lean',
    'StructuralW9A220261020/Graph.lean',
    'StructuralW9A220261020/Localization.lean',
    'StructuralW9A220261020/Counting.lean',
    'StructuralW9A220261020/Final.lean',
    'research-goal-20261019-w9a2-record/official/proof/Solution.lean',
    'research-goal-20261019-w9a2-record/transport/research-goal-20261019-w9a2-certificate-analysis--geometry-audit.json.gzip.part000',
    'research-goal-20261019-w9a2-weighted-graph/weighted-graph.json',
    'research-goal-20261020-w9a2-transitions/extracted-witnesses.json',
    'research-goal-20261020-w9a2-runtime/trusted/ChallengeDeps.lean',
    '.lake/packages/Zeta23/Zeta23/Statement.lean',
    'StructuralS1RTiny20261018/Production/Counting.lean',
    'StructuralS1RTiny20261018/Production/Final.lean',
    'research-goal-20261016/macro-reviews/007-20261019.zh.md',
]


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


raw = {name: (ROOT / name).read_bytes() for name in inputs}
before = {name: {'bytes': len(value), 'sha256': digest(value)}
          for name, value in raw.items()}
core, graph, loc, counting, final = [raw[inputs[k]].decode() for k in range(5)]
original = raw[inputs[5]].decode()
assert digest(raw[inputs[5]]) == '241068ee5abab772ea1aba7533ec33b9140df7dc1728aeb4c61bfb648fe195c7'
geometry_raw = gzip.decompress(raw[inputs[6]])
assert digest(geometry_raw) == '7d860bb023594ecc4dc84308435acbdcdeb5da7d8d81991220045955575b9c67'
geometry = json.loads(geometry_raw)
weighted = json.loads(raw[inputs[7]])


def literal(text, name):
    match = re.search(r'^def ' + re.escape(name) + r'\s*:[^\n]*:=\s*(\[.*?\])\s*(?=\ndef |\Z)',
                      text, re.M | re.S)
    assert match, name
    return ast.literal_eval(match.group(1))


edge_list = literal(graph, 'badEdges')
edges = set(edge_list)
spans = literal(graph, 'sharedSpans')
rows = literal(graph, 'witnessRows')
potentials = literal(graph, 'potentialValues')
costs = literal(graph, 'originalCosts')
qstate_section = core.split('def qState :', 1)[1].split('def qCost :', 1)[0]
states = {int(k): [int(x) for x in value.split(',')]
          for k, value in re.findall(r'\| (\d+) => ⟨([^⟩]+)⟩', qstate_section)}
qcost_section = core.split('def qCost :', 1)[1].split('def qCell', 1)[0]
qcost = {int(k): int(value) for k, value in re.findall(r'\| (\d+) => (\d+)', qcost_section)}
assert sorted(states) == sorted(qcost) == list(range(24))
assert all(states[k] == geometry['first24'][k]['state'] and len(states[k]) == 73
           and states[k][-1] == 0 for k in range(24))
assert all(qcost[k] == geometry['first24'][k]['margin'] // 335544320000000000
           for k in range(24))
assert costs == [qcost[k // 2] for k in range(48)] + [10**12]
assert potentials == weighted['finite_potential_certificate']['potential_numerators']
assert len(edge_list) == len(edges) == 37
assert edges == set(map(tuple, geometry['graphs']['24']['retained_edges']))
assert len(rows) == 48 and all(len(row) == 48 for row in rows)
assert spans == [(i, j) for i in range(1, 8) for j in range(i + 1, 9)]

# Use the ordered pair list, rather than Graph.prIndex's arithmetic expression,
# to obtain bounds; then compare the prepared indexing formula separately.
pair_order = [(i, j) for i in range(8) for j in range(i + 2, 9)]
span_order = [(i, i + 1) for i in range(8)] + pair_order
for k, (i, j) in enumerate(pair_order):
    assert i * (15 - i) // 2 + j - i - 2 == k


def endpoint(v, i, j):
    if v % 2:
        i, j = 8 - j, 8 - i
    k = span_order.index((i, j))
    return states[v // 2][2 * k: 2 * k + 2]


# Symbolic coefficients of the physical span validate all 36 reversal cases,
# and all 28 shared-span identities used by the real-variable proofs.
for i, j in span_order:
    lhs = sorted(7 - r for r in range(i, j))
    rhs = list(range(8 - j, 8 - i))
    assert lhs == rhs
for i, j in spans:
    assert list(range(i, j)) == [1 + r for r in range(i - 1, j - 1)]

differences = []
for u in range(48):
    for v in range(48):
        selected = rows[u][v]
        if (u, v) in edges:
            assert selected == 56
            continue
        assert 0 <= selected < 56
        i, j = spans[selected // 2]
        lo_u, hi_u = endpoint(u, i, j)
        lo_v, hi_v = endpoint(v, i - 1, j - 1)
        delta = (lo_v - hi_u) if selected % 2 == 0 else (lo_u - hi_v)
        assert delta > 0
        differences.append(delta)
assert len(differences) == 2267
all_edges = edges | {(u, 48) for u in range(49)} | {(48, v) for v in range(49)}
assert len(all_edges) == 134
assert all_edges == {(x['from'], x['to']) for x in
                     weighted['finite_potential_certificate']['all_134_edges']}
slacks = [5 * costs[u] - 622387738726 - potentials[v] + potentials[u]
          for u, v in all_edges]
assert min(slacks) == 0
assert min(potentials) == potentials[48] == 0
assert max(potentials) == 2504722000690

Q = Fraction
SA = 10**20
base = Q(893029029923108825, SA)
increment = Q(622387738726, 5 * SA)
boundary = Q(max(potentials) - min(potentials), 5 * SA)
c = base + increment
H = Q(6721237468782417141365717707344332375586, 10**40)
B = Q(454741897490, 10**14)
baseline = Q(3337881639516708570682858853672166187793,
             4955348548503844558750000000000000000000)
candidate = Q(3337881639516708570682858853672166187793,
              4955348542279967171490000000000000000000)
assert 0 <= boundary <= c <= Q(1, 64)
assert c == Q(4465145772003282851, 5 * SA)
assert (H - B) / (1 - base) == baseline < candidate == (H - B) / (1 - c)
assert str(c) == weighted['conditional_candidate']['weighted_average_floor']
assert str(candidate) == weighted['conditional_candidate']['ratio_if_all_actual_localization_and_counting_are_formalized']
assert 'theorem W9_B : W9.B = (454741897490 : ℝ) / 100000000000000' in original
assert '6721237468782417141365717707344332375586 / 10000000000000000000000000000000000000000' in original

# The reused payment/matching part imports the current Core, with no old kernel
# module/data. Compare the entire preserved segment, not theorem names alone.
old_counting = raw[inputs[11]].decode()
old_segment = old_counting.split('section Payment', 1)[1].split('/-- No new ten-point ledger', 1)[0]
new_segment = counting.split('section Payment', 1)[1].split('/-- W9A2\'s current H', 1)[0]
assert old_segment == new_segment
segment_sha = digest(('section Payment' + old_segment).replace('\r\n', '\n').encode())
assert segment_sha == '421c93f7c9c2fc679547017a1a19043855725efa026722fe073aada433af83e0'

# Root definitions and Zeta23 definitions are independent declarations whose
# recursive bodies agree, rather than aliases. This is why Final's exact h can
# cross the root/library counting interface by definitional equality.
trusted = raw[inputs[9]].decode()
statement = raw[inputs[10]].decode()
root_definitions = {}
for name in ['IsNontrivialZero', 'zeroMult', 'zerosIn', 'Ncount', 'N0star']:
    pattern = r'^def ' + name + r'[^\n]*$'
    a = re.search(pattern, trusted, re.M).group(0).strip()
    b = re.search(pattern, statement, re.M).group(0).strip()
    assert a == b
    root_definitions[name] = a
for text in [graph, loc, counting, final]:
    stripped = re.sub(r'/-.*?-/', '', text, flags=re.S)
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b', stripped)
    assert 'import StructuralS1RTiny20261018' not in stripped

after = {name: {'bytes': (ROOT / name).stat().st_size,
                'sha256': digest((ROOT / name).read_bytes())} for name in inputs}
assert after == before, 'Input changed during the independent audit; retain this failure.'
result = {
    'status': 'PASS_INDEPENDENT_STATIC_ARITHMETIC_AND_TEXT_SCOPE_ONLY',
    'not_a_Lean_or_kernel_receipt': True,
    'inputs_before_and_after_identical': True,
    'inputs': before,
    'literal_checks': {
        'states': 24, 'oriented_bad_states': 48, 'all_states': 49,
        'state_fields_each': 73, 'original_state_and_margin_identity': True,
        'reversal_symbolic_span_identities': 36,
        'shared_symbolic_span_identities': 28,
        'strict_closed_interval_exclusions': len(differences),
        'minimum_integer_strict_difference': min(differences),
        'retained_bad_edges': len(edges), 'all_edges': len(all_edges),
        'potential_inequalities': len(slacks), 'minimum_scaled_potential_slack': min(slacks),
        'potential_minimum': min(potentials), 'potential_maximum': max(potentials),
    },
    'exact_constants': {name: str(value) for name, value in [
        ('SA', Q(SA)), ('base', base), ('increment', increment), ('c', c),
        ('boundary', boundary), ('H', H), ('B', B), ('baseline', baseline),
        ('candidate', candidate), ('strict_gain', candidate - baseline)]},
    'unmodified_generic_payment_segment_sha256': segment_sha,
    'matching_charge': 'C occurs only in z=none separated remainder; no C in pair blocks',
    'effective_actual_defect_parameter': 10,
    'root_and_Zeta23_counting_definition_lines_equal': root_definitions,
    'definite_math_or_elaboration_issue_found_by_static_review': False,
    'unexecuted_obligations': [
        'ordinary Lean elaboration and new quantitative finite checks of all original 48 roots',
        'ordinary Lean checking of actual localization, all transition proofs, finite sums and final roots',
        'transitive axiom roots restricted to the three allowed standard axioms',
        'whole final flattened source, trusted fresh CandidateSpec and Comparator contract',
        'independent Lean/nanoda kernels and production total time limit',
        'latest-record comparison, GitHub byte equality and submission materials',
    ],
    'compiler_runs': 0, 'solver_or_optimizer_runs': 0,
    'new_kernel_evaluations': 0, 'new_geometry_searches': 0,
    'main_counter_modified': False,
}
(HERE / 'audit.json').write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print(json.dumps({key: result[key] for key in ['status', 'literal_checks', 'exact_constants']}, ensure_ascii=False))
