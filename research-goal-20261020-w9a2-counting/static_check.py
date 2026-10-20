"""Exact arithmetic and source-identity checks only; no compiler or solver."""
from pathlib import Path
from fractions import Fraction as Q
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
sha = lambda b: hashlib.sha256(b).hexdigest()
source_path = ROOT / 'research-goal-20261019-w9a2-record/official/proof/Solution.lean'
source_raw = source_path.read_bytes()
assert sha(source_raw) == '241068ee5abab772ea1aba7533ec33b9140df7dc1728aeb4c61bfb648fe195c7'
source = source_raw.decode()
assert re.search(r'def cN : ℕ := 893029029923108825\b', source)
assert re.search(r'def SA : ℕ := 100000000000000000000\b', source)
assert '6721237468782417141365717707344332375586 / 10000000000000000000000000000000000000000' in source
assert 'theorem W9_B : W9.B = (454741897490 : ℝ) / 100000000000000' in source

graph_path = ROOT / 'research-goal-20261019-w9a2-weighted-graph/weighted-graph.json'
graph_raw = graph_path.read_bytes()
assert sha(graph_raw) == '7748d5a35b33931dfc66a83d089ca6ad7f9f707fdbb59af75c0a3c2a7cfa3414'
graph = json.loads(graph_raw)
SA = 10**20
H = Q(6721237468782417141365717707344332375586, 10**40)
B = Q(454741897490, 10**14)
base = Q(893029029923108825, SA)
mu = Q(622387738726, 5)
C = Q(2504722000690, 5*SA)
increment = mu/SA
c = base+increment
ratio = (H-B)/(1-c)
baseline = (H-B)/(1-base)
assert 0 < c <= Q(1,64)
assert 0 <= C <= c
assert ratio > baseline
assert str(c) == graph['conditional_candidate']['weighted_average_floor']
assert str(ratio) == graph['conditional_candidate']['ratio_if_all_actual_localization_and_counting_are_formalized']
assert baseline == Q(3337881639516708570682858853672166187793,
                    4955348548503844558750000000000000000000)
assert max(graph['finite_potential_certificate']['potential_numerators']) == 2504722000690
assert min(graph['finite_potential_certificate']['potential_numerators']) == 0

old = (ROOT / 'StructuralS1RTiny20261018/Production/Counting.lean').read_text(encoding='utf-8')
new = (HERE / 'Counting.lean').read_text(encoding='utf-8')
common_old = old[old.index('section Payment'):old.index('/-- No new ten-point ledger')]
common_new = new[new.index('section Payment'):new.index('/-- W9A2\'s current H')]
assert common_old == common_new
assert '6721290091768038344368273523390880473594' not in new
for name in ['Counting.lean', 'Final.lean']:
    raw = (HERE/name).read_bytes()
    assert raw == (ROOT/'StructuralW9A220261020'/name).read_bytes()
    text = raw.decode()
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b', text)
    assert 'import StructuralS1RTiny20261018' not in text

report = {
    'status': 'PASS_STATIC_ARITHMETIC_AND_SOURCE_IDENTITY_NOT_LEAN',
    'scope': 'Checks exact current-source H/B/c0, frozen weighted arithmetic, copy identity of the accepted generic bridge, and absence of admitted new declarations. It does not prove or compile actual localization, graph transitions, or counting.',
    'base': str(base), 'increment': str(increment), 'c': str(c),
    'potential_boundary': str(C), 'H': str(H), 'B': str(B),
    'candidate': str(ratio), 'frozen_baseline': str(baseline),
    'gain': str(ratio-baseline),
    'potential_boundary_below_c': True,
    'current_close_pair_payment_suffices': True,
    'unchanged_generic_bridge_sha256': sha(common_old.encode()),
    'source_sha256': sha(source_raw), 'weighted_graph_sha256': sha(graph_raw),
    'compiler_runs': 0, 'solver_runs': 0, 'independent_kernel_runs': 0,
    'actual_unconditional_result_verified': False,
    'files': [{
        'path': str((HERE/name).relative_to(ROOT)).replace('\\','/'),
        'bytes': len((HERE/name).read_bytes()),
        'sha256': sha((HERE/name).read_bytes()),
    } for name in ['Counting.lean','Final.lean']],
}
(HERE/'static-check.json').write_text(json.dumps(report, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')
print(json.dumps(report, ensure_ascii=False))
