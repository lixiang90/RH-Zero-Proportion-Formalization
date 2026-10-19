"""One fixed weighted graph: old 48 bad vertices/37 edges plus good G.

Only exact finite integer/rational arithmetic. No new cells/edges between bad
vertices, threshold search, LP, kernel, Lean or optimization family.
"""
from __future__ import annotations
import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
HERE = Path(__file__).resolve().parent
INPUT = ROOT / "research-goal-20261019-w9a2-certificate-analysis/geometry-audit.json"
SOURCE_SHA = "241068ee5abab772ea1aba7533ec33b9140df7dc1728aeb4c61bfb648fe195c7"
SLOPE = 335544320000000000
SA = 10**20
GOOD_COST = 10**12
G = 48
NV = 49
sha = lambda raw: hashlib.sha256(raw).hexdigest()

raw = INPUT.read_bytes()
data = json.loads(raw)
assert data["source_sha256"] == SOURCE_SHA
graph = data["graphs"]["24"]
assert graph["n"] == 24
assert graph["vertex_encoding"] == "2*zero_based_leaf_rank + bool(reversed)"
bad_edges = [tuple(edge) for edge in graph["retained_edges"]]
assert len(bad_edges) == len(set(bad_edges)) == 37
assert all(0 <= u < G and 0 <= v < G for u, v in bad_edges)
leaves = data["first24"]
assert len(leaves) == 24
assert [row["margin"] for row in leaves] == sorted(row["margin"] for row in leaves)
assert all(0 <= row["margin"] < SLOPE * GOOD_COST for row in leaves)
quantile = next(row for row in data["quantiles"] if row["floor_increment"] == "1e-8")
assert quantile["exception_count"] == 24
assert Q(quantile["integer_debit"]) == SLOPE * GOOD_COST

cost = [leaves[v // 2]["margin"] // SLOPE for v in range(G)] + [GOOD_COST]
edges = bad_edges + [(v, G) for v in range(G)] + [(G, v) for v in range(G)] + [(G, G)]
assert len(edges) == len(set(edges)) == 134
assert all((v, G) in edges and (G, v) in edges for v in range(G))

# Karp, one fixed source G. All vertices are reachable in at most one edge.
dp = [[None] * NV for _ in range(NV + 1)]
dp[0][G] = 0
for length in range(1, NV + 1):
    for u, v in edges:
        prefix = dp[length - 1][u]
        if prefix is None:
            continue
        candidate = prefix + cost[u]
        if dp[length][v] is None or candidate < dp[length][v]:
            dp[length][v] = candidate
karp_rows = []
for v in range(NV):
    assert dp[NV][v] is not None
    ratios = [(Q(dp[NV][v] - dp[k][v], NV - k), k)
              for k in range(NV) if dp[k][v] is not None]
    value, maximizing_k = max(ratios)
    karp_rows.append((value, v, maximizing_k))
mu, karp_v, karp_k = min(karp_rows)
num, den = mu.numerator, mu.denominator

# Build a finite certificate: shortest potentials in reduced integer weights.
# wi >= mu + p(v) - p(u), for each source-weighted u -> v edge.
potential_num = [0] * NV
passes = 0
for _ in range(NV):
    changed = False
    for u, v in edges:
        candidate = potential_num[u] + den * cost[u] - num
        if candidate < potential_num[v]:
            potential_num[v] = candidate
            changed = True
    passes += 1
    if not changed:
        break
assert not changed, "Karp candidate left a negative reduced cycle"
offset = potential_num[G]
potential_num = [p - offset for p in potential_num]

edge_certificate = []
tight_adj = [[] for _ in range(NV)]
for u, v in edges:
    slack_num = den * cost[u] - num - potential_num[v] + potential_num[u]
    assert slack_num >= 0
    edge_certificate.append({"from": u, "to": v,
                             "source_cost": cost[u],
                             "scaled_slack": slack_num})
    if slack_num == 0:
        tight_adj[u].append(v)

# Extract one attaining cycle from the tight subgraph, no second optimization.
colour = [0] * NV
path = []
cycle = None
def visit(v):
    global cycle
    colour[v] = 1
    path.append(v)
    for w in tight_adj[v]:
        if cycle is not None:
            break
        if colour[w] == 0:
            visit(w)
        elif colour[w] == 1:
            cycle = path[path.index(w):] + [w]
    path.pop()
    colour[v] = 2
for v in range(NV):
    if cycle is not None:
        break
    if colour[v] == 0:
        visit(v)
assert cycle is not None and cycle[0] == cycle[-1]
assert all((u, v) in edges for u, v in zip(cycle, cycle[1:]))
cycle_cost = sum(cost[u] for u in cycle[:-1])
assert Q(cycle_cost, len(cycle) - 1) == mu
assert all(den * cost[u] - num - potential_num[v] + potential_num[u] == 0
           for u, v in zip(cycle, cycle[1:]))

# Source-independent certificate consumer: these exact inequalities and the
# attaining cycle prove optimal mean; Karp is needed only to discover them.
assert len(cost) == len(potential_num) == NV
for row in edge_certificate:
    u, v = row["from"], row["to"]
    assert Q(cost[u]) >= mu + Q(potential_num[v] - potential_num[u], den)
assert Q(sum(cost[u] for u in cycle[:-1]), len(cycle) - 1) == mu

c0 = Q(893029029923108825, SA)
floor_increment = mu / SA
candidate_floor = c0 + floor_increment
old_increment = Q(data["proposed_gate"]["proposed_average_floor_exact"]) - c0
assert old_increment == Q(121390593524, 5 * SA)
kappa = Q(3337881639516708570682858853672166187793,
          4955348548503844558750000000000000000000)
candidate_kappa = kappa * (1 - c0) / (1 - candidate_floor)
gain = candidate_kappa - kappa
B = Q(454741897490, 10**14)
bmax = Q(79272929552, 10**14)
outside_compensation = Q(17, 20) * (B - bmax)
assert outside_compensation >= Q(GOOD_COST, SA)

result = {
    "status": "PASS_exact_fixed_graph_optimum_certificate",
    "scope": "One frozen 49-vertex/134-edge weighted graph, original 48-vertex/37-edge bad graph plus G. No new geometry, LP, kernel, Lean or unconditional record.",
    "input_path": INPUT.relative_to(ROOT).as_posix(),
    "input_sha256": sha(raw),
    "source_sha256": SOURCE_SHA,
    "numeric_leaves_input_sha256": data["numeric_leaves_input_sha256"],
    "vertex_encoding": "0..47 = 2*zero_based_leaf_rank + reversed; 48 = G",
    "source_cost_rule": "bad wi=floor(original_margin(rank)/335544320000000000); G=1000000000000; edge cost is source cost",
    "vertex_count": NV,
    "bad_edge_count": len(bad_edges),
    "edge_count": len(edges),
    "good_threshold_CN_increment": GOOD_COST,
    "good_threshold_floor_increment": str(Q(GOOD_COST, SA)),
    "source_quantile_count_below_good": quantile["exception_count"],
    "mu_exact_CN_units": str(mu),
    "mu_float_CN_units": float(mu),
    "mu_discovery": {"method": "Karp exact rational, one source G", "vertices": NV,
                     "minimizing_v": karp_v, "maximizing_k": karp_k},
    "finite_potential_certificate": {
        "inequality": "cost[u] >= mu + p[v] - p[u] for each edge u->v",
        "common_denominator": den,
        "potential_numerators": potential_num,
        "G_potential": "0",
        "oscillation_CN_units": str(Q(max(potential_num) - min(potential_num), den)),
        "all_134_edges": edge_certificate,
        "verification": "Every scaled_slack is nonnegative; exact Fraction substitution also passed",
        "reduced_weight_Bellman_Ford_passes": passes,
    },
    "attaining_cycle": {"vertices": cycle, "edge_count": len(cycle) - 1,
                        "source_cost_sum": cycle_cost, "mean_exact": str(mu),
                        "all_edges_tight": True},
    "vertices": [{"vertex": v, "cost": cost[v],
                  **({"rank": v // 2, "reversed": bool(v % 2),
                      "root": leaves[v // 2]["root"],
                      "cursor": leaves[v // 2]["pos"],
                      "original_margin": leaves[v // 2]["margin"]} if v < G else {"kind": "good"})}
                 for v in range(NV)],
    "conditional_candidate": {
        "baseline_floor": str(c0),
        "weighted_average_floor_increment": str(floor_increment),
        "weighted_average_floor_increment_float": float(floor_increment),
        "weighted_average_floor": str(candidate_floor),
        "old_first7_DAG_average_floor_increment": str(old_increment),
        "old_first7_DAG_average_floor_increment_float": float(old_increment),
        "weighted_minus_first7_increment": str(floor_increment - old_increment),
        "weighted_to_first7_factor": str(floor_increment / old_increment),
        "ratio_if_all_actual_localization_and_counting_are_formalized": str(candidate_kappa),
        "percentage_float": float(100 * candidate_kappa),
        "proportion_gain": str(gain),
        "percentage_point_gain_float": float(100 * gain),
    },
    "outside_separated_static_compensation": {
        "assumptions": "Original one-gap WZ or tail bound already pays c0; all seven other gaps >=17/20; remaining kernel terms nonnegative. Small gap <=1/2 is impossible in separated remainder.",
        "B": str(B), "max_b": str(bmax),
        "extra_pressure_at_least": str(outside_compensation),
        "extra_pressure_float": float(outside_compensation),
        "extra_pressure_minus_good_threshold_increment": str(outside_compensation - Q(GOOD_COST, SA)),
        "scope": "Static arithmetic implication of original one-gap source contract; no fresh WZ evaluation or upgraded full-cover Lean proof.",
    },
    "open_gate": "Full actual source-walk quantitative localization, exterior guards/reflection, graph transition exclusion and telescoping/counting must be proved in Lean before claiming an unconditional zero proportion. A graph cycle is an outer-model attaining cycle, not an actual periodic kernel configuration.",
}
out = HERE / "weighted-graph.json"
assert not out.exists(), "Do not overwrite a frozen result"
out.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"status": result["status"], "mu": str(mu), "cycle": cycle,
                  "floor_increment": str(floor_increment),
                  "floor_increment_float": float(floor_increment),
                  "old_increment_float": float(old_increment),
                  "factor_float": float(floor_increment / old_increment),
                  "conditional_percentage_float": float(100 * candidate_kappa),
                  "conditional_percentage_point_gain_float": float(100 * gain),
                  "receipt_sha256": sha(out.read_bytes())}, ensure_ascii=False))
