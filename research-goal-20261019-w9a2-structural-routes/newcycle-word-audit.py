"""One fixed six-window word; exact integer difference constraints only.

No periodic value equalities, LP, kernel calls, Lean, other cycle or graph scan.
Cell graph vertex v = 2 * zero-based numeric leaf rank + bool(reversed).
"""
from __future__ import annotations
import hashlib
import json
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
HERE = Path(__file__).resolve().parent
GEOMETRY = ROOT / "research-goal-20261019-w9a2-certificate-analysis/geometry-audit.json"
LEAVES = ROOT / "research-goal-20261019-w9a2-certificate-analysis/numeric-leaves-sorted.jsonl.gz"
SOURCE = ROOT / "research-goal-20261019-w9a2-record/official/proof/Solution.lean"
SOURCE_SHA = "241068ee5abab772ea1aba7533ec33b9140df7dc1728aeb4c61bfb648fe195c7"
LEAVES_SHA = "f2acd938535e00216de3585c85e7c06d9ac213698088a2dc7374005a335a94ae"
WORD = [10, 14, 11, 19, 18, 10]
ORIGINAL_SCALE = 32768
INTEGER_MULTIPLIER = 5
SCALE = ORIGINAL_SCALE * INTEGER_MULTIPLIER
SEP = Fraction(17, 20)
NPOINTS = 14
ALL_SPANS = [(i, i + 1) for i in range(8)] + [
    (i, j) for i in range(9) for j in range(i + 2, 9)
]
LOOK = {span: k for k, span in enumerate(ALL_SPANS)}
sha = lambda b: hashlib.sha256(b).hexdigest()

source_raw = SOURCE.read_bytes()
assert sha(source_raw) == SOURCE_SHA
assert sha(LEAVES.read_bytes()) == LEAVES_SHA
geo_raw = GEOMETRY.read_bytes()
geo = json.loads(geo_raw)
assert geo["source_sha256"] == SOURCE_SHA
assert geo["numeric_leaves_input_sha256"] == LEAVES_SHA
g24 = geo["graphs"]["24"]
assert g24["vertex_encoding"] == "2*zero_based_leaf_rank + bool(reversed)"
assert g24["cycle"] == WORD
assert WORD[0] == WORD[-1]
retained = {tuple(edge) for edge in g24["retained_edges"]}
assert all(edge in retained for edge in zip(WORD, WORD[1:]))
leaves = geo["first24"]
assert len(leaves) == 24

rows = []
windows = []
for shift, vertex in enumerate(WORD):
    rank, reverse_bit = divmod(vertex, 2)
    leaf = leaves[rank]
    state = leaf["state"]
    assert len(state) == 73 and state[-1] == 0
    assert state[:16:2] == leaf["lo"] and state[1:16:2] == leaf["hi"]
    windows.append({"shift": shift, "vertex": vertex, "rank": rank,
                    "reversed": bool(reverse_bit), "root": leaf["root"],
                    "cursor": leaf["pos"], "margin": leaf["margin"]})
    for i, j in ALL_SPANS:
        original_i, original_j = (8 - j, 8 - i) if reverse_bit else (i, j)
        k = LOOK[original_i, original_j]
        lower, upper = state[2*k : 2*k+2]
        assert lower <= upper
        common = {"kind": "original_cell_span", "window": shift,
                  "vertex": vertex, "rank": rank, "reversed": bool(reverse_bit),
                  "root": leaf["root"], "cursor": leaf["pos"],
                  "local_span": [i, j], "original_span": [original_i, original_j],
                  "original_lower": lower, "original_upper": upper,
                  "original_denominator": ORIGINAL_SCALE}
        # row represents position[to] - position[from] <= integer_rhs.
        rows.append({"id": len(rows), **common, "bound": "upper",
                     "from": shift + i, "to": shift + j,
                     "integer_rhs": INTEGER_MULTIPLIER * upper})
        rows.append({"id": len(rows), **common, "bound": "lower",
                     "from": shift + j, "to": shift + i,
                     "integer_rhs": -INTEGER_MULTIPLIER * lower})

sep_scaled = SEP * SCALE
assert sep_scaled.denominator == 1
for i in range(NPOINTS - 1):
    rows.append({"id": len(rows), "kind": "separation_17_over_20",
                 "from": i + 1, "to": i, "integer_rhs": -sep_scaled.numerator})
assert len(rows) == 6 * 36 * 2 + 13 == 445
assert not any(row["from"] == row["to"] for row in rows)

# An implicit zero-weight super-source reaches all vertices.
distance = [0] * NPOINTS
parent_row = [None] * NPOINTS
last = None
passes = 0
for _ in range(NPOINTS):
    last = None
    for row in rows:
        candidate = distance[row["from"]] + row["integer_rhs"]
        if candidate < distance[row["to"]]:
            distance[row["to"]] = candidate
            parent_row[row["to"]] = row["id"]
            last = row["to"]
    passes += 1
    if last is None:
        break

common_result = {
    "scope": "Exactly one six-window free word; 14 points/13 gaps; all original span bounds plus separation 17/20. No periodic value equalities, other cycles, LP, kernel or Lean.",
    "source_sha256": SOURCE_SHA,
    "geometry_input_sha256": sha(geo_raw),
    "numeric_leaves_input_sha256": LEAVES_SHA,
    "vertex_encoding": g24["vertex_encoding"],
    "word": WORD,
    "windows": windows,
    "position_denominator": SCALE,
    "original_span_denominator": ORIGINAL_SCALE,
    "row_count": len(rows),
    "point_count": NPOINTS,
    "separation_rows": 13,
    "periodic_value_equalities": 0,
    "algorithm": "integer Bellman-Ford with implicit zero super-source",
    "passes": passes,
    "all_original_rows": rows,
}
if last is None:
    witness = [v - distance[0] for v in distance]
    assert witness[0] == 0
    for row in rows:
        assert witness[row["to"]] - witness[row["from"]] <= row["integer_rhs"]
    gaps = [witness[i+1] - witness[i] for i in range(NPOINTS - 1)]
    assert all(v >= sep_scaled for v in gaps)
    result = {**common_result,
              "status": "FEASIBLE_all_445_integer_rows_verified",
              "integer_positions": witness,
              "integer_gaps": gaps,
              "rational_positions": [str(Fraction(v, SCALE)) for v in witness],
              "rational_gaps": [str(Fraction(v, SCALE)) for v in gaps],
              "conclusion_scope": "This one free path is geometrically realizable. This is not an actual low-energy or periodic counterexample, and does not show the word can repeat indefinitely."}
else:
    vertex = last
    for _ in range(NPOINTS):
        assert parent_row[vertex] is not None
        vertex = rows[parent_row[vertex]]["from"]
    start_vertex = vertex
    cycle_rows = []
    while True:
        row_id = parent_row[vertex]
        assert row_id is not None
        cycle_rows.append(row_id)
        vertex = rows[row_id]["from"]
        if vertex == start_vertex:
            break
        assert len(cycle_rows) <= NPOINTS
    cycle_rows.reverse()
    certificate = [rows[row_id] for row_id in cycle_rows]
    assert all(a["to"] == b["from"] for a, b in zip(certificate, certificate[1:] + certificate[:1]))
    total = sum(row["integer_rhs"] for row in certificate)
    assert total < 0
    balance = [0] * NPOINTS
    for row in certificate:
        balance[row["to"]] += 1
        balance[row["from"]] -= 1
    assert balance == [0] * NPOINTS
    result = {**common_result,
              "status": "EMPTY_exact_original_row_negative_cycle",
              "negative_cycle_row_ids": cycle_rows,
              "negative_cycle_rows": certificate,
              "all_row_multipliers": "1 on listed cycle rows, 0 elsewhere",
              "balance_14_positions": balance,
              "sum_integer_rhs": total,
              "sum_real_rhs": str(Fraction(total, SCALE)),
              "conclusion_scope": "This free word cannot occur, so a higher-memory graph may forbid this word. Individual original edges cannot be deleted on this evidence alone."}
out = HERE / "newcycle-word-audit.json"
out.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"status": result["status"], "word": WORD,
                  "row_count": len(rows), "passes": passes,
                  "negative_cycle_row_ids": result.get("negative_cycle_row_ids"),
                  "sum_integer_rhs": result.get("sum_integer_rhs"),
                  "integer_positions": result.get("integer_positions"),
                  "receipt_sha256": sha(out.read_bytes())}, ensure_ascii=False))
