"""Separate stdlib reconstruction of the fixed support and rational dual proof.

No producer import, SciPy, NumPy, optimizer, kernel function, tree or Lean.
This checks finite coefficient evidence, not the imported analytic theorems.
"""
from pathlib import Path
from fractions import Fraction
from itertools import combinations
import ast
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
PACKAGE = ROOT / "research-goal-20261017-ninepoint-decomposition"


def read(path):
    data = path.read_bytes()
    return data, {"path": path.relative_to(ROOT).as_posix(), "bytes": len(data),
                  "sha256": hashlib.sha256(data).hexdigest()}


def main():
    inputs = [ROOT / "GramDefect20261015/Core.lean",
              ROOT / "StructuralResearch20261016/W10RefinedCandidate.lean",
              ROOT / "StructuralW10Cert20261016/FinalConditional.lean",
              PACKAGE / "support-obstruction.json", PACKAGE / "coefficient-gluing.json",
              PACKAGE / "presolver-failure.json", PACKAGE / "coefficient_gluing.py",
              PACKAGE / "coefficient_gluing_presolver_failed.py"]
    loaded = {p: read(p) for p in inputs}
    old = loaded[inputs[0]][0].decode()
    lines = old.splitlines()
    start = lines.index("namespace AMW.Cert.PC9QB6M")
    def declaration(name):
        return next(line.split(":=", 1)[1].strip() for line in lines[start:]
                    if line.startswith("def " + name + " :"))
    old_terms = ast.literal_eval(declaration("TS"))
    old_bs = ast.literal_eval(declaration("BS"))
    scale = int(declaration("SA"))
    floor9 = Fraction(int(declaration("cN")), scale)
    total_mass = sum((Fraction(t[2], scale) for t in old_terms), Fraction())
    assert total_mass == Fraction(1599999987, 100000000)
    new = loaded[inputs[1]][0].decode().split("def aN :", 1)[1].split("def bN :", 1)[0]
    target_pairs = {(int(i), int(j)) for i, j, a in re.findall(r"\| (\d+), (\d+) => (\d+)", new) if int(a)}
    support = json.loads(loaded[inputs[3]][0])
    witness = json.loads(loaded[inputs[4]][0])
    for item in support["source_files"] + witness["source_files"]:
        raw = (ROOT / item["path"]).read_bytes()
        assert len(raw) == item["bytes"] and hashlib.sha256(raw).hexdigest() == item["sha256"]
    arrays = {}
    support_checks = []
    for vertices in combinations(range(10), 9):
        omit = next(i for i in range(10) if i not in vertices)
        actual_positive = sum((i, j) in target_pairs for i, j in combinations(vertices, 2))
        assert actual_positive <= 33 < len(old_terms)
        clashes = [(i, j) for i, j, weight, _ in old_terms
                   if weight and (vertices[i], vertices[j]) not in target_pairs]
        assert clashes
        column = [sum((Fraction(weight, scale) for i, j, weight, _ in old_terms
                       if vertices[j]-vertices[i] == distance), Fraction()) for distance in range(1, 10)]
        # Closed pressure formula is independently checked against counting
        # each old interval's incidence on the nine original physical gaps.
        pulled = [sum((Fraction(old_bs[i], scale) for i in range(8)
                       if vertices[i] <= r < vertices[i+1]), Fraction()) for r in range(9)]
        pressure = Fraction(sum(old_bs), scale)
        if omit not in (0, 9):
            pressure += Fraction(old_bs[omit-1], scale)
        assert sum(pulled, Fraction()) == pressure and sum(column, Fraction()) == total_mass
        arrays[omit] = column, pressure, pulled
        support_checks.append({"omitted": omit, "positive_target_edges_in_subset": actual_positive,
                               "clashes": len(clashes)})
    assert len(arrays) == 10
    wrapper = loaded[inputs[2]][0].decode()
    value = re.search(r"def windowFloor : ℝ := (\d+) / 10 \^ (\d+)", wrapper)
    H = Fraction(int(value[1]), 10**int(value[2]))
    value = re.search(r"def currentSiteRatio : ℝ :=\s*(\d+) / (\d+)", wrapper)
    R = Fraction(int(value[1]), int(value[2]))
    K = R + Fraction(1, 100000)
    assert Fraction(witness["old_proved_floor"]) == floor9
    assert Fraction(witness["window_floor"]) == H and Fraction(witness["record"]) == R
    assert Fraction(witness["required_strict_target"]) == K
    for entry in witness["ordered_deletion_embeddings"]:
        a, p, b = arrays[entry["omitted"]]
        assert list(map(Fraction, entry["span_masses"])) == a
        assert list(map(Fraction, entry["pulled_pressure_by_gap"])) == b
        assert Fraction(entry["total_pressure"]) == p
    lam = list(map(Fraction, witness["exact_primal_weights"]))
    y = list(map(Fraction, witness["exact_dual_nonnegative_weights"]))
    assert len(lam) == 10 and len(y) == 9
    assert min(lam) >= 0 and min(y) >= 0
    loads = [sum((arrays[k][0][s]*lam[k] for k in range(10)), Fraction()) for s in range(9)]
    assert max(loads) <= 2 and loads == list(map(Fraction, witness["exact_primal_capacity_loads"]))
    c = floor9*sum(lam, Fraction())
    B = sum((lam[k]*arrays[k][1] for k in range(10)), Fraction())
    assert 0 < c < Fraction(1, 64) and c == Fraction(witness["exact_primal_floor"])
    assert B == Fraction(witness["exact_primal_pressure"])
    ratio = (H-B)/(1-c)
    assert ratio == Fraction(witness["exact_primal_ratio"]) and ratio < K
    gains = [K*floor9-arrays[k][1] for k in range(10)]
    covered = [sum((arrays[k][0][s]*y[s] for s in range(9)), Fraction()) for k in range(10)]
    assert all(a >= b for a, b in zip(covered, gains))
    assert gains == list(map(Fraction, witness["exact_linearized_column_gains"]))
    assert covered == list(map(Fraction, witness["exact_dual_covered_column_gains"]))
    upper = 2*sum(y, Fraction())
    gap = K-H-upper
    assert gap > 0 and upper == Fraction(witness["exact_dual_upper"])
    assert gap == Fraction(witness["exact_strict_gap_threshold_minus_upper"])
    assert floor9*Fraction(18)/total_mass < Fraction(1, 64)
    failure = json.loads(loaded[inputs[5]][0])
    assert failure["solver_calls"] == 0
    assert failure["failed_source_sha256"] == loaded[inputs[7]][1]["sha256"]
    assert witness["optimizer_calls"] == 1 and witness["pre_solver_failed_executions"] == 1
    for path, (raw, _) in loaded.items():
        assert path.read_bytes() == raw
    receipt = {"schema": "separate-stdlib-fixed-global-gluing-dual-audit-v1",
               "passed": True, "dependency_files": [row for _, row in loaded.values()],
               "source": read(Path(__file__))[1], "ordered_embeddings_checked": 10,
               "support_count_checks": support_checks,
               "capacity_rows_checked": 9, "dual_columns_checked": 10,
               "old_pair_mass": str(total_mass), "exact_dual_gap": str(gap),
               "gap_hint": float(gap), "family_cannot_reach_required_target": True,
               "solver_output_optimality_assumed": False,
               "producer_imports": 0, "optimizer_calls": 0, "NumPy_imports": 0,
               "actual_kernel_evaluations": 0, "tree_records_read": 0, "Lean_invocations": 0,
               "preexisting_analytic_theorems_reproved_here": False,
               "new_global_floor_Lean_proven": False,
               "new_unconditional_zero_proportion_proven": False, "website_submission_ready": False}
    output = HERE / "independent-replay.json"
    raw = (json.dumps(receipt, indent=2) + "\n").encode()
    assert not output.exists(), "Preserve frozen independent receipt"
    output.write_bytes(raw)
    print(json.dumps({"passed": True, "exact_gap_hint": float(gap),
                      "receipt_sha256": hashlib.sha256(raw).hexdigest()}))


if __name__ == "__main__":
    main()
