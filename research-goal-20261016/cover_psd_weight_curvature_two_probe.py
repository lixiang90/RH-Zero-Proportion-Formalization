"""Two fixed cells: trace-normalized finite PSD mixtures and exact flow bounds.

The only directions are strict-free coordinate/pair directions and quantized
negative eigenvectors at one feasible midpoint. A single finite LP minimizes
the shared DBM support function over their simplex. No sample, PSD round,
global runner, or Lean process is added. Floating discovery never certifies
an exclusion: integer weights and the independent scalar/flow checker do.
"""
from pathlib import Path
from fractions import Fraction as F
from functools import reduce
from math import gcd
import gzip
import hashlib
import json
import time
import numpy as np
from scipy.optimize import linprog
import cover_correlated_curvature as curv
import cover_psd_weight_curvature_verify as replay
from cover_contractor_verify import flow_bound

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
g = curv.g
SC, DS = g.SC, curv.DS
PATHS = ["r001000001000001101011101", "r001000001000001110011100"]
DEN = 2 * SC * g.D * DS
PARAM = ROOT / "research-20261016-followup/window_reweight_rational.json"
sha = lambda data: hashlib.sha256(data).hexdigest()


def coefficients(data, direction):
    constant = error = 0
    coeff = [0] * 9
    for (i, j, a), (P, m0, m1, err, kind) in zip(g.TERMS, data):
        q = a * sum(direction[i:j]) ** 2
        constant += q * (2 * SC * m0 - m1 * P)
        error += 2 * SC * q * err
        for r in range(i, j):
            coeff[r] += 2 * q * m1
    return constant, error, coeff


def canonical(direction):
    direction = tuple(map(int, direction))
    common = reduce(gcd, map(abs, direction))
    if not common:
        return None
    direction = tuple(v // common for v in direction)
    return tuple(-v for v in direction) if next(v for v in direction if v) < 0 else direction


def candidates(state, oracle, distances):
    free = [r for r in range(9) if state[0][r] > g.SEP]
    # Both shortest-path potentials are feasible. Their mean is a feasible
    # rational midpoint, unlike arbitrary independent interval midpoints.
    prefix = [F(distances[0][r] - distances[r][0], 2) for r in range(10)]
    midpoint = [prefix[r + 1] - prefix[r] for r in range(9)]
    assert all(l <= sum(midpoint[i:j]) <= u for (i, j), l, u in zip(g.ALL, *state))
    H = np.zeros((9, 9))
    for i, j, aw in g.TERMS:
        P = 2 * sum(midpoint[i:j])
        assert P.denominator == 1
        assert 0 <= P <= 64 * SC
        value, _ = oracle.point(int(P))
        H[i:j, i:j] += (aw / g.D) * float((value.l + value.u) / 2)
    seen = set()
    for i in free:
        d = [0] * 9
        d[i] = 1
        seen.add(canonical(d))
        for j in free:
            if j <= i:
                continue
            for sign in [-1, 1]:
                d = [0] * 9
                d[i], d[j] = 1, sign
                seen.add(canonical(d))
    values, vectors = np.linalg.eigh(H[np.ix_(free, free)])
    for col, value in enumerate(values):
        if value >= -1e-12:
            break
        vector = vectors[:, col]
        d = [0] * 9
        for k, i in enumerate(free):
            d[i] = round(float(vector[k] / max(abs(vector))) * 65536)
        if canonical(d):
            seen.add(canonical(d))
    directions = sorted(seen)
    assert directions and all(not d or state[0][i] > g.SEP for v in directions for i, d in enumerate(v))
    return directions, free, midpoint, values.tolist()


def discover(state, data, directions, distances):
    packets = [coefficients(data, d) for d in directions]
    norms = [sum(v * v for v in d) for d in directions]
    edges = [(i, j) for i in range(10) for j in range(10) if i != j]
    count = len(directions)
    scale = 1000000
    const = np.array([float(F(C + E, DEN * n)) * scale for (C, E, _), n in zip(packets, norms)])
    coeff = np.array([[float(F(v * SC, DEN * n)) * scale for v in q]
                      for (_, _, q), n in zip(packets, norms)])
    # Flow out-in = divergence of the gap objective. The omitted tenth
    # node follows by zero sum. This is the exact finite support-function
    # dual formulation; no extra cut-plane directions are generated.
    eq = np.zeros((10, count + len(edges)))
    divergence = np.c_[coeff[:, 0], coeff[:, 1:] - coeff[:, :-1], -coeff[:, -1]]
    eq[:9, :count] = -divergence[:, :9].T
    eq[9, :count] = 1
    for k, (i, j) in enumerate(edges):
        if i < 9:
            eq[i, count + k] = 1
        if j < 9:
            eq[j, count + k] = -1
    objective = np.r_[const, [distances[i][j] / SC for i, j in edges]]
    lp = linprog(objective, A_eq=eq, b_eq=np.r_[np.zeros(9), 1.], bounds=(0, None), method="highs",
                 options={"primal_feasibility_tolerance": 1e-9, "dual_feasibility_tolerance": 1e-9})
    assert lp.success, lp.message
    lam = np.maximum(lp.x[:count], 0)
    lam /= sum(lam)
    quantum = 10 ** 24
    mu = [round(F(str(float(value))) * quantum / norm) for value, norm in zip(lam, norms)]
    common = reduce(gcd, mu)
    assert common > 0
    mu = [v // common for v in mu]
    C = sum(w * p[0] for w, p in zip(mu, packets))
    E = sum(w * p[1] for w, p in zip(mu, packets))
    q = [sum(w * p[2][r] for w, p in zip(mu, packets)) for r in range(9)]
    minimum, flow = g.minimize(0, [-v for v in q], distances)
    upper = C + E - minimum
    trace = sum(w * n for w, n in zip(mu, norms))
    weighted = [{"weight": str(w), "direction": list(d)} for w, d in zip(mu, directions) if w]
    result = {"kind": replay.KIND, "weighted_directions": weighted,
              "scalar_affine_data": [[P, str(m0), str(m1), str(err), kind] for P, m0, m1, err, kind in data],
              "exact_flow": {"constant": str(C), "error": str(E), "coefficient": list(map(str, q)),
                             "negative_maximum": str(minimum), "flow": flow},
              "upper_numerator": str(upper), "denominator": str(DEN)}
    # These are exact bounds on the selected rank-one functions as well.
    best = None
    for index, ((c, e, b), norm) in enumerate(zip(packets, norms)):
        lower, _ = g.minimize(0, [-v for v in b], distances)
        value = F(c + e - lower, DEN * norm)
        if best is None or value < best[0]:
            best = value, index
    return result, {"LP_rounds": 1, "cutplane_rounds": 0, "PSD_rounds_added": 0,
                    "LP_status": int(lp.status), "LP_objective_hint": float(lp.fun / scale),
                    "LP_equality_residual_hint": float(max(abs(eq @ lp.x - np.r_[np.zeros(9), 1.]))),
                    "finite_direction_count": count, "positive_integer_weights": len(weighted),
                    "trace_weight": str(trace), "integer_weight_quantum": str(quantum),
                    "normalized_exact_upper": str(F(upper, DEN * trace)),
                    "normalized_exact_upper_float": float(F(upper, DEN * trace)),
                    "best_rank_one_exact_upper": str(best[0]), "best_rank_one_exact_upper_float": float(best[0]),
                    "best_rank_one_direction": list(directions[best[1]]),
                    "finite_LP_optimality_is_not_a_proof": True}


def main():
    started = time.monotonic()
    packed = (HERE / "cover-curvature-parent64.input.json.gz").read_bytes()
    source = json.loads(gzip.decompress(packed))
    lookup = {row["path"]: row for row in source["cases"]}
    params = json.loads(PARAM.read_bytes())
    taylor = curv.first.TaylorOracle(HERE / "cover_newjet.json")
    oracle = curv.CurvatureOracle(taylor)
    checker = replay.make_checker(HERE / "cover_newjet.json")
    rows = []
    for path in PATHS:
        state = tuple(lookup[path]["before"])
        closed = g.close(*state)
        assert closed is not None and tuple(closed[:2]) == state
        directions, free, midpoint, eigenvalues = candidates(state, oracle, closed[2])
        data = [oracle.affine(state[0][g.LOOK[i, j]], state[1][g.LOOK[i, j]]) for i, j, _ in g.TERMS]
        result, statistics = discover(state, data, directions, closed[2])
        # Reconstruct all scalar arithmetic independently, including the
        # common support restriction, even when the total upper is positive.
        expanded = replay.expand(state, result["weighted_directions"], result["scalar_affine_data"], params, checker)
        assert expanded["constant"] == int(result["exact_flow"]["constant"])
        assert expanded["error"] == int(result["exact_flow"]["error"])
        assert expanded["coefficient"] == list(map(int, result["exact_flow"]["coefficient"]))
        minimum = flow_bound(state, [-v for v in expanded["coefficient"]], result["exact_flow"]["flow"])
        upper = expanded["constant"] + expanded["error"] - minimum
        assert upper == int(result["upper_numerator"])
        verification = replay.verify(state, result, params, checker) if upper < 0 else None
        row = {"path": path, "cell": state, "strict_free_coordinates": free,
               "feasible_midpoint_gap_units": list(map(str, midpoint)), "midpoint_eigenvalue_hints": eigenvalues,
               "candidate": result, "statistics": statistics, "strict_exclusion": upper < 0,
               "independent_scalar_and_flow_replay_passed": True, "strict_verifier_result": verification}
        rows.append(row)
        print(json.dumps({"path": path, "strict_exclusion": upper < 0, **statistics,
                          "seconds": time.monotonic() - started}), flush=True)
    out = {"receipt": {"scope": __doc__, "script_sha256": sha(Path(__file__).read_bytes()),
                       "parent64_input_sha256": sha(packed), "parameter_sha256": sha(PARAM.read_bytes()),
                       "table_sha256": taylor.sha, "verifier_source_sha256": replay.source_hashes(),
                       "cases": 2, "maximum_rounds_per_cell": 20, "actual_LP_rounds_per_cell": 1,
                       "strict_exclusions": sum(row["strict_exclusion"] for row in rows),
                       "independent_scalar_and_flow_replay_passed": True, "new_Lean_soundness_proven": False,
                       "complete_global_cover": False, "new_zero_proportion_proven": False,
                       "seconds": time.monotonic() - started}, "rows": rows,
           "exclusions": [row for row in rows if row["strict_exclusion"]]}
    (HERE / "cover-psd-weight-curvature-two.json").write_text(json.dumps(out, separators=(",", ":")) + "\n")
    print(json.dumps(out["receipt"]), flush=True)


if __name__ == "__main__":
    main()
