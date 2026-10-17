"""Exact static support audit of old-nine-point nonnegative decompositions.

Read coefficient source literals only. No optimizer, actual kernel evaluation,
tree traversal, new witness, Lean or numerical certificate is run.
"""
from pathlib import Path
import ast
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent.parent
HERE = Path(__file__).resolve().parent
OLD = ROOT / "GramDefect20261015/Core.lean"
NEW = ROOT / "StructuralResearch20261016/W10RefinedCandidate.lean"


def source(path):
    raw = path.read_bytes()
    return raw.decode("utf-8"), {"path": path.relative_to(ROOT).as_posix(),
                                "bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest()}


def main():
    text, oldpin = source(OLD)
    target, newpin = source(NEW)
    assert text.count("namespace AMW.Cert.PC9QB6M\n") == 1
    section = text.split("namespace AMW.Cert.PC9QB6M\n", 1)[1]
    terms = ast.literal_eval(re.search(r"^def TS : List Term := (\[[^\n]*\])$", section, re.M)[1])
    olda = {(i, j): a for i, j, a, _ in terms if a > 0}
    definition = target.split("def aN :", 1)[1].split("def bN :", 1)[0]
    newa = {(int(i), int(j)): int(a) for i, j, a in re.findall(r"\| (\d+), (\d+) => (\d+)", definition)}
    assert len(olda) == len(terms) and len(newa) == 39
    assert all(0 <= i < j < 9 for i, j in olda)
    assert all(0 <= i < j < 10 and a > 0 for (i, j), a in newa.items())
    oldmissing = [(i, j) for i in range(9) for j in range(i+1, 9) if (i, j) not in olda]
    newmissing = [(i, j) for i in range(10) for j in range(i+1, 10) if (i, j) not in newa]
    degrees = [sum(v in edge for edge in newmissing) for v in range(10)]
    maps = []
    for omitted in range(10):
        image = [v for v in range(10) if v != omitted]
        clashes = [{"old_pair": [i, j], "image_pair": [image[i], image[j]],
                    "old_positive_integer_coefficient": a,
                    "target_integer_coefficient": 0}
                   for (i, j), a in sorted(olda.items())
                   if (image[i], image[j]) not in newa]
        remaining_missing = sum(omitted not in edge for edge in newmissing)
        assert remaining_missing == len(newmissing) - degrees[omitted]
        assert remaining_missing > len(oldmissing)
        assert clashes
        maps.append({"omitted": omitted, "ordered_image": image,
                     "remaining_missing_edges": remaining_missing,
                     "all_zero_edge_clashes": clashes,
                     "first_exact_clash": clashes[0]})
    assert len(oldmissing) == 2 and len(newmissing) == 6 and max(degrees) == 3
    # A separate graph-count argument rules out every injective relabelling,
    # not merely the ten order-preserving maps explicitly enumerated above.
    assert min(m["remaining_missing_edges"] for m in maps) == 3
    result = {
        "schema": "exact-static-nine-to-ten-support-obstruction-v1",
        "source_files": [oldpin, newpin],
        "old_floor": "859538525913875481/100000000000000000000",
        "target_floor": "433/50000",
        "old_positive_edges": len(olda), "old_missing_edges": oldmissing,
        "target_positive_edges": len(newa), "target_missing_edges": newmissing,
        "target_missing_graph_degrees": degrees,
        "nine_vertex_subset_minimum_missing_edges": 3,
        "ordered_embeddings": maps,
        "all_ordered_embeddings_have_exact_positive_into_zero_clash": True,
        "arbitrary_injective_relabellings_also_fail_by_support_count": True,
        "coefficientwise_nonnegative_combination_forces_all_embedding_weights_zero": True,
        "scope": "Injective embeddings of the unchanged W9 pair ledger into unchanged W10 with coefficientwise nonnegative pair residual. Pressure residual cannot repair a negative coefficient in this specific proof rule.",
        "does_not_rule_out_actual_function_inequalities_with_signed_coefficients": True,
        "does_not_rule_out_paid_remainders_or_other_local_bounds": True,
        "optimizer_calls": 0, "actual_kernel_evaluations": 0,
        "tree_records_read": 0, "Lean_invocations": 0,
        "new_global_floor_proven": False,
        "new_unconditional_zero_proportion_proven": False,
        "website_submission_ready": False,
    }
    output = HERE / "support-obstruction.json"
    raw = (json.dumps(result, indent=2) + "\n").encode()
    if output.exists():
        assert output.read_bytes() == raw, "Preserve frozen receipt"
    else:
        output.write_bytes(raw)
    print(json.dumps({"old_positive_edges": len(olda), "target_positive_edges": len(newa),
                      "ordered_embeddings_blocked": len(maps),
                      "minimum_missing_edges_in_any_nine_subset": 3,
                      "receipt_sha256": hashlib.sha256(raw).hexdigest()}))


if __name__ == "__main__":
    main()
