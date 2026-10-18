"""Independent fixed Stage C feasible-witness review; no DBM scan or solver.

Only the selected B cells are mapped to physical vertices.  Original FS/flow
are decoded in their original states, never in the joint tightened geometry.
Producer scripts are bound as bytes, never imported or executed.
"""
from fractions import Fraction as F
from hashlib import sha256
import argparse
import gzip
import importlib.util
import json
import os
from pathlib import Path
import time
import traceback

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
PROD = ROOT / "research-goal-20261018-stageC-dbm"
B = ROOT / "research-goal-20261018-stageB-classification"
OWN_A = ROOT / "research-goal-20261018-record-baseline-independent"
OWN_B = ROOT / "research-goal-20261018-stageB-independent"
SOURCE = ROOT / "research-goal-20261018-record-source-audit/snapshot/Solution.lean"
SOURCE_SHA = "f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf"
B_SHA = "3f9408f2cf1ceae12339456da034d9e8f175f828cf2d53a652339ee79eec89ad"
OWN_B_SHA = "e6458883bc7588a2302afe435c3b79a08c9236bb895ec3010655024c767d7288"
GATE = ROOT / "research-goal-20261016/gates/stageC-dbm-20261018.json"
GATE_SHA = "8020cdd1c37cf1d5b786f803be0f8a2105b99ab9dab31168eb17af8d856994e7"
CN = 893616123055294719
TAU = 893916123055294719
DEBIT = 335544320000000000 * 300000000000000
SC = 32768
DEN = 20 * SC
N = 1187
ORIENTATIONS = ["id/id", "id/rev", "rev/id", "rev/rev"]


def canon(data):
    return (json.dumps(data, sort_keys=True, separators=(",", ":")) + "\n").encode("ascii")


def pin(path):
    raw = path.read_bytes()
    return {"path": path.relative_to(ROOT).as_posix(), "bytes": len(raw), "sha256": sha256(raw).hexdigest()}


def load(path):
    return json.loads(path.read_text(encoding="utf-8"))


def dump_new(name, data):
    with (HERE / name).open("x", encoding="utf-8", newline="\n") as stream:
        json.dump(data, stream, ensure_ascii=True, indent=2)
        stream.write("\n"); stream.flush(); os.fsync(stream.fileno())


def map_edges(cell, spans, reverse, offset):
    """Derive bounds directly from all original 36 closed source spans."""
    state = cell["state"]
    lower, upper = state["L"] + state["A"], state["U"] + state["B"]
    assert state["M"] == 0 and len(lower) == len(upper) == len(spans) == 36
    edges = []
    for k in range(36):
        i, j = spans[k]
        a, b = (8-j, 8-i) if reverse else (i, j)
        a += offset; b += offset
        assert 0 <= a < b <= 9
        edges.extend([(a, b, 20 * upper[k]), (b, a, -20 * lower[k])])
    assert len(edges) == 72
    return edges


def all_edges(prefix, suffix, spans, orientation):
    assert orientation in ORIENTATIONS
    a, b = orientation.split("/")
    edges = map_edges(prefix, spans, a == "rev", 0) + map_edges(suffix, spans, b == "rev", 1)
    edges += [(r+1, r, -17 * SC) for r in range(9)]
    assert len(edges) == 153
    return edges


def ordered(point, reverse, offset):
    physical_gaps = [point[offset+k+1] - point[offset+k] for k in range(8)]
    original_gaps = list(reversed(physical_gaps)) if reverse else physical_gaps
    lhs, rhs = original_gaps[0], original_gaps[7]
    return {"orientation": "rev" if reverse else "id", "offset": offset,
        "original_h0_scaled": lhs, "original_h7_scaled": rhs,
        "four_point_left_minus_right_scaled": lhs-rhs, "ordered_condition_holds": lhs <= rhs}


def source_witness(own, model, row):
    """Recheck just this original fixed numeric witness, not a tree/pair search."""
    runner = own.Replay(model)
    state = row["state"]
    original = (state["L"] + state["A"], state["U"] + state["B"])
    r, pos, end = row["root"], row["position"], row["end"]
    assert runner.hashstate(original) == row["state_sha256"]
    assert not original[1][7] < original[0][0]
    raw = (model["dispatch_value"](f"WL{r}", pos//32768) >> (pos%32768)) & ((1 << 480)-1)
    assert raw & 3 == 0
    consumed, margin = runner.numeric(original, raw >> 2)
    assert end == pos + 2 + consumed
    assert margin == int(row["original_margin"]) >= 0
    assert margin - DEBIT == int(row["tau_margin"]) < 0
    word, offset, FS = raw >> 2, 0, []
    for i, j, _a, _slot in model["TS"]:
        L, U = runner.bounds(original, i, j)
        fields, offset = runner.decode_term(word, offset, L, U)
        FS.append(list(fields))
    P, S, Cp, Cm, used = runner.flow(original, word, offset)
    assert consumed == used
    semantic = {"FS": FS, "P": P, "S": S, "Cp": Cp, "Cm": Cm, "consumed_bits": used}
    packed = {"bits": used, "value": str(word & ((1 << used)-1))}
    witness = {"WD": r, "original_leaf_position": pos, "payload_bit_position": pos+2,
        "consumed_payload_bits": used, "original_rdw_block": pos//32768, "original_rdw_shift": pos%32768,
        "packed_payload_sha256": sha256(canon(packed)).hexdigest(),
        "decoded_semantic_sha256": sha256(canon(semantic)).hexdigest()}
    assert witness == row["witness"]
    return {"exception_id": row["exception_id"], "root": r, "position": pos, "end": end,
        "original_margin": margin, "tau_margin": margin-DEBIT,
        "source_state_sha256": row["state_sha256"], "source_witness": witness,
        "original_fixed_witness_checks": dict(runner.count),
        "FS_and_flow_decoded_in_original_unmodified_state": True}


def verify_feasible(first, scan, cells, spans):
    i, j = first["prefix_exception_id"], first["suffix_exception_id"]
    assert type(i) is type(j) is int and 0 <= i < N and 0 <= j < N
    orientation = first["orientation"]
    assert first["case_ordinal"] == ORIENTATIONS.index(orientation) * N*N + i*N+j
    assert first["prefix_cell"] == cells[i] and first["suffix_cell"] == cells[j]
    assert scan["cases_checked"] == first["case_ordinal"] + 1
    assert scan["negative_cycle_records"] == first["case_ordinal"]
    assert scan["stopped_at_first_relaxed_feasible"] is True and scan["all_cases_covered"] is False
    assert scan["feasible_case"] == {key: first[key] for key in ["case_ordinal", "orientation", "prefix_exception_id", "suffix_exception_id"]}
    point = first["X_integer_potential"]
    assert len(point) == 10 and all(type(x) is int for x in point) and point[0] == 0
    assert first["X_scale"] == DEN and first["positions"] == [str(F(x, DEN)) for x in point]
    # Reconstruct all four maps independently; only the reported case is tested.
    chart_hashes = {chart: sha256(canon(all_edges(cells[i], cells[j], spans, chart))).hexdigest()
                    for chart in ORIENTATIONS}
    edges = all_edges(cells[i], cells[j], spans, orientation)
    rows = []
    for k, (u, v, bound) in enumerate(edges):
        difference = point[v] - point[u]
        assert difference <= bound, ("infeasible_reported_edge", k, u, v, difference, bound)
        rows.append({"edge_id": k, "u": u, "v": v, "bound": bound,
                     "actual_difference": difference, "slack": bound - difference})
    assert first["all153_edges"] == rows and first["all153_edges_verified"] is True
    a, b = orientation.split("/")
    ptest, stest = ordered(point, a == "rev", 0), ordered(point, b == "rev", 1)
    assert first["prefix_ordered"] == ptest and first["suffix_ordered"] == stest
    holds = ptest["ordered_condition_holds"] and stest["ordered_condition_holds"]
    assert first["ordered_conditions_hold"] == holds
    expected = "ordered_conditions_hold" if holds else "relaxed_box_feasible_ordered_violated"
    assert first["outcome"] == scan["outcome"] == expected
    assert first["is_actual_low_energy_or_counterexample"] is False
    return {"case_ordinal": first["case_ordinal"], "orientation": orientation,
        "prefix_exception_id": i, "suffix_exception_id": j, "X_integer_potential": point,
        "all153_edges_verified_independently": True,
        "edge_minimum_slack": min(row["slack"] for row in rows),
        "source_derived_all153_edges_sha256": sha256(canon(edges)).hexdigest(),
        "all_four_chart_edge_maps_sha256": chart_hashes,
        "prefix_ordered": ptest, "suffix_ordered": stest,
        "ordered_conditions_hold": holds, "outcome": expected,
        "all_real_separation_constraints_hold": True,
        "integer_potential_is_real_feasibility_witness_not_domain_restriction": True}


def review_given_prefix(scan, first, cells, spans):
    """Review the two reported records only, without any infeasibility search."""
    assert scan["cases_checked"] == 2 and first["case_ordinal"] == 1
    packet = scan["proof_stream"]
    path = ROOT / packet["path"]
    assert pin(path)["sha256"] == packet["sha256"]
    raw = gzip.decompress(path.read_bytes())
    assert sha256(raw).hexdigest() == packet["uncompressed_sha256"]
    assert len(raw) == packet["uncompressed_bytes"] == 11
    assert raw[:7] == b"RZDBM1\n" and raw[-1:] == b"\xf0"
    method, length = raw[7] >> 4, raw[7] & 15
    assert method == 0 and length == 2
    ids = list(raw[8:10])
    edges = all_edges(cells[0], cells[0], spans, "id/id")
    selected = [edges[k] for k in ids]
    assert selected[0][1] == selected[1][0] and selected[1][1] == selected[0][0]
    assert 1 <= min(selected[0][:2]) < max(selected[0][:2]) <= 8
    total = sum(edge[2] for edge in selected)
    assert total < 0
    return {"negative_case_ordinal": 0, "orientation": "id/id", "prefix_exception_id": 0,
        "suffix_exception_id": 0, "edge_ids": ids, "edges": selected,
        "strict_negative_cycle_weight_sum": total,
        "feasible_tag_case_ordinal": 1, "records_checked": 2,
        "entire_reported_prefix_verified_without_BF_or_scan": True,
        "uncompressed_stream_sha256": sha256(raw).hexdigest()}


def closure(producer_sha):
    inputs = {}
    def add(path, expected=None):
        row = pin(path)
        if expected is not None: assert row["sha256"] == expected
        if row["path"] in inputs: assert inputs[row["path"]] == row
        inputs[row["path"]] = row
    add(Path(__file__)); add(SOURCE, SOURCE_SHA); add(GATE, GATE_SHA)
    for path, expected in [(PROD / "files.json", producer_sha), (B / "files.json", B_SHA),
                           (OWN_B / "audit-files.json", OWN_B_SHA)]:
        add(path, expected)
        m = load(path)
        for field in ["files", "package_files", "read_only_dependencies", "dependency_files", "dependencies"]:
            for row in m.get(field, []):
                assert pin(ROOT / row["path"]) == row, ("frozen_input_mismatch", row["path"])
                add(ROOT / row["path"])
    gate = load(GATE)
    assert gate["pair_scan_passes_authorized"] == 1 and gate["stop_at_first_feasible"] is True
    assert gate["complete_ordered_pair_case_count"] == 4*N*N
    assert gate["orientations"] == ORIENTATIONS and gate["separation"] == "17/20"
    assert int(gate["tau_numerator"]) == TAU
    own_b = load(OWN_B / "independent-review.json")
    assert own_b["passed"] and own_b["classification_counts"] == {"closed": 11859, "exception": 1187, "reflection": 595}
    return sorted(inputs.values(), key=lambda row: row["path"])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--execute-fixed-feasible-review", action="store_true", required=True)
    ap.add_argument("--producer-manifest-sha256", required=True)
    args = ap.parse_args()
    assert __debug__
    assert not any((HERE / name).exists() for name in ["started.json", "independent-review.json", "failure.json"])
    start = time.monotonic()
    before = closure(args.producer_manifest_sha256)
    dump_new("started.json", {"pid": os.getpid(), "time_unix": time.time(),
        "producer_manifest_sha256": args.producer_manifest_sha256,
        "scope": "One independent fixed two-case result review; no pair scan or solver",
        "inputs_sha256": before})
    try:
        scan, first = load(PROD / "scan.json"), load(PROD / "first-feasible.json")
        terminal = load(PROD / "terminal.json")
        assert terminal["exit_code"] == 0 and terminal["child_launches"] == 1 and terminal["limit_stop"] is None
        assert scan["passed"] and scan["scan_passes"] == 1
        assert scan["total_cases"] == 4*N*N and scan["cases_checked"] == 2
        classification = load(B / "classification.json")
        spans = [tuple(pair) for pair in classification["pair_order_from_source"]]
        assert len(spans) == 36 and len(set(spans)) == 36
        assert set(spans) == {(i,j) for i in range(9) for j in range(i+1,9)}
        assert spans[:8] == [(i,i+1) for i in range(8)]
        cells = []
        with gzip.open(B / "exception-cells.jsonl.gz", "rb") as stream:
            for line in stream:
                row = json.loads(line)
                assert line == canon(row) and row["exception_id"] == len(cells)
                assert row["kind"] == "exception" and row["coordinate_scale"] == SC and row["separation"] == "17/20"
                cells.append(row)
        assert len(cells) == N
        feasible = verify_feasible(first, scan, cells, spans)
        prefix = review_given_prefix(scan, first, cells, spans)
        spec = importlib.util.spec_from_file_location("own_frozen_independent_A", OWN_A / "replay_independent.py")
        own = importlib.util.module_from_spec(spec); spec.loader.exec_module(own)
        model = own.load_source()
        assert model["ALL"] == spans and model["CN"] == CN
        source_rows = [source_witness(own, model, cells[first[key]])
                       for key in ["prefix_exception_id", "suffix_exception_id"]]
        assert scan["inputs_sha256_start"] == scan["inputs_sha256_end"]
        for path, digest in scan["inputs_sha256_end"].items():
            assert pin(ROOT / path)["sha256"] == digest
        for key in ["new_kernel_queries", "new_witnesses_or_cuts", "optimizer_calls", "Lean_runs"]:
            assert scan[key] == 0
        assert scan["complete_source_gate_passed"] is False and scan["complete_source_and_runtime_budget"] == "unknown"
        after = [pin(ROOT / row["path"]) for row in before]
        assert before == after
        result = {"schema": "independent-fixed-StageC-first-feasible-review-v1", "passed": True,
            "pid": os.getpid(), "seconds": time.monotonic()-start,
            "producer_manifest_sha256": args.producer_manifest_sha256,
            "inputs_sha256_start": before, "inputs_sha256_end": after,
            "source_sha256": SOURCE_SHA, "producer_Python_modules_imported": 0,
            "independent_review_executions": 1, "pair_scan_executions": 0, "DBM_solver_calls": 0,
            "original_fixed_FS_witnesses_rechecked": 2, "fixed_source_witness_results": source_rows,
            "feasible_result": feasible, "complete_reported_prefix_certificate": prefix,
            "first_feasible_with_both_actual_ordered_conditions_independently_verified": True,
            "scope": "Exact feasible ordered joint geometry at one original exception pair; all prior reported cases checked by given strict cycle, no new scan",
            "meaning": "The fixed B closed-cell geometry cannot close all window pairs by incompatibility alone. This point is not evidence that either actual energy is below tau.",
            "actual_kernel_energy_evaluated_at_potential": False,
            "new_kernel_queries": 0, "new_witnesses_or_cuts": 0, "optimizer_calls": 0, "Lean_runs": 0,
            "complete_source_and_runtime_budget": "unknown", "complete_source_gate_passed": False,
            "new_joint_floor_proven": False, "new_unconditional_zero_proportion_proven": False,
            "website_submission_ready": False}
        dump_new("independent-review.json", result)
        print(json.dumps({"passed": True, "seconds": result["seconds"], "outcome": feasible["outcome"],
            "case_ordinal": feasible["case_ordinal"], "receipt": pin(HERE / "independent-review.json")}), flush=True)
    except BaseException as exc:
        dump_new("failure.json", {"passed": False, "error": repr(exc), "traceback": traceback.format_exc(),
            "seconds": time.monotonic()-start, "automatic_retry_allowed": False})
        raise


if __name__ == "__main__":
    main()
