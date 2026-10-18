"""Independent fixed-tau classification, using our own frozen Stage A model.

No producer Python modules, new witness, threshold scan, pair query or Lean.
This file is prepared before execution; producer bindings are fixed at launch.
"""
from collections import Counter
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
TAU = 893916123055294719
ORIGINAL = 893616123055294719
DELTA = 300000000000000
SCALE = 335544320000000000
DEBIT = SCALE * DELTA
GATE = ROOT / "research-goal-20261016/gates/stageB-20261018.json"
GATE_SHA = "1548e22dcd1446a7110cb3c2452a574d0edc323c3bb81b35591a1d0e93324273"
A_MODULE = ROOT / "research-goal-20261018-record-baseline-independent/replay_independent.py"
A_MANIFEST = ROOT / "research-goal-20261018-record-baseline-independent/audit-files.json"
A_MANIFEST_SHA = "2d2c8003ed6be6f74d0f53e8624cd631eb1c934415b22b5377a4f2d40c64791c"
A_RECEIPT = ROOT / "research-goal-20261018-record-baseline-independent/independent-replay.json"
PRODUCER = ROOT / "research-goal-20261018-stageB-classification"
PRODUCER_MANIFEST_SHA = "3f9408f2cf1ceae12339456da034d9e8f175f828cf2d53a652339ee79eec89ad"
MAX_SECONDS = 180
MAX_OUTPUT_BYTES = 32000000


def pin(path):
    raw = path.read_bytes()
    return {"path": path.relative_to(ROOT).as_posix(), "bytes": len(raw), "sha256": sha256(raw).hexdigest()}


def canon(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode("ascii")


def load_own_A():
    assert pin(A_MANIFEST)["sha256"] == A_MANIFEST_SHA
    manifest = json.loads(A_MANIFEST.read_text(encoding="utf-8"))
    for item in manifest["package_files"] + manifest["dependency_files"]:
        assert pin(ROOT / item["path"]) == item
    spec = importlib.util.spec_from_file_location("own_frozen_stageA", A_MODULE)
    own = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(own)
    return own


def threshold_identity(tree):
    """Symbolically inspect the unique cN path in the source Nat.ble AST."""
    assert tree[0] == "Nat.ble" and len(tree) == 3
    def paths(node):
        if isinstance(node, str): return [[]] if node == "cN" else []
        found = []
        for index, child in enumerate(node[1:], 1):
            for trail in paths(child): found.append([(node, index)] + trail)
        return found
    lhs, rhs = paths(tree[1]), paths(tree[2])
    assert len(lhs) == 1 and not rhs
    coefficient = 1
    for parent, index in lhs[0]:
        assert parent[0] in ["Nat.add", "Nat.mul"] and len(parent) == 3
        if parent[0] == "Nat.mul":
            other = parent[3 - index]
            assert isinstance(other, str) and other.isdecimal()
            coefficient *= int(other)
    assert coefficient == SCALE
    return {"cN_occurrences_LHS": 1, "cN_occurrences_RHS": 0,
            "exact_positive_affine_coefficient": coefficient,
            "fixed_tau_numerator": TAU, "original_cN": ORIGINAL,
            "fixed_delta_numerator": DELTA, "exact_debit": DEBIT,
            "one_debit_only": True}


def semantic_witness(runner, state, source_word):
    """Decode original fixed FS/flow as metadata without changing A counters."""
    word, at, FS = source_word >> 2, 0, []
    for i, j, coefficient, slot in runner.m["TS"]:
        low, high = runner.bounds(state, i, j)
        fields, at = runner.decode_term(word, at, low, high)
        FS.append(list(fields))
    before = runner.count.copy()
    P, S, positive, negative, consumed = runner.flow(state, word, at)
    runner.count = before
    semantic = {"FS": FS, "P": P, "S": S, "Cp": positive, "Cm": negative, "consumed_bits": consumed}
    used = word & ((1 << consumed) - 1)
    return semantic, {"semantic_sha256": sha256(canon(semantic)).hexdigest(),
        "consumed_payload_bits": consumed, "consumed_payload_hex_sha256": sha256(hex(used).encode("ascii")).hexdigest(),
        "window480_hex_sha256": sha256(hex(source_word).encode("ascii")).hexdigest(),
        "packed_payload_sha256": sha256(canon({"bits": consumed, "value": str(used)})).hexdigest()}


def raised_root_guards(model):
    sep = F(17, 20)
    B = sum(model["BS"], 0) / F(10**20)
    c9, tau = F(ORIGINAL, 10**20), F(TAU, 10**20)
    true_count = sum(flag for row in model["COV"] for _, _, flag in row)
    assert true_count == 160
    unary = c9 + sep * B
    assert unary >= tau
    tails = [F(b * bound, 10**20 * 32768) + sep * (B - F(b, 10**20))
             for b, bound in zip(model["BS"], model["SMAX"])]
    assert len(tails) == 8 and all(value >= tau for value in tails)
    assert sep > F(1, 2)
    for r, row in enumerate(model["COV"]):
        endpoint = 16384
        for lower, upper, good in row:
            assert endpoint == lower <= upper < 1048576
            endpoint = upper
        assert endpoint == model["SMAX"][r]
    return {"domain_sep": str(sep), "variable_domain": "Real gaps; no integer-grid assumption",
        "true_COV_original_rows_reused": true_count, "unary_original_c9_plus_full_sep_pressure": str(unary),
        "unary_margin_above_tau": str(unary - tau),
        "all8_tail_payments": list(map(str, tails)),
        "all8_tail_margins_above_tau": [str(value - tau) for value in tails],
        "small_gap_below_half_empty_in_domain": True,
        "old_WZ_queries_reused_without_new_evaluation": True,
        "COV_endpoints_and_cells_closed": True}


def provenance(model, root, pos, end):
    records = sorted((r for r in model["cursors"] if r["root"] == root), key=lambda r: r["index"])
    return [r["name"] for r in records if r["pos"] <= pos and end <= r["expected"]]


def classify_all(own):
    model = own.load_source()
    assert model["CN"] == ORIGINAL and TAU - ORIGINAL == DELTA
    ast_identity = threshold_identity(model["margin_tree"])
    guards = raised_root_guards(model)
    a = {(i, j): weight for i, j, weight, _ in model["TS"]}
    assert all(a.get((i, j), 0) == a.get((8-j, 8-i), 0) for i, j in model["ALL"])
    assert model["BS"] == list(reversed(model["BS"]))
    reflected_index = [model["LOOK"][(8-j, 8-i)] for i, j in model["ALL"]]
    assert [reflected_index[k] for k in reflected_index] == list(range(36))
    runner = own.Replay(model)
    rows, exceptions, reflection = [], [], []
    counts, all_geometry, all_witness = Counter(), sha256(), sha256()
    for root in range(48):
        runner.run_root(root)
        paths = {}
        def mark(pos, path):
            assert pos not in paths
            paths[pos] = path
            node = runner.nodes[pos]
            if node["kind"] == "branch":
                mark(node["left"], path + "0")
                mark(node["right"], path + "1")
        mark(model["roots"][root]["pos"], "r")
        assert len(paths) == len(runner.nodes)
        for pos, node in sorted(runner.nodes.items()):
            if node["kind"] == "branch": continue
            state = node["state"]
            geometry = [[i, j, state[0][k], state[1][k]] for k, (i, j) in enumerate(model["ALL"])]
            assert len(geometry) == 36 and [tuple(r[:2]) for r in geometry[8:]] == model["PR"]
            base = {"root": root, "pos": pos, "end": node["end"], "path": paths[pos],
                "source_state_sha256": runner.hashstate(state),
                "closed_pair_bounds_in_original_order": geometry,
                "nested_provenance": provenance(model, root, pos, node["end"])}
            if node["kind"] == "reflection":
                assert state[1][7] < state[0][0]
                reflection.append({**base, "meaning": "Excluded only on ordered half-domain h0<=h7; no energy payment"})
                counts["reflection"] += 1
                continue
            assert node["kind"] == "numeric", "No added Farkas/other terminals permitted"
            original = node["margin"]
            raised = original - DEBIT
            classification = "closed" if raised >= 0 else "exception"
            counts[classification] += 1
            word = (model["dispatch_value"](f"WL{root}", pos // 32768) >> (pos % 32768)) & ((1 << 480) - 1)
            semantic, witness = semantic_witness(runner, state, word)
            assert witness["consumed_payload_bits"] == node["end"] - pos - 2
            row = {**base, "original_margin": original, "raised_margin": raised,
                "class": classification, "witness": witness}
            reflected = [[i, j, geometry[k][2], geometry[k][3]]
                         for (i, j), k in zip(model["ALL"], reflected_index)]
            twice = [[i, j, reflected[k][2], reflected[k][3]]
                     for (i, j), k in zip(model["ALL"], reflected_index)]
            assert twice == geometry
            row["reflected_closed_geometry_sha256"] = sha256(canon(reflected)).hexdigest()
            rows.append(row)
            all_geometry.update(canon(base))
            all_witness.update(canon({"root": root, "pos": pos, **witness}))
            if classification == "exception": exceptions.append(row)
        if root % 8 == 7:
            print(json.dumps({"independent_completed_roots": root + 1, "class_counts": dict(counts)}), flush=True)
    baseline = json.loads(A_RECEIPT.read_text(encoding="utf-8"))
    assert dict(runner.count) == baseline["derived_counts"]
    assert dict(runner.contract_count) == baseline["ready_contract_counts"]
    assert runner.trace.hexdigest() == baseline["canonical_trace_sha256"]
    assert len(rows) == 13046 and len(reflection) == 595 and len(exceptions) == counts["exception"]
    assert counts["closed"] + counts["exception"] == 13046
    assert len({(r["root"], r["pos"]) for r in rows + reflection}) == 13641
    return dict(model=model, runner=runner, threshold_AST_identity=ast_identity, raised_root_guards=guards,
        rows=rows, exceptions=exceptions, reflection=reflection, class_counts=dict(counts),
        all_geometry_sha256=all_geometry.hexdigest(), all_witness_sha256=all_witness.hexdigest())


def dump_new(path, data):
    with path.open("x", encoding="utf-8", newline="\n") as stream:
        json.dump(data, stream, ensure_ascii=True, indent=2)
        stream.write("\n")
        stream.flush()
        os.fsync(stream.fileno())


def input_closure():
    """Bind the whole producer package, without importing any of its modules."""
    assert pin(PRODUCER / "files.json")["sha256"] == PRODUCER_MANIFEST_SHA
    manifest = json.loads((PRODUCER / "files.json").read_text(encoding="utf-8"))
    inputs = {pin(path)["path"]: pin(path) for path in [Path(__file__), GATE,
        A_MANIFEST, A_MODULE, A_RECEIPT, PRODUCER / "files.json"]}
    assert inputs[pin(GATE)["path"]]["sha256"] == GATE_SHA
    for item in manifest["files"] + manifest["read_only_dependencies"]:
        actual = pin(ROOT / item["path"])
        assert actual == item, ("producer_package_pin", item["path"])
        if item["path"] in inputs: assert inputs[item["path"]] == item
        inputs[item["path"]] = item
    am = json.loads(A_MANIFEST.read_text(encoding="utf-8"))
    assert pin(A_MANIFEST)["sha256"] == A_MANIFEST_SHA
    for item in am["package_files"] + am["dependency_files"]:
        assert pin(ROOT / item["path"]) == item
        if item["path"] in inputs: assert inputs[item["path"]] == item
        inputs[item["path"]] = item
    gate = json.loads(GATE.read_text(encoding="utf-8"))
    assert int(gate["tau_numerator"]) == TAU and int(gate["delta_numerator"]) == DELTA
    assert int(gate["SLOPE"]) == SCALE and gate["classification_passes_authorized"] == 1
    assert gate["pair_scans_authorized"] is False and gate["Lean_runs_authorized"] is False
    assert gate["resource_limits"] == {"elapsed_seconds": MAX_SECONDS, "closed_output_bytes": MAX_OUTPUT_BYTES}
    return sorted(inputs.values(), key=lambda row: row["path"]), manifest


def read_archive(name, expected):
    """Check closed gzip bytes, full canonical decompressed identity and rows."""
    path = PRODUCER / name
    digest, size, rows = sha256(), 0, []
    with gzip.open(path, "rb") as stream:
        for line in stream:
            obj = json.loads(line)
            assert canon(obj) == line, ("noncanonical_producer_jsonl", name)
            digest.update(line); size += len(line); rows.append(obj)
    assert len(rows) == expected["rows"] and size == expected["uncompressed_bytes"]
    assert digest.hexdigest() == expected["uncompressed_sha256"]
    return rows, digest.hexdigest()


def compare_numeric_and_exception(result, manifest, summary):
    model, runner = result["model"], result["runner"]
    source = result["rows"]
    numeric, numeric_hash = read_archive("numeric-classification.jsonl.gz", manifest["archive_integrity"]["numeric"])
    exceptions, exception_hash = read_archive("exception-cells.jsonl.gz", manifest["archive_integrity"]["exceptions"])
    assert len(numeric) == len(source) == 13046
    assert len(exceptions) == len(result["exceptions"])
    assert summary["pair_order_from_source"] == [list(pair) for pair in model["ALL"]]
    assert summary["PR_order_from_source"] == [list(pair) for pair in model["PR"]]
    contract_map = {row["name"]: row for row in runner.contracts}
    counts, cursor, literal_bytes = Counter(), 0, 0
    for own, prod in zip(source, numeric):
        r, pos, end = own["root"], own["pos"], own["end"]
        w = own["witness"]
        witness = {"WD": r, "original_leaf_position": pos, "payload_bit_position": pos + 2,
            "consumed_payload_bits": w["consumed_payload_bits"], "original_rdw_block": pos // 32768,
            "original_rdw_shift": pos % 32768, "packed_payload_sha256": w["packed_payload_sha256"],
            "decoded_semantic_sha256": w["semantic_sha256"]}
        expected = {"root": r, "position": pos, "end": end, "path": own["path"],
            "kind": "closed_numeric_at_tau" if own["class"] == "closed" else "exception",
            "original_margin": str(own["original_margin"]), "tau_margin": str(own["raised_margin"]),
            "state_sha256": own["source_state_sha256"], "witness": witness}
        assert prod == expected, ("numeric_row_identity", r, pos)
        counts[(r, expected["kind"])] += 1
        if own["class"] != "exception": continue
        geometry = own["closed_pair_bounds_in_original_order"]
        lo, hi = [pair[2] for pair in geometry], [pair[3] for pair in geometry]
        state = {"L": lo[:8], "U": hi[:8], "A": lo[8:], "B": hi[8:], "M": 0}
        nested = []
        for name in own["nested_provenance"]:
            c = contract_map[name]
            assert c["pos"] <= pos and end <= c["expected"]
            nested.append({"name": name, "state": c["state"], "start": c["pos"], "end": c["expected"],
                "fuel": c["fuel"], "state_sha256": c["state_sha256"]})
        # Root traversal proves each reported leaf is fully within every enclosing cut,
        # hence a start-only producer nesting test cannot omit a crossing endpoint.
        start_only = [c["name"] for c in runner.contracts if c["root"] == r and c["pos"] <= pos < c["expected"]]
        assert start_only == own["nested_provenance"]
        rec = model["roots"][r]
        expected_exception = {**expected, "exception_id": cursor, "state": state,
            "coordinate_scale": 32768, "nested_provenance": nested,
            "root_provenance": {"indices": list(rec["indices"]), "fuel": rec["fuel"], "start": rec["pos"], "end": rec["expected"]},
            "separation": "17/20", "relaxed_orientation": True,
            "omitted_orientation_condition": "h0 <= h7", "original_cell_is_closed": True,
            "actual_low_energy_point_claimed": False}
        assert exceptions[cursor] == expected_exception, ("exception_geometry_identity", cursor, r, pos)
        flat = [v for pair in zip(lo, hi) for v in pair] + [0]
        assert len(flat) == 73
        literal_bytes += len(("<" + ",".join(map(str, flat)) + ">,\n").encode("ascii"))
        cursor += 1
    assert cursor == len(exceptions)
    for old, own in zip(summary["per_root"], runner.rows):
        assert all(old[k] == v for k, v in own.items())
        cc = {key: value for key, value in old["classification_counts"].items() if value}
        exp = {kind: counts[(own["root"], kind)] for kind in ["closed_numeric_at_tau", "exception"] if counts[(own["root"], kind)]}
        rc = sum(row["root"] == own["root"] for row in result["reflection"])
        if rc: exp["reflection_ordered_half_exclusions"] = rc
        assert cc == exp
    assert runner.contracts == summary["all70_ready_contracts"]
    assert literal_bytes == summary["source_budget"]["exception_73_decimal_integer_literal_payload_bytes"]
    return {"all_numeric_rows_equal": len(source), "all_exception_complete_36_pair_rows_equal": cursor,
        "numeric_uncompressed_canonical_sha256": numeric_hash,
        "exception_uncompressed_canonical_sha256": exception_hash,
        "exception_73_decimal_integer_literal_payload_bytes": literal_bytes,
        "all_nested_and_root_provenance_equal": True, "all_fixed_witness_payload_and_semantic_hashes_equal": True,
        "all_source_branch_paths_equal": True}


def compare_root_payments(result, summary):
    model = result["model"]
    baseline = json.loads(A_RECEIPT.read_text(encoding="utf-8"))
    source_guards = {(row["gap"], row["lo"], row["hi"]): row for row in baseline["all_original_WZ_guards"]}
    assert len(source_guards) == 160
    expected = []
    sep, B, c, tau = F(17, 20), F(sum(model["BS"]), 10**20), F(ORIGINAL, 10**20), F(TAU, 10**20)
    assert all(b > 0 for b in model["BS"]) and all(a > 0 for i, j, a, _ in model["TS"])
    used = set()
    for r, cov in enumerate(model["COV"]):
        for low, high, good in cov:
            if not good: continue
            key = (r, low, high); used.add(key); row = source_guards[key]
            coefficient = [a for i, j, a, _ in model["TS"] if (i, j) == (r, r+1)]
            assert coefficient == [row["adjacent_coefficient"]]
            assert row["left_cN_times_SW"] == ORIGINAL * 10**13
            assert row["right_a_times_WZ"] == coefficient[0] * row["WZ"]
            assert row["margin"] == row["right_a_times_WZ"] - row["left_cN_times_SW"] >= 0
            expected.append({"kind": "original_true_COV_plus_pressure", "gap": r, "lo": low, "hi": high,
                "original_WZ_guard_margin": row["margin"], "lower_bound": str(c+sep*B),
                "margin_over_tau": str(c+sep*B-tau), "passed": True})
        tail = F(model["BS"][r]*model["SMAX"][r], 10**20*32768) + sep*(B-F(model["BS"][r], 10**20))
        expected.append({"kind": "pressure_tail", "gap": r, "SMAX": model["SMAX"][r],
            "lower_bound": str(tail), "margin_over_tau": str(tail-tau), "same_gap_pressure_counted_once": True, "passed": True})
        expected.append({"kind": "small_gap_disjoint_from_separation", "gap": r,
            "small_gap_upper": "1/2", "separation": "17/20", "passed": True})
    assert used == set(source_guards) and len(expected) == 176
    actual = json.loads((PRODUCER / "root-outside-payments.json").read_text(encoding="utf-8"))
    assert actual["rows"] == expected
    assert actual["sum_pressure_B"] == str(B) and actual["true_COV_common_lower_bound"] == str(c+sep*B)
    assert actual["new_WZ_evaluations"] == 0 and actual["all_raised_root_outside_payments_passed"] is True
    assert summary["root_outside_payments_sha256"] == pin(PRODUCER / "root-outside-payments.json")["sha256"]
    return {"all_original_true_COV_rows_equal": 160, "all_pressure_tails_equal": 8,
        "all_small_gap_empty_cases_equal": 8, "new_WZ_evaluations": 0,
        "all176_rows_exactly_equal": True, "all_raised_payments_passed": True}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--execute-fixed-independent-review", action="store_true", required=True)
    ap.parse_args()
    assert __debug__
    assert not any((HERE / name).exists() for name in ["independent-started.json", "independent-review.json", "independent-failure.json"])
    begun = time.monotonic()
    before, manifest = input_closure()
    dump_new(HERE / "independent-started.json", {"scope": "One independently implemented fixed Stage B classification review",
        "pid": os.getpid(), "time_unix": time.time(), "inputs_sha256": before,
        "producer_manifest_sha256": PRODUCER_MANIFEST_SHA,
        "fixed_tau": str(F(TAU, 10**20)), "resource_limits": {"seconds": MAX_SECONDS, "output_bytes": MAX_OUTPUT_BYTES}})
    try:
        own = load_own_A()
        result = classify_all(own)
        summary = json.loads((PRODUCER / "classification.json").read_text(encoding="utf-8"))
        assert summary["passed"] is True and summary["classification_passes"] == 1
        assert summary["original_cN"] == ORIGINAL and summary["tau_numerator"] == TAU
        assert summary["integer_debit"] == str(DEBIT)
        assert summary["threshold_AST_identity"]["original_printed_Nat_ble_AST_sha256"] == sha256(canon(result["model"]["margin_tree"])).hexdigest()
        assert summary["derived_counts"] == dict(result["runner"].count)
        assert summary["ready_contract_counts"] == dict(result["runner"].contract_count)
        assert summary["classification_counts"] == {"closed_numeric_at_tau": result["class_counts"]["closed"],
            "exception": result["class_counts"]["exception"], "reflection_ordered_half_exclusions": result["class_counts"]["reflection"]}
        matches = compare_numeric_and_exception(result, manifest, summary)
        payments = compare_root_payments(result, summary)
        trace_rows, trace_hash = read_archive("all-node-events.jsonl.gz", manifest["archive_integrity"]["trace"])
        assert trace_hash == result["runner"].trace.hexdigest() == summary["canonical_all_node_trace_sha256"]
        assert len(trace_rows) == 27234
        for key in ["exception_pairs_scanned", "new_kernel_queries", "new_witnesses", "optimizer_calls", "Lean_runs"]:
            assert summary[key] == 0
        for key in ["new_separated_floor_proven", "new_joint_floor_proven", "new_unconditional_zero_proportion_proven", "website_submission_ready"]:
            assert summary[key] is False
        budget = summary["source_budget"]
        assert budget["baseline_source_bytes"] == 1818411 and budget["baseline_only_remaining_bytes"] == 181589
        assert budget["complete_source_and_runtime_gate_passed"] is False
        assert all(budget[key] is None for key in ["new_formal_consumer_bytes", "DBM_pair_proof_bytes",
            "new_actual_kernel_bridges_and_wrapper_bytes", "complete_flattened_Lean_source_bytes", "kernel_export_Nano_seconds"])
        after = [pin(ROOT / item["path"]) for item in before]
        assert before == after
        elapsed = time.monotonic() - begun
        assert elapsed <= MAX_SECONDS
        receipt = {"schema": "independent-fixed-record-StageB-classification-review-v1", "passed": True,
            "pid": os.getpid(), "seconds": elapsed, "independent_execution_count": 1,
            "producer_manifest_sha256": PRODUCER_MANIFEST_SHA,
            "inputs_sha256_start": before, "inputs_sha256_end": after,
            "producer_Python_modules_imported": 0,
            "shared_helper": "Only our own frozen independent Stage A implementation and its independent packing decoder",
            "original_cN": ORIGINAL, "fixed_tau_numerator": TAU, "denominator": 10**20,
            "separation": "17/20", "threshold_AST_identity": result["threshold_AST_identity"],
            "derived_counts": dict(result["runner"].count), "ready_contract_counts": dict(result["runner"].contract_count),
            "classification_counts": result["class_counts"], "row_comparison": matches,
            "raised_root_guards": result["raised_root_guards"], "root_payment_comparison": payments,
            "canonical_all_node_trace_sha256": trace_hash, "all_trace_rows_identity_checked": len(trace_rows),
            "complete_geometry_sha256": result["all_geometry_sha256"], "complete_witness_sha256": result["all_witness_sha256"],
            "source_pair_order": [list(p) for p in result["model"]["ALL"]],
            "reversal_coefficient_and_pressure_invariance_checked": True,
            "reversal_all_numeric_geometry_involution_checked": True,
            "closed_boundaries_real_domain_no_sep_rounding": True,
            "all595_reflections_excluded_only_in_ordered_half": True,
            "reflection_energy_payments": 0, "orientation_relaxation_enlarges_outer_cells": True,
            "full_sublevel_cover_scope": "Every arbitrary h>=17/20 with F9(h)<tau is in an exception cell or a reversal; source analytic soundness and reversal theorem are retained dependencies",
            "analytic_LB_PT_WZ_or_Lean_proofs_reproved": False,
            "source_budget": budget,
            "scope": "Independent complete finite classification and closed outer geometry audit; not a pair exclusion or new floor",
            "exception_pairs_scanned": 0, "new_kernel_queries": 0, "new_witnesses": 0,
            "optimizer_calls": 0, "Lean_runs": 0, "new_joint_floor_proven": False,
            "new_unconditional_zero_proportion_proven": False, "website_submission_ready": False}
        dump_new(HERE / "independent-review.json", receipt)
        assert sum(p.stat().st_size for p in HERE.iterdir() if p.is_file()) <= MAX_OUTPUT_BYTES
        print(json.dumps({"passed": True, "seconds": elapsed, "classification_counts": result["class_counts"],
            "receipt": pin(HERE / "independent-review.json")}), flush=True)
    except BaseException as exc:
        dump_new(HERE / "independent-failure.json", {"passed": False, "seconds": time.monotonic()-begun,
            "error": repr(exc), "traceback": traceback.format_exc(), "automatic_retry_allowed": False})
        raise


if __name__ == "__main__":
    main()
