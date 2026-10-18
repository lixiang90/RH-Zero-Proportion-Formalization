"""Prepared independent review of the first fixed E underpaid feasible witness.

No pair/DBM scan, BF, actual energy evaluation, optimizer or Lean.  An allclosed
outcome requires a separate complete replay authorization and is refused here.
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
import sys
import time
import traceback

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
PROD = ROOT / "research-goal-20261018-stageE-floor-dbm"
B = ROOT / "research-goal-20261018-stageB-classification"
OWN_C = ROOT / "research-goal-20261018-stageC-independent"
OWN_C_SHA = "835389ce30ca1ffab2601105f1da51efc69e40b402fab64eedb1816bdb529a5b"
OWN_A = ROOT / "research-goal-20261018-record-baseline-independent/replay_independent.py"
GATE = ROOT / "research-goal-20261016/gates/stageE-margin-dbm-20261018.json"
GATE_SHA = "4c83f5f157c9dba302c712951f681394df4d15e703770eda64b420a124e0c3bf"
PLAN_SHA = "4a33d80c7fb6ace9e589c1e9fd1a945f7d6a91608fdadf2ed30bf23c99166b0f"
CN,TAU,C = 893616123055294719,893916123055294719,893766123055294719
Q,V,R,SA = 32768,10**10,1024,10**20
KAPPA = Q*V*R
THRESHOLD = KAPPA*(TAU-CN)
N = 1187
ORIENTATIONS = ["id/id","id/rev","rev/id","rev/rev"]


def canon(data):
    return (json.dumps(data,sort_keys=True,separators=(",",":"))+"\n").encode("ascii")


def load(path): return json.loads(path.read_text(encoding="utf-8"))


def pin(path):
    raw = path.read_bytes()
    return {"path":path.relative_to(ROOT).as_posix(),"bytes":len(raw),"sha256":sha256(raw).hexdigest()}


def dump_new(name,data):
    with (HERE/name).open("x",encoding="utf-8",newline="\n") as stream:
        json.dump(data,stream,ensure_ascii=True,indent=2)
        stream.write("\n");stream.flush();os.fsync(stream.fileno())


def module(path,name):
    spec = importlib.util.spec_from_file_location(name,path)
    obj = importlib.util.module_from_spec(spec);spec.loader.exec_module(obj)
    return obj


def source_edge(cells,spans,i,j,orientation,eid):
    """Independent lazy decoder for an original, not closed/tightened, DBM edge."""
    assert 0 <= eid < 153
    if eid >= 144:
        gap = eid-144
        return gap+1,gap,-17*Q
    suffix = eid >= 72
    k,lower_bound = divmod(eid-(72 if suffix else 0),2)
    cell = cells[j if suffix else i]
    a,b = spans[k]
    reverse = orientation.split("/")[int(suffix)] == "rev"
    if reverse: a,b = 8-b,8-a
    if suffix: a,b = a+1,b+1
    state = cell["state"]
    lower = (state["L"]+state["A"])[k]
    upper = (state["U"]+state["B"])[k]
    return (b,a,-20*lower) if lower_bound else (a,b,20*upper)


def reported_prefix(model,cells,spans,first_ordinal):
    """Verify only the producer's saved prefix certificates, never find cycles."""
    assert model["all_cases_covered"] is False
    assert model["cases_checked"] == first_ordinal+1
    packet = model["proof_stream"]
    path = ROOT/packet["path"]
    assert pin(path)["sha256"] == packet["sha256"]
    raw = gzip.decompress(path.read_bytes())
    assert len(raw) == packet["uncompressed_bytes"]
    assert sha256(raw).hexdigest() == packet["uncompressed_sha256"]
    assert raw[:5] == b"RZE1\n"
    at,counts = 5,Counter()
    per_orientation = [Counter() for _ in ORIENTATIONS]
    for ordinal in range(first_ordinal+1):
        ori,remainder = divmod(ordinal,N*N)
        i,j = divmod(remainder,N)
        orientation = ORIENTATIONS[ori]
        scalar = int(cells[i]["original_margin"])+int(cells[j]["original_margin"])
        assert at < len(raw)
        tag = raw[at];at += 1
        if tag == 0x40:
            assert scalar >= THRESHOLD
            key = "original_scalar_floors_pay_target"
        elif tag == 0xf0:
            assert scalar < THRESHOLD and ordinal == first_ordinal and at == len(raw)
            key = "underpaid_feasible_case"
        else:
            method,length = tag >> 4,tag & 15
            assert scalar < THRESHOLD and method < 4 and 1 <= length <= 10
            assert at+length <= len(raw)
            ids = list(raw[at:at+length]);at += length
            selected = [source_edge(cells,spans,i,j,orientation,eid) for eid in ids]
            assert all(a[1] == b[0] for a,b in zip(selected,selected[1:]+selected[:1]))
            assert sum(edge[2] for edge in selected) < 0
            if method == 0:
                assert length == 2 and sum(eid < 72 for eid in ids) == 1 and sum(72 <= eid < 144 for eid in ids) == 1
                assert 1 <= min(selected[0][:2]) < max(selected[0][:2]) <= 8
            key = ["underpaid_shared_span_two_edge_conflict",
                "underpaid_prefix_single_state_sep_negative_cycle",
                "underpaid_suffix_single_state_sep_negative_cycle",
                "underpaid_full_BF_negative_cycle"][method]
        counts[key] += 1;per_orientation[ori][key] += 1
    assert at == len(raw) and counts["underpaid_feasible_case"] == 1
    assert dict(counts) == model["counts"]
    assert sum(counts.values()) == model["cases_checked"]
    cycles = sum(v for k,v in counts.items() if k not in ["original_scalar_floors_pay_target","underpaid_feasible_case"])
    assert cycles == model["negative_cycle_records"]
    return {"records_checked":sum(counts.values()),"counts":dict(counts),
        "per_orientation_counts":[dict(c) for c in per_orientation],
        "uncompressed_stream_sha256":sha256(raw).hexdigest(),
        "all_reported_prior_paid_or_strict_cycle_records_verified":True,
        "strict_given_cycle_certificate_checks":cycles,"complete_reported_prefix_EOF_verified":True,
        "scope":"All reported prefix only, not the unprocessed suffix of5,635,876 cases"}


def fixed_feasibility(first,model,cells,spans,own_c):
    i,j = first["prefix_exception_id"],first["suffix_exception_id"]
    assert type(i) is type(j) is int and 0 <= i < N and 0 <= j < N
    orientation = first["orientation"]
    ordinal = ORIENTATIONS.index(orientation)*N*N+i*N+j
    assert first["case_ordinal"] == ordinal
    assert first["prefix_cell"] == cells[i] and first["suffix_cell"] == cells[j]
    mi,mj = int(cells[i]["original_margin"]),int(cells[j]["original_margin"])
    assert first["prefix_M0"] == str(mi) and first["suffix_M0"] == str(mj)
    assert first["sum_M0"] == str(mi+mj) and mi+mj < THRESHOLD
    assert first["payment_threshold"] == str(THRESHOLD)
    assert first["underpayment"] == str(THRESHOLD-mi-mj)
    difference = F(mi+mj-THRESHOLD,KAPPA*SA)
    assert first["sum_original_floor_minus_twice_c"] == str(difference)
    assert model["first_underpaid_feasible_case"] == {key:first[key] for key in
        ["case_ordinal","orientation","prefix_exception_id","suffix_exception_id"]}
    assert model["stopped_at_first_underpaid_relaxed_feasible"] is True and model["all_cases_covered"] is False
    point = first["X_integer_potential"]
    assert len(point) == 10 and all(type(x) is int for x in point) and point[0] == 0
    assert first["X_scale"] == 20*Q and first["positions"] == [str(F(x,20*Q)) for x in point]
    edges = [source_edge(cells,spans,i,j,orientation,k) for k in range(153)]
    # A second independent representation comes from our previously frozen C review.
    assert edges == own_c.all_edges(cells[i],cells[j],spans,orientation)
    rows = []
    for eid,(u,v,bound) in enumerate(edges):
        delta = point[v]-point[u]
        assert delta <= bound
        rows.append({"edge_id":eid,"u":u,"v":v,"bound":bound,"actual_difference":delta,"slack":bound-delta})
    assert first["all153_edges"] == rows and first["all153_edges_verified"] is True
    left,right = orientation.split("/")
    lp,rp = own_c.ordered(point,left=="rev",0),own_c.ordered(point,right=="rev",1)
    assert first["prefix_ordered"] == lp and first["suffix_ordered"] == rp
    holds = lp["ordered_condition_holds"] and rp["ordered_condition_holds"]
    assert first["ordered_conditions_hold"] == holds
    expected = "underpaid_DBM_feasible_ordered_holds" if holds else "underpaid_relaxed_DBM_feasible_ordered_violated"
    assert first["outcome"] == model["outcome"] == expected
    assert first["is_actual_low_energy_or_counterexample"] is False
    return {"case_ordinal":ordinal,"orientation":orientation,"prefix_exception_id":i,"suffix_exception_id":j,
        "Mi":mi,"Mj":mj,"sum_Mi_Mj":mi+mj,"payment_threshold":THRESHOLD,"underpayment":THRESHOLD-mi-mj,
        "sum_original_floors_minus_2c":str(difference),"X_integer_potential":point,
        "all153_source_edges_verified":True,"minimum_edge_slack":min(row["slack"] for row in rows),
        "source_edges_sha256":sha256(canon(edges)).hexdigest(),"prefix_ordered":lp,"suffix_ordered":rp,
        "ordered_conditions_hold":holds,"outcome":expected}


def closure(producer_sha):
    found = {}
    def add(path,expected=None):
        row = pin(path)
        if expected is not None: assert row["sha256"] == expected
        if row["path"] in found: assert found[row["path"]] == row
        found[row["path"]] = row
    add(Path(__file__));add(GATE,GATE_SHA);add(HERE/"plan-files.json",PLAN_SHA)
    for path,expected in [(PROD/"files.json",producer_sha),(OWN_C/"audit-files.json",OWN_C_SHA),
                          (HERE/"plan-files.json",PLAN_SHA)]:
        add(path,expected)
        manifest = load(path)
        for field in ["files","package_files","read_only_dependencies","dependency_files","dependencies",
                      "read_only_existing_references","dependency_manifests"]:
            for row in manifest.get(field,[]):
                assert pin(ROOT/row["path"]) == row,("frozen_dependency",row["path"])
                add(ROOT/row["path"])
    gate = load(GATE)
    assert gate["pair_model_passes_authorized"] == 1 and gate["stop_at_first_underpaid_feasible"] is True
    assert int(gate["c9_numerator"]) == CN and int(gate["tau_numerator"]) == TAU and int(gate["c_numerator"]) == C
    assert int(gate["kappa"]) == KAPPA and int(gate["payment_threshold"]) == THRESHOLD
    assert 2*C == CN+TAU and THRESHOLD == 2*KAPPA*(C-CN)
    assert gate["total_cases"] == 4*N*N and gate["orientations"] == ORIENTATIONS
    assert gate["separation"] == "17/20" and gate["exception_count"] == N
    return sorted(found.values(),key=lambda row:row["path"])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--execute-fixed-first-underpaid-review",action="store_true",required=True)
    ap.add_argument("--producer-manifest-sha256",required=True)
    args = ap.parse_args()
    assert __debug__
    assert not any((HERE/name).exists() for name in ["started.json","independent-review.json","failure.json"])
    # An allclosed outcome cannot enter this witness reviewer or trigger a replay.
    model = load(PROD/"model.json")
    assert model["all_cases_covered"] is False and (PROD/"first-underpaid-feasible.json").exists()
    start = time.monotonic()
    before = closure(args.producer_manifest_sha256)
    assert model == load(PROD/"model.json")
    dump_new("started.json",{"pid":os.getpid(),"time_unix":time.time(),"inputs_sha256":before,
        "producer_manifest_sha256":args.producer_manifest_sha256,
        "scope":"One fixed E first-underpaid feasible review plus given prefix certificate replay; no new pair/solver scan"})
    try:
        terminal,first = load(PROD/"terminal.json"),load(PROD/"first-underpaid-feasible.json")
        assert terminal["exit_code"] == 0 and terminal["limit_stop"] is None and terminal["child_launches"] == 1
        assert model["passed"] and model["model_passes"] == 1 and model["total_cases"] == 4*N*N
        assert model["KAPPA"] == KAPPA and model["SA"] == SA
        assert model["original_c9_numerator"] == CN and model["tau_numerator"] == TAU and model["target_c_numerator"] == C
        assert model["payment_threshold"] == str(THRESHOLD)
        original = load(B/"classification.json")
        spans = [tuple(pair) for pair in original["pair_order_from_source"]]
        cells = []
        with gzip.open(B/"exception-cells.jsonl.gz","rb") as stream:
            for line in stream:
                cell = json.loads(line)
                assert line == canon(cell) and cell["exception_id"] == len(cells) and cell["kind"] == "exception"
                assert cell["coordinate_scale"] == Q and cell["separation"] == "17/20"
                mi = int(cell["original_margin"])
                assert mi >= 0 and mi-THRESHOLD == int(cell["tau_margin"]) < 0
                cells.append(cell)
        assert len(cells) == N
        own_c = module(OWN_C/"review_feasible.py","own_frozen_C_for_E")
        own = module(OWN_A,"own_frozen_A_for_E")
        source = own.load_source()
        assert source["CN"] == CN and source["ALL"] == spans
        witness = fixed_feasibility(first,model,cells,spans,own_c)
        prefix = reported_prefix(model,cells,spans,first["case_ordinal"])
        source_witnesses = [own_c.source_witness(own,source,cells[first[key]])
            for key in ["prefix_exception_id","suffix_exception_id"]]
        assert model["inputs_sha256_start"] == model["inputs_sha256_end"]
        for path,digest in model["inputs_sha256_end"].items(): assert pin(ROOT/path)["sha256"] == digest
        for key in ["new_kernel_queries","new_FS_or_points_or_cuts","optimizer_calls","Lean_runs"]: assert model[key] == 0
        assert model["website_submission_ready"] is False and model["complete_source_gate_passed"] is False
        assert model["complete_source_and_runtime_budget"] == "unknown"
        after = [pin(ROOT/row["path"]) for row in before]
        assert before == after
        result = {"schema":"independent-fixed-E-first-underpaid-result-review-v1","passed":True,
            "pid":os.getpid(),"seconds":time.monotonic()-start,"independent_result_review_executions":1,
            "producer_manifest_sha256":args.producer_manifest_sha256,
            "inputs_sha256_start":before,"inputs_sha256_end":after,"producer_Python_modules_imported":0,
            "exact_Mi_not_Nat_floor_used":True,"payment_threshold_expression":"(32768*10^10*1024)*(tauN-c9N)",
            "fixed_witness":witness,"all_reported_prefix_certificate_checks":prefix,
            "two_original_source_margin_and_FS_checks":source_witnesses,
            "scope":"First underpaid relaxed feasible witness and full reported prefix only, not all5,635,876cases",
            "interpretation":"This fixed scalar-floor plus relaxed DBM rule did not close. If Ordered fails at the given point, neither ordered feasibility nor infeasibility follows. No actual energy was evaluated.",
            "pair_scan_executions":0,"DBM_solver_calls":0,"actual_kernel_values_computed":0,
            "new_points_or_FS_or_tangents":0,"optimizer_calls":0,"Lean_runs":0,
            "complete_source_and_runtime_budget":"unknown","website_submission_ready":False,
            "new_joint_floor_proven":False,"new_unconditional_zero_proportion_proven":False}
        dump_new("independent-review.json",result)
        print(json.dumps({"passed":True,"seconds":result["seconds"],"case_ordinal":witness["case_ordinal"],
            "outcome":witness["outcome"],"prefix_records_checked":prefix["records_checked"],
            "receipt":pin(HERE/"independent-review.json")}),flush=True)
    except BaseException as exc:
        dump_new("failure.json",{"passed":False,"seconds":time.monotonic()-start,"error":repr(exc),
            "traceback":traceback.format_exc(),"automatic_retry_allowed":False})
        raise


if __name__ == "__main__":
    main()
