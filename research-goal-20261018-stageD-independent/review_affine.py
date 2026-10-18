"""Independent evaluation of fixed original-FS affine lines at the fixed C point.

Prepared before producer freeze; no actual kernel evaluation, solver or new point.
All arithmetic is exact Fraction/signed integer arithmetic on existing literals.
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
Q, R, D, V, SA = 32768, 1024, 10**9, 10**10, 10**20
KAPPA = Q*V*R
CN, C = 893616123055294719, 893766123055294719
DEBIT = KAPPA * 300000000000000
EXPECTED_X = [0,557056,1355776,2131556,2724876,3392856,3986176,4635136,6374116,8254976]
GATE = ROOT / "research-goal-20261016/gates/stageD-affine-point-20261018.json"
GATE_SHA = "4c1ba012a8fa5c42aeec686ac3836ac4e747061cd8cea5d97c30c44cd2bcd87e"
OWN_A = ROOT / "research-goal-20261018-record-baseline-independent/replay_independent.py"
OWN_C = ROOT / "research-goal-20261018-stageC-independent"
OWN_C_SHA = "835389ce30ca1ffab2601105f1da51efc69e40b402fab64eedb1816bdb529a5b"
C_PROD = ROOT / "research-goal-20261018-stageC-dbm"
PROD = ROOT / "research-goal-20261018-fixed-joint-affine"


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


def own_module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec); spec.loader.exec_module(result)
    return result


def window_affine(own, model, row, local_gaps):
    assert len(local_gaps) == 8
    runner = own.Replay(model)
    state = (row["state"]["L"]+row["state"]["A"], row["state"]["U"]+row["state"]["B"])
    assert row["state"]["M"] == 0 and runner.hashstate(state) == row["state_sha256"]
    root, position, end = row["root"], row["position"], row["end"]
    raw = (model["dispatch_value"](f"WL{root}", position//Q) >> (position%Q)) & ((1<<480)-1)
    assert raw & 3 == 0
    consumed, original_margin = runner.numeric(state, raw >> 2)
    assert position+2+consumed == end and original_margin == int(row["original_margin"])
    assert original_margin-DEBIT == int(row["tau_margin"]) < 0
    at, word, FS, terms = 0, raw >> 2, [], []
    constant, alpha = F(0), [F(b) for b in model["BS"]]
    scaled_constant, scaled_alpha = 0, [KAPPA*b for b in model["BS"]]
    point_sum, scaled_point_sum = F(0), F(0)
    for index, (i,j,a,slot) in enumerate(model["TS"]):
        L0 = sum(state[0][i:j])
        L, U = runner.bounds(state, i, j)
        assert L0 <= L <= U
        fields, at = runner.decode_term(word, at, L, U)
        FS.append(list(fields))
        kind, mass, p, other = fields
        w1, w2 = runner.weights(kind, mass)
        wc = R-w1-w2
        assert min(w1,w2,wc) >= 0 and w1+w2+wc == R
        fp = [model["point_value"](sample) & ((1<<96)-1) for sample in [p, other]]
        value_words = [z & ((1<<32)-1) for z in fp]
        slope_words = [(z >> 32) & ((1<<32)-1) for z in fp]
        upper_derivative_words = [z >> 64 for z in fp]
        anchors = [p, other]
        guards = []
        for weight, anchor in zip([w1,w2], anchors):
            if weight:
                actual = model["point_value"](anchor)
                valid_lower, valid_upper = (actual >> 96) & ((1<<24)-1), actual >> 120
                assert L0 <= L <= anchor <= U and 1 <= valid_upper and valid_lower <= L <= anchor <= U <= valid_upper
                guards.append({"mass":weight,"original_point":anchor,"valid_lower":valid_lower,
                    "valid_upper":valid_upper,"guard_passed":True})
        distances = [max(sample-L0, 0) for sample in anchors]
        cp = sum(weight*max(signed-2*D,0)*dist for weight,signed,dist in zip([w1,w2],upper_derivative_words,distances))
        cn = sum(weight*max(2*D-signed,0)*dist for weight,signed,dist in zip([w1,w2],upper_derivative_words,distances))
        msl = w1*slope_words[0]+w2*slope_words[1]
        mw = w1+w2
        lb = runner.lower_bound(L,max(U,L+1))
        mv = wc*lb+w1*value_words[0]+w2*value_words[1]
        delta = msl-2*D*mw
        sigma = F(delta,D*R)
        beta = F(mv,V*R)+F(cp-cn,Q*D*R)-sigma*F(L0,Q)
        int_constant = Q*mv+10*(cp-cn)-10*delta*L0
        int_slope = 10*Q*delta
        assert beta == F(int_constant,KAPPA) and sigma == F(int_slope,KAPPA)
        span = sum(local_gaps[i:j],F(0))
        assert F(L,Q) <= span <= F(U,Q)
        ell = beta+sigma*span
        scaled = F(Q*mv+10*(cp-cn))+10*delta*(Q*span-L0)
        assert KAPPA*ell == scaled == int_constant+int_slope*span
        constant += a*beta
        scaled_constant += a*int_constant
        for gap in range(i,j):
            alpha[gap] += a*sigma
            scaled_alpha[gap] += a*int_slope
        point_sum += a*ell
        scaled_point_sum += a*scaled
        terms.append({"index": index,"i":i,"j":j,"a":a,"slot":slot,
            "L0":L0,"L":L,"U":U,"Uc":max(U,L+1),"FS":list(fields),
            "weights":[wc,w1,w2],"lb":lb,"mv":mv,"cp":cp,"cn":cn,"msl":msl,"mw":mw,
            "active_mokI_guards":guards,
            "signed_delta":delta,"beta":str(beta),"sigma":str(sigma),
            "signed_scaled_constant":int_constant,"signed_scaled_slope":int_slope,
            "span_at_existing_point":str(span),"line_at_existing_point":str(ell),
            "scaled_line_at_existing_point":str(scaled)})
    P,S,Cp,Cm,used = runner.flow(state,word,at)
    assert consumed == used
    semantic = {"FS":FS,"P":P,"S":S,"Cp":Cp,"Cm":Cm,"consumed_bits":used}
    assert sha256(canon(semantic)).hexdigest() == row["witness"]["decoded_semantic_sha256"]
    assert sha256(canon({"bits":used,"value":str(word & ((1<<used)-1))})).hexdigest() == row["witness"]["packed_payload_sha256"]
    pressure = sum((b*h for b,h in zip(model["BS"],local_gaps)),F(0))
    A = (pressure+point_sum)/SA
    A_scaled = (KAPPA*pressure+scaled_point_sum)/(SA*KAPPA)
    A_coeff = (constant+sum((a*h for a,h in zip(alpha,local_gaps)),F(0)))/SA
    assert A == A_scaled == A_coeff
    assert constant*KAPPA == scaled_constant and all(a*KAPPA == b for a,b in zip(alpha,scaled_alpha))
    gamma = [a//(10*Q) for a in scaled_alpha]
    assert all(a == g*10*Q for a,g in zip(scaled_alpha,gamma))
    penalty = sum((state[1][r]-state[0][r])*max(P[r]-S[r]-gamma[r],0) for r in range(8))
    base = V*R*sum(b*l for b,l in zip(model["BS"],state[0][:8]))
    base += Q*sum(t["a"]*t["mv"] for t in terms)+10*sum(t["a"]*(t["cp"]-t["cn"]) for t in terms)
    certified = base+10*(Cm-Cp-penalty)
    assert certified-KAPPA*CN == original_margin
    certfloor = F(certified,SA*KAPPA)
    assert A >= certfloor >= F(CN,SA)
    flow_at_point = sum((P[r]-S[r])*(Q*local_gaps[r]-state[0][r]) for r in range(8))
    assert flow_at_point >= Cm-Cp
    return {"exception_id":row["exception_id"],"root":root,"position":position,"end":end,
        "original_margin":str(original_margin),"tau_margin":str(original_margin-DEBIT),
        "source_state_sha256":row["state_sha256"],"source_witness":row["witness"],
        "local_gaps":[str(h) for h in local_gaps],"terms":terms,"term_count":len(terms),
        "affine_constant":str(constant/SA),"affine_coefficients":[str(a/SA) for a in alpha],
        "scaled_constant_numerator":scaled_constant,"scaled_coefficient_numerators":scaled_alpha,
        "common_physical_denominator":SA*KAPPA,
        "pressure_at_existing_point":str(pressure/SA),"A_at_existing_point":str(A),
        "A_minus_c9":str(A-F(CN,SA)),"all_beta_sigma_vs_signed_scale_termwise_equal":True,
        "original_flow":{"P":P,"S":S,"Cp":Cp,"Cm":Cm,"consumed_bits":used,
            "gamma_scaled":gamma,"box_penalty":penalty,"certified_numerator":str(certified),
            "certified_denominator":SA*KAPPA,"certified_affine_floor":str(certfloor),
            "flow_linear_value_at_fixed_point":str(flow_at_point),"flow_lower_bound":Cm-Cp,
            "original_c9_floor_certificate_reproduced":True}}


def nine_gap_embedding(left,right,gaps):
    assert len(gaps) == 9
    constant = F(left["affine_constant"])+F(right["affine_constant"])
    gamma = [F(0) for _ in range(9)]
    for offset,row in [(0,left),(1,right)]:
        for k,coefficient in enumerate(row["affine_coefficients"]):
            gamma[offset+k] += F(coefficient)
    embedded = constant+sum((a*g for a,g in zip(gamma,gaps)),F(0))
    A_L,A_R = F(left["A_at_existing_point"]),F(right["A_at_existing_point"])
    assert embedded == A_L+A_R
    c9,target = F(CN,SA),F(2*C,SA)
    clipped = max(c9,A_L)+max(c9,A_R)
    return {"constant":str(constant),"coefficients":[str(g) for g in gamma],
        "physical_nine_gaps":[str(h) for h in gaps],"A_left":str(A_L),"A_right":str(A_R),
        "sum":str(embedded),"target_2c":str(target),"sum_minus_2c":str(embedded-target),
        "c9":str(c9),"clipped_sum":str(clipped),"clipped_sum_minus_2c":str(clipped-target),
        "baseline_clipping_changes_neither_value":A_L>=c9 and A_R>=c9,
        "nine_gap_embedding_equals_two_original_window_evaluations":True}


def compare_windows(windows, producer, joint):
    assert len(windows) == len(producer["windows"]) == 2
    compared = 0
    for offset, (own, old) in enumerate(zip(windows,producer["windows"])):
        assert old["offset"] == offset and len(own["terms"]) == len(old["terms"]) == 34
        for term, saved in zip(own["terms"],old["terms"]):
            expected = {"term_id":term["index"],"edge":[term["i"],term["j"]],
                "external_weight_numerator":term["a"],"external_weight_denominator":SA,
                "original_term_bounds":[term["L"],term["U"]],"uc_upper":term["Uc"],
                "original_L0":term["L0"],"FS":term["FS"],
                "mass_constant":term["weights"][0],"mass_first":term["weights"][1],"mass_second":term["weights"][2],
                "original_lb_table_value":term["lb"],"active_mokI_guards":term["active_mokI_guards"],
                "mvT":term["mv"],"mslT":term["msl"],"mwT":term["mw"],"mcpT":term["cp"],"mcnT":term["cn"],
                "beta":term["beta"],"sigma":term["sigma"],"span_at_fixed_point":term["span_at_existing_point"],
                "affine_value":term["line_at_existing_point"],"direct_scaled_numerator":term["scaled_line_at_existing_point"],
                "weighted_value":str(F(term["a"],SA)*F(term["line_at_existing_point"]))}
            assert saved == expected, ("fixed_term_row",offset,term["index"])
            compared += 1
        coefficients = ["0"]*9
        coefficients[offset:offset+8] = own["affine_coefficients"]
        assert old["global9_affine_constant"] == own["affine_constant"]
        assert old["global9_gap_coefficients"] == coefficients
        assert old["pressure_at_fixed_point"] == own["pressure_at_existing_point"]
        assert old["affine_value_at_fixed_point"] == own["A_at_existing_point"]
        assert F(old["whole_direct_scaled_numerator"]) == F(own["A_at_existing_point"])*SA*KAPPA
        assert old["whole_direct_denominator"] == SA*KAPPA
        assert old["original_compact_margin"] == old["original_printed_AST_margin"] == own["original_margin"]
        assert old["original_tau_debit_margin"] == own["tau_margin"]
        assert old["original_flow"] == own["original_flow"]
        assert old["all_beta_vs_direct_scaled_values_equal"] is True
        assert old["flows_not_added_to_definition_of_affine_value"] is True
        assert old["new_kernel_or_point_queries"] == 0
    assert producer["combined_constant"] == joint["constant"]
    assert producer["combined_9_gap_coefficients"] == joint["coefficients"]
    for old,new in [("left_affine_value","A_left"),("right_affine_value","A_right"),
        ("sum_affine_values","sum"),("target_twice_c","target_2c"),("sum_minus_twice_c","sum_minus_2c"),
        ("baseline_c9","c9"),("sum_clipped_affine_values","clipped_sum"),("clipped_sum_minus_twice_c","clipped_sum_minus_2c")]:
        assert producer[old] == joint[new], ("joint_value_identity",old)
    assert producer["clipped_left_affine_value"] == str(max(F(CN,SA),F(joint["A_left"])))
    assert producer["clipped_right_affine_value"] == str(max(F(CN,SA),F(joint["A_right"])))
    assert producer["fixed_joint_affine_model_obstructed_at_this_point"] == (F(joint["sum_minus_2c"]) < 0)
    assert producer["fixed_joint_affine_plus_baseline_model_obstructed_at_this_point"] == (F(joint["clipped_sum_minus_2c"]) < 0)
    return {"all68_fixed_term_rows_equal":compared,"all_beta_sigma_signed_scale_and_embedding_identities_equal":True,
        "all_original_flow_and_main_margin_values_equal":True,"all_joint_and_clipped_values_equal":True}


def closure(producer_sha):
    found = {}
    def add(path, expected=None):
        row = pin(path)
        if expected is not None: assert row["sha256"] == expected
        if row["path"] in found: assert found[row["path"]] == row
        found[row["path"]] = row
    add(Path(__file__)); add(GATE,GATE_SHA)
    for path, expected in [(PROD/"files.json",producer_sha),(OWN_C/"audit-files.json",OWN_C_SHA)]:
        add(path,expected)
        m = load(path)
        for field in ["files","package_files","read_only_dependencies","dependency_files","dependencies","read_only_existing_references"]:
            for row in m.get(field,[]):
                assert pin(ROOT/row["path"]) == row, ("dependency_pin",row["path"])
                add(ROOT/row["path"])
    gate = load(GATE)
    assert gate["affine_evaluations_authorized"] == 1 and gate["expected_X"] == EXPECTED_X
    assert gate["case_ordinal"] == 1 and gate["orientation"] == "id/id"
    assert gate["X_scale"] == 20*Q and int(gate["c_numerator"]) == C
    assert int(gate["baseline_c9_numerator"]) == CN and int(gate["denominator"]) == SA
    assert gate["resource_limits"] == {"elapsed_seconds":60,"closed_output_bytes":8000000}
    assert pin(ROOT/gate["source_static_manifest_path"])["sha256"] == gate["source_static_manifest_sha256"]
    assert load(OWN_C/"independent-review.json")["first_feasible_with_both_actual_ordered_conditions_independently_verified"] is True
    return sorted(found.values(),key=lambda row:row["path"])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--execute-fixed-review",action="store_true",required=True)
    ap.add_argument("--producer-manifest-sha256",required=True)
    args = ap.parse_args()
    assert __debug__ and not any((HERE/name).exists() for name in ["started.json","independent-review.json","failure.json"])
    start = time.monotonic()
    before = closure(args.producer_manifest_sha256)
    dump_new("started.json",{"pid":os.getpid(),"time_unix":time.time(),"inputs_sha256":before,
        "producer_manifest_sha256":args.producer_manifest_sha256,"scope":"One fixed existing-point affine result review, no actual kernel or optimization"})
    try:
        producer, terminal = load(PROD/"evaluation.json"),load(PROD/"terminal.json")
        assert producer["passed"] and producer["arithmetic_passes"] == 1
        assert terminal["exit_code"] == 0 and terminal["limit_stop"] is None and terminal["child_launches"] == 1
        first = load(C_PROD/"first-feasible.json")
        assert first["case_ordinal"] == 1 and first["orientation"] == "id/id"
        assert first["X_integer_potential"] == EXPECTED_X and first["X_scale"] == 20*Q
        own_c = own_module(OWN_C/"review_feasible.py","own_frozen_C")
        own = own_module(OWN_A,"own_frozen_A")
        model = own.load_source()
        assert model["CN"] == CN
        cells = []
        with gzip.open(ROOT/"research-goal-20261018-stageB-classification/exception-cells.jsonl.gz","rb") as stream:
            for line in stream:
                row = json.loads(line)
                assert line == canon(row) and row["exception_id"] == len(cells)
                cells.append(row)
        assert len(cells) == 1187
        feasibility = own_c.verify_feasible(first,load(C_PROD/"scan.json"),cells,model["ALL"])
        assert feasibility["ordered_conditions_hold"] is True
        gaps = [F(EXPECTED_X[k+1]-EXPECTED_X[k],20*Q) for k in range(9)]
        assert all(h>=F(17,20) for h in gaps) and gaps[0]<=gaps[7] and gaps[1]<=gaps[8]
        windows = [window_affine(own,model,cells[0],gaps[:8]),window_affine(own,model,cells[1],gaps[1:])]
        assert producer["windows"][0]["original_cell"] == cells[0] and producer["windows"][1]["original_cell"] == cells[1]
        joint = nine_gap_embedding(*windows,gaps)
        compared = compare_windows(windows,producer,joint)
        assert producer["fixed_9_gap_values"] == [str(h) for h in gaps]
        assert producer["scales"] == {"Q":Q,"R":R,"D":D,"V":V,"SA":SA,"KAPPA":KAPPA,"K":KAPPA*SA}
        assert producer["target_c_numerator"] == C and producer["target_c_denominator"] == SA
        assert producer["inputs_sha256_start"] == producer["inputs_sha256_end"]
        for path,digest in producer["inputs_sha256_end"].items(): assert pin(ROOT/path)["sha256"] == digest
        for key in ["actual_kernel_values_computed","new_point_or_tangent_queries","optimizer_calls","Lean_runs"]:
            assert producer[key] == 0
        assert producer["website_submission_ready"] is False
        after = [pin(ROOT/row["path"]) for row in before]
        assert before == after
        elapsed = time.monotonic()-start
        assert elapsed <= 60
        result = {"schema":"independent-fixed-original-FS-affine-point-review-v1","passed":True,
            "pid":os.getpid(),"seconds":elapsed,"independent_review_executions":1,
            "producer_manifest_sha256":args.producer_manifest_sha256,"inputs_sha256_start":before,"inputs_sha256_end":after,
            "producer_Python_modules_imported":0,"existing_X_integer_potential":EXPECTED_X,"X_scale":20*Q,
            "window_affine_models":windows,"nine_gap_joint_model":joint,"row_comparison":compared,
            "all153_original_bounds_and_both_ordered_conditions_rechecked":True,
            "point_feasibility_review":feasibility,
            "same_original_FS_and_original_states_preserved":True,
            "interpretation":"Fixed affine value at one already valid point; positivity does not certify the whole joint cell, negativity would obstruct only these lower models, not actual energy",
            "actual_kernel_values_computed":0,"new_point_or_tangent_queries":0,"optimizer_calls":0,"DBM_solver_calls":0,"Lean_runs":0,
            "new_joint_floor_proven":False,"new_unconditional_zero_proportion_proven":False,
            "complete_source_and_runtime_budget":"unknown","website_submission_ready":False}
        dump_new("independent-review.json",result)
        assert sum(p.stat().st_size for p in HERE.iterdir() if p.is_file()) <= 8000000
        print(json.dumps({"passed":True,"seconds":elapsed,"sum_minus_2c":joint["sum_minus_2c"],
            "clipped_sum_minus_2c":joint["clipped_sum_minus_2c"],"receipt":pin(HERE/"independent-review.json")}),flush=True)
    except BaseException as exc:
        dump_new("failure.json",{"passed":False,"seconds":time.monotonic()-start,"error":repr(exc),
            "traceback":traceback.format_exc(),"automatic_retry_allowed":False})
        raise


if __name__ == "__main__":
    main()
