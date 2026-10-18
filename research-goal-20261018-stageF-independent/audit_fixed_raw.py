"""Independent source-FS rebuild and original raw-dual audit for fixed F failure.

Standard library only. No producer import, Sympy, LP, repaired point/sign, new
kernel value or Lean. The original invalid primal is retained as invalid.
"""
from fractions import Fraction as F
from hashlib import sha256
from math import lcm
import argparse
import gzip
import importlib.util
import json
import os
from pathlib import Path
import sys
import time
import traceback

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
PROD=ROOT/"research-goal-20261018-stageF-exact-lp"
OWN_D=ROOT/"research-goal-20261018-stageD-independent"
OWN_D_SHA="228105f6ff207a9f89f5bb4341af81f5b84568517063f5bd6d3bfb3f0afe5000"
OWN_A=ROOT/"research-goal-20261018-record-baseline-independent/replay_independent.py"
GATE=ROOT/"research-goal-20261016/gates/stageF-exact-lp-20261018.json"
GATE_SHA="02015ab778511ce8ae424e488ce95ee28f4e34990e96aa5db8c0f4608c76a90d"
Q,R,D,V,SA=32768,1024,10**9,10**10,10**20
KAPPA=Q*V*R
CN,C=893616123055294719,893766123055294719
TARGET=4*KAPPA*C


def canon(x):return (json.dumps(x,sort_keys=True,separators=(",",":"))+"\n").encode("ascii")
def load(path):return json.loads(path.read_text(encoding="utf-8"))
def dot(a,b):return sum((x*y for x,y in zip(a,b)),F(0))
def pin(path):
    raw=path.read_bytes()
    return {"path":path.relative_to(ROOT).as_posix(),"bytes":len(raw),"sha256":sha256(raw).hexdigest()}
def dump_new(name,data):
    with (HERE/name).open("x",encoding="utf-8",newline="\n") as stream:
        json.dump(data,stream,ensure_ascii=True,indent=2);stream.write("\n");stream.flush();os.fsync(stream.fileno())
def module(path,name):
    spec=importlib.util.spec_from_file_location(name,path)
    obj=importlib.util.module_from_spec(spec);spec.loader.exec_module(obj);return obj
def integer(x):
    x=F(x);assert x.denominator==1;return x.numerator


def source_rebuild():
    own=module(OWN_A,"own_frozen_A_for_F")
    affine=module(OWN_D/"review_affine.py","own_frozen_D_for_F")
    source=own.load_source();assert source["CN"]==CN
    cells=[]
    with gzip.open(ROOT/"research-goal-20261018-stageB-classification/exception-cells.jsonl.gz","rb") as stream:
        for line in stream:
            row=json.loads(line);assert line==canon(row) and row["exception_id"]==len(cells);cells.append(row)
    assert len(cells)==1187
    point=load(ROOT/"research-goal-20261018-stageE-floor-dbm/first-underpaid-feasible.json")
    assert point["case_ordinal"]==1192 and point["orientation"]=="id/id"
    assert point["prefix_cell"]==cells[1] and point["suffix_cell"]==cells[5]
    X=point["X_integer_potential"];assert point["X_scale"]==20*Q
    gaps=[F(X[r+1]-X[r],20*Q) for r in range(9)]
    windows=[affine.window_affine(own,source,cells[1],gaps[:8]),affine.window_affine(own,source,cells[5],gaps[1:])]
    joint=affine.nine_gap_embedding(*windows,gaps)
    constant=2*sum(w["scaled_constant_numerator"] for w in windows)
    gap_coeff=[0]*9
    for offset,w in enumerate(windows):
        for r,coef in enumerate(w["scaled_coefficient_numerators"]):
            gap_coeff[offset+r]+=integer(F(coef,10*Q))
    direct_const,direct_gap=0,[0]*9
    for offset,w in enumerate(windows):
        for r,b in enumerate(source["BS"]):direct_gap[offset+r]+=D*R*b
        for t in w["terms"]:
            delta=t["msl"]-2*D*t["mw"]
            direct_const+=2*Q*t["a"]*t["mv"]+20*t["a"]*(t["cp"]-t["cn"]-delta*t["L0"])
            for r in range(t["i"],t["j"]):direct_gap[offset+r]+=t["a"]*delta
    assert constant==direct_const and gap_coeff==direct_gap
    b=[0]*10
    for r,g in enumerate(gap_coeff):b[r]-=g;b[r+1]+=g
    assert sum(b)==0
    assert constant==2*SA*KAPPA*F(joint["constant"])
    assert constant+dot(b,X)==2*SA*KAPPA*F(joint["sum"])
    rows=[]
    def add(a,d,kind,meta):
        assert len(a)==10 and sum(a)==0 and all(type(v) is int for v in a)
        rows.append({"row_id":len(rows),"coefficients":a,"rhs":d,"kind":kind,**meta})
    for offset,cell in [(0,cells[1]),(1,cells[5])]:
        state=cell["state"];lower=state["L"]+state["A"];upper=state["U"]+state["B"]
        for k,(i,j) in enumerate(source["ALL"]):
            a=[0]*10;a[offset+i]=-1;a[offset+j]=1
            meta={"offset":offset,"original_span_index":k,"original_span":[i,j]}
            add(a,20*upper[k],"original_upper",meta)
            add([-v for v in a],-20*lower[k],"original_lower",meta)
    for r in range(9):
        a=[0]*10;a[r]=1;a[r+1]=-1
        add(a,-17*Q,"original_separation",{"gap":r})
    for offset in [0,1]:
        a=[0]*10
        for r,sign in [(0,-1),(1,1),(7,1),(8,-1)]:a[offset+r]+=sign
        add(a,0,"true_ordered_four_point",{"offset":offset})
    assert len(rows)==155
    for k,edge in enumerate(point["all153_edges"]):
        a=[0]*10;a[edge["u"]]-=1;a[edge["v"]]+=1
        assert rows[k]["coefficients"]==a and rows[k]["rhs"]==edge["bound"]
    return affine,windows,joint,rows,constant,b,gap_coeff


def compare_model(affine,windows,joint,rows,constant,b,gap_coeff):
    saved=load(PROD/"model.json")
    components=load(PROD/"affine-components.json")
    assert saved["rows"]==rows
    assert saved["constant"]==str(constant) and saved["position_coefficients"]==list(map(str,b))
    assert saved["gap_coefficients"]==list(map(str,gap_coeff)) and saved["target"]==str(TARGET)
    assert saved["original_pair"]=={"prefix_exception_id":1,"suffix_exception_id":5,"orientation":"id/id"}
    assert saved["scales"]=={"Q":Q,"R":R,"D":D,"V":V,"SA":SA,"KAPPA":KAPPA}
    assert saved["source_sha256"]=="f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf"
    assert saved["target_c_numerator"]==C and saved["denominator"]==SA
    assert saved["gauge_X0"]==0 and saved["variable_count_after_gauge"]==9
    assert saved["affine_components_sha256"]==pin(PROD/"affine-components.json")["sha256"]
    original=load(ROOT/"research-goal-20261018-stageE-floor-dbm/first-underpaid-feasible.json")
    assert components["windows"][0]["original_cell"]==original["prefix_cell"]
    assert components["windows"][1]["original_cell"]==original["suffix_cell"]
    assert components["source_affine_engine_sha256"]==saved["original_affine_engine_sha256"]
    # Check every original term/flow via our already frozen independent D comparator.
    # The global fields below come from the actual saved F coefficients/components.
    vals=[F(w["affine_value_at_fixed_point"]) for w in components["windows"]]
    clipped=[max(F(CN,SA),v) for v in vals]
    view={"windows":components["windows"],"combined_constant":str(F(int(saved["constant"]),2*SA*KAPPA)),
        "combined_9_gap_coefficients":[str(F(int(x)*20*Q,2*SA*KAPPA)) for x in saved["gap_coefficients"]],
        "left_affine_value":str(vals[0]),"right_affine_value":str(vals[1]),"sum_affine_values":str(sum(vals)),
        "target_twice_c":str(F(int(saved["target"]),2*SA*KAPPA)),"sum_minus_twice_c":str(sum(vals)-F(2*C,SA)),
        "baseline_c9":str(F(CN,SA)),"clipped_left_affine_value":str(clipped[0]),"clipped_right_affine_value":str(clipped[1]),
        "sum_clipped_affine_values":str(sum(clipped)),"clipped_sum_minus_twice_c":str(sum(clipped)-F(2*C,SA)),
        "fixed_joint_affine_model_obstructed_at_this_point":sum(vals)<F(2*C,SA),
        "fixed_joint_affine_plus_baseline_model_obstructed_at_this_point":sum(clipped)<F(2*C,SA)}
    checks=affine.compare_windows(windows,view,joint)
    return {"all155_source_rows_equal_saved_model":True,"all_source_C_b_gapcoeff_target_equal_saved_model":True,
        "all68_source_term_and_original_flow_rows_equal":checks["all68_fixed_term_rows_equal"],
        "source_row_sha256":sha256(canon(rows)).hexdigest(),
        "objective_sha256":sha256(canon({"C":constant,"b":b,"gap":gap_coeff,"target":TARGET})).hexdigest()}


def raw_audit(rows,constant,b):
    raw=load(PROD/"primary-raw-result.json")
    point=[F(0)]+list(map(F,raw["primal"]))
    mu=list(map(F,raw["dual"]));o=F(raw["objective"])
    assert len(point)==10 and len(mu)==155
    violations=[]
    for row in rows:
        value=dot(row["coefficients"],point)
        if value>row["rhs"]:
            violations.append({"row_id":row["row_id"],"kind":row["kind"],"lhs":str(value),
                "rhs":str(F(row["rhs"])),"strict_violation":str(value-row["rhs"])})
    negatives=[i for i,x in enumerate(mu) if x<0]
    balance=[F(b[k])+sum((m*row["coefficients"][k] for m,row in zip(mu,rows)),F(0)) for k in range(10)]
    cost=sum((m*row["rhs"] for m,row in zip(mu,rows)),F(0))
    lower=constant-cost
    valid=not negatives and balance==[0]*10
    paid=valid and lower>=TARGET
    certificate=None
    if paid:
        den=lcm(*(m.denominator for m in mu))
        weights=[integer(m*den) for m in mu]
        assert all(n>=0 for n in weights)
        assert all(den*b[k]+sum(n*row["coefficients"][k] for n,row in zip(weights,rows))==0 for k in range(10))
        integer_lower=den*constant-sum(n*row["rhs"] for n,row in zip(weights,rows))
        assert integer_lower>=den*TARGET
        support=[i for i,n in enumerate(weights) if n]
        certificate={"kind":"Lower","origin":"The entire original raw dual unchanged; exact common denominator, zero entries omitted only",
            "row_ids":support,"integer_weights":[str(weights[i]) for i in support],"common_denominator":str(den),
            "weighted_integer_lower_bound":str(integer_lower),"weighted_integer_target":str(den*TARGET),
            "weighted_integer_surplus":str(integer_lower-den*TARGET),"exact_lower_bound":str(lower),
            "exact_lower_minus_target":str(lower-TARGET),"support_count":len(support),
            "full10_balance_and_nonnegative_weights_verified":True,"primal_optimality_claimed":False,
            "original_raw_result_sha256":pin(PROD/"primary-raw-result.json")["sha256"],
            "source_rows_sha256":sha256(canon(rows)).hexdigest(),
            "source_objective_sha256":sha256(canon({"C":constant,"b":b,"target":TARGET})).hexdigest()}
    return {"original_raw_point":list(map(str,point)),"all155_primal_rows_feasible":not violations,
        "primal_violated_rows":violations,"primal_violated_row_count":len(violations),
        "all_raw_dual_weights_nonnegative":not negatives,"negative_dual_weight_indices":negatives,
        "full10_b_plus_muA":list(map(str,balance)),"full10_dual_balance_zero":balance==[0]*10,
        "raw_dual_rhs_cost":str(cost),"raw_dual_lower_bound":str(lower),"target":str(TARGET),
        "raw_dual_lower_minus_target":str(lower-TARGET),"raw_dual_is_valid_lower_certificate":paid,
        "raw_primal_objective_without_constant":str(dot(b,point)),"solver_reported_objective":str(o),
        "raw_objective_matches_bX":o==dot(b,point),
        "raw_primal_full_value_minus_dual_lower":str(constant+dot(b,point)-lower),
        "raw_dual_support_count":sum(m!=0 for m in mu),"raw_dual":list(map(str,mu)),
        "primal_invalid_preserved":bool(violations),"no_optimum_claim":True},certificate


def closure(manifest_name,manifest_sha):
    refs={}
    def add(path,expected=None):
        row=pin(path)
        if expected is not None:assert row["sha256"]==expected
        if row["path"] in refs:assert refs[row["path"]]==row
        refs[row["path"]]=row
    add(Path(__file__));add(GATE,GATE_SHA)
    p=PROD/manifest_name
    assert p.parent==PROD and p.name==manifest_name
    for path,expected in [(p,manifest_sha),(OWN_D/"audit-files.json",OWN_D_SHA)]:
        add(path,expected);manifest=load(path)
        for key in ["files","package_files","read_only_dependencies","dependency_files","dependencies","read_only_existing_references"]:
            for row in manifest.get(key,[]):
                assert pin(ROOT/row["path"])==row;add(ROOT/row["path"])
    gate=load(GATE)
    assert gate["primary_simplex_calls_authorized"]==1 and gate["max_simplex_calls"]==2
    assert gate["prefix_exception_id"]==1 and gate["suffix_exception_id"]==5 and gate["orientation"]=="id/id"
    assert int(gate["c_numerator"])==C and int(gate["kappa"])==KAPPA
    runtime=gate["runtime_read_only"];raw=Path(runtime["path"]).read_bytes()
    assert len(raw)==runtime["bytes"] and sha256(raw).hexdigest()==runtime["sha256"]
    return sorted(refs.values(),key=lambda row:row["path"]),runtime


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--execute-fixed-raw-audit",action="store_true",required=True)
    ap.add_argument("--producer-manifest",default="files.json")
    ap.add_argument("--producer-manifest-sha256",required=True)
    args=ap.parse_args()
    assert __debug__
    assert not any((HERE/name).exists() for name in ["started.json","independent-review.json","failure.json","recovered-lower-certificate.json"])
    start=time.monotonic()
    before,runtime=closure(args.producer_manifest,args.producer_manifest_sha256)
    dump_new("started.json",{"pid":os.getpid(),"time_unix":time.time(),"inputs_sha256":before,
        "producer_manifest_sha256":args.producer_manifest_sha256,"runtime_read_only":runtime,
        "scope":"One independent actual-source model rebuild, original invalid primal and unchanged raw dual audit; no optimizer or new point"})
    try:
        failure,terminal=load(PROD/"failure.json"),load(PROD/"terminal.json")
        assert failure["stage"]=="validate_primary_primal_dual" and failure["simplex_calls_started"]==1
        assert terminal["exit_code"]==1 and terminal["child_launches"]==1 and terminal["limit_stop"] is None
        assert not any((PROD/name).exists() for name in ["result.json","certificate.json","auxiliary-call-started.json"])
        affine,windows,joint,rows,constant,b,gap_coeff=source_rebuild()
        source_identity=compare_model(affine,windows,joint,rows,constant,b,gap_coeff)
        checks,certificate=raw_audit(rows,constant,b)
        assert checks["primal_invalid_preserved"]
        closed=load(PROD/"failure-closure.json")
        assert closed["returned_primal_violated_rows"]==checks["primal_violated_rows"]
        assert closed["returned_primal_violated_row_count"]==checks["primal_violated_row_count"]
        for path,digest in failure["inputs_sha256_start"].items():assert pin(ROOT/path)["sha256"]==digest
        after=[pin(ROOT/row["path"]) for row in before];assert before==after
        runtime_bytes=Path(runtime["path"]).read_bytes()
        assert len(runtime_bytes)==runtime["bytes"] and sha256(runtime_bytes).hexdigest()==runtime["sha256"]
        dump_new("source-rebuilt-model.json",{"rows":rows,"constant":str(constant),"position_coefficients":list(map(str,b)),
            "gap_coefficients":list(map(str,gap_coeff)),"target":str(TARGET),"gauge_X0":0,
            "objective_identity":"C+bX=2*SA*KAPPA*(A_L+A_R)","objective_target_identity":"target=4*KAPPA*cN",
            "source_identity":source_identity,"independent_source_rebuild":True})
        dump_new("source-rebuilt-affine-components.json",{"original_FS_windows":windows,"nine_gap_model":joint})
        if certificate:dump_new("recovered-lower-certificate.json",certificate)
        result={"schema":"independent-fixed-F-source-and-original-raw-dual-review-v1","passed":True,
            "pid":os.getpid(),"seconds":time.monotonic()-start,"independent_executions":1,
            "producer_manifest_sha256":args.producer_manifest_sha256,
            "inputs_sha256_start":before,"inputs_sha256_end":after,"runtime_read_only_sha256":runtime["sha256"],
            "source_model_identity":source_identity,"raw_checks":checks,
            "dual_only_valid_lower_recovered":certificate is not None,
            "recovered_certificate_sha256":pin(HERE/"recovered-lower-certificate.json")["sha256"] if certificate else None,
            "producer_failure_preserved":True,"producer_primal_invalid":True,"producer_primary_calls":1,"producer_auxiliary_calls":0,
            "outcome":"ValidLower_from_unchanged_raw_dual_only" if certificate else "Inconclusive_raw_dual_does_not_pay_target",
            "primal_optimum_claimed":False,"source_and_original_FS_unchanged":True,
            "source_analytic_affine_soundness_reproved_in_Lean":False,
            "scope":"Source-model-backed lower certificate for only original pair1/5 id/id if valid; no all-pair closure or global proportion",
            "producer_Python_modules_imported":0,"Sympy_imported":False,"LP_or_optimizer_calls":0,
            "new_points_or_FS_or_tangents":0,"actual_kernel_values_computed":0,"Lean_runs":0,
            "all_other_exception_pairs_handled":False,"new_global_joint_floor_proven":False,
            "new_unconditional_zero_proportion_proven":False,"complete_source_and_runtime_budget":"unknown","website_submission_ready":False}
        dump_new("independent-review.json",result)
        print(json.dumps({"passed":True,"seconds":result["seconds"],"outcome":result["outcome"],
            "primal_violations":checks["primal_violated_row_count"],"dual_lower_minus_target":checks["raw_dual_lower_minus_target"],
            "receipt":pin(HERE/"independent-review.json")}),flush=True)
    except BaseException as exc:
        dump_new("failure.json",{"passed":False,"seconds":time.monotonic()-start,"error":repr(exc),
            "traceback":traceback.format_exc(),"automatic_retry_allowed":False})
        raise


if __name__=="__main__":main()
