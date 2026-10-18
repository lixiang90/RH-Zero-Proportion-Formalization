"""Independent G committed-evidence audit, not a geometric search.

Standard library, our own frozen source parser and independently audited B data.
No producer Python import, BF, optimizer, LP or actual kernel evaluation.
"""
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
import zlib

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
PROD=ROOT/"research-goal-20261018-stageG-complete-classification"
B=ROOT/"research-goal-20261018-stageB-classification"
OWN_B=ROOT/"research-goal-20261018-stageB-independent/audit-files.json"
OWN_B_SHA="e6458883bc7588a2302afe435c3b79a08c9236bb895ec3010655024c767d7288"
OWN_A=ROOT/"research-goal-20261018-record-baseline-independent/replay_independent.py"
GATE=ROOT/"research-goal-20261016/gates/stageG-complete-classification-20261018.json"
GATE_SHA="1ff39dcea19f6db3fa4b49c8036dfc8b7a22728e00994ef8147173011395acb7"
N,Q,SA=1187,32768,10**20
KAPPA=Q*10**10*1024
CN,TAU,C=893616123055294719,893916123055294719,893766123055294719
T=KAPPA*(TAU-CN)
TOTAL=4*N*N
NAMES=["paid","strict_projection","other_strict_cycle","unresolved"]
CHARTS=["id/id","id/rev","rev/id","rev/rev"]
KNOWN_F=((1*N+5)*4)
KEYS=["status","bitmap","projection","cycles"]


def load(path):return json.loads(path.read_text(encoding="utf-8"))
def canon(x):return (json.dumps(x,sort_keys=True,separators=(",",":"))+"\n").encode("ascii")
def pin(path):
    raw=path.read_bytes()
    return {"path":path.relative_to(ROOT).as_posix(),"bytes":len(raw),"sha256":sha256(raw).hexdigest()}
def dump_new(name,x):
    with (HERE/name).open("x",encoding="utf-8",newline="\n") as stream:
        json.dump(x,stream,ensure_ascii=True,indent=2);stream.write("\n");stream.flush();os.fsync(stream.fileno())


def inputs(producer_sha):
    found={}
    def add(path,expected=None):
        row=pin(path)
        if expected is not None:assert row["sha256"]==expected
        if row["path"] in found:assert found[row["path"]]==row
        found[row["path"]]=row
    add(Path(__file__));add(GATE,GATE_SHA)
    for path,expected in [(PROD/"files.json",producer_sha),(OWN_B,OWN_B_SHA)]:
        add(path,expected);manifest=load(path)
        for field in ["files","package_files","read_only_dependencies","dependency_files","dependencies","read_only_existing_references"]:
            for row in manifest.get(field,[]):
                assert pin(ROOT/row["path"])==row;add(ROOT/row["path"])
    gate=load(GATE)
    assert gate["complete_classification_passes_authorized"]==1 and gate["total_cases"]==TOTAL
    assert gate["index_formula"]=="((i*1187+j)*4+chart)" and gate["chart_order"]==CHARTS
    assert int(gate["kappa"])==KAPPA and int(gate["payment_threshold"])==T and 2*C==CN+TAU
    assert gate["known_F_counted_as_G_closure"] is False and gate["known_F_index"]==KNOWN_F
    audit=load(ROOT/"research-goal-20261018-stageB-independent/independent-review.json")
    assert audit["passed"] and audit["row_comparison"]["all_exception_complete_36_pair_rows_equal"]==N
    return sorted(found.values(),key=lambda row:row["path"])


def original_data():
    spec=importlib.util.spec_from_file_location("own_frozen_A_for_G",OWN_A)
    own=importlib.util.module_from_spec(spec);spec.loader.exec_module(own)
    source=own.load_source();assert source["CN"]==CN
    spans,look=source["ALL"],source["LOOK"]
    assert len(spans)==36 and set(spans)=={(a,b) for a in range(9) for b in range(a+1,9)}
    cells,margins,identities=[],[],[]
    with gzip.open(B/"exception-cells.jsonl.gz","rb") as stream:
        for line in stream:
            row=json.loads(line);state=row["state"]
            assert canon(row)==line and row["exception_id"]==len(cells) and row["kind"]=="exception"
            lo,hi=state["L"]+state["A"],state["U"]+state["B"]
            assert len(lo)==len(hi)==36 and state["M"]==0
            assert all(type(v) is int for v in lo+hi)
            flat=[v for pair in zip(lo,hi) for v in pair]+[0]
            assert sha256(canon(flat)).hexdigest()==row["state_sha256"]
            m=int(row["original_margin"])
            assert 0<=m<T and int(row["tau_margin"])==m-T
            assert row["coordinate_scale"]==Q and row["separation"]=="17/20"
            cells.append((lo,hi));margins.append(m);identities.append(row["state_sha256"])
    assert len(cells)==N
    # For each physical local span, inverse orientation reads the original slot.
    inverse=[[look[(8-b,8-a)] if rev else k for k,(a,b) in enumerate(spans)] for rev in [False,True]]
    assert all(inverse[1][inverse[1][k]]==k for k in range(36))
    ranges=[[],[]];edges=[[],[]]
    for rev in [0,1]:
        for lo,hi in cells:
            ranges[rev].append(([lo[k] for k in inverse[rev]],[hi[k] for k in inverse[rev]]))
            local=[]
            for k,(a,b) in enumerate(spans):
                if rev:a,b=8-b,8-a
                local.extend([(a,b,20*hi[k]),(b,a,-20*lo[k])])
            assert len(local)==72
            edges[rev].append(local)
    shared=[(a,b) for a in range(1,8) for b in range(a+1,9)]
    pslots=[look[pair] for pair in shared]
    sslots=[look[(a-1,b-1)] for a,b in shared]
    return spans,look,cells,margins,identities,ranges,edges,pslots,sslots


def decoded_member(encoded,expected):
    dec=zlib.decompressobj(31)
    raw=dec.decompress(encoded,expected+1)
    assert len(raw)==expected and not dec.unconsumed_tail
    assert dec.eof and dec.unused_data==b"", "Each frame must contain exactly one complete gzip member"
    return raw


def source_edge(P,S,eid):
    assert 0<=eid<153
    if eid<72:return P[eid]
    if eid<144:
        a,b,w=S[eid-72];return a+1,b+1,w
    r=eid-144;return r+1,r,-17*Q


def inspect_frames(prefix,complete,data):
    spans,look,cells,margins,identities,ranges,edges,pslots,sslots=data
    assert set(prefix["streams"])==set(KEYS)
    files={key:(ROOT/prefix["streams"][key]["path"]).open("rb") for key in KEYS}
    hashes={key:sha256() for key in KEYS};rawhashes={key:sha256() for key in KEYS}
    positions={key:0 for key in KEYS};rawsizes={key:0 for key in KEYS}
    loghash=sha256();counts=[0]*4;chartcounts=[[0]*4 for _ in CHARTS]
    start,frame,chain,known,first_open=0,0,"0"*64,None,None
    cycle_min=None;projection_min=None
    with (PROD/"commits.jsonl").open("rb") as log:
        while log.tell()<prefix["commit_log_bytes"]:
            line=log.readline();assert line and log.tell()<=prefix["commit_log_bytes"]
            loghash.update(line);entry=json.loads(line);assert line==canon(entry)
            body=entry["body"]
            assert sha256(canon(body)).hexdigest()==entry["sha256"]
            assert body["previous_commit_sha256"]==chain and body["frame"]==frame and body["start"]==start
            n=body["count"]
            assert n>0 and body["end"]==start+n<=TOTAL and start%8192==0
            assert n==8192 or start+n==TOTAL and n==TOTAL-start
            assert n%4==0
            payload={}
            for key in KEYS:
                seg=body["stream_segments"][key]
                assert seg["start_byte"]==positions[key]
                size=seg["end_byte"]-seg["start_byte"]
                assert size==seg["encoded_bytes"]>=0
                encoded=files[key].read(size);assert len(encoded)==size
                positions[key]+=size;hashes[key].update(encoded)
                assert hashes[key].hexdigest()==seg["prefix_sha256"]
                expected=seg["raw_bytes"]
                assert 0<=expected<=n*11
                raw=decoded_member(encoded,expected) if key in ["projection","cycles"] else encoded
                assert len(raw)==expected and sha256(raw).hexdigest()==seg["raw_sha256"]
                rawhashes[key].update(raw);rawsizes[key]+=len(raw);payload[key]=raw
            status,bitmap,projections,cycles=(payload[k] for k in KEYS)
            assert len(status)==n//4 and len(bitmap)==(n+7)//8
            rebuilt=bytearray((n+7)//8);delta=[0]*4;pc=cc=0
            # Each byte is exactly one source i,j; scalar proof is shared by all charts.
            for localbyte,packed in enumerate(status):
                pair=start//4+localbyte;i,j=divmod(pair,N)
                paid=margins[i]+margins[j]>=T
                if paid:
                    assert packed==0
                    delta[0]+=4
                    for row in chartcounts:row[0]+=1
                    continue
                for chart in range(4):
                    code=(packed>>(2*chart))&3
                    assert code!=0, "Every non-paid status must retain strictly underpaid original Mi"
                    localq=4*localbyte+chart;index=start+localq
                    pr,sr=chart//2,chart%2
                    if code==1:
                        assert pc<len(projections)
                        sid,direction=divmod(projections[pc],2);pc+=1
                        assert sid<28
                        lp,up=ranges[pr][i];ls,us=ranges[sr][j]
                        gap=(lp[pslots[sid]]-us[sslots[sid]]) if direction==0 else (ls[sslots[sid]]-up[pslots[sid]])
                        assert gap>0
                        weight=-20*gap
                        projection_min=weight if projection_min is None else min(projection_min,weight)
                    elif code==2:
                        assert cc<len(cycles)
                        length=cycles[cc];cc+=1
                        assert 1<=length<=10 and cc+length<=len(cycles)
                        ids=cycles[cc:cc+length];cc+=length
                        selected=[source_edge(edges[pr][i],edges[sr][j],eid) for eid in ids]
                        assert all(a[1]==b[0] for a,b in zip(selected,selected[1:]+selected[:1]))
                        weight=sum(e[2] for e in selected);assert weight<0
                        cycle_min=weight if cycle_min is None else min(cycle_min,weight)
                    else:
                        assert code==3
                        rebuilt[localq//8]|=1<<(localq%8)
                        if first_open is None:first_open=index
                    delta[code]+=1;chartcounts[chart][code]+=1
                    if index==KNOWN_F:known=NAMES[code]
            assert pc==len(projections) and cc==len(cycles)
            assert bytes(rebuilt)==bitmap, "Independent status-derived bitmap must match every bit and padding"
            assert {name:delta[k] for k,name in enumerate(NAMES)}==body["delta_counts"]
            counts=[a+b for a,b in zip(counts,delta)]
            assert {name:counts[k] for k,name in enumerate(NAMES)}==body["counts"]
            start+=n;frame+=1;chain=entry["sha256"]
            if frame%64==0:print(json.dumps({"independent_frames":frame,"committed_cases_verified":start,"counts":counts}),flush=True)
        assert log.tell()==prefix["commit_log_bytes"]
        if complete:assert log.read(1)==b""
    assert loghash.hexdigest()==prefix["commit_log_sha256"] and chain==prefix["last_commit_sha256"]
    assert start==prefix["committed_cases"] and frame==prefix["frame_count"]
    assert {name:counts[k] for k,name in enumerate(NAMES)}==prefix["counts"]
    for key,f in files.items():
        assert positions[key]==prefix["streams"][key]["committed_bytes"]
        assert hashes[key].hexdigest()==prefix["streams"][key]["prefix_sha256"]
        if complete:assert f.read(1)==b""
        f.close()
    if complete:assert start==TOTAL and positions["status"]==N*N and positions["bitmap"]==(TOTAL+7)//8
    # Earlier independently verified E potential proves this particular 153-edge box feasible;
    # F's extra Ordered lower was never a permitted G closure rule.
    if start>KNOWN_F:assert known=="unresolved"
    assert prefix["known_F_annotation"]=={"index":KNOWN_F,"counts_as_extra_G_closure":False,"status":known}
    return {"committed_cases_verified":start,"frame_count":frame,"counts":dict(zip(NAMES,counts)),
        "per_chart_counts":{chart:dict(zip(NAMES,values)) for chart,values in zip(CHARTS,chartcounts)},
        "first_unresolved_index":first_open,"known_F_status":known,
        "each_projection_strict_original_bound_checked":counts[1],"each_original_source_cycle_checked":counts[2],
        "scalar_orientation_cases_checked":counts[0],"all_four_stream_committed_hashes":{key:hashes[key].hexdigest() for key in KEYS},
        "all_four_stream_uncompressed_hashes":{key:rawhashes[key].hexdigest() for key in KEYS},
        "all_four_stream_uncompressed_bytes":rawsizes,"encoded_committed_bytes":positions,
        "all_status_bitmap_bits_and_padding_independently_rebuilt":True,
        "published_hashchain_and_exact_committed_EOF_verified":True,
        "complete_files_EOF_verified":complete,"unprocessed_suffix_classified":False,
        "minimum_negative_cycle_weight":cycle_min,"minimum_projection_cycle_weight":projection_min}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--execute-frozen-G-audit",action="store_true",required=True)
    ap.add_argument("--producer-manifest-sha256",required=True)
    ap.add_argument("--prefix-only",action="store_true")
    args=ap.parse_args()
    assert __debug__ and not any((HERE/name).exists() for name in ["started.json","independent-review.json","failure.json"])
    began=time.monotonic()
    before=inputs(args.producer_manifest_sha256)
    classification=load(PROD/"classification.json")
    complete=classification["complete_range_classified"]
    assert type(complete) is bool
    if not complete:assert args.prefix_only,"Partial output requires explicit published-prefix audit only"
    prefix=load(PROD/"prefix.json")
    dump_new("started.json",{"pid":os.getpid(),"time_unix":time.time(),"inputs_sha256":before,
        "producer_manifest_sha256":args.producer_manifest_sha256,"complete_range_requested":complete,
        "scope":"One independent G every-claimed-closure fourstream audit; no producer import or geometric search"})
    try:
        terminal,begin=load(PROD/"terminal.json"),load(PROD/"started.json")
        assert terminal["child_launches"]==1
        if complete:assert terminal["exit_code"]==0 and terminal["limit_stop"] is None
        assert classification["classification_passes"]==1 and classification["total_cases"]==TOTAL
        assert classification["prefix_sha256"]==pin(PROD/"prefix.json")["sha256"]
        assert classification["inputs_sha256_start"]==classification["inputs_sha256_end"]==begin["inputs_sha256"]
        assert classification["committed_cases"]==prefix["committed_cases"]
        assert classification["counts"]==prefix["counts"]
        assert classification["index_formula"]=="((i*1187+j)*4+chart)" and classification["chart_order"]==CHARTS
        assert classification["passed"] is complete
        assert classification["unprocessed_suffix_has_no_status"] is (not complete)
        assert classification["outcome"]==("complete_fixed_classification" if complete else "inconclusive_valid_published_prefix")
        for path,digest in begin["inputs_sha256"].items():assert pin(ROOT/path)["sha256"]==digest
        data=original_data()
        frames=inspect_frames(prefix,complete,data)
        assert frames["counts"]==classification["counts"] and frames["committed_cases_verified"]==classification["committed_cases"]
        assert classification["known_F_annotation"]==prefix["known_F_annotation"]
        sample=sample_check(prefix,frames,data)
        for key in ["new_kernel_queries","new_FS_or_kernel_points_or_thresholds","LP_calls","Lean_runs"]:assert classification[key]==0
        assert classification["website_submission_ready"] is False and classification["whole_source_and_policy_runtime_budget"]=="unknown"
        after=[pin(ROOT/row["path"]) for row in before];assert before==after
        result={"schema":"independent-G-complete-fourstream-claimed-closure-review-v1","passed":True,
            "pid":os.getpid(),"seconds":time.monotonic()-began,"independent_executions":1,
            "producer_manifest_sha256":args.producer_manifest_sha256,"inputs_sha256_start":before,"inputs_sha256_end":after,
            "complete_range_classified":complete,"committed_cases":frames["committed_cases_verified"],"total_cases":TOTAL,
            "counts":frames["counts"],"every_claimed_closed_case_verified":True,
            "frame_stream_audit":frames,"optional_first_unresolved_sample":sample,
            "prefix_sha256":pin(PROD/"prefix.json")["sha256"],"classification_sha256":pin(PROD/"classification.json")["sha256"],
            "status_file_sha256":pin(PROD/"classification.2bit.bin")["sha256"],
            "unresolved_bitmap_sha256":pin(PROD/"unresolved.bitmap.bin")["sha256"],
            "source_sha256":"f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf",
            "own_B_full_source_audit_manifest_sha256":OWN_B_SHA,
            "unresolved_is_conservative_no_exclusion_only":True,"unresolved_set_nonempty_claimed":False,
            "producer_builtin_replay_failure_history_unchanged":True,"known_F_counted_as_G_closure":False,
            "producer_Python_modules_imported":0,"BF_or_LP_or_optimizer_calls":0,"new_geometric_searches":0,
            "actual_kernel_values_computed":0,"Lean_runs":0,
            "scope":"Every paid/projection/source-cycle in committed prefix verified from our independently audited original B states/Mi; unresolved stays open and unvisited suffix has no status",
            "new_global_joint_floor_proven":False,"new_unconditional_zero_proportion_proven":False,
            "whole_source_and_policy_runtime_budget":"unknown","website_submission_ready":False}
        dump_new("independent-review.json",result)
        print(json.dumps({"passed":True,"seconds":result["seconds"],"complete_range_classified":complete,
            "committed_cases":result["committed_cases"],"counts":result["counts"],"receipt":pin(HERE/"independent-review.json")}),flush=True)
    except BaseException as exc:
        dump_new("failure.json",{"passed":False,"seconds":time.monotonic()-began,"error":repr(exc),
            "traceback":traceback.format_exc(),"automatic_retry_allowed":False})
        raise


def sample_check(prefix,frames,data):
    spans,look,cells,margins,identities,ranges,edges,pslots,sslots=data
    expected=prefix["first_unresolved_sample_sha256"]
    if expected is None:
        assert frames["first_unresolved_index"] is None
        return {"present":False,"unresolved_global_nonempty_claim":False}
    assert pin(PROD/"first-unresolved-sample.json")["sha256"]==expected
    sample=load(PROD/"first-unresolved-sample.json")
    q=sample["index"];pair,chart=divmod(q,4);i,j=divmod(pair,N)
    assert q==frames["first_unresolved_index"] and q<frames["committed_cases_verified"]
    assert sample["status"]=="unresolved" and sample["not_a_global_nonempty_claim"] is True
    assert sample["prefix_exception_id"]==i and sample["suffix_exception_id"]==j and sample["chart"]==CHARTS[chart]
    assert sample["prefix_state_sha256"]==identities[i] and sample["suffix_state_sha256"]==identities[j]
    checked=False;orders=None
    if sample["potential_present"]:
        point=sample["X_integer_potential"]
        assert len(point)==10 and point[0]==0 and all(type(x) is int for x in point) and sample["X_scale"]==20*Q
        P,S=edges[chart//2][i],edges[chart%2][j]
        for eid in range(153):
            u,v,w=source_edge(P,S,eid);assert point[v]-point[u]<=w
        orders=[]
        for offset,rev,key in [(0,chart//2,"prefix_ordered"),(1,chart%2,"suffix_ordered")]:
            first=point[offset+1]-point[offset];last=point[offset+8]-point[offset+7]
            a,b=(last,first) if rev else (first,last)
            expected_order={"orientation":"rev" if rev else "id","offset":offset,
                "original_h0_scaled":a,"original_h7_scaled":b,"four_point_left_minus_right_scaled":a-b,
                "ordered_condition_holds":a<=b}
            assert sample[key]==expected_order;orders.append(a<=b)
        assert sample["all153_edges_verified"] is True
        checked=True
    return {"present":True,"index":q,"sample_hash":expected,"potential153edges_checked":checked,
        "ordered_at_sample":orders,"scope":"Only this optional sample, never a nonempty claim about all unresolved"}


if __name__=="__main__":main()
