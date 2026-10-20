"""Frozen, NOT YET EXECUTED, one-shot macro014 geometry/source preparation.

Standard library only. No old generator/model import, WL decode, Lean, kernel or export.
"""
from pathlib import Path
from hashlib import sha256
import gzip
import io
import json
import os
import re
import time

ROOT = Path(__file__).resolve().parents[1]
OUT = Path(__file__).resolve().parent
DEST = ROOT / "research-goal-20261021-w9a2-delivery/draft-v11"
T0 = time.monotonic()
PINS = []
SOURCE_CAP = 2_000_000
META_CAP = 2_000_000
TOTAL_CAP = 4_000_000
SOURCE_SHA = "86e3f46c90648f98d540d01edd45268d89504b45f7fb9d5d8e53d8582d41e14d"
MACRO_SHA = "2c2c95cd40ef75493d74e0cc4e4d9bb03032e8911c7adfb4b041f672469329f4"


def check(ok=True, message="30-second source/metadata budget expired"):
    if not ok or time.monotonic() - T0 > 30:
        raise RuntimeError(message)


def sha(raw):
    return sha256(raw).hexdigest()


def encode(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode("utf-8")


def write_new(path, raw):
    with path.open("xb") as stream:
        stream.write(raw)
        stream.flush()
        os.fsync(stream.fileno())


def read(relative, expected, size=None):
    raw = (ROOT / relative).read_bytes()
    check(sha(raw) == expected and (size is None or len(raw) == size), "Pinned input differs: " + relative)
    PINS.append({"path": relative, "bytes": len(raw), "sha256": expected})
    return raw


def literal(text, pattern):
    found = list(re.finditer(pattern, text, re.M))
    check(len(found) == 1, "Literal declaration must be unique")
    body = found[0].group(1)
    cursor = 0
    for token in re.finditer(r"\s+|true|false|[0-9]+|[\[\](),]", body):
        check(token.start() == cursor, "Unexpected literal token")
        cursor = token.end()
    check(cursor == len(body), "Unconsumed literal tail")
    return json.loads(body.replace("(", "[").replace(")", "]")), sha(body.encode())


def canonical(state):
    return (json.dumps(state, sort_keys=True, separators=(",", ":")) + "\n").encode("ascii")


def unique(pattern, source):
    found = list(re.finditer(pattern, source, re.M))
    check(len(found) == 1, "Unique source edit anchor required")
    return found[0]


def helpers(n, chosen, old_cuts, old_ok):
    prefix = f"v11_r{n}_"
    pos, end, fuel = chosen["pos"], chosen["end"], chosen["fuel"]
    state = ", ".join(map(str, chosen["state_73_fields_M0"]))
    return (f"noncomputable def {prefix}s : St := ⟨{state}⟩\n\n"
        f"theorem {prefix}e :\n"
        f"    U (walkCut TOP BK TOPD BKD PT REG WD{n} {old_cuts} {fuel} {pos}) {prefix}s = {end} := by\n"
        f"  decide +kernel\n\n"
        f"theorem {prefix}c : Covered (toCl {prefix}s) :=\n"
        f"  walkCut_ok lbS lbD ptS hR WD{n} {old_ok} {fuel} {pos} {prefix}s\n"
        f"    (by rw [{prefix}e]; decide)\n\n"
        f"noncomputable def {prefix}cuts : List (Nat × St × Nat) :=\n"
        f"  ({pos}, {prefix}s, {end}) :: {old_cuts}\n\n"
        f"theorem {prefix}cuts_ok : CutsOk {prefix}cuts :=\n"
        f"  cutsOk_cons {prefix}c {old_ok}\n\n").encode("utf-8")


def graph_rows(source, name):
    pattern = (rb"^(?P<header>theorem " + name.encode() +
        rb" : (?P<proposition>[\s\S]*?) := by)(?P<header_newline>\r?\n)  decide(?P<proof_newline>\r?\n)")
    m = unique(pattern, source)
    proposition = m["proposition"].decode("utf-8")
    first = "∀ u v : State,"
    check(proposition.startswith(first) and proposition.count("∀") == 1, "Graph target binder differs")
    tail = proposition[len(first):].replace("\r\n", "\n")
    rows = []
    row_names = []
    for i in range(49):
        row_name = f"v11_{name}_row{i}"
        row_names.append(row_name)
        fixed = re.sub(r"\bu\b", f"({i} : State)", tail)
        check(re.search(r"\bu\b", fixed) is None, "Unfixed row variable")
        rows.append(f"theorem {row_name} : ∀ v : State,{fixed} := by\n  decide\n\n")
    # Keep the old theorem header/type and its original CRLFs. All inserted lines
    # are LF; the old proof's one final newline is retained on the last bullet.
    proof_lines = ["  intro u", "  fin_cases u"] + [f"  · exact {name}" for name in row_names]
    proof = "\n".join(proof_lines).encode("utf-8") + m["proof_newline"]
    new = "".join(rows).encode("utf-8") + m["header"] + m["header_newline"] + proof
    return {"label": "Graph." + name, "start": m.start(), "end": m.end(), "old": m[0], "new": new,
        "graph_metadata": {"name": name, "rows": row_names, "fixed_u_values": list(range(49)),
            "original_header_type_preserved": True, "original_theorem_explicit_bullets": 49,
            "all_rows_quantify_every_v": True, "row_proof": "ordinary decide", "row_constants_opaque_theorems": True}}


def main():
    check(not DEST.exists(), "Fresh draft-v11 directory required")
    expected_files = {"prepare_targeted_v11.py", "README.zh.md", "pre-execution-files.json"}
    check({p.name for p in OUT.iterdir()} == expected_files and all(p.is_file() and not p.is_symlink() for p in OUT.iterdir()), "Fresh preparation directory; no retries/unknown entries")
    pre_raw = (OUT / "pre-execution-files.json").read_bytes()
    pre = json.loads(pre_raw)
    check(pre["execution_authorized"] is False and pre["scope"] == "Preparation frozen; execution requires root authorization", "Wrong pre-execution contract")
    for row in pre["files"]:
        check(row["path"] in {"prepare_targeted_v11.py", "README.zh.md"}, "Unexpected prepared pin")
        raw = (OUT / row["path"]).read_bytes()
        check(len(raw) == row["bytes"] and sha(raw) == row["sha256"], "Prepared code/document changed")
        PINS.append({"path": str((OUT / row["path"]).relative_to(ROOT)).replace("\\", "/"), "bytes": len(raw), "sha256": sha(raw)})
    check({r["path"] for r in pre["files"]} == {"prepare_targeted_v11.py", "README.zh.md"}, "Missing prepared code pin")
    PINS.append({"path": str((OUT/"pre-execution-files.json").relative_to(ROOT)).replace("\\", "/"), "bytes":len(pre_raw), "sha256":sha(pre_raw)})
    write_new(OUT / "started.json", encode({"schema":"targeted-v11-start-v1","attempt":1,"budget_seconds":30,
        "scope":"Root-authorized future one-shot geometry/source preparation only; zero Lean"}))
    read("research-goal-20261016/macro-reviews/014-20261021.zh.md", MACRO_SHA, 8780)
    source = read("research-goal-20261021-w9a2-delivery/draft-v10/Solution.lean", SOURCE_SHA, 1914823)
    archive = read("research-goal-20261019-w9a2-certificate-analysis/walk-events.jsonl.gz",
        "1999185a8409c879a987c697d67040f431a0ccaf0dde3181cb8902ffb1d2dbff", 1596457)
    old_packet = json.loads(read("research-goal-20261021-w9a2-all-root-cut-preparation-v1/packet.json",
        "7b67f9947bdb65b79a87f95e5d9b077b63f0f96a384100d352a398c5051dcab0"))
    baseline = json.loads(read("research-goal-20261019-w9a2-certificate-analysis/baseline-replay.json",
        "a36441559cd2460edb31bc3e312f9379e4fc55c803d79bf8686bee017206e5c6", 115380))
    read("research-goal-20261019-w9a2-certificate-analysis/record_math_w9a2.py",
        "c6da616359214c04a9b0ecb465ff87274bf4487ddbcc986e6e3ffa92a49c2631", 6746)
    read("research-goal-20261019-w9a2-certificate-analysis/replay_w9a2.py",
        "424ceda53589cf9f3911824813220aa09fc47fa5081cf1d2c36c02cae1089322", 13457)
    text = source.decode("utf-8")
    check("v11_" not in text, "Fresh declaration prefix required")
    pr, pr_sha = literal(text, r"^noncomputable def PR : List \(ℕ × ℕ\) := (\[[^\n]*\])\r?$")
    cov, cov_sha = literal(text, r"^noncomputable def COV : List \(List \(ℕ × ℕ × Bool\)\) := (\[[\s\S]*?\])\r?\nnoncomputable def SMAX")
    check(len(pr) == 28 and all(len(p)==2 and all(type(x) is int for x in p) and 0<=p[0]<p[1]<=8 for p in pr), "PR shape")
    check(len(cov)==8 and all(type(row) is list for row in cov) and all(len(v)==3 and type(v[0]) is int and type(v[1]) is int and 0<=v[0]<=v[1] and type(v[2]) is bool for row in cov for v in row), "COV shape")
    bad = [[v[:2] for v in row if not v[2]] for row in cov]
    fields = [v for i in range(8) for v in (f"l{i}",f"u{i}")] + [v for a,b in pr for v in (f"A{a}{b}",f"B{a}{b}")] + ["M"]
    st = re.findall(r"^structure St where\s*\(([^:]+) : ℕ\)",text,re.M)
    check(len(st)==1 and st[0].split()==fields and fields==old_packet["St_field_order"], "Current73-field state order")
    roots = {}
    for n in (37,43):
        m = unique(rb"^theorem rc"+str(n).encode()+rb" : Covered \(RC ([0-9 ]+)\) := [^\r\n]+\r?$",source)
        roots[n] = {"indices":list(map(int,m[1].split())),"old":old_packet["roots"][n]}
        base = next(r for r in baseline["roots"] if r["root"]==n)
        check(roots[n]["indices"]==base["indices"]==roots[n]["old"]["indices"] and base["end"]==roots[n]["old"]["end"], "Root source/archive identity")
    check([(x["pos"],x["end"]) for x in roots[37]["old"]["selected_hints"]]==[(620,79718),(110366,137099)], "Exactly original two root37 cuts")
    check([(x["pos"],x["end"]) for x in roots[43]["old"]["selected_hints"]]==[(169,70606)], "Original root43 target")
    events, stats = {37:{},43:{}},{37:{},43:{}}
    allowed = {"root","pos","kind","axis","mode","cut","left","right","end","state_sha256"}
    archive_lines = 0
    with gzip.GzipFile(fileobj=io.BytesIO(archive),mode="rb") as stream:
        for raw in stream:
            check(len(raw)<=65536, "Archive line cap")
            row = json.loads(raw)
            archive_lines += 1
            check(archive_lines<=24504, "Archive event cap")
            n = row["root"]
            if n not in events:
                continue
            e = {k:v for k,v in row.items() if k in allowed}
            pos = e["pos"]
            check(type(pos) is int and pos>0 and pos not in events[n] and type(e["end"]) is int and e["end"]>pos, "Archive position/end")
            check(re.fullmatch("[0-9a-f]{64}",e["state_sha256"]) is not None, "Archive state hash")
            if e["kind"]=="branch":
                left,right = stats[n][e["left"]],stats[n][e["right"]]
                check(e["left"]==pos+8 and left["end"]==e["right"] and right["end"]==e["end"], "Archive branch cursors")
                s = {k:left[k]+right[k] for k in ("nodes","numeric","reflection","farkas","branches")}
                s["nodes"] += 1; s["branches"] += 1
                s["height"] = 1+max(left["height"],right["height"])
            else:
                check(e["kind"] in ("numeric","reflection","farkas"), "Unknown archive kind")
                s = {"nodes":1,"numeric":int(e["kind"]=="numeric"),"reflection":int(e["kind"]=="reflection"),"farkas":int(e["kind"]=="farkas"),"branches":0,"height":1}
            s["end"] = e["end"]
            events[n][pos],stats[n][pos] = e,s
    check(archive_lines==24504, "Full pinned archive framing")
    edges = [(i,i+1) for i in range(8)]+[tuple(p) for p in pr]
    lookup = {edge:i for i,edge in enumerate(edges)}

    # Copied pure geometry from record_math_w9a2.py:44-58 only. No WL/leaf math.
    def leg(s,a,b):
        return 0 if a==b else s[1][lookup[a,b]] if a<b else -s[0][lookup[b,a]]

    def split(s,i,j,q,upper):
        lo,hi=s
        a,b,w=(i,j,q) if upper else (j,i,-q)
        BB,TB=1<<42,2*(1<<42)
        col=[max(0,BB+leg(s,x,a)) for x in range(9)]
        row=[max(0,BB+w+leg(s,b,x)) for x in range(9)]
        return ([max(l,max(0,TB-col[b]-row[a])) for l,(a,b) in zip(lo,edges)],
                [min(u,max(0,col[a]+row[b]-TB)) for u,(a,b) in zip(hi,edges)])

    states,depths = {37:{},43:{}},{37:{},43:{}}
    for n in (37,43):
        indices=roots[n]["indices"]
        lo=[bad[r][indices[r]][0] for r in range(8)]
        hi=[bad[r][indices[r]][1] for r in range(8)]
        initial=(lo+[sum(lo[i:j]) for i,j in pr],hi+[sum(hi[i:j]) for i,j in pr])
        visited=set()
        def visit(pos,geometry,depth):
            check(pos not in visited and depth<128, "Geometry traversal/depth")
            flat=[v for pair in zip(*geometry) for v in pair]+[0]
            e=events[n][pos]
            check(len(flat)==73 and all(type(x) is int and x>=0 for x in flat) and sha(canonical(flat))==e["state_sha256"], "Original normalized73-state SHA mismatch")
            states[n][pos],depths[n][pos]=flat,depth
            visited.add(pos)
            if e["kind"]=="branch":
                check(type(e["axis"]) is int and 0<=e["axis"]<36 and type(e["cut"]) is int, "Branch geometry fields")
                i,j=edges[e["axis"]]
                visit(e["left"],split(geometry,i,j,e["cut"],True),depth+1)
                visit(e["right"],split(geometry,i,j,e["cut"],False),depth+1)
        visit(1,initial,0)
        top=stats[n][1]
        check(visited==set(events[n]) and len(visited)==roots[n]["old"]["all_state_hashes_checked"] and top["numeric"]==roots[n]["old"]["root_topology"]["numeric_leaves"] and top["end"]==roots[n]["old"]["end"], "Target-root geometry/topology identity")
        for hint in roots[n]["old"]["selected_hints"]:
            check(states[n][hint["pos"]]==hint["state_73_fields_M0"] and 128-depths[n][hint["pos"]]==hint["fuel"], "Existing hint differs from original geometry")
            index=roots[n]["old"]["selected_hints"].index(hint)
            m=unique(rb"^noncomputable def v10_r"+str(n).encode()+b"_s"+str(index).encode()+rb" : St := ⟨([0-9, ]+)⟩\r?$",source)
            check(list(map(int,m[1].decode().split(",")))==hint["state_73_fields_M0"], "Existing literal state/source differs")

    selected,selection_rows = {},[]
    for n,target,total_expected in ((37,1,290),(43,169,249)):
        old=roots[37]["old"]["selected_hints"] if n==37 else []
        target_end=events[n][target]["end"]
        total=stats[n][target]["numeric"]-sum(stats[n][h["pos"]]["numeric"] for h in old)
        check(total==total_expected, "Named failed target residual differs")
        candidates=[]
        for pos in sorted(events[n]):
            check()
            if not (target<pos<target_end):
                continue
            end=events[n][pos]["end"]
            check(end<=target_end, "Descendant interval escapes target")
            inside=any(h["pos"]<=pos<h["end"] for h in old)
            if inside:
                continue
            contained=[]
            for h in old:
                disjoint=end<=h["pos"] or h["end"]<=pos
                contains=pos<=h["pos"] and h["end"]<=end
                check(disjoint or contains, "Unexpected partial old-cut overlap")
                if contains:contained.append(h["pos"])
            residual=stats[n][pos]["numeric"]-sum(stats[n][p]["numeric"] for p in contained)
            check(0<=residual<=total, "Residual arithmetic bounds")
            candidates.append({"pos":pos,"end":end,"numeric":stats[n][pos]["numeric"],"contained_old_cut_positions":contained,
                "remaining_numeric":residual,"outside_remaining_numeric":total-residual,"score":max(residual,total-residual)})
        check(candidates, "No proper-descendant candidates")
        chosen=min(candidates,key=lambda c:(c["score"],c["pos"]))
        check(0<chosen["remaining_numeric"]<total and chosen["score"]<total, "Both sides must strictly decrease; no fallback rule")
        pos=chosen["pos"]
        chosen={**chosen,"depth":depths[n][pos],"fuel":128-depths[n][pos],"state_73_fields_M0":states[n][pos],
            "canonical_JSON_LF_sha256":events[n][pos]["state_sha256"],"topology":stats[n][pos]}
        selected[n]=chosen
        selection_rows.append({"root":n,"target_pos":target,"target_end":target_end,"target_fuel":128-depths[n][target],
            "target_original_state_73_fields_M0":states[n][target],"target_state_sha256":events[n][target]["state_sha256"],
            "total_remaining_numeric":total,"old_cut_positions":[h["pos"] for h in old],"selected":chosen,"candidate_scores":candidates,
            "selection_rule":"Unique min(max(remaining,total-remaining),pos) over proper descendants outside old cuts; subtract only whole contained old cuts."})

    edits=[]
    # Root37: new helper proof uses only original cuts; parent/root consume new::old.
    p37=unique(rb"^theorem v10_r37_parent :[\s\S]*?  decide \+kernel\r?\n",source)
    check(p37[0].count(b"v10_r37_cuts")==1, "Root37 parent source shape")
    edits.append({"label":"r37 helper+parent target","start":p37.start(),"end":p37.end(),"old":p37[0],
        "new":helpers(37,selected[37],"v10_r37_cuts","v10_r37_cuts_ok")+p37[0].replace(b"v10_r37_cuts",b"v11_r37_cuts")})
    rc37=unique(rb"^theorem rc37 : Covered \(RC 0 2 0 1 0 1 0 0\) := [^\r\n]+\r?\n",source)
    check(rc37[0].count(b"v10_r37_cuts ")==1 and rc37[0].count(b"v10_r37_cuts_ok ")==1, "Root37 proof source shape")
    new_rc37=rc37[0].replace(b"v10_r37_cuts ",b"v11_r37_cuts ").replace(b"v10_r37_cuts_ok ",b"v11_r37_cuts_ok ")
    edits.append({"label":"rc37 same Covered proof composition","start":rc37.start(),"end":rc37.end(),"old":rc37[0],"new":new_rc37})
    # Root43: this auxiliary equality deliberately becomes cut-aware. Its final
    # c0 Covered type and the outer root43 cuts/parent/root are unchanged.
    e43=unique(rb"^theorem v10_r43_e0 :[\s\S]*?  decide \+kernel\r?\n",source)
    check(e43[0].count(b"WD43 [] 107 169")==1, "Root43 original raw target required")
    edits.append({"label":"r43 helper+explicit changed internal cursor type","start":e43.start(),"end":e43.end(),"old":e43[0],
        "new":helpers(43,selected[43],"[]","cutsOk_nil")+e43[0].replace(b"WD43 [] 107 169",b"WD43 v11_r43_cuts 107 169")})
    c43=unique(rb"^theorem v10_r43_c0 : Covered \(toCl v10_r43_s0\) :=[\s\S]*?\(by rw \[v10_r43_e0\]; decide\)\r?\n",source)
    check(c43[0].count(b"WD43 cutsOk_nil 107 169")==1, "Root43 Covered proof source shape")
    edits.append({"label":"r43 same Covered type consumes new CutsOk","start":c43.start(),"end":c43.end(),"old":c43[0],
        "new":c43[0].replace(b"WD43 cutsOk_nil 107 169",b"WD43 v11_r43_cuts_ok 107 169")})
    for name in ("edge_potential","exclusion_checked"):
        edits.append(graph_rows(source,name))
    edits.sort(key=lambda e:e["start"])
    check(len(edits)==6 and all(a["end"]<=b["start"] for a,b in zip(edits,edits[1:])), "Exactly six disjoint source edit spans")
    chunks=[];old_cursor=0;new_cursor=0;mapping=[]
    for e in edits:
        unchanged=source[old_cursor:e["start"]]
        chunks.append(unchanged);new_cursor+=len(unchanged)
        check(source[e["start"]:e["end"]]==e["old"], "Original edit span mismatch")
        mapping.append({"label":e["label"],"old_byte_offset":e["start"],"new_byte_offset":new_cursor,
            "old_bytes":len(e["old"]),"new_bytes":len(e["new"]),"old_sha256":sha(e["old"]),"new_sha256":sha(e["new"]),
            "old_utf8":e["old"].decode(),"new_utf8":e["new"].decode()})
        chunks.append(e["new"]);new_cursor+=len(e["new"]);old_cursor=e["end"]
    chunks.append(source[old_cursor:]);candidate=b"".join(chunks)
    check(len(candidate)<=SOURCE_CAP, "Full v11 source exceeds2MB; no automatic repair")
    inverse=candidate
    for row in reversed(mapping):
        start,size=row["new_byte_offset"],row["new_bytes"]
        check(sha(inverse[start:start+size])==row["new_sha256"], "Inverse replacement identity")
        inverse=inverse[:start]+row["old_utf8"].encode()+inverse[start+size:]
    check(inverse==source and candidate.count(b"\r\n")==source.count(b"\r\n")==221, "Exact inverse/CRLF contract")
    check(candidate.count(b" := zfNat64 ")==source.count(b" := zfNat64 ")==135 and candidate.endswith(b"\n") and not candidate.endswith(b"\n\n"), "Packed135/finalLF contract")
    for name in (b"rc37",b"rc43",b"v10_r43_c0"):
        pattern=rb"^theorem "+name+rb" : ([\s\S]*?) :="
        check(unique(pattern,source)[1]==unique(pattern,candidate)[1], "Original Covered type changed")
    for e in edits:
        if "graph_metadata" in e:
            name=e["graph_metadata"]["name"]
            pattern=rb"^theorem "+name.encode()+rb" : ([\s\S]*?) := by"
            check(unique(pattern,source)[1]==unique(pattern,candidate)[1], "Original Graph theorem type changed")
            for i in range(49):
                row_name=f"v11_{name}_row{i}"
                check(candidate.count(("theorem "+row_name+" :").encode())==1 and candidate.count(("  · exact "+row_name+"\n").encode()) + candidate.count(("  · exact "+row_name+"\r\n").encode())==1, "Exactly one row and explicit matching bullet")
    for pin in PINS:
        check(sha((ROOT/pin["path"]).read_bytes())==pin["sha256"], "Frozen input changed during preparation")
    summary={"source_bytes":len(candidate),"source_sha256":sha(candidate),"source_delta_bytes":len(candidate)-len(source),
        "Graph_row_lemmas":98,"Graph_explicit_bullets":98,"new_walk_hints":2,
        "targets":[{"root":r["root"],"target_pos":r["target_pos"],"selected_pos":r["selected"]["pos"],"selected_fuel":r["selected"]["fuel"],
            "selected_end":r["selected"]["end"],"inside_remaining_numeric":r["selected"]["remaining_numeric"],
            "outside_remaining_numeric":r["selected"]["outside_remaining_numeric"]} for r in selection_rows]}
    packet={"schema":"targeted-v11-two-walk-selection-v1","scope":"Pure archive topology and normalized geometry; NOT Lean stEq/cursor/proof/resource PASS",
        "macro014_sha256":MACRO_SHA,"input_pins":PINS,"St_field_order":fields,"PR_literal_sha256":pr_sha,"COV_literal_sha256":cov_sha,
        "archive_lines_read":archive_lines,"normalized_state_hashes_checked":sum(len(states[n]) for n in (37,43)),"selection":selection_rows,
        "source_summary":summary,"WL_decodes":0,"leaf_energy_margin_tangent_recomputation":0,"old_model_or_generator_import":0,
        "Lean_compiler_kernel_export_network_UI_Git_calls":0,"proof_PASS":False,"resource_PASS":False}
    projection={"schema":"v10-v11-six-span-exact-projection-v1","old_source_sha256":SOURCE_SHA,"new_source_sha256":sha(candidate),
        "edits":mapping,"inverse_exact_v10":True,"all_other_bytes_preserved":True,"CRLF":221,"packed_literals":135,
        "original_Graph_and_Covered_types_preserved":True,"public_three_and_K_preserved_by_unchanged_spans":True,
        "intentional_internal_type_change":"v10_r43_e0 now states walkCut with v11_r43_cuts, not the old [] equality. c0 Covered type and outer43 cuts/parent/root are unchanged.",
        "Graph_rows":[e["graph_metadata"] for e in edits if "graph_metadata" in e]}
    contract={"schema":"draft-v11-targeted-prepared-source-v1","summary":summary,"prepared_only":True,"Lean_validated":False,
        "kernel_validated":False,"resource_validated":False,"official_validated":False,"exact_inverse_v10":True,
        "new_proof_obligations":"98 ordinary-decide rows and two new child cursor/coverage proofs plus changed cut-aware parent37/e0_43; no acceptance is claimed here.",
        "source_edits_path":str((OUT/"source-edits.json").relative_to(ROOT)).replace("\\","/")}
    outputs={OUT/"packet.json":encode(packet),OUT/"source-edits.json":encode(projection),DEST/"Solution.lean":candidate,DEST/"source-contract.json":encode(contract)}
    metadata_bytes=sum(len(raw) for path,raw in outputs.items() if path.suffix!=".lean")
    existing_bytes=sum(p.stat().st_size for p in OUT.iterdir() if p.is_file())
    check(metadata_bytes<=META_CAP and existing_bytes+sum(map(len,outputs.values()))+30000<=TOTAL_CAP, "Metadata2MB or total4MB output cap")
    DEST.mkdir(exist_ok=False)
    for path,raw in outputs.items():
        check();write_new(path,raw)
    execution={"schema":"targeted-v11-one-shot-completion-v1","completed":True,"summary":summary,"budget_seconds":30,
        "elapsed_seconds_before_receipt":time.monotonic()-T0,"metadata_bytes":metadata_bytes,"source_cap":SOURCE_CAP,"metadata_cap":META_CAP,"total_output_cap":TOTAL_CAP,
        "attempts":1,"automatic_retries":0,"all_input_pins_unchanged":True,"exact_reverse_v10":True,"Lean_compiler_kernel_export_decoder_calls":0,"proof_PASS":False}
    write_new(OUT/"execution.json",encode(execution))
    for directory in (DEST,OUT):
        rows=[{"path":p.name,"bytes":p.stat().st_size,"sha256":sha(p.read_bytes())} for p in sorted(directory.iterdir()) if p.is_file()]
        write_new(directory/"files.json",encode({"schema":"prepared-source-metadata-files-v1","scope":"No Lean/proof/resource execution","files":rows}))
    actual_files=[p for directory in (DEST,OUT) for p in directory.iterdir() if p.is_file()]
    check(sum(p.stat().st_size for p in actual_files)<=TOTAL_CAP, "Final actual total output4MB cap")
    check(sum(p.stat().st_size for p in actual_files if p.suffix not in (".lean",".py"))<=META_CAP, "Final actual metadata2MB cap")
    check()
    print(json.dumps(execution))


if __name__=="__main__":
    try:
        main()
    except BaseException as exc:
        write_new(OUT/"failure.json",encode({"completed":False,"error":repr(exc),"elapsed_seconds":time.monotonic()-T0,
            "automatic_retry":False,"source_or_numeric_repair_attempted":False,"Lean_execution":0,"proof_PASS":False}))
        raise
