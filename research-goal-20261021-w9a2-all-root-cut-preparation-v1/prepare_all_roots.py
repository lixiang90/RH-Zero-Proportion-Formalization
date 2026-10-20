"""One authorized bounded archive-geometry/source transform. No Lean or WL decoding."""
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
DEST = ROOT / "research-goal-20261021-w9a2-delivery/draft-v10"
T0 = time.monotonic()
PINS = []
TOTAL_CAP = 4_000_000
META_CAP = 2_000_000
SOURCE_CAP = 2_000_000


def check(ok=True, message="30-second metadata/source budget expired"):
    if not ok or time.monotonic() - T0 > 30:
        raise RuntimeError(message)


def digest(raw):
    return sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode("utf-8")


def write(path, raw):
    with path.open("xb") as stream:
        stream.write(raw)
        stream.flush()
        os.fsync(stream.fileno())


def read(relative, size, expected):
    raw = (ROOT / relative).read_bytes()
    check(len(raw) == size and digest(raw) == expected, "Pinned input differs: " + relative)
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
    return json.loads(body.replace("(", "[").replace(")", "]")), digest(body.encode())


def canonical(state):
    return (json.dumps(state, sort_keys=True, separators=(",", ":")) + "\n").encode("ascii")


def fragment(root, selected, indices, end):
    prefix = f"v10_r{root}_"
    parts = []
    for i, row in enumerate(selected):
        state = ", ".join(map(str, row["state_73_fields_M0"]))
        pos, stop, fuel = row["pos"], row["end"], row["fuel"]
        parts.append(f"noncomputable def {prefix}s{i} : St := ⟨{state}⟩\n\n"
            f"theorem {prefix}e{i} :\n"
            f"    U (walkCut TOP BK TOPD BKD PT REG WD{root} [] {fuel} {pos}) {prefix}s{i} = {stop} := by\n"
            f"  decide +kernel\n\n"
            f"theorem {prefix}c{i} : Covered (toCl {prefix}s{i}) :=\n"
            f"  walkCut_ok lbS lbD ptS hR WD{root} cutsOk_nil {fuel} {pos} {prefix}s{i}\n"
            f"    (by rw [{prefix}e{i}]; decide)\n\n")
    tuples = ", ".join(f"({row['pos']}, {prefix}s{i}, {row['end']})" for i, row in enumerate(selected))
    cons = "cutsOk_nil"
    for i in reversed(range(len(selected))):
        cons = f"(cutsOk_cons {prefix}c{i} {cons})"
    args = " ".join(map(str, indices))
    parts.append(f"noncomputable def {prefix}cuts : List (Nat × St × Nat) :=\n  [{tuples}]\n\n"
        f"theorem {prefix}cuts_ok : CutsOk {prefix}cuts :=\n  {cons}\n\n"
        f"theorem {prefix}parent :\n"
        f"    U (walkCutR TOP BK TOPD BKD PT REG WD{root} {prefix}cuts 128 1)\n"
        f"      (ofCl (RC {args}) 0) = {end} := by\n  decide +kernel\n\n")
    return "".join(parts).encode("utf-8")


def main():
    check(not DEST.exists(), "Fresh draft-v10 directory required")
    check(not any((OUT / name).exists() for name in ("started.json", "execution.json", "failure.json")), "No retry/overwrite")
    write(OUT / "started.json", encoded({"schema": "all-root-cut-start-v1", "attempt": 1,
        "budget_seconds": 30, "scope": "Archive geometry and source preparation only; zero Lean"}))
    source = read("research-goal-20261021-w9a2-delivery/draft-v9/Solution.lean", 1861120,
        "7552bbb829b86986798b58cf40caf998ea8c51ab19201998b533dae4b9518c99")
    archive = read("research-goal-20261019-w9a2-certificate-analysis/walk-events.jsonl.gz", 1596457,
        "1999185a8409c879a987c697d67040f431a0ccaf0dde3181cb8902ffb1d2dbff")
    baseline = json.loads(read("research-goal-20261019-w9a2-certificate-analysis/baseline-replay.json", 115380,
        "a36441559cd2460edb31bc3e312f9379e4fc55c803d79bf8686bee017206e5c6"))
    read("research-goal-20261019-w9a2-certificate-analysis/record_math_w9a2.py", 6746,
        "c6da616359214c04a9b0ecb465ff87274bf4487ddbcc986e6e3ffa92a49c2631")
    read("research-goal-20261019-w9a2-certificate-analysis/replay_w9a2.py", 13457,
        "424ceda53589cf9f3911824813220aa09fc47fa5081cf1d2c36c02cae1089322")
    text = source.decode("utf-8")
    check("v10_r" not in text, "Fresh helper prefix required")
    pr, pr_sha = literal(text, r"^noncomputable def PR : List \(ℕ × ℕ\) := (\[[^\n]*\])\r?$")
    cov, cov_sha = literal(text, r"^noncomputable def COV : List \(List \(ℕ × ℕ × Bool\)\) := (\[[\s\S]*?\])\r?\nnoncomputable def SMAX")
    check(len(pr) == 28 and all(len(x) == 2 and all(type(v) is int for v in x) and 0 <= x[0] < x[1] <= 8 for x in pr), "PR shape")
    check(len(cov) == 8 and all(type(row) is list for row in cov), "COV shape")
    check(all(len(v) == 3 and type(v[0]) is int and type(v[1]) is int and 0 <= v[0] <= v[1] and type(v[2]) is bool for row in cov for v in row), "COV record shape")
    bad = [[v[:2] for v in row if not v[2]] for row in cov]
    fields = [v for i in range(8) for v in (f"l{i}", f"u{i}")] + [v for a,b in pr for v in (f"A{a}{b}", f"B{a}{b}")] + ["M"]
    st = re.findall(r"^structure St where\s*\(([^:]+) : ℕ\)", text, re.M)
    check(len(st) == 1 and st[0].split() == fields and len(fields) == 73, "Current St field order mismatch")
    pattern = rb"^(?P<prefix>theorem rc(?P<n>[0-9]+) : Covered \(RC (?P<indices>[0-9 ]+)\) := )rcOf WD(?P<wd>[0-9]+) (?P<end>[0-9]+) \(by decide \+kernel\) \(by decide\)(?P<newline>\r?\n)"
    matches = list(re.finditer(pattern, source, re.M))
    check(len(matches) == 48, "Exactly48 original raw root proofs required")
    roots = {}
    for m in matches:
        n = int(m["n"])
        check(n == int(m["wd"]) and n not in roots, "Duplicate/mismatched root WD")
        roots[n] = {"match": m, "indices": list(map(int,m["indices"].split())), "end": int(m["end"])}
    check(set(roots) == set(range(48)), "Root numbering mismatch")
    bases = {r["root"]: r for r in baseline["roots"]}
    check(set(bases) == set(roots) and baseline["counts"]["nodes"] == 24504, "Baseline shape")
    for n,r in roots.items():
        check(len(r["indices"]) == 8 and r["indices"] == bases[n]["indices"] and r["end"] == bases[n]["end"], "Source/baseline root mismatch")
    events = {n: {} for n in roots}
    stats = {n: {} for n in roots}
    allowed = {"root", "pos", "kind", "axis", "mode", "cut", "left", "right", "end", "state_sha256"}
    lines = 0
    with gzip.GzipFile(fileobj=io.BytesIO(archive), mode="rb") as stream:
        for raw in stream:
            check(len(raw) <= 65536, "Archive line cap")
            e = json.loads(raw)
            n, pos = e["root"], e["pos"]
            check(type(n) is int and n in roots and type(pos) is int and pos > 0 and pos not in events[n], "Archive root/pos uniqueness")
            e = {k: v for k,v in e.items() if k in allowed}
            check(type(e["end"]) is int and e["end"] > pos and re.fullmatch("[0-9a-f]{64}",e["state_sha256"]) is not None, "Archive end/hash shape")
            if e["kind"] == "branch":
                left, right = stats[n][e["left"]], stats[n][e["right"]]
                check(e["left"] == pos + 8 and left["end"] == e["right"] and right["end"] == e["end"], "Branch cursor mismatch")
                s = {k: left[k]+right[k] for k in ("nodes","numeric_leaves","reflection_leaves","farkas_leaves","branches")}
                s["nodes"] += 1
                s["branches"] += 1
                s["height"] = 1+max(left["height"],right["height"])
            else:
                check(e["kind"] in ("numeric","reflection","farkas"), "Unknown archive event")
                s = {"nodes":1,"numeric_leaves":int(e["kind"]=="numeric"),"reflection_leaves":int(e["kind"]=="reflection"),"farkas_leaves":int(e["kind"]=="farkas"),"branches":0,"height":1}
            s["end"] = e["end"]
            events[n][pos], stats[n][pos] = e, s
            lines += 1
            check(lines <= 24504, "Archive event cap")
    check(lines == 24504, "Exactly24504 events required")
    all_edges = [(i,i+1) for i in range(8)] + [tuple(x) for x in pr]
    lookup = {edge:i for i,edge in enumerate(all_edges)}

    # Geometry only: record_math_w9a2.py:44-58; no energy/tangent/leaf math.
    def leg(s,a,b):
        return 0 if a == b else s[1][lookup[a,b]] if a < b else -s[0][lookup[b,a]]

    def split(s,i,j,q,upper):
        lo,hi = s
        a,b,w = (i,j,q) if upper else (j,i,-q)
        BB,TB = 1 << 42, 2 * (1 << 42)
        col = [max(0,BB+leg(s,x,a)) for x in range(9)]
        row = [max(0,BB+w+leg(s,b,x)) for x in range(9)]
        return ([max(l,max(0,TB-col[b]-row[a])) for l,(a,b) in zip(lo,all_edges)],
                [min(u,max(0,col[a]+row[b]-TB)) for u,(a,b) in zip(hi,all_edges)])

    packets, edits, checked = [], [], 0
    fragments = {}
    for n in range(48):
        check()
        r, bypos, summaries, base = roots[n], events[n], stats[n], bases[n]
        top = summaries[1]
        check(top["nodes"] == len(bypos) == base["counts"]["nodes"] and top["height"] == base["height"] and top["numeric_leaves"] == base["counts"]["numeric_leaves"] and top["end"] == r["end"], "Root topology/source identity mismatch")
        frontier = []
        def build_frontier(pos):
            check()
            if summaries[pos]["numeric_leaves"] <= 256:
                frontier.append(pos)
            else:
                e = bypos[pos]
                check(e["kind"] == "branch", "Large frontier node must branch")
                build_frontier(e["left"])
                build_frontier(e["right"])
        changed = top["numeric_leaves"] > 256
        if changed:
            build_frontier(1)
        positions = [pos for pos in frontier if summaries[pos]["numeric_leaves"] >= 64]
        wanted, selected, depths, visited = set(positions), [], {}, set()
        lows = [bad[i][r["indices"][i]][0] for i in range(8)]
        highs = [bad[i][r["indices"][i]][1] for i in range(8)]
        initial = (lows+[sum(lows[i:j]) for i,j in pr], highs+[sum(highs[i:j]) for i,j in pr])
        def visit(pos, geometry, depth):
            check(pos not in visited and depth < 128, "State traversal duplicate/depth overflow")
            e = bypos[pos]
            flat = [v for pair in zip(*geometry) for v in pair]+[0]
            h = digest(canonical(flat))
            check(len(flat) == 73 and all(type(v) is int and v >= 0 for v in flat) and h == e["state_sha256"], "Normalized state SHA mismatch")
            visited.add(pos)
            depths[pos] = depth
            if pos in wanted:
                selected.append({"pos":pos,"end":e["end"],"depth":depth,"fuel":128-depth,
                    "state_73_fields_M0":flat,"canonical_JSON_LF_sha256":h,"topology":summaries[pos]})
            if e["kind"] == "branch":
                check(type(e["axis"]) is int and 0 <= e["axis"] < 36 and type(e["cut"]) is int, "Branch geometry fields")
                i,j = all_edges[e["axis"]]
                visit(e["left"],split(geometry,i,j,e["cut"],True),depth+1)
                visit(e["right"],split(geometry,i,j,e["cut"],False),depth+1)
        visit(1,initial,0)
        check(visited == set(bypos), "All archived states must be verified")
        checked += len(visited)
        check([x["pos"] for x in selected] == positions, "Selected preorder mismatch")
        selected_numeric = sum(x["topology"]["numeric_leaves"] for x in selected)
        remaining = top["numeric_leaves"]-selected_numeric
        check(not changed or (len(selected) > 0 and sum(summaries[p]["numeric_leaves"] for p in frontier) == top["numeric_leaves"]), "Frontier partition mismatch")
        if changed:
            fragments[n] = fragment(n,selected,r["indices"],r["end"])
        packets.append({"root":n,"indices":r["indices"],"end":r["end"],"root_topology":top,
            "changed":changed,"selected_hints":selected,
            "frontier":[{"pos":pos,"end":bypos[pos]["end"],"depth":depths[pos],"fuel":128-depths[pos],"selected":pos in wanted,"topology":summaries[pos]} for pos in frontier],
            "selected_numeric":selected_numeric,"parent_remaining_numeric":remaining,
            "parent_requires_full_walkCutR_fuel128":changed,"all_state_hashes_checked":len(visited)})
    check(checked == 24504, "All24504 state hashes required")
    assembled, old_cursor, new_cursor = [], 0, 0
    for m in matches:
        n = int(m["n"])
        if n not in fragments:
            continue
        kept = source[old_cursor:m.start()]
        assembled.append(kept)
        new_cursor += len(kept)
        body = fragments[n]
        new_line = (m["prefix"] + f"rcOfC WD{n} v10_r{n}_cuts v10_r{n}_cuts_ok {roots[n]['end']} v10_r{n}_parent (by decide)".encode() + m["newline"])
        replacement = body + new_line
        assembled.append(replacement)
        edits.append({"root":n,"old_byte_offset":m.start(),"old_line_utf8":m[0].decode(),
            "new_byte_offset":new_cursor,"inserted_bytes":len(body),"inserted_sha256":digest(body),
            "replacement_bytes":len(replacement),"replacement_sha256":digest(replacement),"new_root_line_utf8":new_line.decode()})
        old_cursor = m.end()
        new_cursor += len(replacement)
    assembled.append(source[old_cursor:])
    candidate = b"".join(assembled)
    check(len(candidate) <= SOURCE_CAP, "Full single-file source exceeds2000000 bytes")
    inverse = candidate
    for e in reversed(edits):
        start, size = e["new_byte_offset"],e["replacement_bytes"]
        check(digest(inverse[start:start+size]) == e["replacement_sha256"], "Projection replacement mismatch")
        inverse = inverse[:start]+e["old_line_utf8"].encode()+inverse[start+size:]
    check(inverse == source and candidate.count(b"\r\n") == source.count(b"\r\n") == 221 and candidate.endswith(b"\n") and not candidate.endswith(b"\n\n"), "Exact inverse/line-ending contract failed")
    for pin in PINS:
        check(digest((ROOT/pin["path"]).read_bytes()) == pin["sha256"], "Frozen input changed")
    changed_packets = [p for p in packets if p["changed"]]
    summary = {"changed_roots":len(changed_packets),"unchanged_roots":48-len(changed_packets),
        "selected_hints":sum(len(p["selected_hints"]) for p in packets),
        "max_selected_numeric":max(x["topology"]["numeric_leaves"] for p in packets for x in p["selected_hints"]),
        "max_parent_remaining_numeric":max(p["parent_remaining_numeric"] for p in changed_packets),
        "selected_numeric_total":sum(p["selected_numeric"] for p in packets),
        "changed_parent_remaining_numeric_total":sum(p["parent_remaining_numeric"] for p in changed_packets),
        "new_cursor_kernel_lemmas":sum(len(p["selected_hints"])+1 for p in changed_packets),
        "source_bytes":len(candidate),"source_sha256":digest(candidate),"source_delta_bytes":len(candidate)-len(source)}
    packet = {"schema":"all-large-root-cut-metadata-v1","scope":"Archive topology and normalized geometry/hash identity; not Lean stEq, proof or resource PASS",
        "rule":"Only roots with numeric_leaves>256; maximal top-down frontier with numeric_leaves<=256; select only frontier members numeric_leaves>=64.",
        "St_field_order":fields,"PR_literal_sha256":pr_sha,"COV_literal_sha256":cov_sha,
        "archive_events":lines,"all_state_hashes_checked":checked,"source_root_ends_verified":48,
        "input_pins":PINS,"roots":packets,"summary":summary,
        "geometry_attribution":"record_math_w9a2.py:44-58; replay_w9a2.py:36-38 JSON+LF interleaved lo/hi+M0",
        "new_proof_obligations":"Every raw child cursor equality, Covered composition, and whole parent walkCutR128 actual full-St equality/residual traversal remain unproved here.",
        "WL_decodes":0,"energy_tangent_or_leaf_arithmetic":0,"numeric_model_imports":0,
        "Lean_compiler_kernel_export_network_UI_Git_calls":0,"proof_PASS":False,"resource_PASS":False}
    mapping = {"schema":"v9-to-v10-exact-byte-edits-v1","original_source":PINS[0],
        "new_source":{"path":"Solution.lean","bytes":len(candidate),"sha256":digest(candidate)},
        "edits":edits,"inverse_exact_original_bytes":True,
        "unchanged_roots":[p["root"] for p in packets if not p["changed"]],
        "all_unedited_bytes_preserved":True,"CRLF_preserved":221,
        "proof_body_change_only":"Before each changed original rcN, insert helpers; original rcN name/type unchanged, replace only rcOf proof term by rcOfC. No old rcN/run shortcut."}
    outputs = {OUT/"packet.json":encoded(packet),OUT/"source-edits.json":encoded(mapping),DEST/"Solution.lean":candidate}
    readme = ("固定规则的全大根 cut 源码准备；只读取冻结 v9 和既有事件/几何归属文件。全部24504 normalized/M0 状态 SHA 及48 root indices/end 核同，不解码 WL，不执行原数值模型。\n\n"
        "每个新子 cursor 必须由现有 raw walkCut [] 的 decide +kernel 重新证明，Covered 经现有 soundness/CutsOk 组合；父 walkCutR128 保留全部实际 St 匹配与余下叶检查。此处只有元数据/字节投影，不是 Lean、独立内核、资源或官网通过。\n\n"
        "source-edits.json 给出原/新 UTF-8 offsets、原根行、新根行、插入与替换长度/hash；从新源码按新位置反向替换原行可逐字恢复 v9。原 v9、Pilot 及冻结数据未改。0 compiler/export/kernel/decoder；单次生成，无自动重试。\n").encode()
    outputs[OUT/"README.zh.md"] = readme
    outputs[DEST/"source-contract.json"] = encoded({"schema":"draft-v10-prepared-source-contract-v1","summary":summary,
        "prepared_only":True,"Lean_validated":False,"independent_kernel_validated":False,"resource_validated":False,"official_validated":False,
        "original_v9_unchanged":True,"exact_reverse_projection":True,"source_size_limit_bytes":SOURCE_CAP,
        "source_edits_path":str((OUT/"source-edits.json").relative_to(ROOT)).replace("\\","/")})
    metadata_bytes = sum(len(v) for k,v in outputs.items() if k.suffix != ".lean")
    existing_bytes = sum(f.stat().st_size for f in OUT.iterdir() if f.is_file())
    check(metadata_bytes <= META_CAP and existing_bytes+sum(map(len,outputs.values()))+30000 <= TOTAL_CAP, "Metadata/total output byte cap")
    DEST.mkdir(exist_ok=False)
    for path,raw in outputs.items():
        check()
        write(path,raw)
    execution = {"schema":"all-root-cut-source-completion-v1","completed":True,"summary":summary,
        "elapsed_seconds_before_receipt":time.monotonic()-T0,"budget_seconds":30,"attempts":1,"automatic_retries":0,
        "metadata_output_bytes":metadata_bytes,"output_caps":{"metadata":META_CAP,"source":SOURCE_CAP,"total":TOTAL_CAP},
        "all_input_pins_unchanged":True,"exact_inverse_v9":True,"Lean_compiler_kernel_export_decoder_calls":0,"proof_PASS":False}
    write(OUT/"execution.json",encoded(execution))
    for directory in (DEST,OUT):
        rows = [{"path":f.name,"bytes":f.stat().st_size,"sha256":digest(f.read_bytes())} for f in sorted(directory.iterdir()) if f.is_file()]
        write(directory/"files.json",encoded({"schema":"prepared-files-v1","scope":"Metadata/source only; zero Lean execution","files":rows}))
    check()
    print(json.dumps(execution))


if __name__ == "__main__":
    try:
        main()
    except BaseException as exc:
        failure = {"completed":False,"error":repr(exc),"elapsed_seconds":time.monotonic()-T0,
            "automatic_retry":False,"Lean_execution":0,"proof_PASS":False}
        with (OUT/"failure.json").open("xb") as stream:
            stream.write(encoded(failure)); stream.flush(); os.fsync(stream.fileno())
        raise
