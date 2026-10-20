"""One bounded rc10 archive/topology and three normalized-geometry state packet.

Standalone stdlib only; no import of existing parser/model, no WL/leaf/margin math.
"""
from pathlib import Path
from hashlib import sha256
import gzip
import io
import json
import re
import time

ROOT = Path(__file__).resolve().parents[1]
OUT = Path(__file__).resolve().parent
T0 = time.monotonic()
LIMIT = 2_000_000
PINS = []


def check(ok=True, message="30-second metadata budget expired"):
    if not ok or time.monotonic() - T0 > 30:
        raise RuntimeError(message)


def read(relative, expected, size=None):
    path = ROOT / relative
    raw = path.read_bytes()
    check()
    digest = sha256(raw).hexdigest()
    check(digest == expected and (size is None or len(raw) == size), "Pinned input differs: " + relative)
    PINS.append({"path": relative, "bytes": len(raw), "sha256": digest})
    return raw


def write(name, value):
    raw = (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()
    check(sum(p.stat().st_size for p in OUT.iterdir() if p.is_file()) + len(raw) <= LIMIT, "2MB output cap")
    with (OUT / name).open("xb") as stream:
        stream.write(raw)


def literal(text, pattern):
    found = list(re.finditer(pattern, text, re.M))
    check(len(found) == 1, "Literal declaration must be unique")
    body = found[0].group(1)
    cursor = 0
    for token in re.finditer(r"\s+|true|false|[0-9]+|[\[\](),]", body):
        check(token.start() == cursor, "Unexpected literal token")
        cursor = token.end()
    check(cursor == len(body), "Literal tail not consumed")
    return json.loads(body.replace("(", "[").replace(")", "]")), body


def canonical(state):
    return (json.dumps(state, sort_keys=True, separators=(",", ":")) + "\n").encode("ascii")


def main():
    check(not (OUT / "packet.json").exists() and not (OUT / "failure.json").exists(), "No retry or overwrite")
    archive = read("research-goal-20261019-w9a2-certificate-analysis/walk-events.jsonl.gz",
        "1999185a8409c879a987c697d67040f431a0ccaf0dde3181cb8902ffb1d2dbff", 1596457)
    baseline = json.loads(read("research-goal-20261019-w9a2-certificate-analysis/baseline-replay.json",
        "a36441559cd2460edb31bc3e312f9379e4fc55c803d79bf8686bee017206e5c6", 115380))
    text = read("research-goal-20261021-w9a2-delivery/draft-v9/Solution.lean",
        "7552bbb829b86986798b58cf40caf998ea8c51ab19201998b533dae4b9518c99", 1861120).decode("utf-8")
    read("research-goal-20261019-w9a2-certificate-analysis/record_math_w9a2.py",
        "c6da616359214c04a9b0ecb465ff87274bf4487ddbcc986e6e3ffa92a49c2631", 6746)
    read("research-goal-20261019-w9a2-certificate-analysis/replay_w9a2.py",
        "424ceda53589cf9f3911824813220aa09fc47fa5081cf1d2c36c02cae1089322", 13457)
    pr, pr_raw = literal(text, r"^noncomputable def PR : List \(ℕ × ℕ\) := (\[[^\n]*\])\r?$")
    cov, cov_raw = literal(text, r"^noncomputable def COV : List \(List \(ℕ × ℕ × Bool\)\) := (\[[\s\S]*?\])\r?\nnoncomputable def SMAX")
    check(len(pr) == 28 and all(len(p) == 2 and all(type(x) is int and 0 <= x <= 8 for x in p) and p[0] < p[1] for p in pr), "PR shape")
    check(len(cov) == 8 and all(type(row) is list for row in cov), "COV shape")
    check(all(len(v) == 3 and type(v[0]) is int and type(v[1]) is int and 0 <= v[0] <= v[1] and type(v[2]) is bool for row in cov for v in row), "COV record shape")
    bad = [[v[:2] for v in row if not v[2]] for row in cov]
    rc = re.findall(r"^theorem rc10 : Covered \(RC ([0-9 ]+)\) := rcOf WD10 ([0-9]+) \(by decide \+kernel\) \(by decide\)\r?$", text, re.M)
    check(len(rc) == 1, "Unique original rc10 header required")
    indices = list(map(int, rc[0][0].split()))
    check(indices == [0, 0, 1, 0, 1, 0, 0, 0], "rc10 indices changed")
    base = [x for x in baseline["roots"] if x["root"] == 10]
    check(len(base) == 1 and base[0]["indices"] == indices and base[0]["end"] == int(rc[0][1]), "Baseline/source rc10 mismatch")
    events, summaries, lines = [], {}, 0
    allowed = {"root", "pos", "kind", "axis", "mode", "cut", "left", "right", "end", "state_sha256"}
    with gzip.GzipFile(fileobj=io.BytesIO(archive), mode="rb") as stream:
        for raw in stream:
            check()
            lines += 1
            check(len(raw) <= 65536, "Archive line cap")
            event = json.loads(raw)
            if event["root"] != 10:
                continue
            check(len(events) < 2500, "root10 event cap")
            e = {k: v for k, v in event.items() if k in allowed}
            check(type(e["pos"]) is int and e["pos"] not in summaries, "Duplicate/invalid event position")
            if e["kind"] == "branch":
                left, right = summaries[e["left"]], summaries[e["right"]]
                check(e["left"] == e["pos"] + 8 and left["end"] == e["right"] and right["end"] == e["end"], "Archive branch cursor mismatch")
                stats = {k: left[k] + right[k] for k in ("nodes", "numeric_leaves", "reflection_leaves", "farkas_leaves", "branches")}
                stats["nodes"] += 1
                stats["branches"] += 1
                stats["height"] = 1 + max(left["height"], right["height"])
            else:
                check(e["kind"] in ("numeric", "reflection", "farkas"), "Unknown event kind")
                stats = {"nodes": 1, "numeric_leaves": int(e["kind"] == "numeric"), "reflection_leaves": int(e["kind"] == "reflection"), "farkas_leaves": int(e["kind"] == "farkas"), "branches": 0, "height": 1}
            stats["end"] = e["end"]
            summaries[e["pos"]] = stats
            events.append(e)
    bypos = {e["pos"]: e for e in events}
    root = bypos[1]
    check(root["kind"] == "branch", "rc10 root must be a branch")
    rootstats = summaries[1]
    check(rootstats["nodes"] == len(events) == base[0]["counts"]["nodes"] and rootstats["height"] == base[0]["height"] and rootstats["numeric_leaves"] == base[0]["counts"]["numeric_leaves"] and rootstats["end"] == base[0]["end"], "Archive topology summary mismatch")
    all_edges = [(i, i + 1) for i in range(8)] + [tuple(p) for p in pr]
    lookup = {edge: n for n, edge in enumerate(all_edges)}
    lows = [bad[r][indices[r]][0] for r in range(8)]
    highs = [bad[r][indices[r]][1] for r in range(8)]
    state = (lows + [sum(lows[i:j]) for i, j in pr], highs + [sum(highs[i:j]) for i, j in pr])

    # Geometry only, copied with attribution from record_math_w9a2.py:48-58.
    # BB/TB are its lines9-10. No other model function is copied/imported/executed.
    def leg(s, a, b):
        if a == b:
            return 0
        return s[1][lookup[a, b]] if a < b else -s[0][lookup[b, a]]

    def split(s, i, j, q, upper):
        lo, hi = s
        aa, bb, w = (i, j, q) if upper else (j, i, -q)
        BB, TB = 1 << 42, 2 * (1 << 42)
        col = [max(0, BB + leg(s, x, aa)) for x in range(9)]
        row = [max(0, BB + w + leg(s, bb, x)) for x in range(9)]
        return ([max(l, max(0, TB - col[b] - row[a])) for l, (a, b) in zip(lo, all_edges)],
                [min(u, max(0, col[a] + row[b] - TB)) for u, (a, b) in zip(hi, all_edges)])

    check(type(root["axis"]) is int and 0 <= root["axis"] < 36 and type(root["cut"]) is int, "Root branch geometry fields")
    i, j = all_edges[root["axis"]]
    geometries = (("root", 1, state), ("left", root["left"], split(state, i, j, root["cut"], True)),
                  ("right", root["right"], split(state, i, j, root["cut"], False)))
    selected = []
    fields = [s for r in range(8) for s in ("l" + str(r), "u" + str(r))] + [s for a, b in pr for s in (f"A{a}{b}", f"B{a}{b}")] + ["M"]
    for role, pos, geometry in geometries:
        flat = [v for pair in zip(*geometry) for v in pair] + [0]
        digest = sha256(canonical(flat)).hexdigest()
        check(len(flat) == 73 and digest == bypos[pos]["state_sha256"], "Normalized geometry state/archive SHA mismatch: " + role)
        selected.append({"role": role, "pos": pos, "end": bypos[pos]["end"], "archive_event": bypos[pos],
            "archive_topology_only": summaries[pos], "normalized_geometry_73_fields_M0": flat,
            "canonical_JSON_with_LF_sha256": digest, "archive_state_hash_matches": True,
            "source_parent_fuel": 128, "inherited_depth_one_fuel_if_child": None if role == "root" else 127})
    for pin in PINS:
        check(sha256((ROOT / pin["path"]).read_bytes()).hexdigest() == pin["sha256"], "Input changed")
    packet = {"schema": "rc10-three-state-archive-metadata-v1", "scope": "Archive topology counts and normalized geometry/hash agreement only; NOT Lean stEq or proof PASS",
        "root": 10, "indices": indices, "root_source_end": int(rc[0][1]), "source_parent_fuel": 128,
        "PR_order": pr, "St_field_order": fields, "COV_false_BAD_intervals": bad,
        "COV_literal_sha256": sha256(cov_raw.encode()).hexdigest(), "PR_literal_sha256": sha256(pr_raw.encode()).hexdigest(),
        "archive_lines_read_sequentially": lines, "root10_events_retained": len(events), "selected": selected,
        "root10_topology_events_without_margin": events, "input_pins": PINS,
        "geometry_formula_attribution": "record_math_w9a2.py:44-58; canonical interleaved lo/hi plus M0 and JSON+LF from replay_w9a2.py:36-38",
        "caveat": "Archive states are normalized geometry with M=0. Actual parent Lean state/stEq and new cursor/proof obligations MUST be checked independently. Source equality, static topology and hash agreement are not a proof or resource PASS.",
        "WL_decode_count": 0, "leaf_arithmetic_or_margin_recomputations": 0, "existing_numeric_model_imports": 0,
        "Lean_compiler_kernel_export_network_UI_Git_calls": 0, "new_source_variant_or_proof_edits": 0,
        "additional_frontier_selection_performed": False, "elapsed_seconds_before_output": time.monotonic() - T0}
    write("packet.json", packet)
    write("execution.json", {"schema": "rc10-metadata-script-completion-v1", "metadata_only_completed": True,
        "elapsed_seconds": time.monotonic() - T0, "budget_seconds": 30, "max_output_bytes": LIMIT,
        "root10_event_limit": 2500, "attempts": 1, "automatic_retries": 0,
        "input_pins_unchanged": True, "proof_PASS": False,
        "selected_counts": [{"role": x["role"], "pos": x["pos"], **x["archive_topology_only"]} for x in selected]})
    check()
    print(json.dumps({"metadata_only_completed": True, "selected_counts": [{"role": x["role"], "pos": x["pos"], **x["archive_topology_only"]} for x in selected], "elapsed_seconds": time.monotonic() - T0}))


if __name__ == "__main__":
    try:
        main()
    except BaseException as exc:
        raw = (json.dumps({"metadata_only_completed": False, "error": repr(exc), "elapsed_seconds": time.monotonic() - T0, "proof_PASS": False}) + "\n").encode()
        with (OUT / "failure.json").open("xb") as stream:
            stream.write(raw)
        raise
