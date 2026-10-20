"""Unexecuted preparation: one bounded inert-JSON scan; never calls Lean."""
import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import sys
import threading
import time

ROOT = Path(__file__).resolve().parent.parent
INPUT = ROOT / "tmp/w9a2-20261020/fullchain-v2/solution.ndjson"
EXPECTED_BYTES = 677296932
EXPECTED_SHA = "1cc0f929919e0d4f58d947223c75a82450df57da11a9fe43fd93a90d8c8433d7"
SECONDS, RSS_CAP, NAME_CAP, LINE_CAP, OUTPUT_CAP = 120, 256 << 20, 32 << 20, 1 << 20, 2 << 20
DECLS = {"def", "thm", "opaque", "axiom", "quot", "inductive"}
EXPRS = {"bvar", "natVal", "strVal", "sort", "const", "app", "lam", "forallE", "letE", "proj", "mdata"}
PUBLIC = {"candidate_strict_improvement", "candidate_critical_line_bound", "candidate_critical_line_bound_cumulative"}

def require(ok, message):
    if not ok:
        raise ValueError(message)

def natural(value):
    require(type(value) is int and 0 <= value < 2**63, "Expected bounded natural index")
    return value

def encoded(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()

def write_new(path, raw):
    with path.open("xb") as stream:
        stream.write(raw); stream.flush(); os.fsync(stream.fileno())

def memory_reader():
    # Called only by a later authorized invocation. This prepared file was never imported/run.
    if os.name == "nt":
        import ctypes
        from ctypes import wintypes
        class PMC(ctypes.Structure):
            _fields_ = [("cb", wintypes.DWORD), ("PageFaultCount", wintypes.DWORD)] + [(name, ctypes.c_size_t) for name in ("PeakWorkingSetSize", "WorkingSetSize", "QuotaPeakPagedPoolUsage", "QuotaPagedPoolUsage", "QuotaPeakNonPagedPoolUsage", "QuotaNonPagedPoolUsage", "PagefileUsage", "PeakPagefileUsage")]
        kernel = ctypes.WinDLL("kernel32", use_last_error=True)
        psapi = ctypes.WinDLL("psapi", use_last_error=True)
        kernel.GetCurrentProcess.argtypes = []; kernel.GetCurrentProcess.restype = wintypes.HANDLE
        psapi.GetProcessMemoryInfo.argtypes = [wintypes.HANDLE, ctypes.POINTER(PMC), wintypes.DWORD]
        psapi.GetProcessMemoryInfo.restype = wintypes.BOOL
        own_handle = kernel.GetCurrentProcess()
        def sample():
            counters = PMC(); counters.cb = ctypes.sizeof(counters)
            require(bool(psapi.GetProcessMemoryInfo(own_handle, ctypes.byref(counters), counters.cb)), "Own RSS query failed")
            return int(counters.WorkingSetSize), int(counters.PeakWorkingSetSize)
        return sample
    def sample():
        values = {}
        for line in Path("/proc/self/status").read_text().splitlines():
            if line.startswith(("VmRSS:", "VmHWM:")):
                key, value, units = line.split()
                require(units == "kB", "Unexpected Linux RSS units")
                values[key] = int(value) * 1024
        return values["VmRSS:"], values["VmHWM:"]
    return sample

def main():
    started = time.monotonic()
    parser = argparse.ArgumentParser()
    parser.add_argument("--authorize-once", action="store_true")
    parser.add_argument("--runner-sha256", required=True)
    parser.add_argument("--output-directory", required=True)
    args = parser.parse_args()
    require(args.authorize_once, "Disabled by default; explicit authorization required")
    runner_raw = Path(__file__).read_bytes()
    require(hashlib.sha256(runner_raw).hexdigest() == args.runner_sha256, "Wrong runner pin")
    out = Path(args.output_directory).resolve()
    require(out.is_relative_to(ROOT.resolve()) and not out.exists(), "Output must be new exclusive workspace directory")
    out.mkdir()
    stopped = threading.Event()
    rss = memory_reader()
    peak = [0]
    output_lock = threading.Lock()
    def receipt(value):
        raw = encoded(value)
        require(len(raw) <= OUTPUT_CAP, "Output budget exceeded")
        with output_lock:
            write_new(out / "result.json", raw)
    def watch():
        try:
            while not stopped.wait(.05):
                current, high = rss(); peak[0] = max(peak[0], high)
                if high >= RSS_CAP or current >= RSS_CAP or time.monotonic() - started >= SECONDS:
                    receipt({"schema": "export-structural-scan-v1", "complete": False, "success": False,
                             "reason": "RSS cap or total deadline reached", "elapsed_seconds": time.monotonic() - started,
                             "observed_peak_RSS_bytes": peak[0], "actual_exit_observed_externally": None})
                    os._exit(2)
        except BaseException:
            os._exit(3)  # Failure to observe our own resource budget is failclosed.
    watcher = threading.Thread(target=watch, daemon=True)
    watcher.start()
    try:
        stat_before = INPUT.stat()
        require(stat_before.st_size == EXPECTED_BYTES, "Input size mismatch")
        names = [""]; name_bytes = sys.getsizeof(names) + sys.getsizeof("")
        levels = 1; exprs = 0; byte_offset = 0; line_count = 0
        tags = Counter(); tag_bytes = Counter(); decl_kinds = Counter()
        digest = hashlib.sha256(); largest_segments = []; largest_literals = []; public_rows = []
        def fresh_segment(start):
            return {"start_byte": start, "bytes": 0, "expression_records": 0, "nat_decimal_characters": 0, "str_UTF8_bytes": 0}
        segment = fresh_segment(0)
        def name(index):
            natural(index); require(index < len(names), "Name reference out of range")
            return names[index]
        def level(index):
            natural(index); require(index < levels, "Level reference out of range")
        def expr(index):
            natural(index); require(index < exprs, "Expression reference out of range")
        def binder(value):
            require(value in {"default", "implicit", "strictImplicit", "instImplicit"}, "Binder kind")
        def fields(obj, expected):
            require(type(obj) is dict and set(obj) == set(expected), "Unexpected record fields")
        def decl_row(kind, obj):
            require(type(obj) is dict, "Invalid declaration")
            required = {"name", "levelParams", "type"}
            require(required <= set(obj), "Missing declaration roots")
            resolved = name(obj["name"]); expr(obj["type"])
            require(type(obj["levelParams"]) is list, "levelParams must be array")
            for n in obj["levelParams"]: name(n)
            value = obj.get("value")
            if kind in {"def", "thm", "opaque"}: expr(value)
            for n in obj.get("all", []): name(n)
            decl_kinds[kind] += 1
            return {"name": resolved, "kind": kind, "type_root": obj["type"], "value_root": value,
                    "origin": "known_v6_namespace_match_not_proven_new" if resolved.startswith(("AMW.", "RiemannFail.", "StructuralW9A220261020.", "_private.Solution.Candidate.")) or resolved in PUBLIC else "origin_unresolved"}
        def rank(rows, row, metric):
            rows.append(row)
            rows.sort(key=lambda item: (item[metric], item["end_byte"]), reverse=True)
            del rows[100:]
        with INPUT.open("rb") as stream:
            while True:
                require(time.monotonic() - started < SECONDS, "Total deadline reached")
                raw = stream.readline(LINE_CAP + 1)
                if not raw: break
                require(len(raw) <= LINE_CAP and raw.endswith(b"\n"), "Oversized or unterminated NDJSON line")
                digest.update(raw); byte_offset += len(raw); line_count += 1; segment["bytes"] += len(raw)
                require(byte_offset <= EXPECTED_BYTES, "Input larger than expected")
                obj = json.loads(raw)
                require(type(obj) is dict, "Expected JSON object")
                declarations = []
                if line_count == 1:
                    fields(obj, {"meta"})
                    require(obj["meta"] == {"exporter": {"name": "lean4export", "version": "3.1.0"}, "format": {"version": "3.1.0"}, "lean": {"githash": "d8b18978322de05a8f3dba51ef03cf5461676c17", "version": "4.33.0-rc2"}}, "Wrong metadata header")
                    tag = "meta"
                elif "in" in obj:
                    require(obj["in"] == len(names), "Nonsequential name index")
                    tag = "name"
                    if "str" in obj:
                        fields(obj, {"in", "str"}); value = obj["str"]; fields(value, {"pre", "str"})
                        require(type(value["str"]) is str, "Name string")
                        pre = name(value["pre"]); suffix = value["str"]
                    else:
                        fields(obj, {"in", "num"}); value = obj["num"]; fields(value, {"pre", "i"})
                        pre = name(value["pre"]); suffix = str(natural(value["i"]))
                    resolved = (pre + "." if pre else "") + suffix
                    require(len(resolved.encode()) <= 4096, "Resolved name too large")
                    name_bytes += sys.getsizeof(resolved) + 16
                    require(name_bytes <= NAME_CAP, "Name-table budget exceeded")
                    names.append(resolved)
                elif "il" in obj:
                    require(obj["il"] == levels and len(obj) == 2, "Level index/schema")
                    tag = next(key for key in obj if key != "il"); value = obj[tag]
                    if tag == "succ": level(value)
                    elif tag in {"max", "imax"}:
                        require(type(value) is list and len(value) == 2, "Level pair")
                        for index in value: level(index)
                    elif tag == "param": name(value)
                    else: raise ValueError("Unknown level tag")
                    levels += 1; tag = "level:" + tag
                elif "ie" in obj:
                    require(obj["ie"] == exprs and len(obj) == 2, "Expression index/schema")
                    kind = next(key for key in obj if key != "ie"); require(kind in EXPRS, "Unknown expression tag")
                    value = obj[kind]; tag = "expr:" + kind; segment["expression_records"] += 1
                    if kind == "bvar": natural(value)
                    elif kind == "sort": level(value)
                    elif kind == "natVal":
                        require(type(value) is str and value.isascii() and value.isdecimal(), "natVal decimal string")
                        segment["nat_decimal_characters"] += len(value)
                    elif kind == "strVal":
                        require(type(value) is str, "strVal string"); segment["str_UTF8_bytes"] += len(value.encode())
                    elif kind == "const":
                        fields(value, {"name", "us"}); name(value["name"])
                        require(type(value["us"]) is list, "Constant universe list")
                        for index in value["us"]: level(index)
                    elif kind == "app":
                        fields(value, {"fn", "arg"}); expr(value["fn"]); expr(value["arg"])
                    elif kind in {"lam", "forallE"}:
                        fields(value, {"name", "type", "body", "binderInfo"}); name(value["name"]); expr(value["type"]); expr(value["body"]); binder(value["binderInfo"])
                    elif kind == "letE":
                        fields(value, {"name", "type", "value", "body", "nondep"}); name(value["name"])
                        for key in ("type", "value", "body"): expr(value[key])
                        require(type(value["nondep"]) is bool, "let nondep bool")
                    elif kind == "proj":
                        fields(value, {"typeName", "idx", "struct"}); name(value["typeName"]); natural(value["idx"]); expr(value["struct"])
                    elif kind == "mdata":
                        fields(value, {"data", "expr"}); require(type(value["data"]) is dict, "Metadata object"); expr(value["expr"])
                    exprs += 1
                else:
                    require(len(obj) == 1, "Unknown outer record schema")
                    kind = next(iter(obj)); require(kind in DECLS, "Unknown declaration tag")
                    value = obj[kind]; tag = "decl:" + kind
                    if kind == "inductive":
                        fields(value, {"types", "ctors", "recs"})
                        for group in ("types", "ctors", "recs"):
                            require(type(value[group]) is list, "Inductive group must be array")
                            for item in value[group]:
                                declarations.append(decl_row(group, item))
                                for key in ("induct",):
                                    if key in item: name(item[key])
                                for n in item.get("ctors", []): name(n)
                                for rule in item.get("rules", []):
                                    fields(rule, {"ctor", "nfields", "rhs"}); name(rule["ctor"]); natural(rule["nfields"]); expr(rule["rhs"])
                    else:
                        declarations.append(decl_row(kind, value))
                tags[tag] += 1; tag_bytes[tag] += len(raw)
                if declarations:
                    row = dict(segment, end_byte=byte_offset, line=line_count, declaration_record_bytes=len(raw),
                               declaration_kind=tag, names=[item["name"] for item in declarations[:8]],
                               group_declarations=len(declarations), roots=declarations[:8], roots_truncated=len(declarations) > 8)
                    rank(largest_segments, row, "bytes"); rank(largest_literals, row, "nat_decimal_characters")
                    public_rows.extend(item | {"end_byte": byte_offset} for item in declarations if item["name"] in PUBLIC)
                    segment = fresh_segment(byte_offset)
        stat_after = INPUT.stat()
        require((stat_before.st_size, stat_before.st_mtime_ns) == (stat_after.st_size, stat_after.st_mtime_ns), "Input stat changed")
        require(byte_offset == EXPECTED_BYTES and digest.hexdigest() == EXPECTED_SHA, "Complete input hash/bytes mismatch")
        require(Path(__file__).read_bytes() == runner_raw, "Runner changed during scan")
        current, high = rss(); peak[0] = max(peak[0], high)
        require(high < RSS_CAP and current < RSS_CAP and time.monotonic() - started < SECONDS, "Final resource bound")
        result = {"schema": "export-structural-scan-v1", "complete": True, "success": True,
                  "scope": "Historical v6 export serialization only; not v8 runtime/profile or mathematical validation",
                  "input": str(INPUT), "bytes": byte_offset, "sha256": digest.hexdigest(), "full_forward_streams": 1,
                  "elapsed_seconds": time.monotonic() - started, "observed_peak_RSS_bytes": peak[0],
                  "name_storage_accounted_bytes": name_bytes, "lines": line_count, "names": len(names), "levels": levels, "expressions": exprs,
                  "record_counts": dict(tags), "record_bytes": dict(tag_bytes), "declaration_counts": dict(decl_kinds),
                  "top100_sequential_segments": largest_segments, "top100_literal_segments": largest_literals,
                  "public_roots": public_rows, "trailing_segment": segment,
                  "metric_caveat": "Previous-declaration LF to current-declaration LF serialization. Shared nodes may belong to earlier segments; dependency declarations reset boundaries. Root indices are exact, per-root DAG/type/value proof sizes and exact-new-vs-challenge set are not computed.",
                  "actual_exit_observed_externally": None, "return_intent": 0,
                  "RSS_limit_scope": "Own process current/peak RSS observed every50ms; failclosed on query failure. Not a hard OS allocator limit."}
        receipt(result)
        print(json.dumps({"result": str(out / "result.json"), "sha256": hashlib.sha256((out / "result.json").read_bytes()).hexdigest(), "complete": True}), flush=True)
        return 0
    except BaseException as error:
        receipt({"schema": "export-structural-scan-v1", "complete": False, "success": False,
                 "error_type": type(error).__name__, "error": str(error)[:1000],
                 "elapsed_seconds": time.monotonic() - started, "observed_peak_RSS_bytes": peak[0],
                 "actual_exit_observed_externally": None})
        return 1
    finally:
        stopped.set(); watcher.join(timeout=.2)

if __name__ == "__main__":
    raise SystemExit(main())
