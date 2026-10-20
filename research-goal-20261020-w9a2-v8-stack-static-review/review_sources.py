"""Fetch only small exact-pin primary source files; statically read PE/log metadata."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import os
import struct
import urllib.request

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
PIN = "d8b18978322de05a8f3dba51ef03cf5461676c17"
SDK = Path("C:/Users/A/.elan/toolchains/leanprover--lean4---v4.33.0-rc2")


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def write_new(path, raw):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("xb") as stream:
        stream.write(raw); stream.flush(); os.fsync(stream.fileno())


def js(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()


def main():
    require(not (HERE / "report.json").exists(), "Exclusive report already exists")
    primary = []
    for relative in ("src/runtime/thread.cpp", "src/runtime/thread.h", "src/runtime/object.cpp", "src/util/shell.cpp", "src/CMakeLists.txt"):
        url = f"https://raw.githubusercontent.com/leanprover/lean4/{PIN}/{relative}"
        request = urllib.request.Request(url, headers={"User-Agent": "Codex-static-source-review"})
        with urllib.request.urlopen(request, timeout=35) as response:
            raw = response.read(1024 * 1024 + 1)
            require(response.status == 200 and len(raw) <= 1024 * 1024, "Source response not small HTTP200")
            primary.append({"path": "primary/" + relative, "URL": url, "effective_URL": response.url,
                            "bytes": len(raw), "sha256": sha(raw), "status": response.status,
                            "ETag": response.headers.get("ETag"), "Date": response.headers.get("Date"),
                            "retrieved_at_UTC": datetime.now(timezone.utc).isoformat()})
        write_new(HERE / "primary" / relative, raw)
    local_paths = [SDK / "src/lean/Lean/Shell.lean", SDK / "bin/lean.exe",
                   ROOT / "tmp/w9a2-20261020/v8-resource-v1/terminal.json",
                   ROOT / "tmp/w9a2-20261020/v8-resource-v1/memory.jsonl",
                   ROOT / "research-goal-20261020-w9a2-v8-resource-gate-v1/gate.json",
                   ROOT / "research-goal-20261020-w9a2-delivery/draft-v8/Solution.lean"]
    inputs = [{"path": str(path), "bytes": path.stat().st_size, "sha256": sha(path.read_bytes())} for path in local_paths]
    executable = local_paths[1].read_bytes()
    require(sha(executable) == "bc137e6662c48eedf2cdf167fb176080e18a15f57e248d214df0cb3939248683", "Wrong pinned Lean executable")
    pe = struct.unpack_from("<I", executable, 0x3c)[0]
    require(executable[pe:pe+4] == b"PE\0\0", "Wrong PE signature")
    optional = pe + 24
    require(struct.unpack_from("<H", executable, optional)[0] == 0x20b, "Expected PE32+")
    pe_data = {"method": "Static byte parsing only, no image load or native/API call", "PE_offset": pe,
               "optional_header_offset": optional, "machine": struct.unpack_from("<H", executable, pe+4)[0],
               "SizeOfStackReserve": struct.unpack_from("<Q", executable, optional+72)[0],
               "SizeOfStackCommit": struct.unpack_from("<Q", executable, optional+80)[0]}
    require(pe_data["SizeOfStackReserve"] == 104857600 and pe_data["SizeOfStackCommit"] == 4096, "Unexpected PE stack defaults")
    terminal = json.loads(local_paths[2].read_bytes())
    samples = [json.loads(line) for line in local_paths[3].read_bytes().splitlines()]
    memory = {"actual_child_exit_code": terminal["actual_child_exit_code"],
              "elapsed_seconds": terminal["elapsed_seconds"], "samples": len(samples),
              "max_observed_PeakWorkingSetSize": terminal["max_observed_PeakWorkingSetSize"],
              "max_observed_PeakPagefileUsage": terminal["max_observed_PeakPagefileUsage"],
              "resource_limit_exceeded": terminal["resource_limit_exceeded"],
              "compiler_resource_gate_passed": terminal["compiler_resource_gate_passed"],
              "thread_count_measured": False}
    require(memory["samples"] == 24 and memory["resource_limit_exceeded"] is True and memory["compiler_resource_gate_passed"] is False, "Unexpected actual resource result")
    for path, row in zip(local_paths, inputs):
        require(path.stat().st_size == row["bytes"] and sha(path.read_bytes()) == row["sha256"], "Frozen local input changed")
    report = {"schema": "w9a2-v8-stack-static-review-v1", "scope": "Only exact-pin GitHub primary-source reads, Microsoft documentation reads via browser, and static local PE/log metadata. No Lean/compiler/version/kernel/probe/API execution, no source/gate/counter changes.",
      "Lean_commit": PIN, "actual_closed_resource_receipt": memory, "static_PE_defaults": pe_data,
      "argument": {"value_KiB": 262144, "Shell_source_lines_1based": [329, 337],
                   "rounding_formula": "(argument / 4 * 4) * 1024 bytes, then runtime adds stack buffer", "requested_bytes_before_buffer": 268435456,
                   "thread_header_default_buffer_bytes": 131072, "configured_lthread_reserve_before_OS_rounding": 268566528},
      "primary_findings": [
        {"source": "src/runtime/thread.cpp", "lines_1based": [21, 27, 68, 77, 92, 100],
         "finding": "64-bit source fallback stack size is1GiB unless build macro overridden. The setter adds128KiB buffer. Windows lthread calls CreateThread with STACK_SIZE_PARAM_IS_A_RESERVATION, deliberately making this size reserve rather than initial commit."},
        {"source": "src/runtime/thread.h", "lines_1based": [12, 14], "finding": "Fallback LEAN_STACK_BUFFER_SPACE=128*1024 bytes."},
        {"source": "src/util/shell.cpp", "lines_1based": [305, 343],
         "finding": "Environment stack setting is applied before CLI parsing and overridden by --tstack. After options, shell constructs task manager and runs shell main inside run_with_thread_stack."},
        {"source": "src/runtime/object.cpp", "lines_1based": [679, 684, 748, 795, 929, 950],
         "finding": "Standard and dedicated workers use lthread. -j1 sets the standard-worker budget, not a measured total thread count; blocked in-pool Task.get can temporarily increase that budget and dedicated-priority work has separate workers."},
        {"source": "src/CMakeLists.txt", "lines_1based": [170, 180],
         "finding": "Windows build sets executable linker stack reserve100MiB. Actual executable PE independently records reserve100MiB and initial stack commit4KiB."}
      ],
      "Microsoft_primary_sources": [
        {"URL": "https://learn.microsoft.com/en-us/windows/win32/api/processthreadsapi/nf-processthreadsapi-createthread", "finding": "With STACK_SIZE_PARAM_IS_A_RESERVATION, dwStackSize specifies reserve; without it, it specifies commit."},
        {"URL": "https://learn.microsoft.com/en-us/windows/win32/procthread/thread-stack-size", "finding": "With reservation flag, initial commit comes from executable header; additional reserved pages are committed as needed. Committed but unreferenced pages need not be resident."}
      ],
      "conclusion": "Source contradicts the simple claim that every thread initially commits256MiB from --tstack. The actual executable default initial commit is4KiB; the large argument reserves address space. Deep actual stack use can still commit touched pages, but thread count and stack commitment were not measured. The7.7GB process commit cannot be quantitatively attributed to stacks from these records.",
      "unresolved": ["Actual process thread count over time", "Per-thread committed-stack pages and high-water marks", "Exact attribution between mappings/heaps/stacks", "Whether other platform/runtime mechanisms dominate the commit-to-RSS gap"],
      "stop_boundary": "No retry, higher cap, smaller stack flag, new source or new enabled gate is proposed or executed here. The failed run is not a mathematical rejection, official OOM or candidate PASS. v8 materials remain parked.",
      "local_input_hashes_before_after_identical": True, "local_inputs": inputs, "primary_files": primary,
      "proof_execution_count": 0, "native_API_or_probe_count": 0, "source_mutation_count": 0}
    write_new(HERE / "report.json", js(report))
    write_new(HERE / "fetch-observations.json", js(primary))
    files = []
    for path in [HERE / "report.json", HERE / "fetch-observations.json", Path(__file__), *[HERE / row["path"] for row in primary]]:
        raw = path.read_bytes(); files.append({"path": path.relative_to(HERE).as_posix(), "bytes": len(raw), "sha256": sha(raw)})
    manifest = js({"schema": "stack-static-review-files-v1", "files": files, "proof_execution_count": 0, "native_API_or_probe_count": 0})
    write_new(HERE / "files.json", manifest)
    print(json.dumps({"manifest_sha256": sha(manifest), "files": len(files), "source_fetches": len(primary), "proof_execution_count": 0}))


if __name__ == "__main__":
    main()
