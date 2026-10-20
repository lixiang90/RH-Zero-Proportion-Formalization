"""One authorized v11 Windows compiler/C-generation resource measurement; no replay or retries.

This file is prepared only. The distributed gate is disabled and has no runner
hash or execution approval. Root must freeze a different enabled gate before execution.
"""
from __future__ import annotations
import argparse
import ctypes
from ctypes import wintypes
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
FIXED_WORK = ROOT / "tmp/w9a2-20261021/v11-resource-v1"
BASELINE_GATE = ROOT / "research-goal-20261016/gates/w9a2-fullchain-v2-20261020.json"
BASELINE_SHA = "3ebcc3b75ee2a75775281a2a0e9321f7610baddcab5965fcf002fd51e2d763fd"
PEAK_LIMIT_BYTES = 7 * 1024**3
TRUSTED = (
    ("ChallengeDeps", "ChallengeDeps.olean", "a9127aa6c9a70793124b7b08c16baac0b205c4d717a44a313de812534aa01542",
     "205f89abe20f187ae73cfeff222940f3082b62386dc70d83f1772947da20bac0", "f05666d0745edbf2dac6ce2a4de675abd1bba3c336fe24aebb80f27d1365ebbd"),
    ("ChallengeDeps.CandidateSpec", "ChallengeDeps/CandidateSpec.olean", "ccff101655371a13baf9d0d9ee6c97201db56493ef8011d3c46e6c4aeb5c037b",
     "6fcbe7e22f2b1e648abe07838ae8f319afaff621924d1cec4f8afd341d2f0cf2", "a503e0611337561cdc82e96129045c19d7146ddbd66f03876c18d10554ea9f2c"),
)


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def utc():
    return datetime.now(timezone.utc).isoformat()


def json_bytes(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()


def write_new(path, raw):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("xb") as stream:
        stream.write(raw)
        stream.flush()
        os.fsync(stream.fileno())


def workspace_path(value):
    require(isinstance(value, str) and value, "Missing workspace path")
    path = Path(value)
    if not path.is_absolute():
        path = ROOT / path
    path = path.resolve()
    require(path.is_relative_to(ROOT.resolve()), "Path escapes the workspace")
    return path


class MemoryCountersEx(ctypes.Structure):
    _fields_ = [("cb", wintypes.DWORD), ("PageFaultCount", wintypes.DWORD)] + [
        (name, ctypes.c_size_t) for name in (
            "PeakWorkingSetSize", "WorkingSetSize", "QuotaPeakPagedPoolUsage", "QuotaPagedPoolUsage",
            "QuotaPeakNonPagedPoolUsage", "QuotaNonPagedPoolUsage", "PagefileUsage", "PeakPagefileUsage", "PrivateUsage")]


class Attempt:
    def __init__(self, args):
        self.args = args
        self.t0 = time.monotonic()
        self.deadline = self.t0 + 3200.0
        self.work = None
        self.proc = None
        self.samples = []
        self.final_memory_observed = False
        self.timed_out = False
        self.resource_limited = False
        self.error = None
        self.immutable = []
        self.receipt = {"schema": "w9a2-v11-compiler-resource-terminal-v1",
            "scope": "One v11 source compiler run with C generation and own-child memory counters; no exporter/kernel/replay/fullchain",
            "started_at_UTC": utc(), "parent_pid": os.getpid(), "parent_argv": sys.argv,
            "monotonic_t0": self.t0, "total_budget_seconds": 3200,
            "automatic_retries": 0, "automatic_repairs": 0,
            "metric": "PeakWorkingSetSize", "commit_diagnostic_only": True,
            "source_discovery_or_repair_performed": False, "cached_user_Candidate_imported": False,
            "fresh_full_runtime_closure_audit_performed": False,
            "equivalent_to_official_Linux_8GB_cgroup": False,
            "official_setup_used": False,
            "official_command_difference": "This Windows diagnostic uses existing trusted import libraries and cached CandidateSpec, without official --setup. It does not emulate official Linux resource containment or the whole pipeline.",
            "actual_parent_exit_code_observed_externally": None,
            "actual_parent_exit_requires_original_root_tool_observation": True,
            "official_accepted": False, "independent_kernel_passed": False, "fullchain_passed": False}

    def remaining(self):
        result = self.deadline - time.monotonic()
        require(result > 0, "Unified 3200-second resource deadline expired")
        return result

    def file_pin(self, path, expected=None, remember=False):
        self.remaining()
        digest = hashlib.sha256()
        size = 0
        with path.open("rb") as stream:
            while block := stream.read(1024 * 1024):
                self.remaining()
                digest.update(block)
                size += len(block)
        result = {"path": str(path), "bytes": size, "sha256": digest.hexdigest()}
        if expected is not None:
            require(result["sha256"] == expected, "Hash mismatch: " + str(path))
        if remember:
            self.immutable.append(result)
        return result

    def pinned_row(self, row, remember=True):
        require(isinstance(row, dict) and isinstance(row.get("sha256"), str) and len(row["sha256"]) == 64,
                "Missing exact input SHA256")
        path = workspace_path(row["path"])
        pin = self.file_pin(path, row["sha256"], remember)
        if row.get("bytes") is not None:
            require(pin["bytes"] == row["bytes"], "Input byte-size mismatch")
        return path

    def preflight(self):
        require(__debug__ and os.name == "nt", "Only non-optimized Windows Python is supported")
        gate_path = workspace_path(self.args.gate)
        require(sha(gate_path.read_bytes()) == self.args.gate_sha256, "Gate SHA256 mismatch")
        gate = json.loads(gate_path.read_bytes())
        self.gate = gate
        require(gate.get("schema") == "w9a2-v11-resource-gate-v1", "Wrong gate schema")
        require(gate.get("allow_compiler_execution") is True and gate.get("proposal_only") is False,
                "Disabled proposal is not execution authorization")
        require(gate.get("sole_owner") == "/root" and gate.get("candidate_version") == "v11", "Wrong owner/version")
        require(gate.get("runner_sha256") == sha(Path(__file__).read_bytes()), "Runner pin missing or changed")
        self.file_pin(Path(__file__).resolve(), gate["runner_sha256"], remember=True)
        require(gate.get("total_budget_seconds") == 3200 and gate.get("automatic_retries") == 0
                and gate.get("automatic_repairs") == 0, "Fixed resource limits changed")
        require(gate.get("observed_peak_stop_bytes") == PEAK_LIMIT_BYTES, "Peak resource threshold changed")
        require(gate.get("metric") == "PeakWorkingSetSize" and gate.get("commit_diagnostic_only") is True,
                "Only peak working-set RSS may trigger the resource stop; commit is diagnostic")
        review_011 = self.pinned_row(gate["macro_review_011"])
        import_review = self.pinned_row(gate["import_memory_static_independent"])
        require(review_011 == (ROOT / "research-goal-20261016/macro-reviews/011-20261020.zh.md").resolve(),
                "Exact macro011 evidence path required")
        require(import_review == (ROOT / "research-goal-20261020-w9a2-v8-import-memory-static-independent/files.json").resolve(),
                "Exact independent import-memory evidence path required")
        self.receipt["metric_change_evidence"] = {"macro_review_011": self.file_pin(review_011),
            "import_memory_static_independent": self.file_pin(import_review)}
        require(gate.get("root_authorized_narrow_historical_cache_reuse") is True, "Narrow cache reuse not authorized")
        require(gate.get("fresh_full_runtime_closure_audit_claimed") is False, "Cannot claim a fresh runtime audit")
        require(workspace_path(gate["work_directory"]) == FIXED_WORK.resolve(), "Wrong exclusive work directory")
        ownership_path = self.pinned_row(gate["root_ownership_observation"])
        ownership = json.loads(ownership_path.read_bytes())
        require(ownership.get("no_other_W9A2_compiler_processes") is True
                and ownership.get("scope") == "this W9A2 workspace/Lean4.33 pipeline only"
                and ownership.get("sole_owner") == "/root",
                "Root must first confirm current W9A2-only process exclusivity")
        observed = datetime.fromisoformat(ownership["observed_at_UTC"].replace("Z", "+00:00"))
        require(0 <= (datetime.now(timezone.utc) - observed).total_seconds() <= 300, "Root ownership observation is stale")
        require(not FIXED_WORK.exists(), "Exclusive work directory already exists; no retry/reuse")
        self.file_pin(BASELINE_GATE, BASELINE_SHA, remember=True)
        baseline = json.loads(BASELINE_GATE.read_bytes())
        runtime = baseline["runtime"]
        self.runtime = runtime
        self.lean = Path(runtime["lean"]["path"]).resolve()
        self.file_pin(self.lean, runtime["lean"]["sha256"], remember=True)
        require(Path(sys.executable).resolve() == Path(runtime["python_controller"]["path"]).resolve(), "Wrong Python controller")
        self.file_pin(Path(sys.executable).resolve(), runtime["python_controller"]["sha256"], remember=True)
        source = self.pinned_row(gate["source"])
        require(source.name == "Solution.lean" and source.parent.name == "draft-v11", "Fixed v11 source is required")
        require(self.file_pin(source)["bytes"] <= 2000000, "Source exceeds size contract")
        self.pinned_row(gate["frozen_source_manifest"])
        self.pinned_row(gate["independent_static_source_review"])
        self.packages = [Path(value).resolve() for value in runtime["package_libs"]]
        package_root = Path(runtime["package_root"]).resolve()
        require(len(self.packages) == 10 and len(set(self.packages)) == 10, "Wrong historical package library list")
        forbidden = ("ChallengeDeps.olean", "ChallengeDeps/CandidateSpec.olean", "Challenge/Candidate.olean",
                     "Solution/Candidate.olean", "StructuralW9A220261020/Core.olean", "StructuralW9A220261020/Final.olean")
        for lib in self.packages:
            require(lib.is_relative_to(package_root) and lib.is_dir(), "Package path escaped historical clean overlay")
            require(not any((lib / relative).exists() for relative in forbidden), "Package library contains candidate/trusted output")
        cached = []
        old = ROOT / "tmp/w9a2-20261020/fullchain-v2"
        for module, relative, artifact_sha, terminal_sha, source_sha in TRUSTED:
            terminal_path = old / "logs" / ("ordinary-" + module + ".terminal.json")
            terminal_pin = self.file_pin(terminal_path, terminal_sha, remember=True)
            terminal = json.loads(terminal_path.read_bytes())
            require(type(terminal["exit_code"]) is int and terminal["exit_code"] == 0, "Trusted ordinary step was not exit0")
            trusted_source = old / "source" / Path(*module.split(".")).with_suffix(".lean")
            trusted_pin = self.file_pin(trusted_source, source_sha, remember=True)
            artifact = old / "lib" / relative
            artifact_pin = self.file_pin(artifact, artifact_sha, remember=True)
            cached.append({"module": module, "relative": relative, "source": trusted_pin,
                           "prior_actual_terminal": terminal_pin, "artifact": artifact_pin})
        require(gate["source"]["sha256"] != baseline["frozen_draft"]["solution_sha256"], "Old source cannot be measured as v11")
        self.receipt.update({"gate": self.file_pin(gate_path, self.args.gate_sha256, remember=True),
            "source": self.file_pin(source), "reused_trusted_modules": cached,
            "historical_runtime_closure_reference_not_reaudited": runtime["closure_manifest"],
            "historical_runtime_gate": self.file_pin(BASELINE_GATE),
            "package_libs_reused_without_recursive_data_rehash": list(map(str, self.packages)),
            "runtime_reuse_scope": "Pinned Lean/Python executables, two pinned trusted source/olean/actual-terminal records, and the exact historical clean package-overlay paths. The SDK, DLL closure and package data trees are historical trust; no fresh complete closure audit or cross-platform evidence is claimed."})
        # A permanent single-use owner marker prevents automatic reuse of this job name.
        write_new(FIXED_WORK.with_suffix(".owner.json"), json_bytes({"pid": os.getpid(), "gate_sha256": self.args.gate_sha256,
                   "monotonic_t0": self.t0, "UTC": utc()}))
        FIXED_WORK.mkdir(parents=True, exist_ok=False)
        self.work = FIXED_WORK
        for name in ("source/Solution", "trusted-lib", "output/Solution", "home", "temporary"):
            (self.work / name).mkdir(parents=True, exist_ok=False)
        self.input_source = self.work / "source/Solution/Candidate.lean"
        write_new(self.input_source, source.read_bytes())
        for row in cached:
            copied = self.work / "trusted-lib" / row["relative"]
            write_new(copied, Path(row["artifact"]["path"]).read_bytes())
            self.file_pin(copied, row["artifact"]["sha256"], remember=True)
        self.receipt["fresh_source_copy"] = self.file_pin(self.input_source, gate["source"]["sha256"], remember=True)
        self.remaining()

    def memory(self):
        counters = MemoryCountersEx()
        counters.cb = ctypes.sizeof(counters)
        require(bool(self.memory_api(wintypes.HANDLE(int(self.proc._handle)), ctypes.byref(counters), counters.cb)),
                "GetProcessMemoryInfo failed for owned child: " + str(ctypes.get_last_error()))
        return {"elapsed_seconds": time.monotonic() - self.t0, "child_pid": self.proc.pid,
            **{name: int(getattr(counters, name)) for name in ("PeakWorkingSetSize", "WorkingSetSize", "PeakPagefileUsage", "PagefileUsage", "PrivateUsage")}}

    def sample(self, journal, final=False):
        row = self.memory()
        row["final_after_wait"] = final
        self.samples.append(row)
        journal.write((json.dumps(row, separators=(",", ":")) + "\n").encode())
        journal.flush()
        os.fsync(journal.fileno())
        print(json.dumps({"elapsed_s": round(row["elapsed_seconds"], 3), "child_pid": row["child_pid"],
            "peak_RSS_MiB": round(row["PeakWorkingSetSize"] / 2**20, 2),
            "peak_commit_MiB": round(row["PeakPagefileUsage"] / 2**20, 2), "final": final}), flush=True)
        self.final_memory_observed = final
        if row["PeakWorkingSetSize"] >= PEAK_LIMIT_BYTES:
            self.resource_limited = True
            raise RuntimeError("resource_limit: owned child peak RSS reached 7 GiB")

    def stop_owned_child(self):
        if self.proc is not None and self.proc.poll() is None:
            # Direct retained Popen handle only; never PID enumeration/taskkill/tree kill.
            self.proc.kill()
            self.proc.wait(timeout=15)

    def compile_once(self):
        psapi = ctypes.WinDLL("psapi", use_last_error=True)
        self.memory_api = psapi.GetProcessMemoryInfo
        self.memory_api.argtypes = [wintypes.HANDLE, ctypes.c_void_p, wintypes.DWORD]
        self.memory_api.restype = wintypes.BOOL
        base = self.work / "output/Solution/Candidate"
        self.outputs = [base.with_suffix(extension) for extension in (".olean", ".ilean", ".c")]
        command = [str(self.lean), "-j1", "-M6500", "--tstack=262144", "-DrelaxedAutoImplicit=false", "-DElab.async=false",
            "-R", str(self.work / "source"), "-o", str(self.outputs[0]), "-i", str(self.outputs[1]),
            "-c", str(self.outputs[2]), "--json", str(self.input_source)]
        env = {"PATH": self.runtime["controlled_path"],
            "LEAN_PATH": os.pathsep.join(map(str, [self.work / "trusted-lib", *self.packages])),
            "LEAN_SYSROOT": self.runtime["lean_sysroot"], "HOME": str(self.work / "home"),
            "LANG": "C.UTF-8", "LC_ALL": "C.UTF-8", "LEAN_ABORT_ON_PANIC": "1",
            "SYSTEMROOT": os.environ["SYSTEMROOT"], "WINDIR": os.environ["WINDIR"],
            "TEMP": str(self.work / "temporary"), "TMP": str(self.work / "temporary"), "USERPROFILE": str(self.work / "home")}
        self.receipt.update({"compiler_argv": command, "compiler_environment": env,
            "compiler_start_elapsed_seconds": time.monotonic() - self.t0,
            "memory_units": "bytes; PeakWorkingSetSize is peak resident working set and the sole stop metric; PeakPagefileUsage is diagnostic-only peak process commit; PrivateUsage is diagnostic-only current private commit. These are not host/system memory measurements.",
            "sampling_period_seconds": 30, "compiler_memory_flag_MiB": 6500,
            "observed_peak_stop_bytes": PEAK_LIMIT_BYTES,
            "memory_flag_is_not_a_hard_OS_RSS_limit": True})
        write_new(self.work / "started.json", json_bytes(self.receipt))
        self.remaining()
        with (self.work / "stdout.jsonl").open("xb") as stdout, (self.work / "stderr.log").open("xb") as stderr, (self.work / "memory.jsonl").open("xb") as journal:
            self.proc = subprocess.Popen(command, cwd=self.work, env=env, stdin=subprocess.DEVNULL,
                stdout=stdout, stderr=stderr, creationflags=subprocess.CREATE_NO_WINDOW, shell=False)
            self.receipt["child_pid"] = self.proc.pid
            self.receipt["child_started_UTC"] = utc()
            write_new(self.work / "child.json", json_bytes({"parent_pid": os.getpid(), "child_pid": self.proc.pid,
                "argv": command, "monotonic_started": time.monotonic(), "owned_Popen_handle": True}))
            try:
                self.sample(journal)
                next_sample = time.monotonic() + 30
                while self.proc.poll() is None:
                    left = self.deadline - time.monotonic()
                    if left <= 0:
                        self.timed_out = True
                        raise TimeoutError("Unified 3200-second deadline; terminate only this owned compiler")
                    try:
                        self.proc.wait(timeout=min(left, max(0.01, next_sample - time.monotonic())))
                    except subprocess.TimeoutExpired:
                        self.sample(journal)
                        next_sample = time.monotonic() + 30
                self.proc.wait()  # Retained actual process handle; no synthetic exit status.
            finally:
                self.stop_owned_child()
                self.receipt["actual_child_exit_code"] = self.proc.returncode
                try:
                    self.sample(journal, final=True)
                except Exception as exc:
                    self.receipt["final_memory_resource_limit" if self.resource_limited
                                 else "final_memory_query_error"] = repr(exc)
                for stream in (stdout, stderr):
                    stream.flush()
                    os.fsync(stream.fileno())

    def finish(self):
        if self.work is None:
            return 2
        success = False
        try:
            if self.error is None:
                require(self.proc is not None and type(self.proc.returncode) is int and self.proc.returncode == 0,
                        "Compiler did not return actual exit0")
                require(self.final_memory_observed, "No final own-process peak measurement")
                require(not self.resource_limited, "resource_limit: owned child peak threshold exceeded")
                self.receipt["output_artifacts"] = []
                for output in self.outputs:
                    require(output.is_file() and output.stat().st_size > 0, "Missing fresh compiler/C-generation output")
                    self.receipt["output_artifacts"].append(self.file_pin(output))
                for row in self.immutable:
                    self.file_pin(Path(row["path"]), row["sha256"])
                self.remaining()
                success = True
        except Exception as exc:
            self.error = repr(exc)
        for name in ("stdout.jsonl", "stderr.log", "memory.jsonl"):
            path = self.work / name
            if path.exists():
                # Cleanup/failed-run evidence can extend past the deadline,
                # and can never turn a deadline failure into success.
                self.receipt.setdefault("evidence_files", []).append({"path": str(path), "bytes": path.stat().st_size,
                    "sha256": sha(path.read_bytes())})
        elapsed = time.monotonic() - self.t0
        if elapsed > 3200:
            success = False
            self.error = self.error or "Unified deadline exceeded during final evidence collection"
        self.receipt.update({"failure": self.error, "budget_expired_and_owned_child_terminated": self.timed_out,
            "resource_limit_exceeded": self.resource_limited,
            "actual_child_exit_code": self.proc.returncode if self.proc is not None else None,
            "elapsed_seconds": elapsed, "resource_sample_count": len(self.samples),
            "final_memory_query_succeeded": self.final_memory_observed,
            "max_observed_PeakWorkingSetSize": max((r["PeakWorkingSetSize"] for r in self.samples), default=None),
            "max_observed_PeakPagefileUsage": max((r["PeakPagefileUsage"] for r in self.samples), default=None),
            "candidate_compile_and_C_generation_completed": success,
            "compiler_resource_gate_passed": success,
            "parent_exit_code_to_return_not_external_observation": 0 if success else 1,
            "finished_at_UTC": utc()})
        terminal = self.work / "terminal.json"
        raw = json_bytes(self.receipt)
        write_new(terminal, raw)
        code = 0 if success else 1
        print(json.dumps({"terminal": str(terminal), "terminal_sha256": sha(raw),
            "parent_exit_code_to_return": code, "actual_child_exit_code": self.receipt["actual_child_exit_code"],
            "compiler_resource_gate_passed": success}), flush=True)
        return code


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gate", required=True)
    parser.add_argument("--gate-sha256", required=True)
    args = parser.parse_args()
    attempt = Attempt(args)
    try:
        attempt.preflight()
        attempt.compile_once()
    except BaseException as exc:
        attempt.error = repr(exc)
        try:
            attempt.stop_owned_child()
        except Exception as cleanup_exc:
            attempt.receipt["owned_child_cleanup_error"] = repr(cleanup_exc)
        if attempt.work is None:
            print(json.dumps({"preflight_rejected": attempt.error, "compiler_spawned": False}), flush=True)
    return attempt.finish()


if __name__ == "__main__":
    raise SystemExit(main())
