"""Seal a source/log-only static review; no Lean, native library, or proof runner."""
from pathlib import Path
import hashlib
import json
import os
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SDK = Path("C:/Users/A/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/src/lean")
SOURCE = ROOT / "research-goal-20261020-w9a2-delivery/draft-v8/Solution.lean"

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def new(path, raw):
    with path.open("xb") as stream:
        stream.write(raw); stream.flush(); os.fsync(stream.fileno())

def data(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()

def pin(path):
    raw = path.read_bytes()
    return {"path": str(path), "bytes": len(raw), "sha256": sha(raw)}

paths = [SOURCE,
    ROOT / "tmp/w9a2-20261020/v8-resource-v2/started.json",
    ROOT / "tmp/w9a2-20261020/v8-resource-v2/terminal.json",
    ROOT / "tmp/w9a2-20261020/v8-resource-v2/stderr.log",
    ROOT / "research-goal-20261020-w9a2-v8-resource-failure-v2/root-outer-observation.json",
    ROOT / "research-goal-20261020-w9a2-v8-resource-failure-v2/files.json",
    ROOT / "research-goal-20261020-w9a2-v7-official-failure-v1/technical-log.dom.txt",
    ROOT / "research-goal-20261020-w9a2-v7-resource-static-formal/files.json",
    ROOT / "research-goal-20261020-w9a2-v7-resource-static-formal/PTT-caller-closure.json",
    SDK / "Lean/Elab/Frontend.lean", SDK / "Lean/Environment.lean",
    SDK / "Lean/KeyedDeclsAttribute.lean", SDK / "Lean/Elab/Util.lean",
    SDK / "Lean/Elab/Tactic/Decide.lean", SDK / "lake/Lake/Build/Module.lean",
    SDK / "Lean/Shell.lean"]
before = [pin(path) for path in paths]
raw = SOURCE.read_bytes()
if len(raw) != 1829382 or sha(raw) != "5424212b6d2cf70b9eeaa632d6bf429dea4e1aadb13b0fedd948d38f94f8ac6b":
    raise RuntimeError("Frozen v8 mismatch")
lines = raw.decode().splitlines()
terminal = json.loads(paths[2].read_bytes())
if terminal["actual_child_exit_code"] != 3221226505 or terminal["compiler_resource_gate_passed"] is not False:
    raise RuntimeError("Wrong actual failure")
rcs = [{"line": i + 1, "source": line} for i, line in enumerate(lines)
       if re.match(r"theorem rc\d+ :", line)]
packed = [{"name": m.group(1), "line": i + 1, "bits": int(m.group(2)), "payload_characters": len(m.group(3))}
          for i, line in enumerate(lines)
          if (m := re.match(r'def (WL\w*) : ℕ := zfNat64 (\d+) "([A-Za-z0-9+_]+)"$', line))]
if len(rcs) != 48 or len(packed) != 135 or not all("decide +kernel" in row["source"] for row in rcs):
    raise RuntimeError("Unexpected static consumer inventory")
report = {
    "schema": "w9a2-v8-interpreter-static-formal-v1",
    "scope": "Only inert exact-pin primary source GETs and static local source/log/JSON reads. No Lean/compiler/version/kernel/exporter/solver/native API/probe run; no frozen source/gate/counter changes.",
    "Lean_pin": "d8b18978322de05a8f3dba51ef03cf5461676c17",
    "actual_failure": {key: terminal[key] for key in ["actual_child_exit_code", "elapsed_seconds", "resource_limit_exceeded", "budget_expired_and_owned_child_terminated", "max_observed_PeakWorkingSetSize", "max_observed_PeakPagefileUsage", "compiler_resource_gate_passed"]},
    "interpretation": [
        {"source": "primary/src/library/ir_interpreter.cpp", "lines": [627, 670], "fact": "IR eval_body entry and its self-tail-call loop call lean::check_system(\"interpreter\"). Only stack_space_exception gets an interpreter stacktrace here; a memory_exception carries no declaration stacktrace from this wrapper."},
        {"source": "primary/src/runtime/interrupt.cpp", "lines": [108, 114], "fact": "check_system calls check_stack and check_memory. do_check_interrupted defaults false, so this site does not add a heartbeat or interruption check."},
        {"source": "primary/src/runtime/memory.cpp", "lines": [14, 18, 42, 109, 157], "fact": "g_max_memory is process-global; the polling counter is per-thread. Every200 check calls by the default macro, peak first short-circuits below the cap, then current nonzero memory at or above the cap throws. Windows non-jemalloc branch reads process PeakWorkingSetSize/WorkingSetSize. HAS_JEMALLOC branch takes precedence and measures allocator stats instead; this review does not probe the binary build configuration."},
        {"fact": "The component string names the check site, not the allocator, phase, declaration, or owner of all retained memory. Native and interpreted meta work, imports, environment/InfoTrees, IR/codegen and other live memory may coexist. The observed exception establishes Lean's own memory-limit rejection at an interpreter check point, not an OS OOM diagnosis."}
    ],
    "setup_difference": [
        {"source": "Lean/Elab/Frontend.lean", "lines": [294, 313], "fact": "With setup, load each setup.dynlib, append setup.plugins, use setup.importArts, setup.package/name/isModule and merge setup.options over CLI defaults. Without setup, use parsed imports/module flag and CLI mainModuleName/options/plugins. Thus the local resource run is not an execution-path equivalent of the website."},
        {"source": "lake/Lake/Build/Module.lean", "lines": [149, 163, 196, 222, 550, 609, 635, 646], "fact": "Lake selects precompiled import libraries/plugins when configured, computes dependencies, and puts their paths and import artifacts/options into ModuleSetup. It need not have nonempty extra dynlibs for every project."},
        {"source": "primary/src/library/ir_interpreter.cpp", "lines": [55, 57, 325, 362, 429, 442, 829, 873, 1046, 1048, 1216, 1219], "fact": "The source default interpreter.prefer_native is true. The interpreter searches loaded modules for native symbols when allowed, otherwise retains IR fallback. --setup can make imported native code available; enabling prefer_native again cannot create unavailable native code. Same-file fresh macro code is not made native by merely emitting that file's future C source."},
        {"fact": "The actual website Candidate.setup.json contents and actual loaded symbol/module set were not captured in the provided failure log. No claim that its dynlibs/plugins are nonempty, that it avoids the observed local path, or that setup alone guarantees lower memory is supported."}
    ],
    "real_consumers": {
        "macro": {"source_lines": [69, 125], "decoding_definitions": ["ZeroForgePackedNat.digit64", "ZeroForgePackedNat.decode64"], "packed_WL_calls": packed, "fact": "The local zfNat64 macro executes decode64 and returns Syntax.mkNumLit(toString value), so these executable definitions have genuine elaboration-time consumers. The decoder is not present in the resulting kernel numeral. Each source payload is expanded at its declaration; it is not decoded by every later root's kernel check."},
        "macro_SDK_bridge": {"KeyedDeclsAttribute.lean": [125, 166], "Elab/Util.lean": [134, 165], "Environment.lean": [2518, 2539], "fact": "Macro registration obtains the executable via evalConstCheck/evalConst, and macro expansion invokes the registered e.value stx. Interpreter/native fallback is relevant to this real meta path and to imported tactics, but the closed log does not identify which such function hit the limit."},
        "root_checks": rcs,
        "decide_SDK": {"source": "Lean/Elab/Tactic/Decide.lean", "lines": [75, 118], "fact": "decide +kernel builds mkDecideProof and checks it via mkAuxLemma, caching the checked proposition. It does not call nativeEqTrue, which belongs to the separate +native branch. Ordinary decide uses meta weak-head reduction then kernel checking. The tactic elaborator itself is executable meta code; this does not convert certificate reduction into native evaluation."},
        "large_data": "v8 already explicitly suppresses codegen for eight checker functions and the complete10 PTT_0..7/PTT/PT caller closure. Their ordinary kernel definitions remain available. Existing static closure shows no candidate macro/#eval/native consumer of these ten data definitions. Other large data definitions can still incur elaboration/IR/codegen costs and kernel reduction costs; no evidence localizes the actual interpreter-limit trigger to them.",
        "duplicate_walk_claim_rejected": "48 rc declarations each check their strengthened Covered goal once. Localization reuses the resulting Data.run; there is no second complete11794-leaf checker to remove."
    },
    "resource_reduction_verdict": "Evidence is insufficient for a justified new source-level resource-reduction patch from the component label. Do not disable or mark the macro decoder noncomputable, replace +kernel by +native, delete the48 root checks, or claim --setup fixes the failure. Additional noncomputable annotations only remove codegen where caller closure and no executable consumer have been independently established; the ten-data closure was already applied in v8. Parent's separate InfoTree/snapshot static study is the relevant remaining metadata-retention candidate, not established by this report.",
    "not_proven": ["Actual failing Lean declaration or source offset", "Relative memory attribution between imports/environment/InfoTrees/IR/compiler/interpreter stacks", "Actual package native symbols loaded on either platform", "Compiler completion or official/fullchain/kernel acceptance", "Any measured improvement from a proposed source change"],
    "execution_count_this_review": {"candidate_compile": 0, "export": 0, "kernel_or_solver": 0, "Lean_or_native_probe": 0},
    "source_and_inputs_before": before
}
after = [pin(path) for path in paths]
if before != after:
    raise RuntimeError("Read-only review input changed")
report["all_inputs_after_equal_before"] = True
new(HERE / "report.json", data(report))
new(HERE / "README.zh.md", ("# v8 interpreter 内存失败：静态结论\n\n"
    "原93095为实际失败：Lean在解释器通用检查点抛出memory_exception，不是本次runner主动停或超时。标签不能定位声明，更不能归因48条rc证书。\n\n"
    "固定pin源码的调用链是ir_interpreter.cpp627–670 → interrupt.cpp108–114 → memory.cpp145–157：进程总内存限额、每线程默认200次轮询；不是该解释器独占内存统计。Windows非jemalloc分支先查峰RSS再查当前RSS，jemalloc分支优先条件仍保留。\n\n"
    "--setup确能加载依赖动态库、插件、限定importArts并覆盖选项；官网setup文件实际内容未留存，所以只能认定本地与官网路径不等价，不能保证setup节省资源。prefer_native源码默认已true，不能凭再设true产生不存在的native代码。\n\n"
    "zfNat64的135处WL调用确会运行本地宏/decoder；宏返回普通Nat numeral，后续kernel不重新解码。48个decide+kernel走mkAuxLemma/kernel而非nativeEqTrue，Localization复用同run，没有第二套完整叶检查。v8的18个显式noncomputable改动保留kernel定义；10个PTT/PT定义没有宏运行consumer的闭包证据仍有效。\n\n"
    "目前没有足以单凭interpreter标签选定的新资源削减补丁。不能把decoder改noncomputable、删除rc或改native证明。另一个独立InfoTree/snapshot静审若给出安全元数据减负，须按其自己的证据审定。本包没有运行Lean、compiler、kernel、export、API或probe，没有改冻结source/gate/counter。\n\n"
    "完整精确路径、SDK行号、135处宏/48条rc静态清单及输入前后hash见report.json。此报告不声称资源门、官网或目标完成。\n").encode())
manifest = {"schema": "static-review-files-v1", "scope": "This exclusive source/log-only report package", "files": []}
for path in sorted(HERE.rglob("*")):
    if path.is_file() and path.name != "files.json":
        value = path.read_bytes()
        manifest["files"].append({"path": path.relative_to(HERE).as_posix(), "bytes": len(value), "sha256": sha(value)})
new(HERE / "files.json", data(manifest))
print(json.dumps({"manifest_sha256": sha((HERE / "files.json").read_bytes()), "report_sha256": sha((HERE / "report.json").read_bytes()), "files": len(manifest["files"]), "all_inputs_before_after_equal": True}))
