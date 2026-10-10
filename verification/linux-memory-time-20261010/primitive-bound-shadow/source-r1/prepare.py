"""Windows source-only preparation. Never imports a Lean/runtime library."""
from pathlib import Path
import difflib
import hashlib
import json
import re

SOURCE = Path(r"E:\codex-build\RH-Zero-Proportion-Formalization\tmp\global-sync-except-am8-source-only-20261010\Solution.global-sync-except-am8.lean")
SOURCE_SHA = "5227a25ea2c5f18c83e0a85c756e34ec9a0176a1ba9d1cd5f5556aab836ba7a2"
OUT = Path(__file__).resolve().parent
START, END = 1933916, 1936778
FIRST, LAST = 23115, 23182
ORIGINAL_NAME = "primitiveBound_sound_probe_original"
EXPLICIT_NAME = "primitiveBound_sound_probe_explicit"
NAMESPACE = "RHWeil.RecordSubmission.FiniteCertificate"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def write(name, data):
    dest = OUT / name
    assert not dest.exists(), f"Refuse existing prepared output: {dest}"
    dest.write_bytes(data)
    return {"path": str(dest), "bytes": len(data), "sha256": sha(data)}


data = SOURCE.read_bytes()
assert len(data) == 1993837 and sha(data) == SOURCE_SHA
assert b"\r" not in data
lines = data.splitlines(keepends=True)
raw = data[START:END]
assert raw == b"".join(lines[FIRST-1:LAST])
assert raw.startswith(b"theorem primitiveBound_sound {g : Nat ")
assert raw.endswith(b"    exact le_min hfirst hsecond\n")
signature, body = raw.split(b" := by\n", 1)
assert b"primitiveBound_sound" not in body
assert not re.search(rb"\b(?:sorry|axiom|native_decide)\b", body)

replacements = [
    (23138, b"        linarith\n", b"        simpa only [neg_mul] using hrev\n"),
    (23155, b"        nlinarith\n", b"        linear_combination hd + 163840 * hs\n"),
    (23165, b"        nlinarith\n", b"        linear_combination 163840 * hs - hd\n"),
    (23180, b"    nlinarith\n", b"    linear_combination 163840 * ht - hd\n"),
]
explicit_lines = raw.splitlines(keepends=True)
for source_line, before, after in replacements:
    index = source_line - FIRST
    assert explicit_lines[index] == before, (source_line, explicit_lines[index])
    explicit_lines[index] = after
explicit_raw = b"".join(explicit_lines)
explicit_signature, explicit_body = explicit_raw.split(b" := by\n", 1)
assert explicit_signature == signature
assert len(explicit_raw) - len(raw) == 101
actual_changed = [FIRST+i for i, (a, b) in enumerate(zip(raw.splitlines(), explicit_raw.splitlines())) if a != b]
assert actual_changed == [x[0] for x in replacements]
restored = explicit_raw.splitlines(keepends=True)
for source_line, before, after in replacements:
    assert restored[source_line-FIRST] == after
    restored[source_line-FIRST] = before
assert b"".join(restored) == raw

# Preserve every explicit active namespace/open/section/source-option line.
context = lines[232] + b"".join(lines[22573:22580]) + b"".join(lines[22935:22937])
assert context == (
    b"set_option Elab.async false\n"
    b"section RHWeilBundleModule_11\n"
    b"open scoped BigOperators\n"
    b"noncomputable section\n"
    b"set_option maxRecDepth 100000\n"
    b"set_option maxHeartbeats 0\n"
    b"namespace RHWeil.RecordSubmission.FiniteCertificate\n"
    b"open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD\n"
    b"open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell AMW.Cert.PC8CL\n"
    b"open RHWeil.RecordSubmission.FiniteCertificateData\n"
)
header = (
    b"/- Copyright 2026 Li Xiang (lixiang90). Apache-2.0.\n"
    b"Prepared source-only controlled shadow probe; not Lean checked.\n"
    b"The target proof is copied from frozen r6 source; see metadata.json. -/\n"
    b"import Solution.Candidate\n"
    + context
)
begin = (
    b"run_cmd do\n"
    b"  let env \xe2\x86\x90 Lean.getEnv\n"
    b"  discard <| IO.wait env.checked\n"
    b"  let ms \xe2\x86\x90 IO.monoMsNow\n"
    b"  IO.eprintln s!\"PRIMITIVE_PROBE_BEGIN {ms}\"\n"
)
end_marker = (
    b"run_cmd do\n"
    b"  let env \xe2\x86\x90 Lean.getEnv\n"
    b"  discard <| IO.wait env.checked\n"
    b"  let ms \xe2\x86\x90 IO.monoMsNow\n"
    b"  IO.eprintln s!\"PRIMITIVE_PROBE_END {ms}\"\n"
)


def probe(chunk, name):
    assert len(ORIGINAL_NAME) == len(EXPLICIT_NAME)
    renamed = chunk.replace(b"theorem primitiveBound_sound ", ("theorem " + name + " ").encode(), 1)
    assert renamed.replace(("theorem " + name + " ").encode(), b"theorem primitiveBound_sound ", 1) == chunk
    footer = (
        end_marker
        + (f"#check {name}\n#print axioms {name}\n").encode()
        + b"end RHWeil.RecordSubmission.FiniteCertificate\nend\nend RHWeilBundleModule_11\n"
    )
    return header + begin + renamed + footer


original_source = probe(raw, ORIGINAL_NAME)
explicit_source = probe(explicit_raw, EXPLICIT_NAME)
assert len(explicit_source) - len(original_source) == 101
normalized_explicit = explicit_source.replace(EXPLICIT_NAME.encode(), ORIGINAL_NAME.encode())
whole_differences = [i+1 for i, (a, b) in enumerate(zip(original_source.splitlines(), normalized_explicit.splitlines())) if a != b]
assert len(whole_differences) == 4

# Explicit later attributes/instances/syntax changes only, not a semantic parser.
later = b"".join(lines[LAST:])
attribute_matches = list(re.finditer(rb"(?m)^\s*(?:attribute\b|@\[)", later))
instance_matches = list(re.finditer(rb"(?m)^\s*(?:private\s+)?instance\b", later))
syntax_matches = list(re.finditer(rb"(?m)^\s*(?:(?:local|scoped)\s+)?(?:macro\b|elab(?:_rules)?\b|notation\b|infix\b|prefix\b|postfix\b|initialize\b)", later))
option_matches = list(re.finditer(rb"(?m)^\s*set_option\b", later))
assert not attribute_matches and not instance_matches and not syntax_matches and not option_matches

outputs = {
    "original": write("PrimitiveOriginal.lean", original_source),
    "explicit": write("PrimitiveExplicit.lean", explicit_source),
    "original_extracted_declaration": write("original-extracted-declaration.txt", raw),
    "four_line_body_diff": write("four-line-body.diff", "".join(difflib.unified_diff(
        raw.decode().splitlines(keepends=True), explicit_raw.decode().splitlines(keepends=True),
        fromfile="frozen-r6-declaration", tofile="uncompiled-four-line-proposal",
    )).encode()),
}
metadata = {
    "status": "PREPARED_SOURCE_ONLY_NOT_LEAN_CHECKED",
    "lean_run": False, "runtime_started": False, "cache_accessed": False,
    "public_candidate_modified": False,
    "frozen_source": {"path": str(SOURCE), "sha256": SOURCE_SHA, "bytes": len(data)},
    "original_declaration": {"name": f"{NAMESPACE}.primitiveBound_sound", "first_line": FIRST, "last_line": LAST,
        "byte_start_zero": START, "byte_end_exclusive": END, "bytes": len(raw), "sha256": sha(raw)},
    "signature": {"bytes": len(signature), "sha256": sha(signature), "explicit_identical_before_name_change": True},
    "original_body": {"bytes": len(body), "sha256": sha(body)},
    "explicit_body": {"bytes": len(explicit_body), "sha256": sha(explicit_body)},
    "context": {"sha256": sha(context), "original_source_lines": [233, *range(22574,22581), 22936,22937], "copied_exact": True},
    "roots": {"original": f"{NAMESPACE}.{ORIGINAL_NAME}", "explicit": f"{NAMESPACE}.{EXPLICIT_NAME}"},
    "four_line_changes": [{"original_source_line": n, "before": a.decode().rstrip("\n"), "after": b.decode().rstrip("\n"), "delta_bytes": len(b)-len(a)} for n,a,b in replacements],
    "whole_probe_delta_bytes": len(explicit_source)-len(original_source),
    "whole_probe_changed_lines_after_normalizing_equal_length_names": whole_differences,
    "guard_exact_type_text_unchanged": True,
    "guard_original_target_not_referenced_in_bodies": True,
    "guard_restore_four_lines_recovers_exact_original_chunk": True,
    "guard_no_sorry_axiom_native_decide_tokens_in_body": True,
    "original_candidate_headroom_bytes": 2000000-len(data),
    "raw_proposed_candidate_headroom_bytes": 2000000-len(data)-101,
    "candidate_rebundled": False,
    "later_environment_static_audit": {
        "source_first_line": LAST+1, "source_last_line": len(lines), "suffix_bytes": len(later), "suffix_sha256": sha(later),
        "explicit_attribute_or_annotation_count": len(attribute_matches), "explicit_instance_count": len(instance_matches),
        "explicit_syntax_or_initialize_count": len(syntax_matches), "explicit_set_option_count": len(option_matches),
        "later_open_commands": ["23584: open AMW.Cert.PC8CLData", "24168: open scoped BigOperators", "24170: open RHWeil.RecordSubmission.FiniteCertificate"],
        "interpretation": "No explicit later simp/reducibility attributes, instances, syntax extensions, or options were found. Later opens are scoped to source sections and are not reproduced as proof context. Both probes import the same complete module. Static search is not a semantic environment snapshot.",
    },
    "imported_artifact_reported_by_owner_not_read_here": {
        "module": "Solution.Candidate", "olean_sha256": "10b3102a06d9dca49000fc6741b3c164a37903db56af80f7131ea0c5b4b8a637", "olean_bytes": 92549312,
        "compile_pass_reported": True, "compile_seconds_reported": 2993.462, "resource_fit_reported": False, "memory_failcnt_reported": 64,
        "fresh_three_root_audit_pass_reported": True, "fresh_three_root_audit_seconds_reported": 25.023,
    },
    "comparison_limits": [
        "The imported module contains later unannotated declarations and the original target. Source guards prevent a direct shortcut; actual used-constant checks must exclude the original target.",
        "Both sources reconstruct the explicit pre-target namespace/open/options, but an imported post-module environment is not the original in-situ command-prefix environment.",
        "No parsed attribute-table snapshot or actual theorem-type equality check has been executed. Those remain runtime gates.",
        "BEGIN/END commands are identical instrumentation, awaiting checked environment. Import time precedes BEGIN. END follows actual checked environment, but source has not been tested.",
        "Any profiler/trace CLI options must be identical for the pair and recorded. Trace timings are diagnostic, not controlled speed measurements.",
        "Two tiny probe compiles do not establish full-candidate timing, kernel-replay gain, serial Nano gain, official resource fit, or website acceptance.",
        "Candidate raw +101 bytes is not a fresh numeral-dictionary rebundling result.",
    ],
    "outputs": outputs,
    "preparation_script": {"path": str(Path(__file__).resolve()), "bytes": Path(__file__).stat().st_size, "sha256": sha(Path(__file__).read_bytes())},
}
write("metadata.json", (json.dumps(metadata, indent=2, ensure_ascii=False)+"\n").encode())
print(json.dumps({"status": metadata["status"], "outputs": outputs, "source_pair_delta": 101}, indent=2))
