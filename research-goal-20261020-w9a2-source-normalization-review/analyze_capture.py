"""Filesystem-only checks; never executes fetched code or the proof."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def read_json(path):
    return json.loads(path.read_bytes())


def pin(path):
    raw = path.read_bytes()
    return {"path": str(path.relative_to(ROOT)).replace("\\", "/"), "bytes": len(raw), "sha256": sha(raw)}


def save(name, value):
    with (HERE / name).open("xb") as output:
        output.write((json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode())


def main():
    inputs = [p for p in HERE.rglob("*") if p.is_file() and "__pycache__" not in p.parts]
    proof = ROOT / "research-goal-20261020-w9a2-delivery/draft-v5/Solution.lean"
    old = ROOT / "submission/single-exception-overlap-accepted-20261019/official/comparison.json"
    inputs += [proof, old]
    before = {str(p): pin(p) for p in inputs}
    capture = read_json(HERE / "capture.json")
    assert capture["commit_sha"] == capture["head_after_sha"] == "1135c0386310a0a038004d3b0fe64d0237e47dce"
    assert capture["HEAD_stable_during_capture"] and capture["source_files_captured"] == 97
    for entry in capture["sources"]:
        raw = (HERE / "source" / entry["path"]).read_bytes()
        assert len(raw) == entry["bytes"] and sha(raw) == entry["sha256"]
        assert hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest() == entry["git_blob_sha1"]
    js_capture = read_json(HERE / "deployed/capture.json")
    assert js_capture["HTTP_methods"] == ["GET"] and js_capture["proof_or_website_write_calls"] == 0
    selected = []
    for row in js_capture["assets"]:
        raw = (HERE / row["file"]).read_bytes()
        assert len(raw) == row["bytes"] and sha(raw) == row["sha256"]
        if b'Creating a private no-egress E2B sandbox.' in raw and b'Public author' in raw:
            selected.append((row, raw))
    assert len(selected) == 1
    asset, raw = selected[0]
    needles = {
        "original_state": b'let[g,b]=(0,i.useState)("")',
        "replace_editor_without_normalization": b'function R(e,t){b(e),',
        "comparison_only_normalization": b'g.replace(/\\r\\n?/g,"\\n").trim()===p.replace(/\\r\\n?/g,"\\n").trim()',
        "post_original_state": b'harness:r||null,solution:g,acceptLicense:',
        "file_text_direct_to_state": b'R(await t.text(),',
        "editable_author": b'name:"displayName",required:!0,maxLength:100,defaultValue:s,disabled:$',
        "editor_change_reads_dom_value": b'onChange:e=>{let t=e.target.value;"idle"===j?b(t):R(t,',
    }
    excerpts = []
    for kind, needle in needles.items():
        assert raw.count(needle) == 1, kind
        offset = raw.index(needle)
        excerpts.append({"kind": kind, "byte_offset": offset, "needle": needle.decode(),
            "context_start_byte": max(0, offset - 100),
            "context": raw[max(0, offset - 100):offset + len(needle) + 240].decode("utf-8")})
    # Treat the historical comparison field as comparison metadata, never as
    # evidence that the receiving server normalized uploaded proof text.
    history = read_json(old)
    history_text = json.dumps(history)
    assert "1979280" in history_text and "1979279" in history_text
    assert "024902a7ef01ccba2a6c71e54682a31712417e5d3c0b4ead5f6f80ad25fd1a81" in history_text
    body = proof.read_bytes()
    assert len(body) == 1830001 and sha(body) == "650ad1762ee36ba1ddf5f6a027900b20f0f85ba087ac099fd2c99a54eaf6ae13"
    assert body.endswith(b"\n") and not body.endswith(b"\n\n") and body.count(b"\r\n") == 221
    assert body.count(b"\r") == 221
    report = {
        "scope": "Read-only public-main source and currently served anonymous client assets; no POST, no browser session, no fetched-code or proof execution",
        "commit_sha": capture["commit_sha"],
        "current_main_stable_during_capture": True,
        "deployed_client": {k: asset[k] for k in ["url", "final_url", "status", "sha256", "bytes", "file"]},
        "deployed_client_excerpts": excerpts,
        "server_source_facts": [
            {"path": "src/lib/challenge.ts", "lines": [174, 186], "fact": "solution schema has no trim transform; displayName/summary/method do have explicit trim transforms"},
            {"path": "src/lib/direct-submission.ts", "lines": [38, 80], "fact": "uses input.solution for byte bound, proof digest and returned solution"},
            {"path": "src/app/api/submissions/route.ts", "lines": [92, 150], "fact": "passes prepared solution to E2B staging and encrypted queue archive"},
            {"path": "src/lib/e2b-verifier.ts", "lines": [183, 186], "fact": "writes input.solution directly as proof/Solution.lean"},
            {"path": "src/lib/submission-archive.ts", "lines": [149, 166], "fact": "checks exact manifest+solution digest and archives JSON payload"},
        ],
        "client_source_facts": [
            {"path": "src/components/direct-submission-form.tsx", "lines": [297, 300], "fact": "normalizedSolution is used only for comparison with the noncompetitive FlowTest"},
            {"path": "src/components/direct-submission-form.tsx", "lines": [341, 354], "fact": "POST JSON contains original solution state"},
            {"path": "src/components/direct-submission-form.tsx", "lines": [143, 144, 392, 394], "fact": "file.text() enters the original solution state without trim or newline conversion"},
            {"path": "src/components/direct-submission-form.tsx", "lines": [415], "fact": "Public author is editable; only disabled while busy, with no readOnly prop"},
            {"path": "src/components/direct-submission-form.tsx", "lines": [469, 475], "fact": "manual edits replace state with DOM textarea.value; actual wire should be checked after any editor change"},
        ],
        "source_to_preserve": {**pin(proof), "CRLF_count": 221, "bare_CR_count": 0, "final_LF_count": 1},
        "historical_comparison_scope": {"input": pin(old), "public_accepted_raw_equals_local_raw": True,
            "raw_bytes": 1979280, "trimmed_preview_bytes": 1979279,
            "UI_normalization_field_is_actual_server_transform_evidence": False,
            "correction": "The existing prepared UI-normalization-preview's historical policy reference must be read as a parallel comparison procedure, not as proof of an intake transform."},
        "decision": "Do not trim or normalize frozen draft-v5 on this evidence. Current served client and current public-main server source transmit/retain the raw state. Prefer file upload with no subsequent editor changes, and verify actual wire bytes and the server-returned manifest+source digest before treating the official proof as the same production source.",
        "evidence_limits": [
            "Anonymous served client was captured, not executed; no authenticated field values or request body was read.",
            "No server deployment commit attestation was exposed by this GET capture; current main server-source conclusions have their fixed source-commit scope.",
            "No official upload, daily slot, verifier run or production claim was made.",
            "A source SHA256 alone is not the website proofDigest: website proofDigest hashes labelled manifest bytes plus labelled raw solution bytes.",
        ],
        "compiler_export_kernel_calls": 0, "website_write_calls": 0,
    }
    for p in inputs:
        assert before[str(p)] == pin(p), p
    save("review.json", report)
    save("input-pins.json", {"inputs": list(before.values()), "all_before_after_pins_equal": True})
    files = [pin(p) for p in sorted(HERE.rglob("*")) if p.is_file() and "__pycache__" not in p.parts and p.name != "files.json"]
    save("files.json", {"scope": "Fixed public source and current anonymous client source normalization review; all read-only", "files": files})
    print(json.dumps({"review_sha256": sha((HERE / "review.json").read_bytes()),
        "manifest_sha256": sha((HERE / "files.json").read_bytes()), "files": len(files),
        "compiler_export_kernel_calls": 0, "website_write_calls": 0}), flush=True)


if __name__ == "__main__":
    main()
