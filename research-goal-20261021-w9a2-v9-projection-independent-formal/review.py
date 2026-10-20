"""Independent byte projection verification, not a source generator or Lean tool."""
from pathlib import Path
from collections import Counter
import hashlib
import json
import os
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
V8 = ROOT / "research-goal-20261020-w9a2-delivery/draft-v8/Solution.lean"
V9DIR = ROOT / "research-goal-20261021-w9a2-delivery/draft-v9"
OFFSETS = ROOT / "research-goal-20261021-w9a2-runtime-closure-formal/candidate-keyword-offsets.json"
PRESERVE = ROOT / "research-goal-20261021-w9a2-runtime-closure-formal/preserved-runtime-closure.json"
inputs = {}
sha = lambda raw: hashlib.sha256(raw).hexdigest()

def require(ok, message):
    if not ok: raise RuntimeError(message)

def read(path):
    raw = path.read_bytes(); inputs[path] = raw; return raw

def masked(raw):
    out = bytearray(raw); i = 0
    while i < len(raw):
        if raw[i:i+2] == b"--":
            j = raw.find(b"\n", i); j = len(raw) if j < 0 else j
        elif raw[i:i+2] == b"/-":
            j, depth = i + 2, 1
            while j < len(raw) and depth:
                if raw[j:j+2] == b"/-": depth += 1; j += 2
                elif raw[j:j+2] == b"-/": depth -= 1; j += 2
                else: j += 1
            require(depth == 0, "Unclosed nested comment")
        elif raw[i] == 34:
            j = i + 1
            while j < len(raw):
                if raw[j] == 92: j += 2
                elif raw[j] == 34: j += 1; break
                else: j += 1
        else: i += 1; continue
        for k in range(i, min(j, len(raw))):
            if raw[k] not in (10, 13): out[k] = 32
        i = j
    return bytes(out)

v8 = read(V8)
v9 = read(V9DIR / "Solution.lean")
manifest_raw = read(V9DIR / "files.json")
offset_raw = read(OFFSETS)
preserved = json.loads(read(PRESERVE))
require(len(v8) == 1829382 and sha(v8) == "5424212b6d2cf70b9eeaa632d6bf429dea4e1aadb13b0fedd948d38f94f8ac6b", "Frozen v8 mismatch")
require(len(v9) == 1861120 and sha(v9) == "7552bbb829b86986798b58cf40caf998ea8c51ab19201998b533dae4b9518c99", "Frozen v9 mismatch")
require(sha(manifest_raw) == "d5cb77b9915dc7437a66a5739acd57093f0ed6acc6f0643e995f415169f2a454", "Wrong v9 manifest")
manifest = json.loads(manifest_raw)
for row in manifest["files"]:
    require(row["path"] in {"Solution.lean", "projection.json"}, "Unexpected member")
    value = read(V9DIR / row["path"])
    require(len(value) == row["bytes"] and sha(value) == row["sha256"], "Manifest member differs")
require(len(manifest["files"]) == 2, "Wrong manifest membership")
require(sha(offset_raw) == "d25c727a385cdd758fa8027c0530cabbf870f6aee6039be72af4daabcd5464f2", "Wrong independent offset list")
proposal = json.loads(offset_raw)
rows = proposal["candidates"]
require(len(rows) == 2267, "Wrong insertion count")
old_pos = new_pos = 0
edits = []
for row in rows:
    offset = row["UTF8_keyword_byte_offset_0based"]
    require(offset >= old_pos, "Offsets not strictly monotonic")
    unchanged = v8[old_pos:offset]
    require(v9[new_pos:new_pos+len(unchanged)] == unchanged, "Non-insertion bytes differ")
    new_pos += len(unchanged)
    require(v9[new_pos:new_pos+14] == b"noncomputable ", "Wrong inserted bytes")
    keyword = row["kind"].encode()
    require(v8[offset:offset+len(keyword)] == keyword and v9[new_pos+14:new_pos+14+len(keyword)] == keyword, "Wrong keyword target")
    line_start = v8.rfind(b"\n", 0, offset) + 1
    original_prefix = v8[line_start:offset]
    require(re.fullmatch(rb"(?:(?:private|protected|local|scoped)\s+)*", original_prefix) is not None, "Illegal original modifier position")
    require(row["name_as_written"] not in {"digit64", "decode64"}, "Decoder selected")
    edits.append({"source_keyword_byte_offset_0based": offset, "v9_insertion_byte_offset_0based": new_pos,
                  "line_1based": row["line_1based"], "kind": row["kind"], "name_as_written": row["name_as_written"],
                  "original_modifiers": row["original_modifiers"]})
    new_pos += 14; old_pos = offset
tail = v8[old_pos:]
require(v9[new_pos:] == tail, "Final tail differs or has extra bytes")
require(len(v9) - len(v8) == 2267*14, "Wrong size delta")
# Reverse projection is verified independently by skipping only the prescribed14B regions.
reverse_sha = hashlib.sha256(); reverse_bytes = 0; cursor = 0
for edit in edits:
    cut = edit["v9_insertion_byte_offset_0based"]
    segment = v9[cursor:cut]
    reverse_sha.update(segment); reverse_bytes += len(segment); cursor = cut + 14
reverse_sha.update(v9[cursor:]); reverse_bytes += len(v9)-cursor
require(reverse_bytes == len(v8) and reverse_sha.hexdigest() == sha(v8), "Reverse projection mismatch")
prefix_end = preserved["macro_prefix_byte_interval"][1]
require(v8[:prefix_end] == v9[:prefix_end] and sha(v9[:prefix_end]) == preserved["macro_prefix_sha256"], "Macro prefix changed")
clean8, clean9 = masked(v8), masked(v9)
def stats(raw, clean):
    return {"bytes": len(raw), "sha256": sha(raw), "CRLF": raw.count(b"\r\n"), "CR": raw.count(b"\r"),
            "trailing_LF_bytes": len(raw)-len(raw.rstrip(b"\n")),
            "packed_WL_definitions": len(re.findall(rb"(?m)^(?:noncomputable )?def WL\w* : \xe2\x84\x95 := zfNat64 ", clean)),
            "rc_theorems": len(re.findall(rb"(?m)^theorem rc\d+ :", clean)),
            "decide_plus_kernel": len(re.findall(rb"\bdecide\s+\+kernel\b", clean)),
            "public_theorems": {name: len(re.findall(rb"(?m)^theorem " + name.encode() + rb"\b", clean)) for name in ("candidate_strict_improvement", "candidate_critical_line_bound", "candidate_critical_line_bound_cumulative")}}
stats8, stats9 = stats(v8, clean8), stats(v9, clean9)
for key in ("CRLF", "CR", "trailing_LF_bytes", "packed_WL_definitions", "rc_theorems", "decide_plus_kernel", "public_theorems"):
    require(stats8[key] == stats9[key], "Invariant changed: " + key)
require(stats9["CRLF"] == stats9["CR"] == 221 and stats9["trailing_LF_bytes"] == 1, "Wrong newline policy")
require(stats9["packed_WL_definitions"] == 135 and stats9["rc_theorems"] == 48 and stats9["decide_plus_kernel"] == 72 and all(count == 1 for count in stats9["public_theorems"].values()), "Wrong preserved structural counts")
kinds = dict(Counter(row["kind"] for row in rows))
require(kinds == {"def": 2257, "instance": 5, "abbrev": 5}, "Wrong candidate kind counts")
for path, value in inputs.items():
    require(path.read_bytes() == value, "Input changed after verification")
report = {"schema": "independent-v9-byte-projection-formal-v1", "result": "PASS_STATIC_BYTE_PROJECTION",
          "v9_manifest_members_verified": 2, "v8": stats8, "v9": stats9,
          "insertions": {"count": 2267, "bytes_each": 14, "total_delta": 31738, "exact_bytes": "noncomputable ", "kind_counts": kinds,
                         "private_protected_modifier_order_checked": True},
          "forward_all_unmodified_segments_equal": True, "reverse_projection_bytes": reverse_bytes,
          "reverse_projection_sha256": reverse_sha.hexdigest(), "entire_macro_prefix_unchanged": preserved,
          "proof_and_numeric_data_byte_scope": "Every original byte outside these2267 keyword insertion sites matched directly. Therefore all original proof bodies, data payloads, notices, macro/decoder bytes and structure/inductive declarations remain exact raw bytes. No decoder/math/proof execution performed.",
          "other_source_changes": False, "original_v8_inputs_unchanged": True,
          "scope": "Static byte projection and lexical count checks only. No author generator, Lean/parser/AST/import/compiler/kernel/export/solver/decoder/API/process/network/Git or counter/source change. This does not certify compilability, kernel validity, resource reduction or official acceptance.",
          "compiler_resource_PASS": False, "mathematical_verification_performed": False,
          "inputs_before_after_equal": [{"path": str(path), "bytes": len(value), "sha256": sha(value)} for path, value in inputs.items()]}
def new(name, value):
    data = value if isinstance(value, bytes) else (json.dumps(value, ensure_ascii=False, indent=2)+"\n").encode()
    with (HERE / name).open("xb") as stream:
        stream.write(data); stream.flush(); os.fsync(stream.fileno())
new("review.json", report)
new("verified-insertion-offsets.json", {"scope": "Independent verified mapping of old keyword offsets to v9 insertion offsets; no modified source generation", "edits": edits})
new("README.zh.md", ("完整字节projection通过：v9恰2267处插入14B noncomputable空格（2257def+5abbrev+5instance），净增31738B。所有其余byte直接逐段与冻结v8相等；独立跳过这些插入后的reverse SHA精确回到5424212b…/1829382B。新源7552bbb8…/1861120B，manifest两成员均核同。\n\n真正keyword offset和private/protected顺序逐处核对。完整宏前缀、两个decoder、所有proof/data/结构与归纳声明的原始字节未改。221CRLF、恰1末LF、135packed WL、48rc、72个decide+kernel及三个公开theorem均保留。原v8和所有输入前后不变。\n\n仅字节与词法静态核对，不运行作者生成器、Lean/parser/AST/import/compiler/kernel/export/decoder，不改counter/Git。不证明可编译、数学重验、资源收益或官网接受。\n").encode())
members = []
for path in sorted(HERE.iterdir()):
    if path.is_file() and path.name != "files.json":
        value = path.read_bytes(); members.append({"path": path.name, "bytes": len(value), "sha256": sha(value)})
new("files.json", {"schema": "independent-v9-projection-files-v1", "files": members})
print(json.dumps({"result": "PASS_STATIC_BYTE_PROJECTION", "manifest_sha256": sha((HERE / "files.json").read_bytes()), "review_sha256": sha((HERE / "review.json").read_bytes()), "members": len(members), "counts": stats9}))
