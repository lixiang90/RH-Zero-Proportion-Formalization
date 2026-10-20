"""Static byte lexer/inventory only: no Lean parser, AST, import or compiler."""
from pathlib import Path
from collections import Counter
import hashlib
import json
import os
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SOURCE = ROOT / "research-goal-20261020-w9a2-delivery/draft-v8/Solution.lean"

def sha(value):
    return hashlib.sha256(value).hexdigest()

def mask(raw):
    out = bytearray(raw); i = 0
    while i < len(raw):
        if raw[i:i+2] == b"--":
            j = raw.find(b"\n", i); j = len(raw) if j < 0 else j
        elif raw[i:i+2] == b"/-":
            j = i + 2; depth = 1
            while j < len(raw) and depth:
                if raw[j:j+2] == b"/-": depth += 1; j += 2
                elif raw[j:j+2] == b"-/": depth -= 1; j += 2
                else: j += 1
            if depth: raise RuntimeError("Unterminated nested comment")
        elif raw[i] == 34:
            j = i + 1
            while j < len(raw):
                if raw[j] == 92: j += 2
                elif raw[j] == 34: j += 1; break
                else: j += 1
        else:
            i += 1; continue
        for k in range(i, min(j, len(raw))):
            if raw[k] not in (10, 13): out[k] = 32
        i = j
    return bytes(out)

def new(name, value):
    with (HERE / name).open("xb") as stream:
        raw = (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()
        stream.write(raw); stream.flush(); os.fsync(stream.fileno())

raw = SOURCE.read_bytes()
if len(raw) != 1829382 or sha(raw) != "5424212b6d2cf70b9eeaa632d6bf429dea4e1aadb13b0fedd948d38f94f8ac6b":
    raise RuntimeError("Wrong frozen source")
clean = mask(raw)
line = lambda offset: raw.count(b"\n", 0, offset) + 1
mods = rb"(?:(?:private|protected|noncomputable|unsafe|partial|local|scoped)\s+)*"
kind = rb"def|abbrev|opaque|theorem|lemma|instance|structure|inductive|class|axiom|example"
decl_pattern = rb"(?m)^(?P<indent>[ \t]*)(?P<attrs>(?:@\[[^\r\n]*\][ \t]*)*)(?P<mods>" + mods + rb")(?P<kind>" + kind + rb")\b[ \t]*(?P<tail>[^\r\n]*)"
matches = list(re.finditer(decl_pattern, clean))
rows = []
for m in matches:
    k = m["kind"].decode(); tail = m["tail"]
    if k in {"instance", "example"}:
        name = None
    else:
        match = re.match(rb"([^\s(:={]+)", tail)
        name = match[1].decode() if match else None
    # Keep explicit byte spans only; this is not name elaboration or a body parser.
    rows.append({"line": line(m.start()), "byte_offset": m.start(), "kind": k, "name": name,
                 "modifiers": m["mods"].decode().split(), "indent_bytes": len(m["indent"]),
                 "header_preview": raw[m.start():m.end()].decode()[:220]})
attribute_rows = []
for m in re.finditer(rb"@\[([^\]]*)\]", clean):
    attribute_rows.append({"line": line(m.start()), "byte_offset": m.start(), "tokens": m[1].decode(), "source": raw[m.start():m.end()].decode()})
for m in re.finditer(rb"(?m)^[ \t]*attribute\b[^\r\n]*", clean):
    attribute_rows.append({"line": line(m.start()), "byte_offset": m.start(), "command": raw[m.start():m.end()].decode()})
token_names = ["macro", "macro_rules", "elab", "elab_rules", "syntax", "run_cmd", "run_tac", "initialize", "builtin_initialize", "deriving", "native_decide", "evalConst", "evalExpr", "implemented_by", "extern", "export", "compiler_simp", "csimp", "simp", "norm_num", "infer_instance"]
token_rows = {}
for token in token_names:
    hits = list(re.finditer(rb"(?<![A-Za-z0-9_'])" + token.encode() + rb"(?![A-Za-z0-9_'])", clean))
    token_rows[token] = [{"line": line(m.start()), "byte_offset": m.start()} for m in hits]
hash_commands = [{"line": line(m.start()), "name": m[1].decode(), "byte_offset": m.start()}
                 for m in re.finditer(rb"(?m)^[ \t]*#([A-Za-z_]+)\b", clean)]
runtime_source_refs = {}
for token in ["digit64", "decode64", "zfNat64"]:
    hits = list(re.finditer(rb"(?<![A-Za-z0-9_'])" + token.encode() + rb"(?![A-Za-z0-9_'])", clean))
    runtime_source_refs[token] = [{"line": line(m.start()), "byte_offset": m.start()} for m in hits]
counts = Counter(row["kind"] for row in rows)
plain = [row for row in rows if row["kind"] in {"def", "abbrev", "opaque", "instance"} and "noncomputable" not in row["modifiers"]]
existing = [row for row in rows if "noncomputable" in row["modifiers"]]
candidate = [row for row in plain if row["name"] not in {"digit64", "decode64"}]
if SOURCE.read_bytes() != raw: raise RuntimeError("Source changed")
inventory = {"scope": "Byte-preserving nested-comment/string mask, then explicit lexical declaration/attribute/token inventory. No Lean AST or name/type elaboration; anonymous instance names and all generated declarations remain unknown.",
             "source": {"path": str(SOURCE), "bytes": len(raw), "sha256": sha(raw)},
             "declaration_counts": dict(counts), "all_explicit_declarations": rows,
             "existing_explicit_noncomputable": existing,
             "ordinary_def_abbrev_opaque_instance_candidates_excluding_decoder": candidate,
             "candidate_kind_counts": dict(Counter(row["kind"] for row in candidate)),
             "attributes": attribute_rows, "runtime_token_hits": token_rows, "hash_commands": hash_commands,
             "decoder_and_packing_refs": runtime_source_refs,
             "not_a_runtime_call_graph": True}
new("source-inventory.json", inventory)
print(json.dumps({"declaration_counts": dict(counts), "existing_noncomputable": len(existing), "candidate_kind_counts": inventory["candidate_kind_counts"], "attributes_count": len(attribute_rows), "runtime_token_counts": {k: len(v) for k,v in token_rows.items()}, "hash_commands": hash_commands, "indented_declarations": [r for r in rows if r["indent_bytes"]]}))
