"""Independent radix-64 ordinary-Nat inventory for one immutable source.

This imports no producer decoder.  It does not execute Lean, interpret a
certificate walk, read a leaf witness, or evaluate an actual kernel.
"""
from pathlib import Path
import hashlib
import json
import re
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
REL = "research-goal-20261018-record-source-audit/snapshot/Solution.lean"
SOURCE_SHA = "f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf"
ALPHABET = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+_"


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def pin(path):
    raw = path.read_bytes()
    return {"path": path.relative_to(ROOT).as_posix(), "bytes": len(raw),
            "sha256": digest(raw)}


def mask_comments(text):
    """Preserve all offsets/newlines/strings while masking nested Lean comments."""
    out = list(text)
    i, depth, quoted = 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                out[i:i + 2] = "  "
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                out[i:i + 2] = "  "
                depth -= 1
                i += 2
            else:
                if text[i] not in "\r\n":
                    out[i] = " "
                i += 1
        elif quoted:
            if text[i] == "\\":
                i += 2
            elif text[i] == '"':
                quoted = False
                i += 1
            else:
                i += 1
        elif text.startswith("/-", i):
            out[i:i + 2] = "  "
            depth = 1
            i += 2
        elif text.startswith("--", i):
            while i < len(text) and text[i] not in "\r\n":
                out[i] = " "
                i += 1
        elif text[i] == '"':
            quoted = True
            i += 1
        else:
            i += 1
    assert depth == 0 and not quoted
    return "".join(out)


def independent_decode(bits, payload):
    """Use a positional sum, not the producer's mutating shift/fold decoder."""
    assert 0 <= bits <= 65536
    payload.encode("ascii")
    assert all(ch in ALPHABET for ch in payload)
    if bits == 0:
        assert payload == "A"
        value = 0
    else:
        assert len(payload) == (bits + 5) // 6
        digits = [ALPHABET.index(ch) for ch in payload]
        value = sum(d << (6 * (len(digits) - 1 - j))
                    for j, d in enumerate(digits))
        assert value.bit_length() == bits
        leading_bits = (bits - 1) % 6 + 1
        assert 1 << (leading_bits - 1) <= digits[0] < 1 << leading_bits
    # Independent inverse via Euclidean division, with unique zero spelling.
    working, inverse = value, []
    while working:
        working, digit = divmod(working, 64)
        inverse.append(ALPHABET[digit])
    reconstructed = "".join(reversed(inverse)) if inverse else "A"
    assert reconstructed == payload
    return value


def numeral_record(name, line, byte_offset, original_line, value, kind, **extra):
    decimal = str(value).encode("ascii")
    assert int(decimal) == value
    encoded = value.to_bytes(max(1, (value.bit_length() + 7) // 8), "big")
    return {"name": name, "line": line, "byte_offset": byte_offset,
            "source_line_sha256": digest(original_line), "literal_kind": kind,
            "ordinary_nat_bits": value.bit_length(), "ordinary_nat_decimal_digits": len(decimal),
            "ordinary_nat_decimal_sha256": digest(decimal),
            "ordinary_nat_minimal_unsigned_big_endian_sha256": digest(encoded),
            "ordinary_nat_minimal_unsigned_big_endian_bytes": len(encoded), **extra}


def main():
    output = HERE / "packing-replay.json"
    assert not output.exists(), "One execution; preserve this receipt"
    # The bounded payloads have at most 19,729 decimal digits.  Python's global
    # 4,300-digit default limit is unrelated to the checked 65,536-bit source cap.
    sys.set_int_max_str_digits(20000)
    raw = (ROOT / REL).read_bytes()
    assert len(raw) == 1818411 and digest(raw) == SOURCE_SHA
    source = raw.decode("utf-8")
    masked = mask_comments(source)
    raw_lines = raw.splitlines(keepends=True)
    lines = masked.splitlines()
    assert len(raw_lines) == len(lines)
    offsets, cursor = [], 0
    for line in raw_lines:
        offsets.append(cursor)
        cursor += len(line)
    assert cursor == len(raw)
    packed_calls = list(re.finditer(r'\bzfNat64\s+(\d+)\s+"([^"\r\n]*)"', masked))
    declaration = re.compile(r"^(?:noncomputable\s+)?def\s+([A-Za-z_][A-Za-z_0-9']*)\s*:\s*ℕ\s*:=\s*(.*?)\s*$")
    packed_rhs = re.compile(r'zfNat64\s+(\d+)\s+"([^"\r\n]*)"')
    ordinary_rhs = re.compile(r"(?:0x[0-9a-fA-F]+|[0-9]+)")
    numerals, packed, derived_prefixed = [], [], []
    for number, line in enumerate(lines, 1):
        match = declaration.fullmatch(line)
        if not match:
            continue
        name, rhs = match.groups()
        common = (name, number, offsets[number - 1], raw_lines[number - 1])
        pack = packed_rhs.fullmatch(rhs)
        if pack:
            bits, payload = int(pack[1]), pack[2]
            value = independent_decode(bits, payload)
            row = numeral_record(*common, value, "zfNat64",
                declared_bits=bits, payload_ascii_characters=len(payload),
                payload_ascii_sha256=digest(payload.encode("ascii")),
                ASCII_and_alphabet_checked=True, canonical_bits_checked=True,
                encode_decode_inverse_checked=True, decimal_roundtrip_checked=True)
            packed.append(row)
            numerals.append(row)
        elif ordinary_rhs.fullmatch(rhs):
            base = 16 if rhs.startswith("0x") else 10
            row = numeral_record(*common, int(rhs, base), "hexadecimal" if base == 16 else "decimal")
            numerals.append(row)
        elif name.startswith(("TOP", "BK", "WL")):
            derived_prefixed.append({"name": name, "line": number,
                "byte_offset": offsets[number - 1], "source_line_sha256": digest(raw_lines[number - 1]),
                "scope": "Computed Nat declaration, indexed only; value not evaluated"})
    assert len(packed_calls) == len(packed) == 137
    assert sum(1 for item in numerals if item["literal_kind"] == "zfNat64") == 137

    def index_decl(pattern):
        rows = []
        matcher = re.compile(pattern)
        for number, line in enumerate(lines, 1):
            match = matcher.match(line)
            if match:
                rows.append({"name": match[1], "line": number,
                    "byte_offset": offsets[number - 1],
                    "source_line_sha256": digest(raw_lines[number - 1]),
                    "signature": line.strip()})
        return rows

    roots = index_decl(r"^theorem\s+(rc\d+)\s*:")
    parents = index_decl(r"^theorem\s+(ready\d+_parent_cursor)\s*:")
    nested = index_decl(r"^theorem\s+(ready\d+_\d+_cursor)\s*:")
    states = index_decl(r"^(?:noncomputable\s+)?def\s+(ready\d+_\d+_state)\s*:")
    stream_roots = index_decl(r"^(?:noncomputable\s+)?def\s+(WD\d+)\s*:")
    assert len(roots) == len(parents) == len(stream_roots) == 48
    assert {row["name"] for row in roots} == {f"rc{j}" for j in range(48)}
    assert {row["name"] for row in parents} == {f"ready{j}_parent_cursor" for j in range(48)}
    assert {row["name"] for row in stream_roots} == {f"WD{j}" for j in range(48)}
    assert len(nested) == len(states) == 70
    assert {row["name"].replace("_cursor", "_state") for row in nested} == {row["name"] for row in states}
    # Static AST production audit only: the macro's success branch constructs
    # exactly an ordinary numeral token; this is not execution of that macro.
    macro_start = source.index('macro "zfNat64 "')
    macro_end = macro_start + re.search(r"\r?\n\r?\n", source[macro_start:]).start()
    macro = source[macro_start:macro_end]
    assert "return ⟨(Lean.Syntax.mkNumLit (toString value)).raw⟩" in macro
    assert "Lean.Macro.throwErrorAt payload message" in macro
    canonical = json.dumps(numerals, ensure_ascii=False, sort_keys=True,
                           separators=(",", ":")).encode("utf-8")
    prefixed = [row for row in numerals if row["name"].startswith(("TOP", "BK", "WL"))]
    result = {
        "schema": "independent-source-packing-and-declaration-inventory-v1",
        "scope": "Only source packing and named declarations; no finite mathematical certificate replay",
        "source": pin(ROOT / REL),
        "independent_algorithm": "ASCII alphabet lookup plus positional 6-bit MSB sum; inverse by divmod64; no producer imports",
        "decimal_identity_digest_representation": "SHA256 of unsigned canonical base10 ASCII without leading zeros; zero is ASCII 0",
        "binary_identity_digest_representation": "SHA256 of minimal unsigned big-endian bytes; zero is one zero byte",
        "all_packed_calls_covered_by_exact_Nat_literal_declarations": True,
        "packed_literal_count": len(packed), "ordinary_named_literal_count": len(numerals),
        "literal_kind_counts": {kind: sum(row["literal_kind"] == kind for row in numerals)
                                for kind in ["zfNat64", "hexadecimal", "decimal"]},
        "maximum_declared_packed_bits": max(row["declared_bits"] for row in packed),
        "all_137_ASCII_canonical_inverse_decimal_checks_pass": True,
        "macro_source_success_branch_is_mkNumLit_only": True,
        "macro_source_sha256": digest(macro.encode("utf-8")),
        "ordinary_named_literal_inventory_sha256": digest(canonical),
        "ordinary_named_literals": numerals,
        "TOP_BK_WL_literal_digests": prefixed,
        "TOP_BK_WL_computed_Nat_declarations_not_evaluated": derived_prefixed,
        "root_declaration_count": len(roots), "root_declarations": roots,
        "parent_cursor_declaration_count": len(parents), "parent_cursor_declarations": parents,
        "nested_cursor_declaration_count": len(nested), "nested_cursor_declarations": nested,
        "nested_state_declaration_count": len(states), "nested_state_declarations": states,
        "WD_root_declarations": stream_roots,
        "expected_terminal_leaf_count_from_task_only": 13046,
        "terminal_leaf_count_replayed": False,
        "decoded_WL_values_interpreted_as_walks": False,
        "leaf_witnesses_decoded": 0, "actual_kernel_evaluations": 0,
        "finite_guard_checks_replayed": 0, "Lean_invocations": 0,
        "producer_packing_inventory_compared": False,
        "new_floor_proven": False, "website_submission_ready": False,
    }
    output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"path": output.relative_to(ROOT).as_posix(),
        "packed": len(packed), "ordinary_named_literals": len(numerals),
        "roots": len(roots), "parents": len(parents), "nested": len(nested),
        "PASS": True, "leaf_witnesses_decoded": 0}))


if __name__ == "__main__":
    main()
