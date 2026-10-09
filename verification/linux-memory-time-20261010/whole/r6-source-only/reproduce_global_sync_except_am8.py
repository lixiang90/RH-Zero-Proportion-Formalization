#!/usr/bin/env python3
"""SOURCE ONLY: add a base-scope scheduling option; never invoke Lean."""
import argparse, hashlib
from pathlib import Path
INPUT_SHA256 = "f40d0cb3566d4e71a6bb624a4d4375ca3ade977d3850e14e134a8a850f4abd50"
OUTPUT_SHA256 = "5227a25ea2c5f18c83e0a85c756e34ec9a0176a1ba9d1cd5f5556aab836ba7a2"
ANCHOR = b"section RHWeilBundleModule_0\n"
INSERT = b"set_option Elab.async false\n"
def transform(raw):
    if len(raw) != 1993809 or hashlib.sha256(raw).hexdigest() != INPUT_SHA256:
        raise ValueError("Expected exact f40 public-wrapper output")
    if raw.count(ANCHOR) != 1:
        raise ValueError("First bundle boundary is not unique")
    at = raw.index(ANCHOR)
    if b"set_option Elab.async" in raw[:at]:
        raise ValueError("Unexpected global async directive; do not replace AM option")
    result = raw[:at] + INSERT + raw[at:]
    if result[:at] + result[at+len(INSERT):] != raw:
        raise ValueError("Original byte reconstruction failed")
    if len(result) != 1993837 or hashlib.sha256(result).hexdigest() != OUTPUT_SHA256:
        raise ValueError("Expected exact output bytes/hash")
    return result
if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--input", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    a = p.parse_args()
    transformed = transform(a.input.read_bytes())
    with a.output.open("xb") as f:
        f.write(transformed)
    print(hashlib.sha256(transformed).hexdigest())
