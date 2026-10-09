# Experimental base-scope synchronous candidate

PREPARED SOURCE ONLY. Not compiled or measured. No public source edits or Lean, Linux, runtime-cache, or proof operations.

Input: exact f40 public-wrapper output, 1,993,809 bytes, SHA-256 `f40d0cb3566d4e71a6bb624a4d4375ca3ade977d3850e14e134a8a850f4abd50`.
Output: `5227a25ea2c5f18c83e0a85c756e34ec9a0176a1ba9d1cd5f5556aab836ba7a2`, 1,993,837 bytes, 6,163 bytes below the 2,000,000-byte source limit.

Original f40 has no global async directive. Its only true is inside the AM section. This recipe inserts exactly 28 bytes (`set_option Elab.async false\n`) immediately before `section RHWeilBundleModule_0`. Removing that insertion reconstructs every original byte.

Pinned Lean's command-line frontend defaults Elab.async to true when no override is provided. Options restore on section/namespace end. The AM final false and Data, Point, Geometry false options do not set the base scope; original FiniteCertificate suffix module11 (lines22573–24152) consequently inherits true. This candidate forces base false, preserving scoped AM true, all162 waits, all original options, numeric inputs, and proof text.

Reproduce from an exact f40 output of the public wrapper:

```powershell
python reproduce_global_sync_except_am8.py --input PATH_TO_EXACT_F40_OUTPUT --output NEW_SOLUTION_PATH
```

The script refuses changed input hashes and existing outputs. `source-only-provenance.json` records the complete static scope ledger, byte guards, failures, and pinned Lean source evidence. Compile, fresh root/axiom audits, independent verification, and website acceptance remain pending separate work.
