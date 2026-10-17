# Independent pre-solver exact aggregation gate

The one complete independent stdlib preflight passed in 16,455 ms. It did
not import the producer, NumPy, SciPy or SCS. No solver or Lean process was
started. All source and prepared-data hashes remained unchanged.

Read-only replay:

```powershell
python -S -B -X utf8 research-goal-20261017-actual-sextic-cone-audit/preflight.py
```

The frozen receipt was created using `--write-receipt`, which refuses to
replace a receipt. Do not rerun `prepare_rows.py` or overwrite its outputs.

The independently audited factor packet remains the authority for the
polynomials. This preflight accumulates its coefficients by integer moment
IDs, rather than importing producer polynomial operations. For all 181 rows
it independently reconstructs:

- The exact coefficients, bound, positive row scale and metadata, and both
  the individual canonical JSON hashes and the complete JSONL hash
  `3491df37b6f36e00359c1af20ee89f15fe2ccfddba50892286064b77828b2475`.
- The lower-energy inequality `L6 <= c` and the gradient inequalities
  `E6 + sign * test * P5 >= 0`, with the correct conversion to CSR
  `a dot moments <= b`. In particular only P5 is shifted by the test;
  E6 is not. These are the 181 unsoftened rows of the fixed packet.
- All 905,724 exact nonzero coefficients. The CSR has shape 181 by 5,005,
  but every new coefficient column is below 5,004: the diagnostic energy
  slack column is absent from every new row.
- All CSR column indices and row pointers, and all 905,905 rounded
  float64 values (coefficients plus 181 bounds) by exact IEEE754 bytes.
  The compressed NPZ was decoded with stdlib ZIP, NPY header parsing and
  native arrays; no numerical library was imported.
- All 5,803 retained old scalar rows after the sole slack-column remap
  `714 -> 5004`, reproducing the old canonical JSONL hash. The only old
  slack occurrences are rows 5,793 and 5,794. The 4,290 higher-moment
  boxes, representing 8,580 inequalities, are also checked independently.
  The old 73 PSD blocks remain bound by their frozen model hash; their
  separate full representation audit is not repeated here.

The producer's fixed rational rank-one y values are used solely to compare
expanded-row and factored polynomial packing identities. They are not an
actual function sample, feasible solution, warm seed, fit or claim that a
point extends the earlier pseudo-moments.

This gate checks the prepared rows and rounded data. It does not check a
future worker's solver settings or concatenation unless accompanied by a
separate source review. It proves no numerical feasibility, exclusion,
strict projection shrink, analytic Lean instance, global floor or new zero
proportion.
