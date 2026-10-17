# Additive static worker gate

The source-only review passed in 524 ms. This add-on leaves every file in
the earlier `preflight-files.json` pin unchanged. It does not import or run
the worker or a numerical solver. Read-only source review can be repeated
with:

```powershell
python -S -B -X utf8 research-goal-20261017-actual-sextic-cone-audit/review_worker.py
```

The approved immutable sources are:

- `worker.py`: SHA256 `c0c9c942eae956576934ca9bd8b60aa3146077f062f80e1bed672fffc1e59626`.
- `run_once.py`: SHA256 `df7b67869457d4c523b81f047447b36dda025ceae1747a27e604662280499cc5`.

The AST has exactly one `scs.SCS` construction and one
`engine.solve(warm_start=False)` call. The selected backend is
`scs.LinearSolver.QDLDL`, with a 45-second solver limit, 2,000 iterations,
absolute and relative tolerances of 1e-7, and no retry, warm start, fallback
or settings scan. The four BLAS/thread environment controls are set to one
before NumPy/SciPy/SCS imports and also in the worker's process environment.
The existing direct-extension binary is hash bound; it is not imported by
this review.

An independent static count reproduces the matrix dimensions and nonzero
count: 111,144 rows, 5,005 variables and 3,153,411 nonzero entries. All 14,383
old scalar rows are retained, followed by the 181 new unsoftened rows. The
73 PSD blocks retain 96,580 packed lower-triangle rows and sizes
220, 46 copies of 55, and 26 copies of 10. The sole old scalar column map is
714 to 5004; the new rows have no slack coefficient. The earlier preflight
is required by exact status and unchanged start/end source hashes.

The PSD assembly uses one positive rational divisor per block, with the
SCS sqrt(2) off-diagonal convention. Its signs give `b - A*x` equal to the
scaled positive multiplier times the moment outer product. The fixed
rational rank-one identity is only a packing diagnostic, not a feasible
point, warm seed or actual analytic function evaluation.

After a successful solver return, full native x, y and s arrays are encoded,
gzip-compressed, flushed, fsynced and renamed before the derived numerical
diagnostics run. Those arrays and any status remain numerical hints rather
than exact certificates.

The external monitor starts its 90-second total timer before process
creation, so imports, assembly, setup, solve and postprocessing all count.
It samples only its created process handle and terminates only that process
if its current or peak working set exceeds 1.5 GiB, total time exceeds
90 seconds, or a live-worker memory reading fails. It launches one process
and contains no retry. The worker also checks its own peak working set at
phase boundaries. These are source-reviewed controls, not a claim that a
future runtime has already completed within budget.

Both the exact prepared-row gate and this source gate passed before the
producer was notified to perform the one separately authorized attempt.
No solver or Lean execution, numerical outcome, exact exclusion, global
floor or new zero proportion is asserted by this add-on.
