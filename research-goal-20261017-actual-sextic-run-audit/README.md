# Independent completed-run record audit

The one stdlib audit of the completed run records passed in 229 ms. It
checked all frozen input/source endpoints, both previous preflight gates,
the monitor record, and the complete native-array archive. It did not
import a producer or numerical library, reconstruct a matrix, compute an
eigenvalue, extract a dual certificate, run a solver, fit a point or invoke
Lean.

Read-only command:

```powershell
python -S -B -X utf8 research-goal-20261017-actual-sextic-run-audit/audit_record.py
```

The receipt was created with `--write-receipt`, which refuses overwrite.
The prepared-row preflight and worker-source review pins are unchanged.

The records agree on a single worker PID 32848, one SCS initialization and
one cold solve, exit code zero, no retries and no resource termination. The
parent elapsed time is 68.198 seconds and the observed peak working set is
728,928,256 bytes, below the 90-second and 1.5-GiB monitor guards. The source
configuration remains QDLDL CPU direct, 45 seconds of solver time, 2,000
iterations, tolerances 1e-7 and one BLAS thread. Reported setup plus solve
time is 60.637799 seconds; setup is covered by the parent total-time guard.

SCS reports `infeasible` after 125 iterations with reported `res_infeas`
4.130910915064931e-12. This audit confirms that record and its source
configuration; it does not independently recompute a conic residual or
certify infeasibility.

The complete native archive has 1,057,101 compressed bytes and 3,187,403
uncompressed bytes. Both hashes match its receipt. The arrays have lengths
5,005 / 111,144 / 111,144 for x / y / s. Every dual entry is finite. All x
and s entries are the quoted JSON string `NaN`, which is expected for this
infeasibility return; unquoted nonfinite JSON tokens are rejected by the
auditor. The array shape, encoding and hash checks make no assertion that
these arrays are a feasible primal point or an exact dual certificate.

The unchanged source's flush/fsync/rename order and its recorded phase
sequence agree that the full native arrays were archived before derived
diagnostics. Standard error is empty and the single standard-output
summary matches the worker receipt. No mathematical consequence is
inferred from a finite numerical dual vector by this audit.

The worker explicitly records `actual_certificate = null`, no newly proved
analytic Lean instances, no cell exclusion and no new zero proportion.
Those limits remain in the independent receipt. Exact reconstruction and
verification of a strict conic certificate, its actual analytic inputs,
the global root cover and the website source limit remain separate work.
