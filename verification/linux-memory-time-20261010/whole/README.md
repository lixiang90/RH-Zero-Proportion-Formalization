# Whole-file resource trials

The fixed result is 66812491/99194740. The original public Solution remains
unchanged; none of these trials establishes official resource compliance.

- [r5 completed cutoff](r5-completed/README.md): intentional SIGTERM after
  failed memory charges; complete compilation and downstream checks absent.
- [r6 completed diagnostic](r6-completed/README.md): complete Lean compilation
  and separately authorized dependency/three-root axiom checks passed; the
  compile memory gate failed with 64 charges, no OOM/timeout/swap.
- [r6 source-only recipe](r6-source-only/README.md): immutable preparation
  history; its pending labels precede the completed results above.

r6 proof-stage time was 2993.462 seconds. Shared elapsed through its later
audit was 3471.979 seconds, including local cold preparation and caller gaps.
Exports, Comparator/default replay and serial Nano were not run. The frozen
current record was 6735015/10000000, while the subsequently observed live
record is 66812491/99194876; no fresh live-contract check is asserted.
Earlier prepared and preflight directories are retained as historical inputs.
