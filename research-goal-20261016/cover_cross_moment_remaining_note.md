# Fixed six-case extension: stopped without additional exclusions

The first two parents from the original eight residuals have independent
strict integer moment-system contradictions, maintained separately by the
root task. This batch uses exactly the remaining six parents from the same
frozen `cover-curvature-parent64.input.json.gz` cohort and target 11/1250.

Each parent uses one feasible midpoint of the two DBM prefix potentials,
one whole-span quadratic energy lower packet and one LP with a common
nonnegative energy-unit slack. The unchanged base model retains the old
derivative graph, boundary-aware KKT, all cross-coordinate RLT products and
McCormick rows. No PSD cut rounds, new samples, alternate anchors, threshold
changes or full-cover jobs are used.

All six LPs returned zero energy slack. Their position-moment matrices have
smallest eigenvalue hints between -0.3452 and -0.1683. Thus they provide no
strict separation and no PSD-feasible primal claim. The integer Farkas
extraction is not triggered. This 31.36-second fixed experiment is stopped;
its zero positive hints do not invalidate the first two strict certificates
or prove that a stronger moment model would fail.

The lossless standalone archive is 90,395 bytes. It contains all six finite
packets and LP diagnostics, complete required ancestor operations and the
source hashes. It also reconstructs the original 190,771-byte discovery
JSON exactly by SHA (including its final CRLF); the original discovery
file and the full parent64 input are not needed for replay.

`cover_cross_moment_remaining_replay.py` runs with `python -S` and rebuilds
57 nodes and 449 OBBT ancestor bounds, checks all six midpoint memberships,
reruns their point energy and nine gradient interval evaluations, rechecks
246 whole-span second-derivative lower bounds and all quadratic row
identities. The point calculations use the same rational interval kernel
implementation as the provider; this is not an implementation-independent
transcendental audit. No optimization package is imported. These supply
checks pass; the floating LP primals are not certified as exact feasible
moment points, and no Lean leaf is asserted for this batch.

```text
python -S -B -X utf8 research-goal-20261016/cover_cross_moment_remaining_replay.py
```

`cover-cross-moment-overlap.json` separately audits parent-path unions.
The two strict moment parents have no equal, ancestor or descendant overlap
with the prior 13 direct graph parents. The second moment parent,
`r001000001000001110011100`, equals the already certified one-split graph
parent. Only `r001000001000001101011101` is a new region. Consequently the
prior 14 non-nested local regions become 15, rather than 16. These are
local independently replayed numerical certificate regions; they are not
a global cover or a count of actual Lean leaf instantiations.

The sole running full cover is unchanged. This batch proves no new zero
proportion and is not submission-ready.
