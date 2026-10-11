# RH Zero Proportion Formalization

Author: **Li Xiang** ([lixiang90](https://github.com/lixiang90)).

Lean proofs and exact rational certificates for lower bounds on the proportion
of Riemann zeta zeros on the critical line. The research project and papers are
maintained in [RH-Weil](https://github.com/lixiang90/RH-Weil); this repository
contains the proportion formalization and its reproducibility records.

The latest bound is

\[
\frac{941021}{1397107}=\frac{66812491}{99194597}
=0.673549699486152456\ldots,
\]

or **67.3549699486152…%**, for **simple** critical-line zeros relative to all
nontrivial zeros counted with multiplicity. It also implies the same bound for
distinct critical-line zeros. The statements are asymptotic: every smaller
proportion holds for all sufficiently large heights, both on \([T,2T]\) and
on \([0,T]\).

The complete new theorem is in
[RecordProportion/NinthSpan.lean](RecordProportion/NinthSpan.lean). All four
actual counting theorems and the strict improvement over the previous bound
pass ordinary Lean compilation and a fresh transitive axiom audit. The full
dependency graphs also pass independent nanoda replay: the recorded run checked
82,804 declarations in 702.610 seconds with four threads. Their only permitted
axioms are `propext`, `Quot.sound`, and `Classical.choice`; the proof does not use
`sorry`, `native_decide`, or new analytic axioms. The source and artifact hashes,
commands, and results are recorded in the
[complete Lean report](verification/ninth-span-complete-formal-kernel.json) and
[independent replay report](verification/ninth-span-complete-independent-nanoda.json).

The previous bound **66812491/99194740 = 67.3548728491047…%**, its Lean proofs,
papers, certificates, verification records, and single-file submission remain
available without replacement. The previous README is archived
[verbatim](docs/c260-repository-status-20261010.md). A
[preservation manifest](verification/ninth-span-old-record-baseline.json) and
[publication check](scripts/verify_ninth_span_publication.py) verify this.

## Proof and certificates

The improvement strengthens a nine-point local inequality while retaining the
existing analytic majorant and counting bridge. It divides 47 previous domains
into 84 closed branches according to the total span, checks exact tangent and
dual certificates, and transports the bound to the actual zeta-zero counts.
The coverage concerns real gaps, including branch endpoints.

| Entry | Purpose |
|---|---|
| [NinthSpan.lean](RecordProportion/NinthSpan.lean) | Unconditional local inequality and simple/distinct dyadic and cumulative theorems |
| [NinthSpanFinite.lean](RecordProportion/NinthSpanFinite.lean) | Real-domain soundness, closed coverage, and complete orbit/reflection transport |
| [NinthSpanFiniteData.lean](RecordProportion/NinthSpanFiniteData.lean) | Literal data and closed integer certificate checks |
| [NinthSpanPathSoundness.lean](RecordProportion/NinthSpanPathSoundness.lean) | Integer path witnesses and real potential bounds |
| [NinthSpanPoints.lean](RecordProportion/NinthSpanPoints.lean) | 541 original tangent values and exact safe reanchoring |
| [NinthSpanLocal.lean](RecordProportion/NinthSpanLocal.lean) | Low-domain and outside-domain combination |
| [NinthSpanAnalytic.lean](RecordProportion/NinthSpanAnalytic.lean) | Improved reward and actual asymptotic counting transport |

See the [formalization guide](docs/ninth-span-formalization.md) for the exact
statement, proof structure, and reproduction steps. The new mathematical
[paper source](papers/ninth-span-simple-critical-paper.tex) and
[PDF](output/pdf/ninth-span-simple-critical-paper.pdf) are preserved as the
research snapshot; a [verification addendum](papers/ninth-span-lean-verification-addendum.md)
records the subsequent completed formalization.

## Fixed environment and reproduction

| Component | Pinned version |
|---|---|
| Lean | `leanprover/lean4:v4.33.0-rc2` |
| Mathlib | `51e6992efd06126df61a496bebf8f49482a4e129` |
| Zeta23 | `3635e74826a4c1fcece7d1cd2b6fa75e43a00510` |
| lean4export | `b18d673bd29b476466a51a3be1012df2ed322b10` |
| nanoda | `418320295890faed83a96fd97907b12a3b6728c2` |

```powershell
lake --no-cache exe cache get
lake --no-cache build +RecordProportion.NinthSpan:olean
python -B -X utf8 scripts/am_ninth_span_certificate.py --check
python -B -X utf8 scripts/generate_ninth_span_certificate.py --check
python -B -X utf8 scripts/review_ninth_span_data.py
```

Lake checks the complete new Lean theorem and its dependencies. The Python
checks use exact integers and rationals; they also verify the correspondence
between the frozen JSON and the Lean literals. They supplement the Lean and
independent kernel checks.

The committed toolchain and Lake manifest pin the dependencies. Recorded local
verification scripts additionally bind the compiler, source closure, compiled
artifacts, exporter, and independent kernel. Their Linux-cache mode describes
the measured local environment; a fresh checkout builds its own dependencies.

## Website submission and history

This update publishes the new modular formalization. It does not submit a new
candidate to the website or establish official resource compliance. The old
[single-file candidate](submission/proof/Solution.lean) is preserved exactly.
Its local Lean and independent replay checks passed, but the reported website
attempt exited with code 137 during compilation; no accepted website record
has been obtained. See the [submission requirements](docs/submission-contract.md),
[failed-attempt diagnosis](verification/site-compilation-exit137/diagnosis.json),
and [resource work](docs/resource-optimization.md).

Historical component checks, measured optimization experiments, and their
scope remain in `verification/` and `docs/`. Research papers remain available
here and in the main project; old results are retained under their original
namespaces and filenames.
