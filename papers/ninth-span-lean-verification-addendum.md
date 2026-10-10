# Lean verification addendum to the ninth-span paper

**Li Xiang (lixiang90), 10 October 2026**

This addendum records the formal verification completed after the mathematical
snapshot in [the paper](ninth-span-simple-critical-paper.tex)
([PDF](../output/pdf/ninth-span-simple-critical-paper.pdf)). The original paper
and its certificate are retained with their original hashes. Its statement that
the improvement had not yet been ported to Lean describes that earlier snapshot.

The new bound is

\[
\frac{N_{0,\mathrm{simple}}(0,T)}{N(0,T)}
\geq \frac{941021}{1397107}-\varepsilon
\]

for every positive \(\varepsilon\) and all sufficiently large \(T\), with the
corresponding dyadic statement. Here the denominator counts all nontrivial zeros
with multiplicity and the numerator counts multiplicity-one critical-line zeros.
The corresponding distinct critical-line statements follow from the actual
simple-to-distinct counting inclusion.

The unconditional entry point is
[`RecordProportion/NinthSpan.lean`](../RecordProportion/NinthSpan.lean).
Its theorem namespace is `RHWeilRecord.NinthSpan`:

| Declaration | Statement |
|---|---|
| `local_certificate` | Uniform reward `805403/100000000` for all eight real gaps at least `4/5` |
| `simple_dyadic` | Improved proportion for actual `Zeta23.N0simple T (2*T)` |
| `simple_cumulative` | Improved proportion for actual `Zeta23.N0simple 0 T` |
| `distinct_dyadic` | The same bound for actual `Zeta23.N0star T (2*T)` |
| `distinct_cumulative` | The same bound for actual `Zeta23.N0star 0 T` |
| `previous_recordRatio_lt` | Strict improvement over the retained `66812491/99194740` bound |

The finite proof covers all 2,399 feasible domains from the complete 482 × 482
physical-pair enumeration. It uses 25 patched representatives and 1,199
strengthened existing representatives. The 47 patched domains contain 84 closed
total-span branches. Exact reanchoring covers 2,955 tangent-row occurrences;
signed residuals are controlled by the full 42-variable box. All integer
certificate conclusions are checked by ordinary Lean kernel reduction, and
their soundness is proved for real gaps, including every branch endpoint.

The analytic transport retains the admitted majorant, energy bound, pair mass,
gap pressure, and zero-counting conventions. The changed local reward gives

\[
\frac{2-C_{\rm AM}-B}{1-c}
=\frac{66812491}{99194597}
=\frac{941021}{1397107}.
\]

There is no unproved finite-certificate hypothesis in the headline declarations.
The complete modular proof passes ordinary Lean compilation and a fresh
transitive axiom audit. Independent nanoda replay checks the full dependency
graphs of all six entries above. The recorded run checks 82,804 declarations
in 702.610 seconds with four threads; all bound inputs remain unchanged. Only `propext`, `Quot.sound`, and
`Classical.choice` are permitted. No additional analytic axiom, `sorry`, or
`native_decide` is used.

The [complete Lean receipt](../verification/ninth-span-complete-formal-kernel.json)
binds the final source closure, compiled artifacts, fixed dependencies, build
commands, and fresh axiom audit. The
[independent replay receipt](../verification/ninth-span-complete-independent-nanoda.json)
binds the same graph, a freshly compiled pinned exporter, and the independent
kernel run. See the [formalization guide](../docs/ninth-span-formalization.md)
for reproduction.

This verification completes the new modular formalization. The old single-file
website candidate remains unchanged. No new website submission or official
resource-compliance result is asserted by this addendum.
