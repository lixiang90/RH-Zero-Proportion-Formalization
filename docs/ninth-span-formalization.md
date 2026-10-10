# Closed ninth-span formalization

This additive development formalizes the strengthened simple critical-line zero proportion

\[
p=\frac{941021}{1397107}=\frac{66812491}{99194597}
  =0.673549699486152456\ldots .
\]

The numerator counts critical-line zeros of multiplicity one. The denominator counts all nontrivial zeros with multiplicity. Inclusion of simple zeros among distinct critical-line zeros also yields the corresponding distinct-zero proportion.

The previous result, `66812491/99194740`, remains available in its original namespaces, source files, submission, and verification records. The new declarations use the separate namespace `RHWeilRecord.NinthSpan` and its finite-certificate support modules.

The improvement uses the same AM kernel, energy estimate, and gap pressure. It strengthens the uniform nine-point reward from `805260/100000000` to `805403/100000000` by subdividing the total-span interval of the weakest pair domains. The ratio is transported through

\[
p=\frac{2-C_{\mathrm{AM}}-B}{1-c},
\qquad c=\frac{805403}{100000000}.
\]

The certificate applies to continuous real gaps. Integer endpoints encode rational inequalities with denominator `5 SC`, where `SC = 32768`; the gaps themselves are arbitrary real numbers. Closed intervals include their shared endpoints. The added affine cuts use a proved genuine tangent and a certified derivative interval, with exact reanchoring endpoints.

The complete compatible cover has **2,399 pair domains**. The new data replace **47 physical pair domains** with **84 closed branches**. Reflection reduces the relevant old finite assembly to 1,224 representatives: **25 weak representatives** use the new patches, while the other **1,199 representatives** reuse their old sparse duals at the strengthened threshold. The residual correction retains the complete coordinate box.

Six assembly modules and one generic path module form the following proof chain:

| Module | Role |
| --- | --- |
| [`NinthSpanPoints.lean`](../RecordProportion/NinthSpanPoints.lean) | Checks the 541 entries of the new catalog against the original proved AM point table and proves exact real-interval tangent reanchoring. |
| [`NinthSpanPathSoundness.lean`](../RecordProportion/NinthSpanPathSoundness.lean) | Proves that an integer path certificate bounds a real potential difference by summing the adjacent directed inequalities. This generic module imports only mathlib. |
| [`NinthSpanFiniteData.lean`](../RecordProportion/NinthSpanFiniteData.lean) | Encodes the 84 branches, 47 patches, routing, row guards, and exact integer dual checks. |
| [`NinthSpanFinite.lean`](../RecordProportion/NinthSpanFinite.lean) | Proves branch rows and the real bounds certified by integer path witnesses, covers the closed branches, and transports the representative bounds to all compatible physical pairs. |
| [`NinthSpanLocal.lean`](../RecordProportion/NinthSpanLocal.lean) | Combines the low-pair cover with the stronger outer-frame case to obtain the uniform nine-point reward. |
| [`NinthSpanAnalytic.lean`](../RecordProportion/NinthSpanAnalytic.lean) | Transports the strengthened reward through the retained Gram assembly, lossless defect inequality, and asymptotic count estimates. |
| [`NinthSpan.lean`](../RecordProportion/NinthSpan.lean) | Discharges the local-certificate hypothesis and assembles the unconditional theorems for actual Zeta23 zero counts. |

The exact checker computes the stored closure bounds by Floyd's algorithm. The Lean certificate pays for these bounds with explicit paths through primitive integer inequalities and the closed total-span inequalities. Each checked path has between one and nine vertices, uses vertex labels below nine, has the claimed endpoints, and has integer cost at most the stored bound. The path soundness theorem telescopes the corresponding real potential differences. This representation retains the closure values while keeping their proof replay small.

The headline declarations are:

| Declaration in `RHWeilRecord.NinthSpan` | Actual counts |
| --- | --- |
| `simple_dyadic` | `Zeta23.N0simple T (2*T)` against `Zeta23.Ncount T (2*T)` |
| `simple_cumulative` | `Zeta23.N0simple 0 T` against `Zeta23.Ncount 0 T` |
| `distinct_dyadic` | `Zeta23.N0star T (2*T)` against `Zeta23.Ncount T (2*T)` |
| `distinct_cumulative` | `Zeta23.N0star 0 T` against `Zeta23.Ncount 0 T` |

Each statement has the asymptotic form: for every real `ε > 0`, there is a threshold `T₀` such that, for every `T ≥ T₀`, `(p - ε)` times the specified total count is at most the specified critical-line count. `previous_recordRatio_lt` proves the strict comparison with the preserved previous proportion.

To reproduce the build, use the versions pinned by `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`:

| Dependency | Fixed version |
| --- | --- |
| Lean | `leanprover/lean4:v4.33.0-rc2` |
| mathlib | `51e6992efd06126df61a496bebf8f49482a4e129` |
| Zeta23 | `3635e74826a4c1fcece7d1cd2b6fa75e43a00510` |

Run these commands from the repository root after installing the pinned Lean toolchain:

```text
lake --no-cache exe cache get
lake --no-cache build +RecordProportion.NinthSpan:olean
python -B -X utf8 scripts/generate_ninth_span_certificate.py --check
python -B -X utf8 scripts/am_ninth_span_certificate.py --check
```

The generator checks the frozen input identities, reconstructs the integral rows, and compares the generated Lean data with the saved source. The exact checker replays all 2,399 domains with rational arithmetic and checks the closed branch cover. These Python checks complement the Lean proof; the ordinary Lean build checks the proof terms connecting the finite inequalities to the actual count theorems.

Run results are recorded separately in [`verification/ninth-span-complete-formal-kernel.json`](../verification/ninth-span-complete-formal-kernel.json) and [`verification/ninth-span-complete-independent-nanoda.json`](../verification/ninth-span-complete-independent-nanoda.json). The first records the fresh Lean build and transitive axiom audit; the second records the independent kernel replay. Their status fields, bound source identities, and logs identify the results of the respective runs. The permitted transitive axioms are `propext`, `Classical.choice`, and `Quot.sound`. Component evidence is also retained, including [`verification/ninth-span-points.json`](../verification/ninth-span-points.json).

The [`paper source`](../papers/ninth-span-simple-critical-paper.tex) and [`PDF`](../output/pdf/ninth-span-simple-critical-paper.pdf) retain the mathematical snapshot prepared during the research stage. Their recorded identities are preserved. The full formal proof structure and its run records are documented here and in the separate verification receipts; the older papers and their identities remain intact as well.

All previous proof code, data, theorems, verification records, and `submission/proof/Solution.lean` are retained unchanged. This update does not perform a new website submission; the existing submission file continues to represent the previous record.
