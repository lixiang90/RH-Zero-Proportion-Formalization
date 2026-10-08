# Submission contract and current status

Checked again 2026-10-09 against the website's live homepage and public source at
`josusanmartin/riemann@668e239f30c7c56494611b1825306a3d65f95537`.
Authoritative contract:
https://github.com/josusanmartin/riemann/blob/668e239f30c7c56494611b1825306a3d65f95537/CONTRIBUTING.md

The current accepted score when checked was `6734832/10000000`.
The target is `66812491/99194740`; the server's freshly generated current score
must be rechecked immediately before submission.

Three exact declarations are required:

```lean
theorem candidate_strict_improvement :
    currentRecordKappa < candidateKappa

theorem candidate_critical_line_bound :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T)

theorem candidate_critical_line_bound_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Ncount 0 T : ℝ) ≤ N0star 0 T
```

`Ncount` and `N0star` are the trusted website counting functions. The latter
counts distinct critical-line zeros. A proved simple-zero bound requires a
genuine count inclusion bridge and the fixed dyadic theorem.

Submit through https://www.riemannzeta.fun/submit with GitHub sign-in, an exact
rational score, public name, method, summary and one Lean file. No PR is needed.
There are three admitted uploads per UTC day; even failed queued attempts count.
Validate locally before uploading. A CLI uses a dedicated fine-grained GitHub
token without repository permissions; do not reuse a repository write token.

The source limit is 2,000,000 UTF-8 bytes and the JSON request limit 4,000,000 bytes.
The permitted axiom subset is `propext`, `Quot.sound`, `Classical.choice`.
`sorry`, new mathematical axioms and `native_decide` dependencies cannot pass.
Lean and nanoda must both accept. Every admitted source is retained in an
encrypted maintainer archive; accepted proofs are public under Apache-2.0.

No upload, job ID, kernel acceptance or formal record currently exists for this target.
