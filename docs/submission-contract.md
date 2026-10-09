# Submission contract and current status

Checked again 2026-10-10 against the public website source at
`josusanmartin/riemann@6664d243005e12e155c19775b83f53721757414b`.
Authoritative contract:
https://github.com/josusanmartin/riemann/blob/6664d243005e12e155c19775b83f53721757414b/challenge/contract.json

The current accepted score when checked was `6735015/10000000`
(`attempt-016`). The target is `66812491/99194740`; the server's freshly
generated current score must be rechecked immediately before submission.
Historical whole-proof checks used `6734832/10000000`; preparing the new
CandidateSpec is not a fresh whole-proof pass.

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

A user-provided website log now records a failed attempt prepared as
`lixiang90-20261009-6735476624`: Solution.Candidate compilation exited 137
after 683 seconds. No website job UUID was provided, and no kernel acceptance
or formal record is inferred. See the [failed-attempt record](../verification/site-compilation-exit137/diagnosis.json).

The public display name is **Li Xiang**. The GitHub login is bound by the server
after OAuth; `lixiang90` is the intended account. The direct submission schema
has no `paperUrl` field: paper and repository links belong in the summary or
source attribution. The local draft JSON is a prepared submission manifest,
not a direct API payload. The reported upload was performed by the user; the agent did not perform it.

The fixed E2B template has four CPUs and 8,192 MB of memory. Its Comparator
process has a 3,200-second timeout (with a separate 3,240-second outer wrapper).
The complete verification must fit these constraints; a passed module does
not demonstrate that it does.
