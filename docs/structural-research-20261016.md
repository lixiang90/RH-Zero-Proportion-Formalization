# Structural research, 16 October 2026

This work investigates changes to the mathematical certificate, beyond raising
the floor of a fixed tree or adding terms to an enclosure. **No larger
unconditional zero-proportion theorem has yet completed Lean verification.**
The proved bound and website-ready proof in `GramDefect20261015` and
`submission/gram-defect-20261015` are unchanged.

## Overlapping windows: replace a local minimum by a mean bound

The existing nine-point proof pays for a function of eight consecutive gaps,
`Fw W9 g`. Its pointwise minimum lets each window choose its own worst gaps.
Consecutive windows share seven gaps, so these choices need not be compatible.
We instead seek a bounded seven-gap potential `V` such that, on gaps at least
`17/20`,

\[
 F_9(g)+V(g_0,\ldots,g_6)-V(g_1,\ldots,g_7)\ge c.
\]

For a separated `m`-point string with `m ≥ 9`, summing all `m-8` windows cancels
every interior potential. The total loss is at most `osc(V)`, independently of
the number of zeros. Thus

\[
 \sum_iF_9(g^{(i)})\ge c(m-8)-\operatorname{osc}(V).
\]

This permits a stronger mean floor without demanding that every isolated
window have that floor. `Coboundary.lean` proves the cancellation, the finite
band payment, and the separated remainder estimate. `CoboundaryCounting.lean`
proves a conditional transfer from that separated summed certificate to actual
simple and distinct zeta-zero counts. For an admissible certificate with
`0 < c ≤ 1/64` and `0 ≤ C ≤ c`, the existing counting interface with
`n_eff = n+1` absorbs the extra boundary charge `C`. Here `n=9`, so
`n_eff=10`; the geometric energy still uses W9. This effective parameter changes
only the error and boundary budgets. The local summed certificate remains an
explicit premise and has not been instantiated for the proposed new floor.

The fixed rational potential uses three gap classes, separated at `3/2` and
`5/2`. It has ten nonzero binary affine branches and seventeen ternary constant
corrections. `PotentialRange.lean` proves its range
`[-133/100000,143/100000]` on every seven-gap vector whose coordinates are at
least `17/20`, including arbitrarily large gaps. Its oscillation on that domain
is therefore at most `69/25000`, which is below the proposed `c`.
The fixed candidate is in
[`overlap_rational_candidate.json`](../research-20261016/overlap_rational_candidate.json).

The research target is `c = 4299/500000 = .008598`, with the existing pressure
and window. **If the remaining certificate is proved**, its score is

\[
 \frac{3338957652820594373879991756052499665323}
 {4957010000000000000000000000000000000000}
 \approx 0.6735829971738194.
\]

This conditional target is about `0.00017765` percentage points above the
current repository theorem. It is not a submitted or kernel-verified record.

### Exact arithmetic evidence and remaining gap

The old 48-root tree and its reflection give 21,874 numerical cells. Splitting
at the potential's class boundaries and the separation threshold produces
936,274 candidate subcells, of which 667,410 survive exact difference-constraint
closure. A first affine replay leaves 8,004 unresolved subcells. All 8,004
subsequently pass an exact-arithmetic tangent-mixture and integer-flow replay.
The exported mixtures and flows also pass a separate integer-only verifier:
[`independent-certificate-audit.json`](../research-20261016/independent-certificate-audit.json).
It checks all 8,004 exceptions without calling an optimizer. It does not
independently establish the initial tree's complete coverage.

The optimizer only discovers mixture weights. They are rounded down, their
kernel-weight capacities are checked with integers, and a nonnegative balanced
flow gives the affine lower bound. The tangent validity intervals come from
the attributed, already proved packed `PT` table; the source offset packing
`pwD` must be decoded before reading its endpoints.

`TangentSupport.lean` proves the enclosed-slope affine bound, `AffineFlow.lean`
proves the mixture and flow inequalities, and `GenericCover.lean` proves
coverage propagation for an arbitrary replacement leaf predicate. Its
reflection theorem requires certificates for both the original and reversed
potential orientations; it does not assume `V` is symmetric.
**The concrete finite data and every classified leaf have not yet been
instantiated in Lean.** Python replay is not a substitute for that step.
The [compression analysis](../research-20261016/certificate-compression-summary.md)
lists the remaining interfaces. Most subcells need no stored flow; at most
12,604 exceptions remain after a cheap affine check.

The complement of the 48 roots also matters. The inherited one-gap cover bound,
the other gaps' positive pressure, and the proved potential range give the
exact arithmetic margin

\[
 c_{\rm old}+\frac{17}{20}(B-\max_r b_r)-\frac{69}{25000}
 > .008598.
\]

Here `c_old` denotes the inherited one-gap cover floor. This is the proposed
route for the good-gap branches; that concrete complement proof remains to be
instantiated in Lean along with the numerical tree.

## Longer-range pairs and full weight reoptimization

Ten, eleven and twelve points allow pair distances unavailable to W9. Their
coefficients are optimized together under the exact capacity constraint
`spanMass s ≤ 2`; this changes the energy being paid, rather than the number of
digits in its old certificate. Positive pressure also makes the relevant
counterexample search domain bounded.

An early W10 floor `.00866` was **refuted** by a symmetric configuration with
central gap about `2.911`. An independent exact-rational interval calculation
bounds its energy below `.0086495`. The refuted parameters, counterexample and
their history are retained. Adding 19,683 local continuous searches over the
ternary boxes leads to replacement weights that pass this counterexample.

The replacement fixed W10 candidate is
[`spectral-w10-refined-rational.json`](../research-20261016/spectral-w10-refined-rational.json).
Its exact admissibility and pressure are checked separately from any analytic
floor. The stronger numerical challenges and proposed conditional score are
recorded with the parameters. No observed minimum is treated as a certified
lower bound. W11/W12 remain earlier, less challenged discovery experiments.

## Other structural results and rejected routes

- `FractionalPinching.lean` proves
  `sum_b w_b defect(A[B_b]) ≤ defect(A)` for a Hermitian matrix `A`,
  nonnegative weights, and total weight at each coordinate at most one.
- `Fenchel.lean` proves
  `tr(S(A-I)) - tr(S*S)/4 ≤ tr(Psi(A))` for Hermitian `A,S` with
  positive semidefinite slack `2I-S`. The matrices may fail to commute;
  neither matrix is required to be positive semidefinite.
- Uniform 24/32-point spectral candidates failed sparse large-gap adversaries.
  Their early optimistic scores are not valid records.
- A fixed-weight two-window perturbation has adverse numerical Rayleigh
  quotients at an active configuration, through 1,024 Fourier modes. This is
  evidence against the tested perturbation family, not a proved impossibility
  theorem for window changes.
- A binary clipped potential misses gaps near three. The three-class candidate
  passes the reported arithmetic checks for these cases; the rejected model
  is retained, and the full new local inequality remains unproved in Lean.

## Verification and submission status

The independent structural modules have ordinary Lean compilation and
transitive axiom receipts in `research-20261016`. They use only `propext`,
`Classical.choice` and `Quot.sound`; no new analytic floor is smuggled in as an
axiom. These receipts are distinct from a complete final theorem's statement
comparison and independent nanoda replay, which have **not** been performed
for either new candidate.

The existing upload at `submission/gram-defect-20261015/proof/Solution.lean`
remains the verified material for the repository's proved proportion. See
`submission/structural-20261016/status.json` for the status of these new routes.
Do not enter their conditional scores as proven website bounds.

To replay the exported arithmetic evidence from the repository root:

```powershell
python -B -X utf8 research-20261016/verify_exported_certificates.py
python -B -X utf8 research-20261016/research_manifest.py
```

The first command checks the two committed gzip data files. The second binds
the current local sources to the archived ordinary-Lean receipts; it does not
run a compiler. The `window-verify-*.py` scripts and the commands recorded in
the other receipts perform the actual Lean checks in the prepared pinned
runtime. See the [fixed W10 research summary](../research-20261016/spectral-final-summary.txt)
for the independent longer-window reproduction commands.
