# Actual bridge plan for the fixed swap (6,7)

This is a static implementation plan, with one authorized finite arithmetic audit. No Lean source was generated or compiled for this packet. The fixed necessary row separates one old exact pseudo-moment point; it does not exclude the whole parent cell. The complete eight-swap model and any exact infeasibility certificate remain separate decisions.

The actual target bridge is

```text
Contains cell g ->
  Fw24 (WindowGlobalCompetitor.swapGap g 6 7) - Fw24 g <= Dplus(g).
```

Together with the already proved `WindowGlobalCompetitor.upper_change_nonneg`, this gives `Relevant sep g -> 0 <= Dplus(g)` on that cell. The actual energy, separated orthant and global-minimum quantifier are already connected. No orientation of the swapped point, or membership of the swapped point in the original cell, is required.

## What is reusable now

| Obligation | Existing actual Lean interface | Remaining work |
|---|---|---|
| Normalized coefficients at integer centres | `WindowFixedTablesAll.w_sound`; `WindowRawCoefficients.table_eq` and `sound` | Reuse the frozen table; no new transcendental sampling or sinc/trigonometric proof. |
| Actual derivative at a rational point | `WindowFixedDerivative.interval`, with `q=j`, `d=23-j`, for `j=0,...,4`; also `WindowDerivativeAffineOracle.point_error` | Finite endpoint/error checks. Its FI Horner rounds at scale `10^30`, so the packet's exact rational endpoints cannot be identified with this result without checking containment or adding a guard. |
| Taylor remainder after translating each derivative | `WindowDerivativeTableArithmetic.derivative_remainder q d`, where `q+d+1=24`; `shifted_coeff` and `coeff_sound` | No new analytic derivative bound. The remainder is `(44/7)^24 * abs(p-n)^(24-q)/(24-q)!`. |
| Actual fifth derivative on a grid cell | `WindowCellDerivative.interval`, instantiated at `q=5`, `d=18`, `a=k/64`, `b=(k+1)/64` | New finite Horner-choice and endpoint checks for the 391 selected cells; no old grid theorem currently supplies these fifth-derivative values. |
| Consecutive grid coverage | `WindowGridRange.covered` | A thin consumer for fifth-derivative rows, analogous to the existing first/third-derivative consumer. `GridAll` itself proves first/third bounds, not fifth bounds. |
| Smoothness and global order-24 bound | `WindowConvexityCertificate.w_contDiff`, `w_iterated_contDiff`; `WindowTaylorBridge.w24_twentyfour_abs_le` | Reuse. Do not differentiate an inequality for a remainder. |
| Original span bounds | `WindowScalarLine.span_bounds`; `WindowDifferenceCell.adjacent_difference`; `WindowValueFlow.span_sum` | Explicitly identify the packet's 45-span state with a concrete `DifferenceCell.Cell 10`. This is a local cell obligation, not a formal ancestor/root-cover proof. |
| Actual 41-term energy and positive weights | `WindowGramTransfer.actual_energy_expansion` and `weight_nonneg` in `WindowGramExpansion.lean`; `WindowValueFlow.weight_cast` | Prove the fixed swap's pressure identity, eight changed terms and 33 exact cancellations, then sum the scalar bounds. |
| Necessary inequality at a global minimum | `WindowGlobalCompetitor.swap_energy_le`, `upper_change_nonneg` | Apply the actual difference upper bound. A negative pseudo-expectation does not supply a uniform negative upper bound on every actual point. |

There are **16 scalar packets but only 14 distinct rational anchors**. Each anchor needs orders 0 through 4: 70 distinct derivative intervals, rather than 80 independent recomputations. Their nearest integer centres are 2 through 8. All 391 fifth-derivative cells use centres 2 through 9; the selected cell indices lie between 120 and 566, with gaps. Every cell is inside the existing centre range 1 through 32 and its required half-unit Taylor interval. Centre zero is not needed.

## The old w-prime table is a separate input

The packet's point jets use `window_normalized_interval.json`, whose 32-by-24 nonzero-centre literals agree exactly with the already proved `WindowRawCoefficientData.W`. Its old fifth-derivative provider instead used `cover_newjet.json`'s w-prime coefficients. These are not byte-identical derivative-table entries. This observation does not show that the old provider is invalid; it shows that its soundness cannot be inherited just by equality or blanket interval containment from the current proved table.

The whole-table comparison has 736 entries: 32 centres (1 through 32), times old w-prime coefficient orders 0 through 22. Of these, 445 are contained by the corresponding normalized-W-derived interval, 135 contain that normalized interval, and none are exactly equal. The actually used subset is smaller: 8 centres (2 through 9), times old w-prime orders 4 through 22, giving 152 entries. There the corresponding counts are 81 and 40, again with no exact equalities. The two containment counts need not sum to the total.

The shortest formal route avoids proving the old high-precision w-prime table. Differentiate the already proved normalized-W Taylor polynomial five times instead. The resulting degree-18 coefficient is `W[n,j+5] * (j+5)!/j!`. This has the same analytic remainder `M24*(1/2)^19/19!` as the old w-prime degree-22 polynomial differentiated four times. The exponent is **19** in both routes.

The authorized static audit `m5-compatibility-audit.json` performed this comparison on exactly the selected 391 cells, using both exact rational interval Horner and the existing fixed-integer, outward-rounded `10^30` Horner. The latter encloses the former in every cell. A few individual cell bounds need at most one additional `10^-15` tick compared with the old provider. Nevertheless, the maxima over **all 16 whole scalar spans stay at or below their original packet M5 values**. Thus this swap's original M5 payments can be retained by a future proof using the normalized-W route. This receipt is an arithmetic feasibility audit, not a Lean proof of the 391 checks.

## New generic inequalities actually needed

Two small analytic/arithmetic bridges are missing, in addition to concrete finite checks.

1. **A local fourth-degree Taylor envelope.** Existing `WindowConvexityCertificate.taylor_remainder` requires a bound on every real argument. Here M5 is proved only on the scalar span. Add a local version using the same Mathlib Lagrange theorem, with `p,x` in a closed interval and the intermediate point in that interval. Prove

   `abs(w(x) - taylorPoly w 4 p x) <= M5 * abs(x-p)^5 / 120`.

   Then combine the five jet error intervals with `abs(x-p)<=R` to obtain the packet's precise envelope. With `d=x-p`, retain

   ```text
   P4(d) = sum(j=0..4) mu[j]*d^j/j!
   E4(d) = eps[0] + eps[1]*R
         + (eps[2]/2 + eps[3]*R/6)*d^2
         + (eps[4]/24 + M5*R/120)*d^4.
   P4(d)-E4(d) <= actual_w(x) <= P4(d)+E4(d).
   ```

   Nonnegative `eps[j]`, M5 and R are explicit. Use `abs(d)^3 <= R*d^2` and `abs(d)^5 <= R*d^4`; do not replace the dynamic fourth power by `R^4` or the fifth remainder by a constant `R^5` payment.

2. **If preserving the packet's exact point-jet endpoints: exact interval Horner.** The Python point-jet recurrence uses unrounded rational addition and multiplication. Existing `WindowPointTableArithmetic.polyI` and the FI implementation round at `10^30`, so they may produce a slightly wider endpoint. A short recurrence using the already proved `WindowRationalInterval.add_sound` and `mul_sound`, followed by `shifted_coeff` and `derivative_remainder`, proves the exact packet intervals without new analysis. This is the cleanest route if the fixed polynomial row is to remain byte-for-byte unchanged. An alternative is to widen the point errors by a checked finite guard and re-evaluate the model; that is a different packet and was not done here.

The image span bounds also need short finite algebraic proofs. For edges `(i,7)`, use both `s_i6+g7` and `s_i8-g6`; for `(7,j)`, use both `g6+s_8j` and `s_6j-g7`, together with the sum of permuted adjacent boxes. Intersect the three valid intervals. These are consequences of the original cell, not an assumption that the image lies in it.

## Smallest future dispatch, only after a model gate

No dispatch is started by this plan. If the full eight-family experiment later supplies useful exclusion evidence, a conservative sequence is:

1. One new exact-point-Horner/local-quartic core, ordinary Lean plus fully qualified axiom audit.
2. A small fifth-grid checker wrapper reusing `WindowCellDerivative.interval`, then a pilot of a few selected cells. Materialize independent numeric auxiliaries and checkpoint them; do not put 391 recursive computations into one huge `decide`.
3. Reuse 14 anchors and 70 derivative intervals, with independent auxiliaries per anchor/order. If their exact rational constants are expensive, use exact interval-operation checkpoints, not a monolithic 80-statement normalization.
4. Only after measured cost, finish the selected cell blocks and their grid-coverage consumer. No new transcendental table is needed.
5. A fixed swap geometry/cancellation bridge and a scalar-envelope sum giving actual `hD`. Keep the factored eight-term quartic formula as long as possible; a finite coefficient identity can later connect it to the 715 monomial order without expanding the whole formula in every real-valued proof.

The existing 464-variable degree-two moment lift is not the 715-monomial quartic lift. A later exact outer-relaxation infeasibility proof would need its own actual quartic row, moment/localizer soundness and exact dual certificate. The current negative expectation eliminates only one old pseudo-moment point. Neither the original parent, its ancestor tree, a global floor, nor a new zeta-zero proportion is proved by this plan.

`plan-dependencies.json` records the exact current source bytes and their available ordinary-Lean receipt bindings. `formal-plan-files.json` freezes only this new plan/audit package; no old source, receipt or published manifest is modified.
