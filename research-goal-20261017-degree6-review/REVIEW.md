# Static necessity review of the proposed degree-six extension

Scope: the same cell `r001000001000100110011001`, actual target `11/1250`, the frozen quartic model and its eight normalized-W swap rows. This review runs no model builder, solver, new point, Lean or matrix-feasibility test. It checks mathematical necessity and index/principal-submatrix structure. It does not show that the old exact pseudo-moment has no extension.

## Actual meaning and the KKT sign

For an actual edge let `d=s_e(g)-p_e`, with `abs(d)<=R_e`. The old packet uses actual derivative midpoints/error bounds for orders 1 through 4 and an actual whole-span fifth-derivative bound as explicit analytic premises. Its cubic and even error polynomial are

```text
U3_e(d) = mu1 + mu2*d + mu3*d^2/2 + mu4*d^3/6,
E4_e(d) = eps1+eps2*R
          +(eps3/2+eps4*R/6)*d^2 + M5*d^4/24.
```

With sound input bounds, `abs(w'(s_e(g))-U3_e)<=E4_e`. The order-four Taylor remainder here is for w-prime, hence uses w^(5), not w^(4). The odd anchor-error payment uses `abs(d)^3<=R*d^2`; the dynamic fourth power is retained.

The coordinate polynomials are

```text
P3_r = b_r + sum(e contains r) a_e*U3_e,
E4_r = sum(e contains r) a_e*E4_e,
abs(actual_gradient_r-P3_r)<=E4_r.
```

All retained ledger weights are nonnegative. At a free actual minimizer, the gradient vanishes and **E4_r+P3_r>=0 and E4_r-P3_r>=0**. These are the legal two localizer multipliers. The literal alternative `P3_r +/- E4_r >=0` is wrong: its minus branch reverses one necessary inequality. The old source correctly implements `E[r]+sign*H[r]`. It also retains `E[r]+sign*y_s*H[r]`, using `abs(y_s)<=1`; those 180 old scalar rows should remain unchanged.

The stored linear-row convention is `coefficients·moments<=bound`. `append_nonnegative(p)` stores minus the nonconstant coefficients of p with bound equal to its constant. Thus it means p>=0. A new localizer must use the positive polynomial itself, not that row's negated coefficient vector.

## All nine coordinates really are free

The original orthant floor is `SEP=123/128`, or 31488 in SC=32768 units. The cell's adjacent lower endpoints are

```text
32248,32889,32431,32446,32465,32615,64179,61684,58403.
```

Their margins above the original floor are

```text
760,1401,943,958,977,1127,32691,30196,26915 > 0.
```

Consequently every actual point contained in this cell is strictly interior in all nine original orthant coordinates. `WindowKKTInstance.of_relevant` and the actual `WindowGapEnergy.coordinate_hasDerivAt` give all nine gradient equalities. A cell's artificial boundary is irrelevant. The orientation `g0<=g8` also imposes no extra multiplier: Relevant's minimization clause ranges over the entire orthant, including unoriented competitors.

## Degree and principal embedding

Use one canonical sorted monomial list of the same nine normalized coordinates y. There are 5005 monomials through degree six, including 1; hence 5004 nonconstant moment columns. The degree-at-most-three basis has 220 entries, the degree-at-most-two basis 55, and the degree-at-most-one basis 10.

| Proposed block | Size | Multiplier degree | Maximum entry degree |
|---|---:|---:|---:|
| M3 | 220 | 0 | 6 |
| 45 geometry products and the old L2 sublevel localizer | 46 × 55 | 2 | 6 |
| Eight global-competitor D4 localizers | 8 × 10 | 4 | 6 |
| Nine pairs E4 +/- P3 localizers | 18 × 10 | 4 | 6 |

This gives 73 blocks and 96580 lower-triangle entries if stored explicitly. It does not require a sixth-order Taylor approximation or a new derivative order: these are larger polynomial-square test bases for the already stated polynomials.

For any actual relevant point and any nonnegative multiplier q(y),

`lambda^T [q(y)*v(y)*v(y)^T] lambda = q(y)*(lambda·v(y))^2 >= 0`.

This proves necessity for a Dirac point, and hence for positive combinations of such points. Geometry multipliers are nonnegative at all cell points. The L2 multiplier `(c-L2)/c` requires actual `L2<=F<c` and c>0. The D4 and KKT multipliers require genuine global minimality/KKT; they are not asserted nonnegative at every arbitrary cell point.

The old M2 is the first 55-by-55 principal block of M3. Each old 10-by-10 geometry/L2 block is the first 10-by-10 principal block of its 55-by-55 upgrade. The multipliers and normalizations must remain identical. Therefore no stronger actual hypothesis is needed for the upgrades. The static audit checks all 4070 old stored entries against their multiplier-times-monomial definition and this embedding, without materializing the 96580 new entries.

Preserving all 5803 old scalar rows and those principal blocks proves only the non-strict inclusion of the new feasible set's projection into the old feasible set. It does not prove strict inclusion, elimination of a particular old pseudo-moment, or infeasibility. A larger PSD block may still admit an extension of the old moments. This review does not attempt one.

## Slack and variable bookkeeping

The first 715 monomials remain the old degree-at-most-four list. Nonconstant moment columns 0 through 713 therefore stay unchanged. The **old energy slack column 714 must move to 5004**. Column 714 now means the first degree-five monomial, y0^5. Only that distinguished slack index is remapped; shifting all high columns would corrupt the old moments.

The fixed constant moment is not an optimization column. There are 5004 nonconstant moments plus one scalar energy slack, hence 5005 optimization variables. This number happens to equal the monomial count including the constant; their meanings differ. The slack is not a tenth underlying variable, and no power of it belongs in M3.

The old quadratic sublevel multiplier remains unsoftened. Do not replace c-L2 by an expression containing the diagnostic energy slack. Only the old quartic energy row is softened. The new eight swap rows and KKT multipliers must not be weakened by that slack.

There are 4290 new degree-five/six moments: 1287 and 3003 respectively. Explicit bounds -1<=moment<=1 are necessary because each actual normalized coordinate is in [-1,1]. For the 165 new all-even monomials (all degree six), the lower bound is 0. This adds 8580 scalar bounds; retaining 5803 old rows gives 14383 rows before any optional duplicates. These are moment bounds, not new actual scalar samples.

## Actual analytic premises still visible

1. Actual F0 at the common old anchor and the old L2 minorant must be connected to the current cell by concrete checked packets. Generic `WindowMomentEnergyCertificate.lower` exists; it does not instantiate every old packet in this model.
2. The old P3/E4 construction uses `cover_newjet.json`'s w-prime literals and 658 old w5 grid cells. Their exact use was independently replayed numerically, but the entire old high-precision literal table is not identified with the already proved normalized-W table. The earlier static audit found only partial interval containment, so current generic derivative theorems do not silently discharge these particular endpoints.
3. One future route is to derive old point orders 1..4 and w5 directly from proved normalized W via `WindowFixedDerivative.interval` and `WindowCellDerivative.interval` (q=5,d=18), with concrete finite containment checks or explicitly guarded replacement packets. This may change the old model if bounds widen. No such replacement is made here.
4. The eight new swap rows use normalized W rather than old w-prime literals, but their 87 exact-rational scalar packets and 622 selected w5 cells still need concrete finite Lean checks. The previous 391-cell feasibility audit concerns only swap67 and does not prove the whole 622-cell family. Exact rational point Horner also needs its small soundness bridge or checked FI guards.
5. Local cubic/quartic Taylor envelopes and the actual geometry/cancellation-to-D4 inequality remain to be instantiated. Existing smoothness, actual order-24 bound, ledger signs, derivative/energy identities and global-competitor APIs support them; the generic global-competitor theorem alone is not the numerical D4 bridge.
6. Actual profile positivity is already available through the current profile/kernel proofs. Use the corrected `WindowProfile.V_ge_core`/`WindowKernel.v24_nonneg`, not the superseded claim that the cosine-based profile is at least 1-4/25.
7. Polynomial localizer/PSD soundness, actual quartic or sextic moment indexing and any exact dual/PSD certificate would still need formal consumers. The existing 464-variable quadratic lift is not automatically the new 5004-moment layout.

None of these obligations is discharged by introducing degree-five/six variables. The static combinatorial audit does not validate a future model implementation; that implementation must separately demonstrate exact old-row retention, the slack remap and every matrix entry. No new region exclusion, global cover or zero-proportion improvement is established here.
