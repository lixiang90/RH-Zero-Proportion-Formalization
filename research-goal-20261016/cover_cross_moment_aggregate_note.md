# Additional one-row forms: single outward round and exact LCM

These are read-only forms of the same Friendly/global-box aggregate. No
factor, energy weight, threshold, sample, LP or old file changes. The
exact sum of 103/106 valid affine-factor rows and one weighted energy row
has 320/330 nonzero coefficients among 464 variables.

The first form sums all rational rows exactly and then outward-rounds only
one row at 1e30. Independent canonical-RLT expansion and an independent
rounding implementation agree and both residual-box margins are strict.
`cover-cross-moment-single-round.json` retains this optional form.

The simpler form clears the exact least common denominator of all rational
coefficients and the bound. Denominators D0 have only 51/54 decimal digits.
The complete integer-row records are 20,509/21,748 JSON bytes; the combined
owner packet `cover-cross-moment-exact-aggregate.json` is 43,337 bytes.
It contains exact A_i and B_int with the convention

```text
sum_i A_i * variable_i <= B_int,
exact rational aggregate = (A_i/D0, B_int/D0),
residual constant = -B_int.
```

The global boxes have integer endpoints L_i,U_i over
`boxDen=32768*10^15`. Both cases satisfy the strict integer comparison

```text
boxDen * B_int < sum_i min(A_i * L_i, A_i * U_i).
```

No rounding or rounding-payment proof is needed for this form. Its exact
normalized margins are approximately 0.002186353792546525 and
0.00010148292670532981. The verifier checks the minimal common denominator,
all 464 rational/integer coefficient identities, the bound and the strict
box inequality using independent Fraction and integer computations.

```text
python -S -B -X utf8 research-goal-20261016/cover_cross_moment_single_round.py --verify
python -S -B -X utf8 research-goal-20261016/cover_cross_moment_exact_aggregate.py --verify
```

The existing global-box proof supplies row validity and ancestry. The
additional finite equality required by a Lean consumer is that the valid
rational group sum equals the displayed integer row divided by D0; it can
then use one bounded-row contradiction. The actual analytic/Lean inputs
are not reproved by this data conversion. This supplement adds no new
local region or global zero-proportion result.
