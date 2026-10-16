# Fixed-cell affine-slack RLT diagnostic

This experiment keeps the frozen original464-variable moment model and its
single DBM-feasible-midpoint energy0 packet at floor11/1250. Its only cell
is `r001000001000100110011001`, the first of the previously frozen six
remaining parents. There are no new kernel samples, anchors, PSD cuts,
cases, threshold changes or changes to the main search.

For every old affine residual R-B<=0, a nonadjacent span bound
L<=x_ij<=U gives the valid products

```text
2(x_ij-L)/(U-L) * (R-B) <= 0,
2(U-x_ij)/(U-L) * (R-B) <= 0.
```

Only bounds that improve on the sum of the corresponding independent gap
bounds are candidates. Adjacent-gap factors are omitted because the old
model already contains them. The single pressure sublevel factor
2(c-P(g))/(c-P(sep)) is also a candidate: c-P(g)>=0 follows from F<c and
the nonnegative kernel-square terms. A factor can be negative on the
larger independent gap box; its actual DBM/sublevel positivity is checked
directly. No assertion A>=sum|b| is made.

All products use the existing position moments and position-times-gradient
moments. The exact rational factor and the integer old-atom index are
stored with every selected row. The selector inspects candidates in small
arrays rather than allocating the full product matrix. Scores are divided
by max(1,abs(bound),maxabs(coefficients)), matching the LP row scaling.

There are2192 old atoms and39 candidate factors (38 DBM, one pressure).
Starting from the previous zero-slack floating primal, the first pass
inspected85488 products and found2883 positive violation hints. It added
the64 most violated rows. Default HiGHS solved that system in4.83seconds,
with energy slack0 and maximum softened-row error about2.29e-14.

The second pass found927 further violated candidates and added64 rows.
Default HiGHS hit the45-second limit without returning an accepted primal
or dual. This call is inconclusive. Both rounds and the exact128 selected
rows were saved; no further cuts were added. All128 selected factors were
DBM slacks; the pressure candidate was not selected by this limited ranking.

An authorized algorithm-only comparison reuses exactly those128 rows and
the same energy packet. `highs-ipm` solved in1.29seconds, with3 interior
iterations and293 crossover iterations. It reports slack0, maximum
floating row error7.14e-8, and no box violation. This is an approximate
floating primal, not a rational feasibility proof. Neither run produced a
strict integer exclusion. The limited128-row model therefore gives no new
closure; it does not test the entire stronger slack-product cone.

The independent Python-S replay reconstructs108 distinct old atoms from
canonical DBM/KKT/facet/slab metadata, checks the five active scalar slabs
and actual derivative-grid finite inputs with the earlier GraphReplay,
checks all39 exact affine factor identities/positivity reasons, and checks
all128 stored product polynomials using a separately implemented signed
coordinate-RLT expansion. The signed expansion checks algebra only;
positivity is supplied by the actual span inequality. No optimizer or
NumPy is imported in this replay. Ancestry and energy0 provenance are
reused from the already frozen remaining-six standalone evidence.

The independent abstract cone counterexample is in the separate recovery
and structure pin. It proves that the new cone is mathematically stronger
than coordinate RLT, KKT, McCormick and position PSD. It does not supply an
actual-window exclusion or a runtime improvement.

All new exclusion counts are0. Complete global cover, unconditional new
zero-proportion record, and new actual Lean consumer flags remain false.
