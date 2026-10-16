# Exact nonnegative-affine-factor compression of the same two certificates

This changes only the representation of the two frozen local moment
certificates. No LP, new sample, threshold change, point-kernel evaluation,
Lean execution or running-cover change is used.

For an old row R<=B, its base and signed RLT rows have residuals R-B and
(R-B)(1 +/- y_s). The retained positive integer dual weights combine to

```text
(R-B) (A + sum_s b_s y_s) <= 0,
A = mu_base + sum_s (mu_s_plus + mu_s_minus),
b_s = mu_s_plus - mu_s_minus.
```

Each factor is nonnegative when |y_s|<=1 because A>=sum_s |b_s|. The
independent replay uses the canonical nonnegative decomposition
(A-sum |b|)*base + sum_s |b_s|*RLT(s,sign b_s). It then separately rebuilds
the original, unmerged integer multipliers and compares every unrounded
coefficient in all 464 variables and the constant term exactly.

| Case | Original product/base rows | Affine-factor groups | With energy row | Active distinct scalar slabs |
| --- | ---: | ---: | ---: | ---: |
| r001000001000001101011101 | 329 RLT | 103 | 104 | 10 |
| r001000001000001110011100 | 340 RLT + 1 base | 106 | 107 | 13 |

The original energy-zero integer weight is retained. Each weighted group,
including the weighted energy row, is outward-rounded once at denominator
1e30. The exact residual-box contradiction remains strict. Normalizing
only for comparison by 1e30 times the sum of the original integer weights:

| Energy packet | Case 0 margin | Case 1 margin |
| --- | ---: | ---: |
| Original precise packet | 0.002187302624264076 | 0.00010164513016933413 |
| Friendly centre-zero packet | 0.0021863744914656447 | 0.00010150187655611776 |

The Friendly variant changes only energy0. All factors and its energy
weight remain unchanged. The full unrounded polynomial also agrees with
the original multipliers after exactly that energy substitution.

The old full certificate JSON is 1,920,688 bytes, or 247,277 bytes with
deterministic gzip. The new standalone original-packet proof is 37,457
gzip bytes; the Friendly-packet version is 35,656 bytes. Both include their
complete ancestor projection. The optional original-multiplier comparison
archives are 4,410 and 4,408 bytes. Neither proof needs the original 2 MB
old-row/coefficient table or the full mutable cover checkpoint.

Schema `quadratic-energy-affine-factor-certificate-v1` stores each factor
as `old_meta`, decimal integer `A`, and sparse `b=[[coordinate,integer],...]`.
Old DBM/slab/facet/KKT coefficients are reconstructed from canonical metadata,
the active slab data, actual cell geometry and the frozen derivative table.
The remaining fields are the energy packet/weight, integerization scale
and expected strict aggregate. No repeated old-row table, per-product
rounded coefficient vectors or 464-entry box table is stored. Tight boxes
are reconstructed from the same scalar graph bounds.

`cover-cross-moment-factor-friendly-cases.json` is an ordinary JSON view for
the actual Lean consumer. It adds explicit cell bounds, physical gap centres
and radii, and the 41 tight derivative boxes. It preserves `old_meta,A,b`.

The stdlib-only independent replay passes for both variants (about 6.3
seconds each). It reconstructs ancestors, validates actual old graph row
inputs, checks factor nonnegativity and unmerged equality, independently
rounds all groups and verifies the strict aggregate. Stored energy point
intervals and whole-span second bounds remain supplied analytic inputs;
the new replay checks their quadratic algebra and, for Friendly packets,
their coarse point/grid composition. It does not repeat point transcendental
evaluation or prove the new Friendly analytic interfaces in Lean.

```text
python -S -B -X utf8 research-goal-20261016/cover_cross_moment_factor_replay.py
python -S -B -X utf8 research-goal-20261016/cover_cross_moment_factor_replay.py --folder research-goal-20261016/cover-cross-moment-factor-friendly-evidence
```

These are smaller proofs of the same two local numerical contradictions,
not new regions. Their union with the previous graph evidence remains 15
non-nested local regions. Actual Lean instantiation, global coverage and
a new unconditional zero-proportion record are not claimed here.
