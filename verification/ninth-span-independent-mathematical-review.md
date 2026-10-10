# Ninth-span finite and continuous bridge review

Reviewed by the Codex agent `/root/ninth_span_analytic_transport`, 2026-10-10.
This is an automated, software-assisted mathematical review independent of the
finite-certificate and point-certificate implementation authors. The reviewer
also authored `NinthSpanAnalytic.lean`; this document is not an independent human
peer review of the entire project. Compilation, transitive-axiom checks, and
independent kernel replay have their own receipts and are not asserted by this
review alone.

At the refreshed snapshot below, the complete production ordinary-kernel
and Nanoda checks were still in progress. Two earlier full-build invocations
were manually stopped; their incomplete observations establish neither a
completed build nor a mathematical failure. The refreshed source adds
`Elab.async false` and progress messages while retaining the frozen
mathematical literals verified by the exact data audit.

The full ordinary-kernel compilation and final transitive-axiom audit are
reported by [`ninth-span-complete-formal-kernel.json`](ninth-span-complete-formal-kernel.json).
Independent declaration replay is reported by
[`ninth-span-complete-independent-nanoda.json`](ninth-span-complete-independent-nanoda.json).
Their final success fields and source bindings govern those statuses. A generic
semantic probe with temporary finite-family parameters does not discharge the
production file's closed finite families and is not a substitute for those
final receipts.

The reviewed finite bridge has no identified mathematical gap. The accompanying
`ninth-span-independent-data-audit.json` records an exact, independent comparison
of the generated Lean literals with the frozen public payload. The review script
parses both new literals and the old packed Lean cell, point, representative, and
orbit tables; it does not invoke the finite implementation author's generator,
an optimizer, or floating-point arithmetic. Its input pins use canonical LF,
while the source snapshot below records actual file bytes.

## Real total-span intervals and closed coverage

`gapPotential g i = 5 * 32768 * sum_{r<i} g r` is a real-valued potential.
The two-frame primitive edge bounds are inequalities for this actual potential.
The branch edge matrix also incorporates the new lower and upper total-span
bounds in entries `(8,0)` and `(0,8)`. A stored path starts and ends at the
corresponding matrix indices. Summing its true edge inequalities telescopes to
the desired potential difference. The integer guard checks
`path cost <= stored upper bound`, so that stored upper bound is a valid real
bound. The opposite inequality would not suffice. Integer endpoint storage
does not impose a lattice or round any actual gap.

`NinthSpanPaths.cost_real_bound` proves the telescoping inequality by induction
on the list of vertices, and `check_real_bound` combines it with the exact
integer cost check. Its premises require every traversed vertex to be below
9 and the same primitive/branch edge function to bound the true potential.
The source correctly casts and sums signed integer edges; no positive-edge
assumption or shortest-path equality is needed.

`patchShape` checks primitive paths for the first lower endpoint (direction
`8 -> 0`, cost at most its negative) and the last upper endpoint (direction
`0 -> 8`, cost at most that endpoint). These path bounds hold on the complete
original real two-frame domain. All branch labels match that same original
cell pair, and consecutive closed intervals overlap.
`patch_real_bound` uses three exhaustive real inequalities. A split endpoint is
covered by the preceding branch; a point beyond it has the next lower bound by
the checked overlap inequality. Repeating the last branch handles one or two
pieces without leaving a gap. All 47 patches and all 84 stored branch closures
match the published payload and have zero diagonal entries in the independent
exact reconstruction. The independent audit verifies all 6,804 branch paths
and all 94 outer coverage paths, including their packed lengths, vertices,
endpoints, and exact costs. It separately reconstructs the original Floyd
closures and verifies that the stored bounds agree; the formal path soundness
does not rely on recomputing these closures.

## Added rows and genuine tangents

Closure rows are inequalities for exact prefix differences. Tangent rows use
the existing true AM squared kernel, not a replacement polynomial. For derivative
bounds `dm <= d <= dp`, with expanded endpoints `l <= p,x <= u`, the two affine
lines are

```
v + dp * (l - p) + dm * (x - l)
v + dm * (u - p) + dp * (x - u).
```

The differences between the true tangent and these lines are, respectively,
`(d-dm)*(x-l) + (dp-d)*(p-l)` and
`(dp-d)*(u-x) + (d-dm)*(u-p)`, both nonnegative. The Lean proof
`safe_anchor_cuts` proves precisely these comparisons before scaling them to
integer rows. It does not take the maximum of two raw derivative-endpoint
lines across the tangent point.

The direct-region rows pass exact `min/max` containment in the original convex
region and obtain their true tangent and packed value through the checked
541-entry catalog. The old-enabled rows instead obtain
`PointSoundness.old_tangent_value` for the original cell atom and its exact tight
interval. They check that the new closure interval is contained in that original
interval, then apply `oldTVal_reanchor_scaled`. This path requires the inherited
true `TVal` tangent; it does not assume that the complete original interval lies
in a single convex region. The offset, local span, term membership, enabled
point index, derivative bounds, and packed value are all connected to the
original frame in `addedCheck` and `added_tangent_cuts`.

The data comparison found 2,553 direct-region tangent rows and 402 old-enabled
rows. They use 541 and 97 distinct points, respectively, with 32 old-enabled
points outside the direct set, for 573 distinct points overall. All 2,955 rows
are accounted for; the 541-entry catalog is not claimed to contain every
old-enabled point.

## Positive multipliers, residuals, and the actual objective

The added branch multipliers are positive ordinary integers after the common
`10^10` rational denominator is paid, with the additional documented scale for
geometric rows. Every selected row is proved against `actualValue g`, including
the safe zero default in the generic row selector. The independent audit also
checks that every supplied positive row index is in range and that each integer
multiplier exactly equals the public rational multiplier times `10^10`.

The residual correction uses all 42 coordinates and its sign chooses the lower
or upper box endpoint. The eight gap coordinates use the new Floyd closure and
the separation bound; all 34 squared-kernel coordinates retain their full
`[0,1]` boxes. `SparseDualSoundness.threshold_sound` proves the list-fold integer
calculation bounds the actual real objective even with nonzero residuals.
`integerObjective_identity` identifies that objective with the actual
`scalarF9`, including coefficient `400000000` for the total-span `(0,8)` square.
No stationary-dual, zero-residual, or floating-point LP premise is used.

All 84 exact integer lower bounds agree with the public rational branch lowers.
The minimum over the replaced branches is
`1649885502177217292764764541 / 204800000000000000000000000000`.
Together with the 2,352 unchanged ordered pair domains, the frozen public
certificate's full-cover minimum is

```
263917374155379049835090394947 / 32768000000000000000000000000000
```

which is strictly greater than the required `805403 / 100000000`. The Lean
headline local proof needs only that required threshold. The actual canonical
representative/reflection routing used by Lean has the independently recomputed
minimum `32989671769422422666509432681 / 4096000000000000000000000000000`,
which is also strictly greater than that threshold. These are different exact
minimum values because the public computation separately optimized reflected
domains.

For the optimized kernel checks, 1,144 representatives use their primitive
boxes and 55 use the explicit path boxes. The independent audit also computes
the exact minimum paid by those checked boxes and the patched branches:
`32989671769422422651997857781 / 4096000000000000000000000000000`.
It remains strictly greater than the stated uniform threshold. None of these
auxiliary minima is substituted for the published headline constant.

## Representative routing and the final true counts

Of the 1,224 existing reflection representatives, 25 use a new patch and 1,199
retain an existing dual freshly checked at the stronger integer threshold.
`allRepRoutes` connects each selected patch to the actual original representative
packet. `allOldOrPatch` discharges every representative through that patch,
`strongBasicCheck`, or `strongPathCheck`; the weaker old c260 conclusion is not
used as evidence for the stronger threshold. There are 1,144 primitive-box
passes and 55 explicit path-box passes.

Each of the 55 `OldBox` records stores the 16 directed adjacent-gap bounds.
The even slot bounds `c -> c+1`, and the odd slot bounds `c+1 -> c`.
Consequently the actual gap box is
`[max(4*32768,-reverse bound), forward bound]`. All 880 path witnesses are
checked on the original primitive graph, in the correct upper-bound direction.
The path-based real soundness uses these bounds directly in the signed-residual
dual payment. A valid path does not imply that its stored bound is less than the
full Floyd closure, and the argument does not infer that inequality.

The independent audit separately confirms that the 55 stored boxes equal the
corresponding adjacent entries of the full closure for these frozen data, and
that their exact signed-box lower bounds equal the original full dual bounds.
The 55 indices are exactly the strong representatives whose primitive boxes
fail the new threshold; no other representative is omitted or substituted.
The independent audit additionally decodes all 1,224 actual old packed duals,
reconstructs their rows and signed-box lower bounds, and compares every exact
bound with the public payload. All 1,199 unpatched duals pass the new threshold.
The public computation assigns separately optimized duals to reflected pairs;
these need not have identical lower bounds. The formal proof consistently
transports the canonical representative's verified dual, and the independent
audit recomputes its actual lower bound for every one of the 2,399 routes.

`low_pair_bound` starts from the actual real two-frame potential.
`physical_pair_covered` considers all 482 × 482 ordered label pairs and returns a
member of the actual 2,399-pair packed table; excluded pairs are ruled out by
real-potential compatibility. Existing `orbit_coverage`, label injectivity,
cell reflection, and `reverseEight_scalar` then transport the correct
representative conclusion. Independent decoding confirmed all 2,399 orbit
codes against their actual packed label and representative tables.

`NinthSpanLocal.local_from_low_pairs` covers the exterior case using the exact
average of `805803/10^8` and `805003/10^8`, namely `805403/10^8`, and nonnegativity
of the total-span square. Its both-low case supplies the fully proved new
`low_pair_bound`. Consequently `NinthSpan.local_certificate` has only an arbitrary
real gap vector and its separation inequalities as inputs.

The final `simple_dyadic` and `simple_cumulative` statements use the actual
`Zeta23.N0simple` and `Zeta23.Ncount` definitions. They have no outstanding finite
certificate, geometry, numerical, or analytic hypothesis. The distinct-count
corollaries use the already proved simple-to-distinct inclusion. The new ratio
is `941021/1397107 = 66812491/99194597`; all old c260 theorems and historical
submission records remain separate.

## Reproduction and snapshot

Run the independent, exact data audit from this repository with:

```
python -B scripts/review_ninth_span_data.py --output verification/ninth-span-independent-data-audit.json
```

This review records the sources inspected at the timestamp in the accompanying
JSON receipt. A later source change requires a fresh source inspection and audit;
Lean and independent-kernel success must be read from their own final receipts.

Snapshot audited at `2026-10-10T04:31:33.848145+00:00`.

| Source | Actual SHA256 |
| --- | --- |
| `RecordProportion/NinthSpanFiniteData.lean` | `6dc433120474fd991cb6721cad05e69d45401a25002f8e3d021a7d04249d97ed` |
| `RecordProportion/NinthSpanFinite.lean` | `267080c98e4d5f35cf989f163cc2a672fbcaf352fc9ce4458dcb2be94602df73` |
| `RecordProportion/NinthSpanPoints.lean` | `084d4518eb4a8b7039903f5616d92c378a4c739c79e97ff9eb94aa89d4406256` |
| `RecordProportion/NinthSpanLocal.lean` | `23d5674bfdc4b4b98b6e457340c062a5084913e842d70308f14aab5c9fe6b388` |
| `RecordProportion/NinthSpan.lean` | `71ee98aee541c2523d6383c22fab2940544c8fe439bb2992723a7438a91d5f68` |
| `RecordProportion/NinthSpanAnalytic.lean` | `9809646e5d52c103c92e0edec7d8bc514049565497fce61eb8e690c1218f138e` |
| `RecordProportion/NinthSpanPathSoundness.lean` | `f31dae379c2200807ec392dfd7bf91d6375bd09a269cee78a676a54ac107bf8d` |
| `RecordProportion/FiniteCertificateData.lean` | `0b12cba764e62ac55f1d7acdebc6c86cf1a26253ccb31939519b983f01b1bc59` |
| `RecordProportion/FiniteCertificate.lean` | `6c6cb5dc10588e430c28118107ad66e1da93dcd0b0e62bd579fcc92a3f078cb5` |
| `scripts/generate_ninth_span_certificate.py` | `f1cc82375f1f99ca1bf60b96e5eaf14cc7d09ec38dedf33003700ec0f41d8b18` |
| `output/am-ninth-span-certificate.json` | `9fc7f9d8a00ebbc3e2f8ff236b247af5ac3173c3942ec72b9180c4473a65cf96` |
| `output/am-ninth-span-point-catalog.json` | `cda8ce5fce3d0a639975f54e57b1991c7d5a2a2cb112df4e3dd13237a954fb27` |
| `output/am-expanded-nine-point-certificate.json` | `45fa9a71c1aa87296ac3cdb5b260c32d1ffe22d2b36b979d58b9cbf16c754c33` |
| `scripts/review_ninth_span_data.py` | `8ce60e6a7e1d78ff7d20c2e55a8d8140528ac48dd97b7e74a569d8adf5104d00` |
