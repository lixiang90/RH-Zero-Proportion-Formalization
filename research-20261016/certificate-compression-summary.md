# Fixed overlap candidate: certificate size and remaining Lean work

This is a research summary. The new local energy inequality and improved
numerical zero proportion have **not** yet been proved in Lean. The frozen
published proof remains unchanged.

The fixed potential is `overlap_rational_candidate.json`: ten nonzero binary
affine rows, zero extension when a state contains a gap above 2.5, plus seventeen
nonzero ternary state constants. Its proposed local floor is `4299/500000`.
`PotentialRange.lean` proves its range on every gap vector with gaps at least
`17/20`, including arbitrarily large gaps:

```
-133/100000 <= V(g) <= 143/100000
V(g) - V(h) <= 69/25000
```

Ordinary Lean and axiom checks passed for the canonical source
`StructuralResearch20261016/PotentialRange.lean` (SHA256
`109e8d57bd5cb459d34cbed028dc770b9960cbfcc8f9f0bcbc8d32ef1d226716`).
Its two exported range roots use only `propext`, `Classical.choice`, `Quot.sound`.
The generator is `generate_potential_range.py`; the source/olean receipt is
`potential-range-canonical-compile.json`.

The inherited 48 geometric trees contain 10,937 numerical leaves. Including
reflected cells gives 21,874 leaves. Intersecting their gap boxes with the
three classes and the separation condition produces:

| Check | Count |
|---|---:|
| Cartesian ternary subboxes | 936,274 |
| Feasible subboxes after all pair constraints | 667,410 |
| Infeasible subboxes | 268,864 |
| Cheap independent-gap affine bound already passes | 923,670 |
| Need flow or an infeasibility certificate after that cheap bound | 12,604 |
| Need additional tangent mixtures after the exact inherited affine/flow bound | 8,004 |

The 923,670 cheap passes can include infeasible cells; their affine lower bound
is nevertheless valid and needs no separate feasibility test. Thus a final
checker should try this inexpensive path first and store exceptional flow or
tangent data for at most 12,604 subboxes. It should not store a separate flow
for every one of the 667,410 feasible subboxes.

`probe_certificate_compression.py` reproduces the cheap-bound counts. Its full
3,301,835-byte output list has SHA256
`af48fec67f6b7872c6403063934819206abfe9e7ca904b23de90372feaaa7357`.
The list need not be committed if the script and this hash are retained.
The two `tangent-envelope-part*.json` exploratory runs close all 8,004 remaining
boxes using inherited TVal points, rational mixtures and exact integer flow;
those arithmetic runs are not substitutes for the pending Lean instance.

The canonical `StructuralResearch20261016/GenericCover.lean` passed ordinary
Lean and axiom checks (SHA256
`50cea1df4eacda7dd0a56f5bba925c4fde0deaca4fa31290583c3153d6b19e16`).
It reuses the frozen state, closures, splits, and bit geometry. Its arbitrary
leaf callback must prove `CovK P (leaf pos)`, and `covered_of_walk` then proves
coverage for any target `P`. Its reflection interface explicitly retains both
potential orientations, so the inherited reversal pruning cannot silently
drop the asymmetric potential case. These are generic coverage theorems;
they assert no new energy floor.

The shortest complete instance still needs these concrete links:

1. Bind each leaf callback to its actual root/tree position, state bounds,
   original bitstream and pointer endpoint. A valid certificate for another
   cell must not pass this binding check.
2. Prove the complete inherited affine minorant before its old gapwise minimum
   is discarded. Then prove the cheap exact box check for the chosen ternary
   state and its reflected energy orientation.
3. For exceptional cells, instantiate `TangentSupport` with original `ptS` and
   `pwD`-decoded validity intervals, and instantiate `AffineFlow` with checked
   nonnegative rational mixtures and balanced nonnegative flows. The SciPy
   discovery solve must remain outside the proof.
4. Prove the ternary partition, separated root coverage, and the good-gap
   complement. The old checked cover floor plus the other seven gap pressures
   and the new `69/25000` oscillation already exceeds the target, so no sharper
   cover constant is required. A gap at least 40 is closed by pressure and the
   same potential range.
5. Run the 48 generic walkers with the concrete leaf callback and checked
   endpoints, eliminate the reflection clause, and derive the global local
   inequality. Only then instantiate the existing new coboundary counting
   bridge and perform full kernel/axiom verification of the numerical theorem.

