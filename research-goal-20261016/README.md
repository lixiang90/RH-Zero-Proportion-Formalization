# Research continuation: actual new window and minimizer coverage

No new unconditional zero proportion is asserted by this directory.

The primary candidate changes the Fourier profile to 24 rational cosine
modes and changes the pair ledger. It is not a tightening of the old numerical
constant. Its frozen parameters are in
`research-20261016-followup/window_reweight_rational.json`.

The target floor is 221/25000. A backup floor of 11/1250 still gives a
conditional proportion of 67.36017669582563%, exceeding the recorded website
proportion by more than 1/100000 in absolute proportion. Both require an
actual global floor and the complete analytic/counting and validation chain.

## Current mathematical change

The pressure-plus-energy functional is coercive on the separated orthant.
Its global minimum therefore exists. A cover need only retain every possible
global minimizer. A strictly negative derivative in a feasible direction
excludes a cell without proving a pointwise energy bound there.

The first coordinate-wise test was ineffective. Independent ranges also lose
the cancellation of a long-span derivative shared by several coordinates.
The new method keeps the common nine gap variables in the affine Taylor
parts of all span derivatives and maximizes their sum by exact integer flow.
Floating LP chooses a direction; it never certifies a negative bound.

On a frozen prefix of 10,000 nodes, the complete scalar derivative-grid test
excluded 1,109 cells. The correlated method found 1,612 additional exclusions,
covering 396 original branch nodes. All 1,612 certificates passed a separate
standard-library replay of scalar Taylor errors, feasible directions and
flow balance/cost. This is finite numerical evidence, not a global theorem.

The next structural improvement uses the sublevel condition `F < c`. For
each span separately, an epigraph LP selects a capacity-valid affine energy
minorant `A <= F`. A nonnegative rational multiplier and integer flow bound
`z + lambda*A` or `-z + lambda*A`; hence `F < c` gives a new lower or upper
bound on that span. Distinct spans can use distinct mixtures. The contracted
cell only needs to preserve potential counterexample minimizers. It is not
presented as a pointwise cover of the original cell.

In a fixed 1,000-parent sample, 191 cells were already excluded by the first
direction test. Of the remaining 809, the epigraph method contracted 806,
and then closed 506 (472 new directions and 34 value bounds). Independent
replay checked all 12,180 span bounds, including mixtures, capacities,
multipliers, flow and outward rounding. These are sample results; they do
not prove a full cover. A new full search starts from the root, rather than
retaining the large prefix of the older search.

For the 472 immediately direction-excluded sample cells, independent replay
also permits removal of unnecessary contraction bounds: 7,903 bounds reduce
to 2,258 while preserving all 472 exclusions. This simplification cannot be
applied to a branch or to a later Newton leaf without rechecking the affected
subtree or contraction chain.

The new edge-forest flow representation stores only directed edges. The
surrounding checker recomputes the divergence and edge costs; leaf elimination
reconstructs the integer amounts. All 24,866 flows in the original 806-path
sample were reconstructed exactly. `AffineFlowCertificate` and
`FlowBasisCodec` have ordinary-kernel proofs: the decoder is untrusted and
the final Boolean checker verifies nonnegativity, balance and cost. No
decoder correctness or optimizer optimality is a premise.

The pruned sample with this representation occupies 1,511,223 gzip bytes.
This is not a pass of the website's 2,000,000-byte **Lean source** limit and
does not cover the full domain. The standalone archive replay reconstructs
the witness cells from the root/ancestor projection, independently checks
the mathematical certificates, and recovers the original proof SHA.

A separate nine-point alternative jointly redesigns the same 24-mode
profile and its ledger, reducing the number of gap variables to eight. Its
frozen rational parameters in `window-nine-point-rational.json` would give
67.35935579342542% if the floor 433/50000 were proved. The exact capacity,
profile-budget and conditional comparison checks passed. The tested point
energy is an upper bound on the infimum, not a proof of that floor. This
alternative does not replace the primary ten-point parameters.

## Reproducible entry points

- `window_interval_kernel.py`: rational enclosures for the actual new kernel
  and its derivatives, and 16 local convexity certificates. The generic
  derivative/Taylor connection in Lean is a separate obligation.
- `window_jet_crosscheck.py`: a 100-digit diagnostic against independently
  differentiated shifted sinc functions, including removable poles.
- `cover_newjet.py`: a complete [0,32] derivative grid from 33 integer-centred
  order-23 jets and the order-24 Taylor remainder.
- `cover_correlated_api.py`: the stable direction-discovery API.
- `cover_correlated_verify.py`: independent standard-library verification API.
- `window_global_cover.py`: the primary 221/25000 value-cover discovery.
- `window_minimizer_cover.py`: the backup 11/1250 minimizer-cover discovery.
- `window_correlated_minimizer_cover.py`: the correlated continuation, frozen
  reproducibly by `window_make_correlated_variant.py`.
- `window_cover_replay.py`: exact geometry, capacity, value-flow and directional
  replay for mixed covers; it does not trust the LP status or floating objective.
- `cover_sublevel_obbt_api.py`, `cover_sublevel_obbt_verify_api.py`: explicit
  target discovery and independent replay for the per-span sublevel contraction.
- `cover_flow_basis.py`, `cover_flow_basis_archive_replay.py`: edge-only flow
  decoding, exact arithmetic replay and recovery of the original proof bytes.
- `window_normalized_interval.py`: the factorial-normalized sinc recurrence
  on a fixed rational grid. Its numerical audit preserves all 16 original
  curvature constants and 2,829 scalar minorants. The separate grid audit
  distinguishes the separated domain from unused near-zero grid cells.
- `window_nine_point_rationalize.py`: exact rational audit of the smaller
  alternative, explicitly retaining its unproved global floor.
- `lean_generate.py`, `lean_verify.py`: resumable ordinary-kernel verification
  of the complete old-window fallback. A list of generated parts is not evidence
  that those parts passed.

The large evolving search checkpoints are local working data. A frozen
checkpoint must be archived with its hash before an audit is used as a durable
receipt. Completed proofs require current source hashes, ordinary Lean, the
website's independent kernel check, theorem comparison, and the source-size
limit. Generated or failed sources must not be described as verified.

## Lean status

The sealed receipt `ordinary-verified-current.json` records the modules with
current ordinary-kernel passes. They now include the actual kernel and
energy identities, the actual high derivative and Taylor chain, the
separated spectral/counting connection, ordered minimum existence, the
counterexample-minimizer cover bridge, and sublevel/Newton contraction
lemmas. `WindowGramBasins` proves 69 rational quadratic bounds; its scalar
connection and global coverage remain distinct obligations. Their printed
axioms are limited to `propext`, `Classical.choice`, and `Quot.sound`. These
are checked with source/log hashes; a frozen full-name audit disambiguates
scope-dependent printed names. The first actual finite table pilot proves
all 24 E coefficients and the first full base recurrence using kernel
evaluation and the soundness theorem. Compiled table definitions alone are
recorded separately and are not counted as interval-enclosure proofs.
The full finite tables, actual scalar bounds and complete global cover
remain unfinished. Consult hash-bound receipts;
source existence alone does not establish a theorem. No new independent
nanoda replay has yet been run for these modules.

The frozen mixed-cover snapshot `snapshots/correlated-26000.json` describes
an archived checkpoint of 26,000 checked nodes with 17 frontier cells. Its
mixed replay passed for 10,674 value leaves, 1,788 directional exclusions and
530 reflection exclusions. The snapshot receipt and replay both retain the
explicit incomplete/conditional status.

The first 612-leaf old-window block was deliberately stopped after actual
memory pressure; it was not passed. The later monolithic geometry module
terminated with recursion-depth errors and was not passed. Smaller independent
blocks and declarations are used to preserve real checkpoints. These execution
issues do not establish or refute the mathematical floor.
