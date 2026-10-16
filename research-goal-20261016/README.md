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
current ordinary-kernel passes. These include `LeanCoverBase`, `WindowEnergy`,
`WindowKernel`, `WindowEnergyBound`, `WindowProfile`, `WindowRealization`,
and `CoverCoerciveKKT`. Their printed
axioms are limited to `propext`, `Classical.choice`, and `Quot.sound`. These
include the actual new integral energy identity and rational energy bound,
the actual kernel formula, and genuine existence of a global minimum with
the boundary/interior KKT conditions. The actual derivative, Taylor and
counting connections are still being checked. Consult hash-bound receipts;
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
