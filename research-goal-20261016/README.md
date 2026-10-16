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
All 32 actual integer-centred kernel/derivative tables and all 1,567 actual
value/slope anchors now have ordinary-kernel proofs, as does the actual
short-pair bound. All 128 convex subintervals in the 16 required wells,
their combined actual convexity theorem, and the scalar-to-actual-kernel
bridge have now passed the ordinary kernel. All 69 actual coherent basins
have passed through a shared rational/diagonal certificate. The full
minimizer cover remains unfinished.
`WindowRecordFromFloor` and `WindowRecordDyadic` reduce the actual cumulative
and dyadic counting conclusions to an explicit global floor hypothesis.
That hypothesis remains a mathematical obligation.

`WindowPressureRoot` retains the full shared pressure budget when bounding
a span, rather than inferring those coupled bounds from independent
coordinate bounds. `DifferenceCell` proves single-edge closure and split
soundness for actual real positions. These are interfaces for an eventual
complete checked cover, not substitutes for that cover.
Consult hash-bound receipts; source existence alone does not establish a
theorem. A selected independent replay has now passed both Lean's default
kernel and nanoda: 22 partial roots, 73,398 declarations, and exactly the
three allowed axioms. All 472 bound inputs were rehashed after verification.
The frozen evidence is in `window-independent-20261017/`; the large export
is represented by its SHA and byte count rather than copied into Git.
The selected roots cover all actual centre tables and anchors, one actual
convex interval, the short-pair bound, pressure/KKT/flow tools, and counting
implications with their explicit energy-floor input. This is a self-replay
of those selected roots, not a website-statement comparison or a global
floor proof. Per-module receipts do not assert independent replay of every
declaration in every ordinary-passed module.

The full 22,500-node OBBT prefix was recovered into the compact representation
and independently replayed: 164,093 contraction bounds, 17,785 Newton steps,
and all accepted leaves passed. The recovered checkpoint shrank from
882,186,203 to 147,894,201 bytes. Its frontier is nonempty. The small frozen
600-node archive also replays without the original checkpoint; the immutable
`cover-compact-progress-files.json` pins all selected recovery artifacts.

Further mathematical diagnostics are explicitly negative evidence rather
than proofs: adjacent-term localization does not force all coordinates into
integer wells; truncating interactions at range six, even after reoptimizing
the ledger on the fixed profile, falls short of the requested gain in sampled
LP diagnostics. Finite integer moves to competing wells are a distinct
global-minimizer exclusion currently under investigation.

The first signed-curvature global-competitor sample is now independently
replayed. A feasible integer vector sends every gap vector in a cell to
another point in the original orthant. If the entire cell satisfies
`F(g+delta)-F(g)<0`, it cannot contain a global minimizer, even if it contains
local stationary points. For each affected span, the checker subtracts the
same-phase Taylor coefficients before bounding the difference kernel
`h_s(x)=w(x+s)-w(x)`. An upper bound on the signed `h_s''` suffices; concave
intervals need no absolute-curvature remainder penalty. Exact integer flow
bounds the correlated sum over all nine gaps.

This test newly excludes 15 of the fixed 300 OBBT/Newton residual sample
cells, distinct from the previous seven joint energy-gradient sample leaves.
All preceding 193 OBBT bounds and 53 Newton steps, scalar difference bounds,
and final flow certificates were independently replayed. The standalone
72,868-byte gzip archive reconstructs the ancestor geometry and covers 141
old descendant branches; it does not cover the full domain.
A further sublevel-conditioned test checks
`DeltaF + lambda*(c-A) < 0`, with `A <= F < c` and `lambda >= 0`, and finds
nine additional replayed exclusions after skipping all 15 known moves.
Six of these certificates have positive energy multipliers. Replay checks
their preceding 102 OBBT bounds and 30 Newton steps, and the separate
48,466-byte gzip archive reconstructs their geometry without the large
source checkpoint. The two batches are topmost disjoint regions, together
covering 251 old descendant branches; both are distinct from the previous
seven joint gradient sample leaves. Formal actual finite-move consumers are
now ordinary-kernel verified, including actual energy differences,
signed-curvature scalar bounds and sublevel objective payment. The frozen
numerical witnesses still need concrete Lean instantiation; these numerical
receipts are not Lean passes.

A direct positive combination of multiple moves found no new separation in
the fixed 100-cell portfolio pilot. This negative evidence motivates using
the valid inequalities `U_v >= DeltaF_v >= 0` as cuts in contraction, rather
than blindly increasing the size of the direct separation trial.

Using those global-competitor inequalities as contraction cuts does yield
new exact certificates. In the first 50 genuinely residual parents, 17 paths
contracted through 24 rounds and 149 new coordinate bounds; eight resulting
directional exclusions passed independent replay, including their prior
262 OBBT bounds and 65 Newton steps. These eight regions have no ancestor or
descendant overlap with the earlier 24 and cover another 55 old branches.
The cuts preserve original global minima below the target, not all KKT
points. The small frozen package remains dependent on the previously
published OBBT archive and is not described as standalone geometry.

A paired discovery control reapplied energy-only OBBT for the same two
rounds at the same 17 starting cells. It classified three terminal leaves,
with only one shared success, suggesting seven exclusions attributable to
the global cuts in this sample. Those control terminal classifications are
diagnostic; the independently verified claim is the eight cut certificates.
Energy-only contraction had a smaller median box-volume ratio, so global
cuts are not claimed to dominate it on every metric. A separate variant
will retain both kinds of bounds instead of dropping energy-only bounds.

The subsequent inclusive and signed-difference-hypograph cuts have
complementary successes. Their union with the first cut trial closes 15
regions; intersecting both valid hulls and applying Newton adds four.
The standalone 211,364-byte gzip in `cover-global-cut-union-evidence/`
independently reconstructs 184 ancestor nodes and all 19 closing chains,
including 277 prior OBBT bounds, 89 prior Newton steps, 391 cut bounds and
16 extra Newton steps selected for this projection. These 19 and the prior
24 finite-move regions are mutually nonnested: 43 topmost regions, covering
558 old descendant branch records. This is a partial c=0.00884 sample,
distinct from the running c=0.0088 full search. The immutable file manifest
is `cover-global-cut-union-files.json`.

The actual dynamic LP support consumer now has an ordinary-kernel proof,
including convex-core tangents and their valid zero extensions. The actual
k/k' Horner point intervals and the whole-cell k-based constant lower
support also passed. Directional affine aggregation, Newton retention,
signed difference upper bounds and the cross-grid range consumer passed.
`WindowScalarLine` dispatches actual zero/tangent/constant supports and
supplies the value-flow scalar premise; all eight concrete scalar pilots
passed. `WindowValueSublevel` checks the actual sublevel objective bound
from these scalar checks, capacities, augmented integer flow and rounding.
Neither theorem assumes an externally asserted analytic minorant.
All 1,987 separated grid cells (indices 61 through 2047), their combined
range theorem and the actual derivative oracle now have ordinary-kernel
proofs. Actual integer directional and dual-flow Newton aggregate
consumers also passed. Full tree instantiation remains an obligation,
recorded alongside per-module verification in
`ordinary-verified-current.json`; source presence alone is not a pass.
`WindowBasinCell` now checks the 41 rational cell-span containment conditions
and supplies the actual basin region automatically, yielding the local
0.00884 (and weaker 0.0088) floor without an external region premise.

Targeted diagnostics explain why the remaining search is difficult. Deep
frontier cells are outside all 69 currently registered basin regions;
nearby unconstrained stationary points lie outside those cells. Their
independent scalar derivative intervals admit correlated false candidates.
Integer translations and feasible affine reflections found no strict
whole-cell exclusion on the current coarse sample, despite midpoint hints.
These are research diagnostics, not impossibility or record claims.

Targeting those six identified cells, second-order necessity gives three
whole-cell negative-curvature certificates with independently replayed
ancestor geometry: 28 reconstructed nodes, 178 unique prior OBBT bounds
and zero prior Newton steps. Two of the three tested first-order affine
upper bounds remain positive. `WindowCurvatureAffine` has an ordinary
kernel proof of the actual 41-edge second-variation identity and correlated
affine upper aggregation. Its selected actual scalar bounds and concrete
integer witnesses have now passed the ordinary kernel, as detailed below. The small frozen
`cover-targeted-curvature-files.json` package also records the unsuccessful
quadratic-gradient trial. These three c=0.0088 cells cannot be added to the
43 c=0.00884 sample regions. The running cover already closes the first
targeted path by its older contraction process, so a branch-count reduction
from the new curvature alternative has not yet been demonstrated.
The integer curvature aggregate and negative-flow consumer in
`WindowCurvatureFlow` also passed the ordinary kernel; the actual scalar
second-derivative feed is verified separately from that aggregate theorem.

The selected actual second-derivative feed has now been instantiated in Lean.
All three concrete curvature leaves passed, using 331 selected second/fourth
derivative grid cells, actual point jets, feasible interior-supported
directions and strict integer-flow inequalities. The 24 actual OBBT bounds
connecting their local common-ancestor subtree also passed, as did the finite
matrix-closure and split geometry checks. `WindowCurvatureSubtree` has also
passed: the local tree's complete Boolean check is proved true, and its
exclusion theorem has only relevance and membership in the local ancestor
cell as hypotheses. This removes numeric
scalar premises for these leaves; it does not connect the local ancestor
to a complete pressure-root cover.

## Multi-facet derivative-graph improvement

The new method lifts each actual scalar value
`u_e = w'(span_e(g))` and keeps the shared nine gap coordinates `g`.
Several affine supporting inequalities for each graph replace the loss of
shape information in a single symmetric affine slab. They are valid over
the entire current span interval, checked cell by cell on the existing
derivative grid. The old slab inequalities remain available. Genuine
orthant KKT equations apply only at strictly interior coordinates; boundary
coordinates retain the one-sided gradient inequality.

On the same fixed 64 difficult depth-24 parent cells, the old single-slab
KKT relaxation produced no strict certificate. The graph relaxation gave
13 strict integer Farkas/flow certificates, including the four positive
cases of the initial eight-parent pilot. They are thirteen regions, not
seventeen. Independent standalone replay reconstructs 153 ancestor nodes,
1,209 prior OBBT bounds and three prior Newton steps, and independently
recomputes 741 used derivative grid cells from rational jets. The archive
also checks thirteen nonclosing old controls. The 13 excluded parent cells
have 27 branch records and 40 accepted leaves below them in the frozen
source projection. A separate exact replacement replay now verifies every
old node and every new graph leaf in these thirteen complete local subtrees,
including all 422 old contraction bounds and 69 Newton steps. The local
forest reduces from 67 nodes to 13 graph leaves, with its gzip payload
falling from 98,724 to 31,947 bytes (67.6%). This is a measured local
certificate reduction, not a speedup or completed proof for the global
search. `cover-lifted-graph-replacement-files.json` binds the independent
standard-library-only replay and both complete local forests.

The exact inequality combines nonnegative integer row weights. Residual
coefficients of the `u_e` variables need not cancel: their absolute sum is
paid with the proved global `|w'| <= 7` bound. A checked edge-forest flow
then gives a strict integer contradiction on the shared gap polytope.
`WindowLiftedFarkas` has passed ordinary Lean for this aggregation and
payment. `WindowDerivativeGraph` and `WindowLiftedKKT` have also passed:
their actual grid facets, slab bounds, DBM rows and original-orthant KKT
rows discharge the analytic row-validity premises. The concrete
`WindowLiftedPilot` has also passed ordinary Lean: all 43 rows, ten actual
slabs, 22 facets over 623 grid cells, all aggregate coefficients and the
strict residual-paid flow bound are checked. Its local exclusion theorem
retains only relevance and cell membership, with no numeric oracle premise.
Current source and log hashes are bound in `ordinary-verified-current.json`.
The immutable numerical manifests deliberately retain the scope
at the time they were frozen:
`cover-lifted-graph8-files.json` and `cover-lifted-graph64-files.json`.

An energy-epigraph extension on the first eight remaining cells produced
no further strict certificate and was stopped without expanding the sample.
The successful graph method has not changed the live full-cover runner.
Its stable API reproduces all thirteen certificates on the frozen cohort.
The minimal 516,598-byte discovery input and a recomputation driver that
writes to a new output directory are pinned by
`cover-lifted-graph-discovery-input-files.json`, so the fixed-cohort
experiment can be repeated without the evolving large search checkpoint.
`WindowGraphCover` also has an ordinary-kernel proof connecting checked
graph leaves, the existing leaves and contractions, and the actual counting
chain. Its hypothesis is still the complete tree check at the pressure
root; no such complete check is asserted here.
An additional fixed eight-parent test uses a one-level disjunction chosen
from the graph relaxation's inconsistent scalar value. One new parent is
excluded by two strict child certificates, with independently reconstructed
split geometry and scalar/flow checks. It is disjoint from the thirteen
direct graph exclusions, giving fourteen parent regions: thirteen direct
leaves and one split with two leaves. The additional parent has not yet
been instantiated in Lean. `cover-lifted-disjunction-files.json` pins its
23,051-byte standalone archive and the full small experiment. Neither the
old single-slab test on that same split nor the old split rule with graph
leaves closed both children in the paired diagnostic. No second-level or
whole-domain job was started for this experiment.
This is a substantive new exclusion criterion, still local progress toward
an unproved global floor and no new unconditional zero-proportion record.

The separate future phase route is audited in
`window_phase_hermitian_audit.txt`: the actual 24-mode kernel admits a smooth
positive-domain decomposition into a perturbation amplitude and first
phase harmonics, and its square uses first and second phase layers. Forty
point checks and the full actual 41-edge Hermitian identity diagnostic are
consistent. This is an identity audit, not a uniform bound or Lean proof.
`cover-phase-psd-files.json` freezes an independent challenge: two independent
phase layers can lose square positivity, and the weak frozen-amplitude value
proxy does not improve the earlier bound on seven of eight tested cells.
The linked model retaining the old gap/derivative graph, actual phase arcs,
KKT and cross-layer moment constraints remains untested. The note specifies
a concrete next test using rational rank-one PSD cuts in the existing LP
solver. No strict phase certificate, global floor or new proportion is
asserted by these research notes.

Independent three-floor probes on the same 300 original parents found
80/81/80 remaining branches for `c=0.00884/0.0088/0.008785`, respectively.
The small nonmonotonicity is due to heuristic certificate choices. Compact
sample payloads fell only about 4.1%/4.5% at the lower floors. This is useful
complexity evidence, not an impossibility theorem. The single active compact
full-cover search uses `c=0.0088`, whose conditional score still meets the
requested improvement margin.

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
