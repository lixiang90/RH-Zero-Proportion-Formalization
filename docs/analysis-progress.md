# Analytic bridge to the c260 submission

The target remains 66812491 / 99194740. The challenge requires both dyadic and
cumulative distinct critical-line counts divided by the count of all zeros
with multiplicity. A simple critical-line lower bound can feed these two
statements through the proved inclusion of simple in distinct zeros.
A cumulative estimate alone does not supply a dyadic estimate.

## Fixed source and the shortest bridge

The original AM source is the fixed RH-Weil tmp/pc8-am-admission/Solution.lean
(19,049 lines; raw SHA256
012c6ac5f9282158a686500dc0c967bf0a9b00e1a6192734d8f237bb23dd2d5f).
RecordProportion/ImportedAM.lean is a standalone copy within this repository.
Only the old candidate-dependent assemblies were removed. The full original
AM window, PC8 certificate, multiplicity-aware seam and tail proofs remain.
Their written code still needs compilation with the challenge's pinned tools.

| Original declaration | Original line | Exact role |
|---|---:|---|
| AMW.phiW_sq_eq | 307 | AM13 squared window, taper and MAM=5/4 |
| AMW.HW_eq, AMW.HW_ge | 1601, 1746 | AM energy and HW >= 67216841/10^8 |
| AMW.eventually_tailPackageAM | 3078 | Complete actual-window tail inputs |
| StableRankTrace.stable_rank_trace | 3400 | Spectral defect retained in inertia bound |
| Bridge.count_defect | 4641 | Entire zero block, repeated and off-line zeros included |
| Bridge.tail_passage | 4664 | (HW-epsilon)N + Dcirc <= N0simple |
| Bridge.kernel_limit | 4707 | Realized finite AM Gram approaches the AM kernel |
| Bridge.deleted_strips | 4739 | Retained simple zeros differ by o(N) |
| Bridge.pinching_partition | 4958 | Convex spectral defect of the full partition |
| Bridge.span_retained_le | 5028 | Actual normalized span <= (1+epsilon)N |
| Bridge.eventually_h7 | 5112 | Defect-bearing original zero-side seam |
| BridgeW.window_pairs_le_energy_w | 5196 | Sparse sliding windows, span capacity <= two |
| AMW.N0simple_le_N0star' | 5985 | Genuine final counting inclusion |

All Bridge names above belong to Zeta23Ext. The defect uses
Psi(t) = (t-1)^2 for t <= 2 and 2t-3 otherwise. If phi2 is t^2 below two and
4t-4 above, Psi = phi2-2t+1 exactly. This allows the new lossless reward to
enter the original seam directly, without the old block-size/square-root ratio.

## New obligations and exact interfaces

1. Prove the new nine-point certificate for every real gap vector with all
   gaps at least 4/5. A JSON or successful program run is not a Lean theorem.
   The low-cover guards, 241 leaves, reflected halfspaces, 2,399 full closure
   intersections and exact box residual corrections require kernel soundness.
2. Lift the new frame to the original sparse sliding-window theorem. Its
   span budget is at most two; the missing eight windows cost 8*c260.
3. Bound the actual separated AM Gram operator below two. The majorant mass
   61/32 is below two, but the actual taper normalizer must be paid.
   The multiplier is aInf/a_T, not the external paper's 2/(5*a_T).
   Choosing a_T/aInf > 61/64 eventually suffices.
4. Partition retained simple zeros into close pairs and a 4/5-separated
   remainder. Combine block rewards using Psi convex pinching.
5. Prove the exact missing estimate for every d>0, eventually:
   Dcirc >= c260*N0simple - B*Ncount - d*Ncount,
   where B=404350/10^8. The endpoint, deleted strips, Gram approximation and
   normalized span errors must all be absorbed here.
6. Apply the existing AM tail_passage, then simple <= distinct, then the
   upstream cumulative_of_dyadic theorem.

For a near pair the existing block_defect_of_isHermitian gives
min(1, offDiagSq) <= defect. The continuous near bound now written in AnalyticBridge is
K_AM >= 51/550 for |x|<=4/5. Its square exceeds c260 by the exact
margin 330177/605000000, and supplies the pair reward including tolerance.
For the separated remainder, a spectral bound <=2 implies
defect = frobSq(G-I) >= offDiagSq, with no clipping loss.

AnalyticBridge now has written proofs of the real-quadratic-form eigenvalue
bound, this unclipped separated estimate, the min-one near reward, finite
partition pinching, and the actual AM simple/distinct dyadic/cumulative
endgame conditional on the displayed missing defect estimate.
These are explicit mathematical hypotheses, not new axioms or a certified
challenge solution. Compilation and axiom audits are still pending hydration.

The new sparse-window proof also admits a genuine two-index, nonstationary
energy E(i,j). It retains the old span-capacity calculation but no longer
assumes entries depend only on a point difference. Summing actual frame
inequalities costs one frame error per point and the full endpoint 8*c260.
The kernel-to-frame helper pays two times the Gram tolerance times the exact
pair mass. It never replaces this sparse error by the number of all pairs.

## External constants that must not be silently reused

The external Simple673 code uses another window, separation 17/20, reward
.008722, pressure .004389, norm 19/10 and ratio 1669159/2478195. These cannot
be renamed to the AM constants without proving the relevant hypotheses.
In particular 19/10 is less than the AM majorant bound 61/32.
The real/imaginary eigenvector argument is reused with parameters explicit.
The generic Fourier/Poisson portions may be reused after separating their
parameters from those numerical instances.

High owns the finite dual/data layer; Checkpoint owns the continuous AM
majorant and Fourier layer. This file records the analytic assembly only.
All new code resides in this separate repository. No record claim follows
until the three exact challenge declarations compile and their transitive
axioms pass the prescribed checker.

## Current complete analytic assembly, still awaiting compilation

The bridge now explicitly proves (in source, not yet compiled) the complete
nine-point-certificate to lossless-defect estimate and exposes
am_distinct_dyadic_of_nine_point_certificate and
am_distinct_cumulative_of_nine_point_certificate. Their inputs are exactly a
WCert 9 with admissibility, total pressure 404350/10^8, pair mass at most 16,
and the finite local reward 805260/10^8 on all gaps at least 4/5. High owns the
kernel-checked finite proof of these hypotheses.

The original gram_close_of is uniform over every retained pair, with error
10*K/L^4+12*w/L. The old kernel_limit proof never uses its R0 or distance
premise. eventually_am_all_entries_close copies that proof without the
unused premise; this is reuse of an existing analytic estimate, not a new
zero-density or zero-free result. Consequently unbounded gaps require no
new cutoff or missing far-pair premise. Only the sparse nine-point pair mass
is charged: 32*eta per frame, rather than eta times all pairs.

The retained estimate is
(c260-32*eta)*cardRetained - B*actualSpan - 8*c260 <= Dcirc.
The close matching preserves all original points. Each separated remainder
uses its actual principal Gram matrix and the actual AM Fourier transform.
Convex Psi pinching combines the pair and separated rewards. The final
transport uses deleted_strips, span_retained_le, the original trivial_chain
N0simple<=Ncount, and tendsto_N_atTop; all endpoint errors are absorbed
before passing to the exact dyadic and cumulative contract.

The sinc near proof uses the all-real alternating degree-ten Taylor lower
polynomial and six positive Bernstein coefficients on
v=(pi*x)^2 in [0,158/25]. The integral inequality is
rawK >= sinc(pi*x)+Z-1-13/200, with Z>=11/12. No sampling, imported headline
axiom or unproved covariance theorem is involved.

## Imported-source pruning provenance

The full pre-pruning local import remains in ignored
tmp/imported-am-full-before-pruning.lean:
19016 lines, 1674316 LF bytes, SHA256
80f3fe1d9d2bc9d53d9f7ea4e78c724e0242da6cd0ba6669782c5645363657b7.
Its original upstream Solution input was
012c6ac5f9282158a686500dc0c967bf0a9b00e1a6192734d8f237bb23dd2d5f.

The deterministic pruning deletes full-local lines 5195--7189 (obsolete
block/window-count, tau, band-profile and square-root assemblies), reinserts
only the exact N0simple_le_N0star' proof, and removes Aeff_W8 through the old
literal terminal record. It preserves the complete original all-zero tail
through full-local line 5144 and all typed ST/split, PT/PTF/REG, interval,
PC8 core and coverage/data declarations. The pruned source is
16980 lines, 1567168 LF bytes, SHA256
1f85df6a76e6a3f515202b51c039883487d95b68b1597c62bcfaff64cfee62dd.

The root will compress long hexadecimal Nat syntax in the final single-file
bundle using a pure macro, with exact-value replay and another compiler/
axiom audit. That submission-only transformation is separate from these
analytic source proofs.

The second pruning pass removes 114 unannotated, nonrecursive declaration
leaves whose names have no textual consumer in any current RecordProportion
module, recursively after each removal. High explicitly requested that
PC8CL_cert_full and PC8CL_G_rev be pinned; both and every shared dependency
remain. No original declaration before full-local line 5144 is changed.
Attributes, implicit instance declarations, section/namespace commands,
entity tables, ST/split/walk and all referenced PCell/PyrD proofs remain.

This removes a further 53254 bytes. The current ImportedAM source is
16133 lines, 1513914 LF bytes, SHA256
ed2cbc91ae14c4e79ce4e727e0ee30ba4a0df68d7e0c47f64aac2c0e4258607a.
The ignored tmp/imported-unused-pruning-manifest.json records every removed
block hash, dynamic source range, per-step hashes, exact pins and all scanned
module identities. The full pre-pruning source still allows byte-exact
restoration. Actual compiler validation is required before the pruned
dependency graph is admitted.

The final provenance preface is corrected to describe the actual pruning;
no proof body changes in this correction. The pending-compile import is
16133 lines, 1513913 LF bytes, SHA256
e8cb972f70bc9455a194672eb498ed423a10f73c097e4adc89228a68f8a03732.

## Actual compilation diagnostics (2026-10-09)

The fixed Lean 4.33.0-rc2 environment and public Zeta23/ChallengeDeps dependencies are ready. The first complete ImportedAM build exited 1 with only 29 dependent Boolean-recursion motive inference errors introduced by the generic coverage parameter. Explicit motives repaired those errors. The 750028-byte source prefix, including the original AM analytic chain and all generic target/coverage interfaces, then compiled with exit 0. The complete module is being checked again; prefix success does not certify its final literal table.

Independent pure-Mathlib slices of the counting/o(N) transport, finite near matching, and real-form Hermitian eigenvalue/complete Gram-square algebra also compiled with exit 0. The printed axiom dependencies of the asymptotic transport and eigenvalue theorem contain only `propext`, `Classical.choice`, and `Quot.sound`. These slices do not replace the final complete-module and challenge audits.

Current ImportedAM source before the complete rerun: 16140 lines, 1515412 canonical LF bytes, SHA256 `7a2fb08c598a32b05f041b51a762c3dc789ce36e0a3ff871e9f3776a69cd64f8`. The original mcheckP target and coverage predicate remain the defaults; only their proved interfaces were generalized. No original leaf computation or certificate data changed.

The repaired complete ImportedAM target subsequently compiled with exit 0 (2026-10-08 16:17 UTC). A fresh standalone axiom audit also exited 0: all nine inspected declarations, including the original full PC8 certificate and generalized target/coverage interfaces, depend only on allowed axioms. The source above is now frozen. `verification/imported-am-check.json` records actual process metadata, current input/olean hashes, and the new audit observation; `verification/imported-am-axioms.txt` contains the complete audit output. Majorant and the new finite certificate compile next; the final challenge is not yet certified.

## Complete analytic target and independent axiom audit

The complete `RecordProportion.AnalyticBridge:olean` target now compiled with actual exit code 0 against the frozen ImportedAM and Majorant modules. Its 26 audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`. The source is frozen at SHA256 `5d2af7529d7c41cad519bf1b815df3ee32bb8069e718767516631233f169d57f` (1365 lines; 61553 canonical LF bytes). The subprocess verification ledger is `verification/analytic-bridge-check.json`, SHA256 `ade7043d141aa5ff5b9946bb30c2a134798a66a29f69090b852b52a4b269d5f6`. This verifies the analytic implication from the genuine nine-point finite certificate; the final finite certificate and challenge assembly are still being completed.

## Complete point guards and span membership

The complete point/tangent layer was actually kernel compiled against the
corrected transparent Data snapshot: all 482 frames, all 1224 extra
representatives and 70 ordinary top-level closed blocks passed. Its ten
axiom audits contain only the allowed three axioms. This run is recorded
in `verification/point-soundness-isolated-check.json`; its mathematical
body is the prior 379-line PointSoundness source.

An independently compiled 120-line addition then checks every extra
occurrence's span belongs to the original 26-term weight list, using
39 ordinary kernel blocks. Its two audits contain only `propext` and
`Quot.sound`; `verification/point-soundness-span-check.json` records the
actual exit code 0 and the exact recovery of the prior mathematical body.
The combined public PointSoundness source is 499 lines / 29007 canonical
LF bytes, SHA256 `e0feca589d54ae049e8ff721dfd1bbe7ea9804f0fac0c42ba96ef0d5bd153764`.

These validations use identical corrected transparent Data definitions;
they do not claim the pending full formal Data certificate or whole
challenge has passed. The public PointSoundness target will be compiled
again against the final formal Data module once that dependency is ready.


## Packed single-file analytic chain

The complete ImportedAM, Majorant, qualified AnalyticBridge and exact trusted-count
identities were compiled together in one packed Lean file with actual exit code 0.
All 29 requested declarations use only the three permitted axioms. The unchanged
1,466,729-byte input and actual 826.73-second subprocess are recorded in
`verification/analytic-single-file.json`. This check does not include the uniform
W9 certificate, final unconditional website statements, Comparator or nanoda.
