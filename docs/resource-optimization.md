# Verification resource engineering

The result and all numeric inputs are fixed. This work changes how ordinary
proofs are checked so the eventual single-file submission can fit the site's
time and memory limits. No new zero-proportion estimate is being researched.

The pinned [inner launcher](https://github.com/josusanmartin/riemann/blob/668e239f30c7c56494611b1825306a3d65f95537/scripts/run-comparator-e2b.sh#L96)
allows 3,200 seconds for the whole Comparator invocation; the
[outer job](https://github.com/josusanmartin/riemann/blob/668e239f30c7c56494611b1825306a3d65f95537/e2b/run-verification-job.sh#L32)
has a 3,240-second timeout. Compilation, export, comparison, serial nanoda,
and the default Lean replay share that budget. A local proof pass establishes
neither the official resource limits nor website acceptance.

## Actual bounded comparison

| Same 64 original representative goals | Baseline | Classified two-edge route |
|---|---:|---:|
| Lean proof phases | 119.710 s | 81.620 s |
| Complete scratch module compile wall | 211.532 s | 175.777 s |
| Fresh transitive axiom audit | 65 roots passed | 68 roots passed |
| Serial nanoda replay wall | 69.359 s | 53.781 s |
| Exported declarations checked | 4,317 | 4,425 |

Only subsets of propext, Classical.choice and Quot.sound were used. Input/source
hashes remained unchanged. The ordinary proof-phase reduction was 31.8%;
the serial replay reduction was 22.5%. Both are sample measurements on a shared
host. They are not whole-file speedups or an official deadline result.
See [the combined record](../verification/finite-two-edge-64-cost-comparison.json)
and its referenced independent replay records.

The primitive edge bound already pays 1,169 of the 1,224 representatives.
The new ten-candidate bound takes the original edge and all nine primitive
two-edge paths. A generic kernel theorem proves that the original full
Floyd9 entry is at most this bound, even without a no-negative-cycle premise.
The lower-box correction is monotone, so 49 representatives can use that
cheaper check. Six keep the original full closure. Classification chooses
proof syntax; it is never a hypothesis. Every conclusion remains the original
integerCertificateCheck index=true, so a wrong classification fails checking.

The generic helper is [FloydTwoEdge.lean](../RecordProportion/FloydTwoEdge.lean);
its formal module build and five fresh axiom audits passed:
[verification](../verification/floyd-two-edge-formal-module.json).
The complete isolated 1,224-target candidate also passed: ordinary compilation
exited 0, and a fresh audit of all original representative goals, the aggregate
and three transport bridges (1,228 roots) exited 0. All 58 original computational
definitions, including the full lower bound and its Boolean check, remained
byte-for-byte unchanged. Compilation took 1,538.310 seconds and the fresh audit
20.610 seconds. The archived baseline compile-plus-audit took 1,672.840 seconds;
these are different shared-host runs with different audit workloads, so the
113.920-second difference is an observation rather than a controlled full-stage
speedup estimate. See [the full-family record](../verification/finite-two-edge-full-candidate.json).

Both complete Data dependency graphs then passed actual serial independent
nanoda replay with the same 33 roots and the same configuration. The original
graph checked 6,908 declarations in 1077.766 seconds; the
two-edge graph checked 7,016 in 934.157 seconds, saving
143.609 seconds (13.3%). Both exited 0, retained their input hashes and used
only the three permitted axioms. This is a full-family replay comparison,
rather than an extrapolation from the 64-goal sample; it still covers only the
Data graph, on a shared host. The baseline reused a validated byte-for-byte
export, but actually replayed its proofs again. Export wall time is not being
compared. See [the complete replay comparison](../verification/finite-two-edge-1224-serial-comparison.json).

The public [reproduction generator](../scripts/generate_two_edge_candidate.py)
reads the committed, hash-pinned Data and generic helper. It writes only under
the ignored tmp directory and retains every original integer-check target.
Its default output uses the public formal helper import; that header variant
has not been separately compiled by the isolated record. The historical header
can reproduce the exact compiled candidate, but its scratch helper import needs
the corresponding ordinary helper artifact. Generating source alone proves
nothing; every generated original goal still needs kernel verification.

## Complete point-reflection comparison

A generic theorem proves frameCheck(label+241)=frameCheck(label) for label<241.
The candidate numerically checks the 241 original cells and transports their
results to the full original 482-label statement. Every original computational
definition and the complete extra-point and semantic suffix remain byte-for-byte
unchanged. The new Point source does not import the old Point numeric proofs.

[FrameReflection](../RecordProportion/FrameReflection.lean) passed an ordinary
formal-module build and four fresh transitive axiom audits. The complete Point
candidate compiled in 212.323 seconds; a fresh audit of the exact original
12 interfaces passed in 19.945 seconds, using only the permitted three axioms.
See [the complete candidate record](../verification/point-reflected-full-candidate.json)
and [the public helper check](../verification/frame-reflection-formal-kernel.json).
The old archived module time is not an exclusive-host controlled comparison.

Actual serial independent replay of the same 12 interfaces then gave:

| Complete Point dependency graphs | Original | Reflection |
|---|---:|---:|
| nanoda wall time | 228.141 s | 184.250 s |
| User CPU time | 223.45 s | 180.28 s |
| Declarations checked | 46,464 | 46,470 |
| Exit status / unchanged snapshots | 0 / yes | 0 / yes |

The observed wall reduction is 19.2%. The original run initially overlapped the
Data tests and whole compile; the reflected run overlapped only the whole
compile. Both used the same fixed executable, configuration and interface roots.
This is a shared-host component measurement, not a whole-submission saving.
See [the comparison](../verification/point-reflection-serial-comparison.json).
The [Point generator](../scripts/generate_reflected_point_candidate.py) now
reproduces the checked f7d766f8 source from public inputs, including actual
rejection of an isolated redirected tmp-root test.

## Reproduce the optimized source

The [guarded bundler](../scripts/bundle_optimized_candidate.py) reads only
committed, hash-pinned inputs. It composes two-edge proof routing, synchronous
AM elaboration, the checked 21-declaration source pruning and existing exact
numeric compression. Its optional reflection mode inlines the checked Point
helper body. It writes into a fresh ignored tree and rejects nonempty output,
active-overlay paths, formal-source paths and disabled assertions.

```powershell
python -B -X utf8 scripts/bundle_optimized_candidate.py --reflection --output-dir tmp/optimized-repro/combined
```

The combined source has 1,998,462 bytes, leaving 1,538 bytes under the site's
2,000,000-byte source limit. Its SHA256 is
642f68af1c2f4a44db4ca7ef8955a8a5b2bbbefa81c47e69cce4d4438c69d2f0.
Generation and guarded reproduction passed; this combined single file has
not received a fresh full compilation, independent replay or Comparator pass.
The manifest states that scope explicitly.
See [the generator record](../verification/optimized-candidate-generator-perron.json).

Without reflection, the generator exactly reproduces the separately tested
1,994,836-byte source, SHA256
583c5becafd39bc083240afa64d4468be15df67a86d819ac4544b18e2bfd98c7.
That local one-thread Windows compile/audit attempt was deliberately stopped
at 3,200.500 seconds by its experimental wall guard, before a complete result
or the final four axiom audits. It reached all 1,224 integer representatives
and their aggregate, but that partial progress is not a full proof pass.
The sampled owned-process tree peaked at 8,372,035,584 bytes; the observed Lean
working-set peak was 8,343,334,912 bytes. These local observations do not establish
Linux resource compliance or an official timeout failure.
See [the cutoff summary](../verification/whole-optimized-sync-cutoff-summary.json)
and [resource trace](../verification/whole-optimized-sync-resources.json).

## Rejected and unconfirmed alternatives

Directly constructing kernel-checked reflexivity terms for four original goals
took 4.702 seconds versus 4.633 for decide+kernel and was rejected.
[Its record](../verification/direct-reflexivity-isolated-cost.json) preserves
the failed first universe choice and the repaired fresh audit path ordering.

Bare norm_num variants left the actual packed Array/List-fold expression
unsolved in a bounded basic0 trial. Failed tactic timings are not proof
speedups, and recovery placeholders were not admitted. That trial gives no
general impossibility statement about proof reflection.

A 43-slot sparse difference accumulator has a generic equality proof:
one weighted row traversal, eight prefix entries and 34 square entries
reconstruct the original 42-column lower expression for arbitrary objective
and box bounds, without row-shape premises. Its actual four-goal test passed
the original conclusions and fresh axiom checks, but took 5.860 seconds versus
4.534 seconds for the existing primitive route (29.2% slower). Serial nanoda
also passed both groups and took 5.157 seconds versus 3.375 seconds. This Array
implementation is rejected; lower paper operation counts did not predict
kernel cost. The [Lean cost record](../verification/sparse-difference-four-representative-cost.json)
and [baseline](../verification/sparse-basic-four-serial-nanoda.json) /
[sparse replay](../verification/sparse-sparse-four-serial-nanoda.json) retain
the measurements. The separately checked generic equality is useful evidence,
but gives no general impossibility result for sparse methods.

## Review and next step

The exact rational result and numeric inputs remain fixed. Both complete
component families have ordinary Lean proofs, fresh audits and serial independent
replays. Two-edge routing reduces Data replay by 13.3%; reflection reduces Point
replay by 19.2%. Their percentages cannot be added or applied to a whole pipeline.
Direct reflexivity and the current Array sparse accumulator did not reduce cost.

A bounded secondary probe found eight AM helpers whose original interfaces
can be proved by exact references to the pinned Zeta23 ModWindow helpers.
The eight aliases and eight interface identities passed in 76.797 seconds,
using only allowed axioms. They do not overlap the existing 21 deletions and
would save a further 6,125 source bytes including the new import. This is source
capacity evidence, not a measured runtime gain, and is not included in either
generated candidate. Fixed template scripts imply the upstream module is
prebuilt at the site, but no live sandbox observation or independent replay was
performed. See [the bounded probe](../verification/am-helper-alias-bounded-probe.json).

The next decision needs a complete combined-candidate measurement in the pinned
Linux 4CPU/8GiB environment, accounting for every Comparator stage. The Windows
one-thread cutoff leaves the total deadline unresolved. Further work should
target measured dominant kernel computations rather than source cleanup alone.
Mathematical research remains paused and no site acceptance is asserted.

## Published candidate

The verified public Solution.lean is still the original 1,996,187-byte file,
SHA256 d52f013f7edcc8536a28ef3908e64a967e5b9184d6546952cb5a541dc6d65e8a.
Its ordinary kernel and independent checks passed. Its resource compliance
remains unconfirmed. A replacement needs fresh full compilation, transitive
axiom checks, independent replay and the exact website contract comparison.
No optimization sample authorizes a website acceptance claim.
