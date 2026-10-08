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

The public [reproduction generator](../scripts/generate_two_edge_candidate.py)
reads the committed, hash-pinned Data and generic helper. It writes only under
the ignored tmp directory and retains every original integer-check target.
Its default output uses the public formal helper import; that header variant
has not been separately compiled by the isolated record. The historical header
can reproduce the exact compiled candidate, but its scratch helper import needs
the corresponding ordinary helper artifact. Generating source alone proves
nothing; every generated original goal still needs kernel verification.

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

The working result, rational certificate and exact theorem types remain fixed.
The controlled two-edge sample supports using a simpler sufficient check for
49 expensive representatives; the complete family confirms correctness.
Direct reflexivity and the current sparse accumulator did not reduce cost.
The next candidate removes duplicated point checks by proving reflection
invariance, while preserving the original all-482-label conclusion. Its source
and runtime must pass actual checks before it can replace the published proof.
Whole-file synchronous compilation and full-family serial replay are being
measured independently. They do not establish the official total deadline.

## Published candidate

The verified public Solution.lean is still the original 1,996,187-byte file,
SHA256 d52f013f7edcc8536a28ef3908e64a967e5b9184d6546952cb5a541dc6d65e8a.
Its ordinary kernel and independent checks passed. Its resource compliance
remains unconfirmed. A replacement needs fresh full compilation, transitive
axiom checks, independent replay and the exact website contract comparison.
No optimization sample authorizes a website acceptance claim.
