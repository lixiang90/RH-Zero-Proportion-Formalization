# Completed local whole-file records

This packet preserves explicitly completed local text records. Failed, timed-out
and intentionally stopped attempts remain distinguishable. Missing phases stay
unverified. It does not replace preflight history or the original d52 public
submission.

| Selected phase | Recorded outcome | Proof-stage seconds |
|---|---|---:|
| contract | COMPLETED_PROOF_PASS | 27.968 |
| compile | COMPLETED_PROOF_PASS_RESOURCE_GATE_FAILED | 2993.462 |
| deps | COMPLETED_PROOF_PASS | 0.598 |
| audit | COMPLETED_PROOF_PASS | 25.023 |
| challenge-export | NOT SUPPLIED | — |
| solution-export | NOT SUPPLIED | — |
| core | NOT SUPPLIED | — |
| nano | NOT SUPPLIED | — |

Diagnostic identifier: **r6-completed-old-current-diagnostic**.
Candidate source: `5227a25ea2c5f18c83e0a85c756e34ec9a0176a1ba9d1cd5f5556aab836ba7a2`, 1993837 bytes.
Frozen configuration: `ec3cc48754945e0fb7361bd88edced444bd8a491fce20bc6452b4a465c61afbf`.
Complete local proof gates passed: **False**.
File-integrity/provenance review: **PASS**.
Actual shared elapsed: **3471.979 s**; sum of observed proof-stage time
excluding tools: **3047.051 s**; observed cold preparation sum: **122.568 s**.
The sums cover only supplied selected phases and must not be presented as an
end-to-end official runtime. Shared elapsed includes local preparation, wrappers
and caller delays; tools were prebuilt outside that clock.

The exact compiler flags and commands are preserved in `summary.json`; official
stack/worker equivalence is not established. The independent local phases differ
from the official retained-strings pipeline and may use a different order.
Per-phase cgroup settings and separately sampled outside-group caller/supervisor
PSS do not cover unrelated cache ownership, kernel or host memory. An enclosing
VM size is reported only when supplied in handoff metadata. Separate memory
maxima are not added.

Only an actual completed fresh audit of all three final roots can establish
standard-only transitive axioms (`propext`, `Quot.sound`, `Classical.choice`).
Missing, failed or timed-out compilation/audit/export/independent replay/core
phases do not satisfy the complete gates. No website acceptance or official
resource-fit claim is made even if local proof gates pass.

`archive-manifest.json` binds exact compressed/decompressed raw bytes; gzip
mtime is zero and filenames are omitted from headers. No executables, compiled
artifacts, dependency caches or live partial logs are copied. `summary.json`
preserves source/artifact provenance and discrepancies. Review issues, if any,
make this scratch packet unpublishable until reviewed.

Completion classification: **R6_COMPILE_PROOF_PASS_RESOURCE_GATE_FALSE_INDEPENDENT_DEPS_AUDIT_PASS**.
Root diagnostic note: No intentional cutoff: completed compile pass with configured resource gate false (64 failed memory charges). Independent deps and audit passed; exports/core/Nano unrun. Original d52 public proof unchanged.

A proc snapshot, when supplied, records sampled states and cumulative
read_bytes/fault counters. Those counters are not resident-memory peaks. A page
wait can be consistent with pressure; one snapshot does not establish deadlock
or identify a single proof culprit. Follow-up metadata, when supplied, comes
only from the root handoff. No running record is read or included, and no future
attempt result is inferred. Completed proof claims concern only this packet
and only gates actually checked above.

The completed r6 compile proof passed, but its configured memory resource gate
failed: final memory.failcnt is 64, with no observed OOM kill, timeout or swap.
Independent deps and three-root axiom audit subsequently passed. Challenge and
solution exports, Comparator/default-kernel replay and Nanoda remain unrun, so
the whole pipeline has not passed. The shared clock continued during separately
authorized diagnostic phases after the failed resource gate. Its final elapsed
time exceeds 3200 seconds; this is not an observed official timeout.

This is a historical contract diagnostic: the frozen current record is
6735015/10000000 at website commit 6664d243005e12e155c19775b83f53721757414b.
The subsequently observed live accepted record is 66812491/99194876
(master-of-puppets, verified 2026-10-09 17:13:57.608 UTC; fixed public source
commit d95a6d7d11d7836306ec7ec1eb5be3478663718e). Our fixed score
66812491/99194740 remains larger, but a fresh current-contract validation has
not been performed here. Existing old-current deps/root audit passes must not
be presented as live-contract or website acceptance.

The local compiler explicitly used -j4 and --tstack=32768, in a 4 CPU/8 GiB/no
swap cgroup inside a locally configured 32 GiB WSL VM. Cold preparation and
sampled caller/supervisor memory are outside the proof cgroup. Official worker,
stack, retained-string and VM equivalence are not established.
