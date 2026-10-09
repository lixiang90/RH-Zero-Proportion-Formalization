# Completed local whole-file records

This new packet preserves completed r5 text records, including failed and
timed-out attempts. Missing phases remain unverified. It does not replace
preflight history or the original d52 public submission.

| Selected phase | Recorded outcome | Proof-stage seconds |
|---|---|---:|
| contract | COMPLETED_PROOF_PASS | 31.429 |
| compile | COMPLETED_INTENTIONAL_LOCAL_RESOURCE_CUTOFF | 2733.628 |
| deps | NOT SUPPLIED | — |
| audit | NOT SUPPLIED | — |
| challenge-export | NOT SUPPLIED | — |
| solution-export | NOT SUPPLIED | — |
| core | NOT SUPPLIED | — |
| nano | NOT SUPPLIED | — |

Complete local proof gates passed: **False**.
File-integrity/provenance review: **PASS**.
Actual shared elapsed: **2854.274 s**; sum of observed proof-stage time
excluding tools: **2765.057 s**; observed cold preparation sum: **64.608 s**.
The sums cover only supplied selected phases and must not be presented as an
end-to-end official runtime. Shared elapsed includes local preparation, wrappers
and caller delays; tools were prebuilt outside that clock.

The experimental compiler uses the flags preserved in `summary.json` (r5
-j4 and --tstack=32768); official stack/worker equivalence is not established.
The independent local phases differ from the official retained-strings pipeline
and may use a different order. A four-CPU, no-swap 8 GiB cgroup inside a 32 GiB
WSL VM is not the official 8 GiB sandbox. Outside-cgroup caller/supervisor samples
are preserved separately; unrelated cache ownership, kernel and host memory are
not fully measured. Separate memory maxima are not added.

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

Completion classification: **R5_INTENTIONAL_RESOURCE_CUTOFF**.
Root diagnostic note: r5 tools and contract passed. Compile was deliberately SIGTERM-cut off after failcnt 242 and persistent page pressure. Owned Lean -15, worker/harness 241, driver 1. No final Solution compile pass or downstream verification is established.

An intentional resource cutoff leaves no completed mathematical proof result.
Recorded failed memory charges and sampled peaks do not by themselves establish
a kernel OOM kill, a Lean mathematical rejection or an official website timeout.
The proc snapshot read_bytes/fault counters are cumulative, not resident-memory
peaks. Page-wait state is consistent with pressure; one snapshot does not establish
a deadlock or identify a single proof culprit.

Follow-up experiment metadata in summary.json comes only from the root handoff.
No running r6 record was read or included; no complete r6 proof is asserted.
