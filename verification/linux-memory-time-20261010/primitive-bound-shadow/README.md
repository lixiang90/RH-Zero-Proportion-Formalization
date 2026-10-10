# Primitive-bound shadow probe: three completed runs

The original proof passed. The first explicit rewrite failed at source line 43:
`simpa only [neg_mul] using hrev` did not match the normalized inequality. Its
error log prints `sorryAx` during failed elaboration; no compiler artifact or
fresh audit was produced. This is retained as a failed source experiment.
Replacing that line with `linear_combination hrev` produced a passing repaired
proof and a fresh audit of the identical type, standard three axioms and absence
of the original theorem from its used-constant closure.

| Recorded diagnostic | Original r1 | Failed explicit r1 | Repaired explicit r2 |
|---|---:|---:|---:|
| Lean exit / accepted proof | 0 / PASS | 1 / FAIL | 0 / PASS |
| Owned-worker elapsed, including driver/bindings/cleanup | 29.763 s | 26.005 s | 29.677 s |
| Actual Lean command sum | 29.110 s | failed compile only | 29.361 s |
| Successful checked-body marker span | 875 ms | not applicable | 528 ms |
| Peak sampled process-tree PSS | 7,129,774,080 B | 7,019,896,832 B | 7,151,198,208 B |
| Fresh closure constants checked | 9,492 | none | 9,509 |

The owned-worker difference is only **0.086 seconds**, while the actual Lean
command sum increased **0.251 seconds** (26.190 + 2.920 versus 26.403 + 2.958).
The successful body-marker difference of 347 ms is one observation. The failed
499 ms span is excluded from proof-performance comparisons. PSS increased by
21,424,128 bytes; this does not establish a RAM improvement or stable overall
gain. The immutable owner's earlier timing label is interpreted precisely in
[summary.json](summary.json); its original analysis is preserved unchanged.

The successful original and failed r1 share boot
`6caf73ed-1ebc-467a-ba2a-dd9aa31b1417`; the repaired result used boot
`5122a683-459b-4584-8073-e57b69843ef0`. This is a single comparison across boots
with the same pinned dependencies, not an uninterrupted same-boot controlled
pair. Cold preparation is recorded separately (28.363 / 28.907 / 27.717 s).
The complete phase totals were 59.104 / 56.096 / 59.098 s. Separate memory peaks
are not added; caller/supervisor PSS outside the proof cgroup is recorded.

Both successful probes use only `propext`, `Quot.sound`, `Classical.choice`.
They import the exact completed r6 module, whose own memory gate remains failed.
They exclude a direct dependency on the original target but operate after the
whole imported module; they do not reproduce its command-prefix environment.
No replacement is adopted, no whole-file speedup is inferred, and no fresh
live-contract, export, Comparator/default replay, Nanoda or website acceptance
is asserted. The original public d52 submission remains unchanged.

[Original source preparation](source-r1/README.md) and
[repaired source preparation](source-r2/README.md) retain their historical
pre-run labels. [Original completed pair](owner-r2/archive-manifest.json),
[repaired completed record](owner-r3/archive-manifest.json), and
[completed handoff](provenance/completed-three-run-handoff.json) are immutable
producer snapshots. [Exact raw/compressed bindings](archive-bindings.json) and
[inventory](archive-manifest.json) cover every selected source/log and generated
record. [Reproduction scope](reproduction/README.md) explains the preserved
runner/plans and frozen dependency sources. No compiled binary or cache is
included. Absolute paths in retained input metadata are historical provenance;
[path-relocation.json](path-relocation.json) maps selected records to usable
packet-relative paths. File-only packaging did not run a compiler or verifier.
