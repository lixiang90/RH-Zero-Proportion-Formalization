# AM controlled component evidence

This prospective packet records one same-Linux paired experiment using the pinned Lean4.33.0-rc2 compiler and v3 harness. It is a file-only archive proposal; no public files were changed and no compiler/cache action ran during packaging.

| Component | Compile wall time | Cgroup CPU time | Sampled peak PSS |
|---|---:|---:|---:|
| bounded8 | 448.761s | 526.1086613s | 7,998,533,632B |
| synchronous alias8 | 553.329s | 533.2747335s | 8,061,101,056B |

The bounded run was 18.90% faster in this single pair. PSS differed by 0.78% (62,567,424B), insufficient to claim a significant memory gain or repeatability. Both observed cgroup peaks reached 8GiB, so no memory headroom in a whole 8GiBVM is established. The surrounding WSL VM was 32GiB. Each compiler used `-j4 --tstack=32768`, a four-CPU cgroup quota, memory+memsw8GiB, no swap and a 1200s compile guard. Fresh deps and20-root audits each had a 180s guard.

Both variants compiled ordinarily with actual exit0, then imported the exact newly generated `RecordProportion.ImportedAM.olean` and audited all main 12+alias8 roots. The identical axiom lists are subsets of `propext`, `Classical.choice`, `Quot.sound`; no new axioms, sorry/native_decide or weakened targets were introduced. Raw before/after input bindings, PSS/RSS/cgroup/CPU samples, logs and scoped cold-page residency checks are preserved under `runs/`.

Control compilation finished 2026-10-10 at 02:02:31 China time. A host/runtime session restart occurred afterward; the coordinating root reported a resume around 06:12. Pending control deps/audit resumed at 06:16 and completed 06:17, using the same exact source and `.olean` hashes. There was no control recompilation. This validation-phase gap is disclosed in `validation-phase-gap.json`; it does not change the completed paired compile measurements.

`comparison.json`, `summaries/` and `packet-scope.json` state the checked scope. `analysis/` preserves finalized monotonic barrier timing and a coarse peak-sample attribution with plus-or-minus 1s uncertainty. Live barrier output was buffered and only a lower bound; no individual proof is identified as a memory culprit. There are no timestamped checkpoints for synchronous source attribution.

`archive-manifest.json` binds each local record to compressed and decompressed exact byte counts and SHA256 hashes. Every gzip has `mtime=0` and an empty filename header. Full bounded8 source and parser recipes already exist byte-exactly in the finite publication proposal, and are referenced by content hashes in the manifest rather than duplicated. `source-review/AMSyncAlias8.lean.gz` supplies the additional exact control source. Root must preserve/relocate the external packet references when merging publication proposals.

The exact prepared runner/config and Windows-archived v3 harness/environment inventories are source/text provenance. Earlier prepared/static files retain their original pending labels; actual completed summaries take precedence for component validation. No Lean executables, `.olean`/IR files, cache archives or entire scratch trees are included. Whole bundled Solution, independent verifier/Comparator and website acceptance remain separate checks.
