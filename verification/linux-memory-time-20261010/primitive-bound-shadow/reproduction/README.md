# Reproduction inputs and limits

The packet preserves both historical source preparations, their generation
scripts, the exact three tested theorem sources, audit sources, two native
runner versions, plans and frozen bindings. The prepared-only metadata is
historical; the completed owner records and top-level summary state outcomes.

- [Original/failed plan](../owner-r2/plan.json) and
  [runner](../owner-r2/primitive_bound_shadow_driver_20261010.py).
- [Repaired plan](../owner-r3/plan.json) and
  [runner](../owner-r3/primitive_bound_shadow_driver_20261010.py).
- [One-line repair diff](../source-r2/r1-to-r2.diff) and
  [four-line original-to-repaired proof diff](../source-r2/four-line-body.diff).
- [Repaired frozen bindings](../owner-r3/frozen-input-manifest.json) and
  [original frozen bindings](../provenance/frozen-r2-input-manifest.json).
- [Exact imported r6 source](../dependency-source/r6/source/Solution/Candidate.lean.gz),
  [frozen r6 config](../dependency-source/r6/config.json.gz),
  [whole runner text](../dependency-source/r6/whole_candidate_native_driver_20261010.py.gz),
  and project [Lean pin](../dependency-source/project/lean-toolchain),
  [package definition](../dependency-source/project/lakefile.toml),
  [dependency pins](../dependency-source/project/lake-manifest.json).

The four frozen r6 source texts are included as exact gzip payloads, including
ChallengeDeps and the generated historical CandidateSpec/Challenge. They use
the historical 6735015/10000000 current-record contract, not the observed new
live record. The `.olean` family is bound in the plans and completed records;
its bytes are deliberately absent. All cache/package paths are historical.

The exact [V3 scoped-cache harness source](../dependency-source/runtime/linux_cgroup_resource_harness_v3_20261010.py)
matches both plans' harness binding e192787f…f4d24ec and is included as text.
These runners depend on the original scoped-cache harness and runtime layout,
pinned compiler, matching r6 dependency artifacts and isolated resource setup.
The source/config/runner texts are evidence, not a portable one-command clone
recipe. Reproduction requires a separately prepared pinned environment and
explicit regenerated path bindings; editing paths changes a plan hash and must
be documented. No script here was executed during packaging. The tested flags
were -j4 and --tstack=32768, with a 240-second per-probe guard and a 4 CPU/8 GiB/
no-swap proof cgroup. Imported pages were checked cold; outer caller memory and
cold-preparation work remain separate. This does not establish official sandbox
fit. Source generation or file-hash checks alone do not verify a proof.
