# Whole-file verification

The selected f40d0cb3 source is undergoing fresh full-file compilation.
No complete whole-file pass, independent replay or current-contract
Comparator result is available at this checkpoint. The original public
Solution remains unchanged.

`prepared/` preserves the frozen r5 driver, configuration and ten
file-only negative guard fixtures. `preflight/` contains only completed
tool builds and the freshly generated current contract, both exit 0.
Their source and artifact bindings, owned-process resource traces and
process logs have exact compressed/decompressed hashes in
`preflight-archive-manifest.json`. The tools and contract stages do not
check the selected whole Solution. No running compile file is published.

The experimental Lean invocation uses -j4 and --tstack=32768; its
four-CPU, swap-free 8 GiB cgroup runs inside a 32 GiB WSL VM.
This is local diagnostic evidence, not official sandbox compliance.
Cold preparation and actual shared-clock elapsed time are accounted for
separately from proof-stage wall time. Completed component checks do not
establish whole-file or website acceptance.
