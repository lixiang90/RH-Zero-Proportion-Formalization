# Whole-file verification

The f40d0cb3 source's r5 full-file attempt was deliberately stopped after the
local memory-resource gate failed. No complete f40 proof or downstream
verification was obtained. The original public d52 Solution remains unchanged.
The [completed r5 archive](r5-completed/README.md) preserves the exact records
and the intentional-cutoff authorization.

`prepared/` and `preflight/` retain their earlier frozen driver, configuration,
guard fixtures and completed tools/current-contract builds. Their immutable
manifests remain unchanged. The tools and contract stages do not check the
selected whole Solution.

The raw compile proof stage took 2,733.628 seconds and the enclosing phase
2,770.896 seconds before termination. Actual shared elapsed was 2,854.274
seconds, including current-contract preparation and caller delays. Summed
observed proof-stage time excluding prebuilt tools was 2,765.057 seconds;
scoped cold preparation was 64.608 seconds. The compilation and remaining
audit/export/core/independent replay gates did not complete.

The compile sampled peak PSS was 8,317,437,952 bytes; failed memory charges
reached 242, with zero OOM kills and timeout false. Lean received intentional
SIGTERM and exited -15; worker/harness exit was 241 and outer driver exit 1.
These records do not establish a mathematical rejection, kernel OOM or official
website timeout. The separately sampled outside-group PSS peak was 173,293,568
bytes. The independent local phases used `-j4 --tstack=32768` and a swap-free
four-CPU 8 GiB cgroup inside a 32 GiB WSL VM; official stack/worker equivalence,
sandbox resource compliance and retained-strings pipeline equivalence are not
established. Memory maxima from different times are not added.

The r6 follow-up has source SHA256 prefix 5227a25 and 1,993,837 bytes. It sets
global `Elab.async false` outside the retained bounded-eight AM region.
At the recorded parent handoff, tools and current-contract stages had passed
and the full compile had begun. Its full proof and subsequent checks remain
pending. No running r6 record is published with the r5 archive.
