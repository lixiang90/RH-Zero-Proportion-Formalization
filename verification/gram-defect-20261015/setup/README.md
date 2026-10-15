# Fresh local runtime provenance

This directory records the local verification environment prepared for the
2026-10-15 refinement. These setup receipts alone do not establish a candidate
theorem, a website resource pass, an upload, or official acceptance.

- `runtime.json` binds the exact Lean compiler binary, official release archive,
  source archive pins, and isolated package search paths.
- `source-archives.json` records source archives downloaded over HTTPS and their
  checked SHA256 hashes. Native Git transport was unavailable; no Git checkout
  is claimed.
- `rust-components.json` and `nanoda-build.json` bind the verified Rust components,
  exact nanoda source pin, unchanged Cargo lockfile, actual build command, exit
  status, and resulting kernel binary hash. `nanoda-build.txt` is its transcript.
- `mathlib-cache.json` records the actual successful official-cache command and
  its exit status. `mathlib-cache.txt` is the download/decompression transcript.
- `dependencies.json` records successful ordinary Lean compilation of all 140
  Zeta23 modules required by the frozen Core's ten explicit Zeta23 imports.
  It binds source and output hashes and actual process results, with no changed
  source inputs. The first 135-module `FinalMult` closure is preserved in
  `dependencies-finalmult-135.json`; its outputs were checked by hash and retained
  when the five additional imports were compiled. `zeta-import-closure.json`
  records the complete import graph.

The Linux runtime and build use `/var/tmp/rh-zero-20261015`. This machine removes
`/tmp` during WSL restart, so the initial ephemeral runtime was recreated in
persistent temporary storage before dependency compilation. Large downloads and
cache artifacts remain in ignored scratch locations. The reproducible recipes
are in `scripts/setup_record_20261015/`.

Those recipes document the recorded environment and its system prerequisites.
The verification driver binds the recorded nanoda binary hash; a rebuild with
another distribution or linker may require a separately reviewed provenance
record even when its source and Cargo lockfile are identical.
