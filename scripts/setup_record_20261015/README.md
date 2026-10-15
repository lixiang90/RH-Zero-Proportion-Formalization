# Pinned temporary verification runtime

These recipes download and build the exact challenge toolchain without changing
system Lean, Rust, or project dependency settings. Source archives are bound to
the commits and SHA256 values in `source-archives.lock.json`; the compiler is
bound to the official release asset digest. The Rust components are checked
against the official component SHA256 files, and nanoda builds its unchanged
`Cargo.lock` with `--locked`.

These commands describe the recorded Windows/WSL Linux x86-64 environment.
Use Python 3.12 or later for archive fetching and Python 3.10 or later for the
Linux build and verification stages. The recipes require working HTTPS access,
sufficient disk space, and Linux `tar`, `xz`, `zstd`, `curl`, `/usr/bin/time`, and a C
linker/toolchain for the Rust build. They do not install these prerequisites.
The verification driver also binds the exact recorded nanoda binary hash;
rebuilding on another distribution or with a different linker can change that
hash even with identical sources. Such a build needs a separately reviewed
binary provenance record rather than an assertion of byte-identical reproduction.

From the repository root, fetch artifacts into the ignored setup directory:

```powershell
python -B -X utf8 scripts/setup_record_20261015/fetch_compiler.py --setup-dir tmp/setup-20261015
python -B -X utf8 scripts/setup_record_20261015/fetch_sources.py --setup-dir tmp/setup-20261015
python -B -X utf8 scripts/setup_record_20261015/fetch_rust.py --setup-dir tmp/setup-20261015
```

Run the Linux stages in WSL, mapping the repository and setup directory to their
actual Linux paths. The following paths describe this checkout:

```bash
python3 /mnt/d/codex-build/Riemann-Zero/RH-Zero-Proportion-Formalization/scripts/setup_record_20261015/prepare_linux_runtime.py --setup-dir /mnt/d/codex-build/Riemann-Zero/RH-Zero-Proportion-Formalization/tmp/setup-20261015 --runtime-dir /var/tmp/rh-zero-20261015
python3 /mnt/d/codex-build/Riemann-Zero/RH-Zero-Proportion-Formalization/scripts/setup_record_20261015/build_nanoda.py --setup-dir /mnt/d/codex-build/Riemann-Zero/RH-Zero-Proportion-Formalization/tmp/setup-20261015
python3 /mnt/d/codex-build/Riemann-Zero/RH-Zero-Proportion-Formalization/scripts/setup_record_20261015/build_dependencies.py --setup-dir /mnt/d/codex-build/Riemann-Zero/RH-Zero-Proportion-Formalization/tmp/setup-20261015
```

The dependency stage discovers every explicit import of the frozen
`GramDefect20261015/Core.lean`, rather than assuming `Zeta23.FinalMult` is the
entire closure. Its `--root-source` option can select another root source.
The historical `extend_dependencies.py` recipe preserves the first verified
135-module receipt, validates those sources and outputs by SHA256, and builds
only the five extra Core dependencies. A fresh reproduction can build all 140
modules directly with `build_dependencies.py`.
The last two stages are independent and may run concurrently. They write
`nanoda-build.json` and `dependencies.json` in the setup directory. A successful
runtime setup alone does not verify the candidate theorem. The separate
`scripts/verify_record_20261015.py` driver checks the actual modular and single-file
proofs, exact trusted statements, permitted axioms, and both kernels.

Use persistent Linux temporary storage for the runtime and build. This WSL
installation removes `/tmp` when it restarts; `/var/tmp` survives that cleanup.
Ext4 temporary storage also avoids the substantial metadata overhead of
compiling thousands of modules on the mounted Windows filesystem.

The recipes download source archives over HTTPS and check their recorded SHA256
hashes when Git transport is unavailable.
They report archive provenance explicitly and do not claim a Git checkout.
Existing Windows Mathlib `.ltar` cache files, when present at the optional local
path in the preparation script, are used through symbolic links without
intentionally modifying the seed files; the links do not enforce read-only
access. Missing matching hashes come from the official Mathlib cache.
Adjust or remove that optional seed for a
different machine. The archive and tool hashes are checked again during proof
verification. The downloaded binaries, source archives, and cache stay outside
tracked paths.
