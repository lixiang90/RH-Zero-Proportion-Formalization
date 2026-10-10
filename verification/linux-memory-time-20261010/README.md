# Linux memory and time evidence

These records concern resources for the fixed result `66812491/99194740`.
The f40 full-file trial was intentionally cut off after the local memory gate
failed; no complete proof or downstream check was obtained. Its
[completed archive](whole/r5-completed/README.md) retains the measurements.
The global-synchronous follow-up passed complete local compilation and a
fresh three-root standard-axiom audit, but failed its memory resource gate
(64 failed charges, no OOM kill). Its [completed records](whole/r6-completed/README.md)
preserve that distinction and the historical contract. Exports, independent
replay, Comparator and live-contract validation remain unrun. The original
checked d52 public Solution remains unchanged; no website acceptance is claimed.

| Checked component | Observed result | Limit |
|---|---|---|
| Complete AM, same-Linux pair | 553.329 → 448.761 s; both fresh 20-root audits passed | One pair, 18.9% lower wall time; repeatability unresolved |
| AM sampled peak PSS | 7.51 → 7.45 GiB | No significant memory gain; both cgroup peaks reached 8 GiB |
| All 49 selected-pivot goals | 36.751 → 33.881 s numeric proof time; both compiles and fresh audits passed | One ordered pair; extra whole-helper elaboration/replay cost excluded |
| Packet equality checkpoint | 2.780 → 2.617 s including preparation | Rejected for adoption; negligible memory change |

The [primitive-bound shadow test](primitive-bound-shadow/README.md) preserved
an original pass, a source-error failure, and a repaired pass. Actual Lean
compile/audit commands took 29.110 versus 29.361 seconds across a reboot;
there is no stable overall speed or memory improvement, and no adoption.

All audited roots use only subsets of `propext`, `Classical.choice` and
`Quot.sound`. Native Linux component runs used the pinned compiler, an 8 GiB
cgroup, no swap, a four-CPU quota, and imported-artifact pages checked cold.
The host WSL VM had 32 GiB, so these runs do not reproduce the official sandbox.
Preparation time is recorded separately from proof time.

The [AM packet](am/README.md) preserves raw traces, fresh source/artifact bindings
and the disclosed control-validation phase gap. `evidence/finite49-actual.json`
and the finite raw manifests preserve all 49 original goals and their fresh
audits. Earlier prepared labels remain historical; completed summaries give
the checked component scope. Compressed and decompressed hash bindings allow
review without storing Lean binaries or compiled caches.

`reproduce_candidate.py` generates source only from frozen public inputs and
explicit recipes. The default is bounded8: 1,993,809 bytes, SHA256
`f40d0cb3566d4e71a6bb624a4d4375ca3ade977d3850e14e134a8a850f4abd50`.
The optional chosen49 source is 1,998,362 bytes, SHA256
`d9d245aabbae53abf7da5788813ca84dee6c65b2476a330096a33c859c22464b`.
Both exact reproductions passed; the optional variant is not selected for
adoption. Gzip components are review artifacts and are never generator inputs.

```text
python reproduce_candidate.py --repo-root PATH_TO_REPO --output-dir tmp/repro-bounded8-unique
```

The script refuses existing outputs, tracked destinations and paths outside
the ignored `tmp/` tree. It never compiles or submits the generated source.
Whole-file evidence belongs in `whole/`; compilation, final-root audits,
serial independent replay, current-contract Comparator checks and official
acceptance remain separate requirements. Component percentages cannot be
combined into a whole-pipeline estimate.
