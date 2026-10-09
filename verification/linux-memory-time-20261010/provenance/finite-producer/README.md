# Memory and time optimization evidence

This prospective bundle records component checks and source reproduction. The original mathematical inputs and submission sources remain frozen. It contains no new zero-proportion theorem or website acceptance claim.

| Item | Actual result | Scope |
|---|---|---|
| bounded8 AM | Lean exit 0; 448.761 s; peak PSS 7.45 GiB; no OOM or swap; fresh 20-root audit uses only standard axioms | Component check. Same-OS synchronous comparison is pending. The cgroup peak reached 8 GiB, so this does not establish memory headroom in an 8 GiB VM. |
| chosen pivot, indices 35/54/1199 | First 3.005 → 2.197 s (26.89%); reverse 2.461 → 2.248 s (8.65%) | The baseline varied 18.10%. Gain magnitude is unstable; no established memory gain or complete 49-goal result. |
| packet checkpoint, indices 64/65/1198 | 0.218 s preparation + 2.399 s proof = 2.617 s, versus 2.780 s; net 5.86% | Rejected for adoption. PSS differs by 1.9 MB. A finish-only 14% figure omits preparation cost. |
| bounded8 whole source | 1,993,809 B; 6,191 B headroom; SHA `f40d0cb3…` | Exact source reproduction only. Whole compilation, Nano, Comparator and website checks are pending. |
| optional bounded8 + chosen49 | 1,998,362 B; 1,638 B headroom; SHA `d9d245aa…` | Exact source reproduction. Its 49 original goals and fresh audits passed as a component; whole checks remain pending. |

The complete 49-goal pair passed ordinary Lean compilation and fresh audits of all original Bool targets. Numeric proof time was 36.751 → 33.881 s (7.81% reduction); full component compilation was 62.098 → 59.258 s (4.57%). This is one ordered full-family pair, with no established memory gain. Both variants share the same generic import, so this pair does not isolate the additional chosen-helper elaboration/replay cost in the whole file. The default remains bounded8; independent Nano and whole-file results are pending. `evidence/finite49-actual.json` and `evidence/raw-finite49-manifest.json` bind its raw measurements and fresh artifacts.

The native Linux trials used the pinned v3 harness with imported-artifact pages checked cold by `mincore`, an 8 GiB cgroup, no swap, and a four-CPU quota. AM used `-j4`; finite probes used `-j1`. Cache preparation costs are recorded separately from proof time. The host VM has 32 GiB, so component cgroup success is not an exact official 8 GiB VM reproduction.

`reproduce_candidate.py` defaults to bounded8. It reconstructs the candidate from hash-pinned committed inputs: 21 guarded deletions, eight ordinary upstream aliases, actual parser boundaries with 162 waits, and full fresh numeral-dictionary bundling. The optional chosen49 variant computes pivot hints from the committed integer certificate and mechanically adapts the original basic lower formula. All original 58 computation definitions and the existing three two-edge definitions retain their exact bytes. Gzipped generated components are review artifacts only and are never generator inputs.

The explicit alias edits and parser-boundary provenance are in `recipe/`. `source-recipe.json` binds public sources and exact expected outputs. `review-components.json` identifies complete component archives. `evidence/raw-finite-manifest.json` binds raw finite logs to compressed and decompressed SHA-256 hashes. No Lean binaries or compiled caches are included. AM raw logs await root selection.

Both variants were regenerated from public inputs and matched the exact hashes above. Existing outputs, tracked areas and parent-directory escape routes were refused before output creation. The wrapper pins every dynamically loaded generator, disables bytecode writes to public script folders, checks frozen inputs, rejects symlink/junction output routes, and writes only fresh ignored source output. Its read-only Git queries use a temporary subprocess-local ownership configuration for compatibility with older Git; persistent Git configuration is untouched.

```text
python reproduce_candidate.py --repo-root PATH_TO_REPO --output-dir tmp/repro-bounded8-unique
python reproduce_candidate.py --repo-root PATH_TO_REPO --variant bounded8-chosen49 --output-dir tmp/repro-chosen49-unique
```

Source generation does not run Lean or submit anything. Same-OS AM comparison, whole compilation, fresh whole-root audit, independent Nano, Comparator and website acceptance remain separate checks. This folder is a publication proposal in ignored scratch; it has not been committed or published.
