# Full old-W10 source-size audit

The best measured lossless layout still exceeds the website's **2,000,000 UTF-8 byte** limit. This audit does not prove a new floor and performs no Lean compilation.

| Component | Exact bytes |
|---|---:|
| Field-Huffman printable Lean data | 3,461,607 |
| Retained analytic proof, codecs, wrappers and notices | 542,851 |
| Known retained source plus data | 4,004,458 |
| Explicit budget for the unimplemented decoder/auxiliary expander | 128,000 |
| Budgeted source skeleton | 4,132,458 |
| Alternative full-term-delta printable data | 3,528,019 |

These are actual printable source counts, not gzip artifact sizes. `assemble_size.py` reproduced the previous 5,777,945-byte bundle and its exact SHA before removing the complete Certificate block. It disabled the old bundler's reporting side effect in memory; no published file was changed. The reserved space is an engineering budget, not an implemented or verified decoder. The known parts already exceed the limit independently of that budget.

## Sufficient witness fields and mathematical checking

The complete input has 95,778 branches and 95,779 leaves: 95,615 numerical, 163 empty and one reflection leaf. A preorder stream determines all paths. Each branch needs its axis and cut; the root is fixed by `RootBounds.initialCell`. Full cell literals are unnecessary. Geometry must use `AdaptiveCoverage.normalize`'s conditional normalization and then the actual left/right child operations. It must not be silently replaced by an unconditional two-round walker.

A numerical witness contains 39 support tuples `(kind, mixture, first point, second point)` and eight decimal Prüfer digits. Kind zero has no point data; kind one has no mixture or second point. Mixtures have ten bits, and points lie on the existing 32-grid. Original large dual amounts, `P/S/Cp/Cm`, paths and complete cells need not be stored. `FastPruefer` reconstructs proposed nonnegative `DualMove`s from the support slopes and tree code. These proposals remain subject to `LocalChecker.checkLeaf` / `mcheckGX`, including its coordinate residual penalty and the actual certified tangent intervals. Optimality, flow balance and the Prüfer implementation are not trusted mathematical premises.

The measured layout uses shared canonical Huffman code-length tables, term-position streams, signed point deltas, signed cut deltas and separate tree-digit streams. A second layout skips unchanged full support tuples; on the full input this worsened size, so it is rejected. No tangent, mixture, point, tree code, floor or branch cut was changed by either encoding.

An eventual pure command expander may decode the data to the same kind of small auxiliary declarations already tested by the 127- and 478-leaf implementations. Each numerical declaration must still prove its actual Boolean check, every materialized geometry equality must still be checked, and the opaque declarations must be composed to the root. Neither the Huffman decoder, the streaming expander, nor a complete new Lean cover has been implemented or compiled here.

## Independent complete replay

`independent_codec_replay.py` imports neither extractor nor encoder. It reconstructed the 10,907 printable literals byte for byte, checked all 60 Huffman channels, varints, padding and complete consumption, and recovered all node, support and tree-code cache hashes. It independently rebuilt all normalized states and recomputed all Prüfer amounts and all 95,615 exact integer leaf inequalities from the frozen analytic table. The minimum integer margin was **2,623,983,786,731,307,008 > 0**. The replay took 51.013 seconds. This is supporting exact arithmetic evidence, not Lean or independent-kernel verification.

## Mathematical merge target and one concrete missing obligation

At the observed average source cost, retaining the current fixed base and a 128,000-byte implementation budget would require reducing 95,615 numerical leaves to about **36,713**, or merging **58,902 (61.60%)**. Even ignoring all new decoder cost, the proportional target is 40,248 remaining, or 55,367 merged. These are explicit engineering targets under average-cost scaling. They are **not** information-theoretic lower bounds or a proof that another lossless codec cannot do better.

The existing 612-leaf formal region includes parent `r001100`, whose two children are `r0011000` and `r0011001`. Reusing the left child's complete witness on the normalized parent gives a positive arithmetic margin, but **does not pass the checker**: its term 5, span `(0,9)`, anchor 328704 has certified interval `[287648,350112]`, whereas the parent requires `[327680,360448]`. The check's tangent-validity guard is essential. The right child's witness also fails whole-parent tangent guards and the arithmetic inequality. A single deterministic proposal replacing the left child's invalid tangent by the old whole-interval lower bound is valid analytically but has a negative margin; it is not a merge.

A real uniform proof must therefore supply a sound whole-parent lower bound for this total span, with any loss explicitly paid in the full energy inequality, or prove a stronger joint gap-energy bound exploiting the parent constraints. Extending the tangent merely because the arithmetic margin is positive is unsound. The old kernel is the inherited `AMW.Cert.wfun`; a new-window scalar theorem cannot be substituted without an identity bridge. `parent-uniform-probe.json` records the exact missing interval and failed margins. No parent merge is claimed by this audit.

## Reproduction and scope

`extract_semantics.py` reads the two hash-bound old inputs and writes only this new directory. `encode_channels.py` emits the two encodings. The independent replay can be run read-only; its pinned receipt is not overwritten. `assemble_size.py` counts the retained source. The 26MB semantic cache and the size-only skeleton are rebuildable outputs, not required independent replay inputs. `audit-files.json` distinguishes the small retained package from those derived artifacts and from frozen external dependencies.

No global coverage, unconditional zero proportion, website submission readiness, or new Lean decoder verification is asserted. All previously published Lean sources and generators remain frozen.
