# Bounded proof-store prototype and adoption boundary

The old search is stopped. No new search or optimizer has been launched,
and no frozen main/math source has changed. This prototype changes storage
only. It is not a new cover checker, unconditional bound or Lean proof.

## Actual132000-node baseline

The importer opened one stable compact-v2 snapshot handle and bound all
912240992 source bytes to SHA
`2e50e2303ca3705ae9ba91e741764e84550c382049b88ae5cbd064247bba671d`.
It streamed65988 accepted leaves,66012 branches,23112 complete Newton
chains,89306 OBBT records,25 frontier cells and2540 support records. Every
complete compact unit is stored as canonical JSON bytes, with its SHA and
original section order/key. All nested data and the existing decoded-unit
SHA fields inside the compact codec are preserved. No mathematical
decoding or pruning is performed. The largest individual unit is25075bytes.

The baseline is a single SQLite transaction using synchronous=FULL,
journal_mode=DELETE,8MiB page cache, temp_store=FILE and mmap_size=0.
The final database name is published only after the complete transaction
commits. Original metadata is immutable. The initial frontier is retained
both as an immutable baseline collection and as a separate mutable working
table, so future node commits cannot erase the initial roundtrip boundary.

The local database is1091756032bytes. Import took45.01seconds and its
process peak working set was42762240bytes, about40.8MiB. This is a storage
importer measurement, not a prediction of a future producer's RSS: the
mathematical engines have their own caches and unbounded HINTS maps.

The independent replayer imports neither the store producer nor numerical
discovery modules. Its separate incremental JSON decoder re-read the
source and compared all246983 units, payloads, keys, order and unit hashes,
all small metadata and the exact initial frontier. It independently
recomputed the raw source SHA and whole canonical-document SHA, then
streamed the database to reconstruct that document SHA again. All matched:
`cf9e5d3e4618d3fdc96b37d6c6c5bb97ed5276cd290dc4e845f183f2365816e5`.
Source guards matched and SQLite integrity_check returned ok. Replay took
34.24seconds; its largest text buffer was284499characters. No whole
history, complete JSON serialization or giant output document was loaded.

Canonical roundtrip preserves all decoded JSON values and collection order;
it does not promise to reproduce the original whitespace or nested key
serialization byte-for-byte. The original full byte digest is retained as
provenance. SQLite physical-file SHA is local evidence, not a promise of
identical page layout on another SQLite version.

## Per-node transaction interface

`append_node(database, packet, root, expected_frontier_sha256=...)` checks
the baseline source guards, expected ordered frontier, incoming top-node
path/depth/cell hash and uniqueness. The packet supplies complete supports,
packed OBBT, packed Newton chain and either a packed leaf or a branch with
its children in the original append order. It inserts supports/witnesses
first, then changes frontier/counters and the hash-chained node journal,
all in the same SQLite commit. A caller may never treat a partially written
node as committed. The mathematical soundness of the packet remains the
caller's obligation; this API validates storage identities only.

The isolated toy suite passes12 tests, including a real subprocess
os._exit(77) before commit followed by SQLite recovery, injected failures
after witnesses and before commit, stale-frontier/source-guard rejection,
duplicate-node and conflicting-support rejection, identical support reuse,
atomic counters/frontier/witness updates, two successful commits, and
independent baseline roundtrip after those commits. Toy proof fields are
opaque placeholders and make no mathematical claim. The actual132000
database contains zero appended node transactions and is never used by
these tests.

## Remaining adoption work

This is not yet a replacement search producer. A separately pinned fork
must load only the runtime counters/frontier and connect the unchanged
mathematical discovery calls to complete node transactions. It must carry
the exact floor/root/source guards and remaining original budget1890500,
preserve OBBT-before-Newton ordering and all original RelevantBelow/KKT
semantics, and admit exactly one writer. The fork/store/consumer code must
be pinned in its own epoch; the original sources remain frozen.

A future proof reader must validate every mathematical packet with the
existing independent verifiers and audit the entire journal/frontier/tree,
not just storage hashes. Baseline semantic replay of125968 Newton steps
and996433 OBBT bounds remains outstanding. No existing whole-document
replayer becomes bounded-memory merely by pointing it at this database.
The runtime HINTS/cache policies also need review; proof-store boundedness
alone does not bound the mathematical engines' heap. Any performance
change to guard checks or hint retrieval needs its own review.

The crash tests cover process termination and ACID rollback, not every
power-loss/filesystem failure. The original JSON remains untouched. No
source deletion, OS-readonly transition, producer adoption, resumed search
or global proof completion occurs here. The1.09GB local database and912MB
source are excluded from the small publication pin.

## Reproduce on new output paths

```text
python -S -B -X utf8 research-goal-20261016/cover_sqlite_proof_store_test.py --folder NEW_TOY_FOLDER --receipt NEW_TOY_RECEIPT.json
python -S -B -X utf8 research-goal-20261016/cover_sqlite_proof_store.py SOURCE.json --database NEW.sqlite --expected-sha256 SOURCE_SHA --receipt NEW_IMPORT.json
python -S -B -X utf8 research-goal-20261016/cover_sqlite_proof_store_replay.py SOURCE.json --database NEW.sqlite --receipt NEW_REPLAY.json
```
