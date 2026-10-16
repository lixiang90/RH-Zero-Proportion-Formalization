# Streaming checkpoint design: storage proposal only

No producer, running process, frozen numerical API or proof packet is
changed. No new search, LP or optimizer is run. This is a static design;
there is no implemented streaming producer or new mathematical closure.

The original session1700 returned live progress through130600 nodes. A
subsequent read-only, shared-handle header/tail inspection opened the
complete131500 checkpoint:908998905 bytes,65740 accepted leaves,21 pending
cells,125608 Newton steps and992616 OBBT bounds. The snapshot still binds
the verified117500 recovery copy. Only its header/tail were read; the
review does not claim a new full-file hash or semantic witness replay.
The companion JSON preserves the pending and maximal completed prefixes.
Broad siblings r1, r01, r0011 remain pending. A21-item DFS stack is not a
domain-volume or remaining-work percentage.

## What source inspection establishes

`window_compact_obbt_guarded_cover.py` keeps all accepted leaves, branches,
Newton maps and OBBT maps in Python containers for the whole run. After
resume, the831108505-byte `raw` object remains a local variable for the
whole main call. `old` also remains live, sharing its proof containers with
the active containers. Every500 nodes `save` constructs `json.dumps(out)`
for the entire accumulated document and writes another complete snapshot.
Encoding and filesystem writes create additional peak allocations.

There are also multiple200000-entry interval/Taylor caches, unbounded
`HINTS` maps keyed by interval, and caches declared with no size cap. Source
inspection cannot assign the parent's observed6.7GB RSS among these
objects, and neither RSS nor witness bytes can be extrapolated linearly to
the2M-node budget. The code nevertheless has an explicit accumulating
proof-store term and a repeated whole-document serialization term.

The existing `cover_compact_checkpoint.Stream`/`open_snapshot` reader can
reuse a stable atomic snapshot without loading it all. Its current
`convert` function still collects every output array/map, so that function
is not itself a bounded-memory migration. The compact-v2 codec already
preserves each unit's canonical decoded SHA and forest-flow encoding. Its
encoding can be retained without changing any mathematical witness.

## Proposed immutable baseline and node journal

Keep one immutable baseline manifest containing the source/parameter/root/
floor guards, counters, exact ordered frontier, and references to lossless
shards for each existing collection. Stream accepted/branch arrays and
Newton/OBBT/support map entries into shards. Baseline collections can stay
separate; this avoids a large in-memory path join. An optional on-disk path
index is an untrusted lookup accelerator. Every witness entry is retained.
Existing fully completed prefix subtrees can be indexed as immutable
groups, but they still need all ancestor branches and contractions. A list
of completed prefix names or a digest alone does not replace their proofs.

For subsequent work, keep only the current frontier, aggregate counters,
one active node's certificates, and a small output buffer in memory. After
a node is fully processed, emit one transaction containing its path/depth,
incoming-cell binding, all OBBT steps, all Newton steps, and exactly one
terminal leaf or split with its children. Preserve the actual order:
OBBT first, then Newton, then split/leaf on the refined cell. The unit still
proves preservation only for F<c and original global-minimum KKT points;
it must never be treated as a pointwise cover.

Seal a bounded buffer into an immutable shard with ordered sequence range,
previous-shard digest, raw digest, compressed digest, byte count and record
count. Target about3MiB raw and enforce a final compressed cap explicitly;
a single larger node must be preserved as a separately hashed blob or
framed across shards, never dropped. Support records must be durable before
or in the same transaction as their first reference. Keep their immutable
dictionary on disk and a bounded hot cache if needed.

Commit protocol: write and flush the new shards, atomically publish them,
then atomically replace the small frontier manifest naming their committed
high-water mark. Only after that manifest commit may the producer release
those witness objects. A crash before the manifest replacement leaves the
previous generation resumable. Unreferenced tail files are ignored or
fully replayed before adoption. Never combine a new frontier with missing
proof shards, and reject duplicate final node transactions.

A future resume loads only the manifest/frontier and counters; it does not
load all old witness collections. Shard publication and verification cost
then tracks newly produced bytes instead of rewriting the cumulative
document every500 nodes. This removes the proof-history component of heap
growth. It does not alone prove bounded total RSS: the unbounded interval
hint maps and large caches must also be addressed. To preserve discovery
inputs exactly, hint sets can be moved to an on-disk key/value store with
identical retrieval/order; simply deleting hints changes future LP choices.
Cache/hint policy changes are a separate future source change, not part of
this storage-only proposal.

## Replay and adoption obligations

An independent reader must verify all shard bytes/digests, sequence ranges,
input guards, exact frontier transitions and full tree accounting. It must
decode and pass every old unit through the existing mathematical verifiers:
sublevel OBBT, original-orthant KKT contraction, scalar/value/derivative
queries, exact flow, Gram membership, reflection and split geometry.
The existing `window_compact_obbt_replay.replay` loads complete maps; a new
bounded reader must use its checks per node, with a DFS stack or on-disk
index, while also rejecting unvisited/orphan proof records.

Hashes prove integrity, not mathematical validity. The previously frozen
117500 structural audit did not semantically replay its880632 OBBT bounds.
Using that snapshot as a baseline does not discharge this obligation. A
full final certificate must replay the baseline and every committed
continuation unit, then prove there is no remaining frontier and connect
the actual Lean minimizer-cover consumer. Until then all complete-cover
and new-zero-proportion flags remain false.

This design cannot reduce the already running process's heap from outside.
Adoption would require a separately reviewed producer and safe future
handoff from one immutable checkpoint, with one writer and an independently
checked baseline migration. No adoption, stop, restart, data deletion,
proof pruning or mathematical-checker change is authorized by this note.
