# A storage engine for Wiz: mmap'd snapshots, pure optics, commutative writes

Status: design + prototype, 2026-11-19. Base: `integration/train6` at
`66398557` (branch `storage-engine-design`, no PR; train6 is untouched). The
prototype is `drafts/storage-engine/` and typechecks with a `wiz` built from
train6 (see §12). No heavy build was used.

The shape this note is written to:

```wiz
do
  db  <- getDb handle                 -- IO: the latest snapshot
  let db' := over (lens \comp lens') (+1) db
  putDb handle db'                    -- IO: commit this transaction (or reject it)
```

Everything between `getDb` and `putDb` is pure. `Snapshot` is an immutable value;
`over` builds a new one; the transaction *is* the diff it carries. The core may
write pages under the hood, but nothing mutable is observable through the API.

---

## 0. The short version

* **Layout: an LMDB-style copy-on-write B+tree in one file, two meta slots, a
  read-only `mmap` for snapshots, `pwrite` + `fsync` for commits.** A commit
  appends new pages and switches a root pointer in the inactive meta slot. A
  snapshot is `(generation, root page)`; pages reachable from a live root are
  never overwritten. A logical append-only log is the *stepping stone* (slice 2)
  and the audit/replication record; it is not the read path.
* **Validation: per-key first-committer-wins for `set`/`del`, no version check
  for `add`/`append` deltas, plus a global delete epoch.** Two `+1`s from the
  same base both commit and sum; a `+1` and a `set`/`delete` on the same key
  conflict; any transaction that began before a delete is rejected by the epoch.
* **Optics: the existing store encoding, not profunctor optics.** `Store A S =
  A × (A → S)` already has the one place a write can be recorded: the backward
  function. The store's lenses' `put` records a `Patch` into the snapshot's
  write-set, so `Lens.over` produces the diff with no second pass. The note adds
  only two *new, clearly marked* pieces for this engine: a `Traversal`
  (`view`/`overAll`) for index updates, and a **linear `Cursor`** for queries.
* **Queries: a linear cursor.** `Cursor a` is consumed exactly once by `next`;
  the checker rejects duplication, use-after-`next`, and dropping the
  continuation. Index scans and table scans are the same `Cursor` type; the
  index→table composite is `Cursor.follow`. The prototype demonstrates the
  rejections and the accepted consumer.
* **Blockers:** slice 1 (this prototype) has none. Slice 2 (durable) is blocked
  on `fsync`; slice 3 (mmap) on `mmap` + a wide/unaligned load; multi-process on
  `flock`. `msync`/`ftruncate` are optional depending on the write path.

---

## 1. What the engine must guarantee

1. `getDb : Handle → IO Snapshot` and `putDb : Handle → Snapshot → IO Outcome`
   are the only IO. A `Snapshot` is an ordinary value; `over` is pure.
2. A snapshot is stable: once `getDb` returns it, its logical contents never
   change, however many commits happen afterwards.
3. Writes are either **append facts** or **commutative-monoid additions**.
   The engine never has to merge two non-commutative edits. A transaction that
   started before a delete (or another non-commutative edit on a key it touches
   or read) is rejected.
4. A commit is all-or-nothing and survives a crash at any point.
5. A secondary index is addressable by the update optics and the query cursor,
   and is itself derived (so it can be rebuilt and checked).

The design keeps (1)–(2) by construction, (3) by the validation rule in §3,
(4) by the commit protocol in §4, and (5) by the index derivation in §6.

---

## 2. On-disk and in-memory layout

### 2.1 The choice, and the alternatives

| option | reads | commits | snapshots | implementation cost | verdict |
|---|---|---|---|---|---|
| append-only logical log (event sourcing) | replay or in-memory index | one append + `fsync` | a log offset | smallest; open is O(log) unless checkpointed | **stepping stone (slice 2)**, not the final read path |
| **COW B+tree (LMDB)** | O(log n) directly from `mmap` | COW pages + root switch | root page number; pages immutable | medium; the LMDB shape is well understood | **chosen** |
| LSM tree | O(log n) with read amplification | append memtable, later compaction | needs a snapshot/compaction protocol | high; compaction interacts badly with long-lived snapshots | rejected |
| SQLite WAL/rollback | b-tree pages | WAL frames + checkpoint | readers on a WAL snapshot | would mean reimplementing SQLite's format and locking | rejected |

LMDB is the closest fit because it already has exactly the two properties this
task needs: **COW pages make a snapshot a root pointer**, and **two meta pages
make the root switch atomic**. It also has a single writer, which matches the
commit critical section; readers never block the writer and vice versa. The
design borrows LMDB's meta-page discipline and page COW, not its exact file
format.

The logical log is kept for two reasons: slice 2 is much easier to get right
before pages exist, and an audit/replication record is useful later. It is not
on the read path in the final layout.

**What `mmap` buys.** A page is a pointer plus an offset, so a read is a load,
not a syscall and a copy; the OS page cache is the cache, shared by every reader
of the file; a snapshot's root is just a page number, and pages reachable from a
live root are immutable, so two snapshots share every page they have in common;
adjacency and index pages are reachable at random without a read buffer. The
costs are also real: the mapping has a fixed length (map a maximum, or remap on
growth), truncating a mapped file raises `SIGBUS` (never shrink under a live
map), and writes are done with `pwrite` rather than through the shared mapping so
that the commit path does not depend on dirty-page writeback. `mmap` is a read
accelerator here, not the durability mechanism.

### 2.2 Files and pages

One file, little-endian:

```
+------------------------------------------------------------------+
| page 0: meta slot A (64 B) | page 1: meta slot B (64 B) | pad      |
+------------------------------------------------------------------+
| page 2 ..: COW B+tree pages (primary), index pages, free-list pages|
| optional: contiguous log segments (audit / slice-2 store)          |
+------------------------------------------------------------------+
```

* **Page size 4096 B.** A page is the unit of COW, checksum, and `mmap` access.
* **Page header (32 B):**

  ```text
  0  u16 kind       (leaf, internal, index-leaf, index-internal, free, log, meta)
  2  u16 n          (entries used)
  4  u16 free       (first free byte / slot)
  6  u16 flags
  8  u64 txid       (the generation that wrote this page)
  16 u64 checksum   (over the page with this field zeroed)
  24 u32 right      (right sibling for leaves, 0 for none)
  28 u32 reserved
  ```

* **Primary leaf payload:** a sorted array of fixed-size entries, `32 B` each:

  ```text
  key: u64 node id
  kind: u32
  label: u32
  count: u64
  version: u64        (the generation of the last write to this key)
  ```

  `4096 − 32 = 4064`; `4064 / 32 = 127` entries per leaf. The node id is the
  key, so it is not repeated; the record is 32 B, a power of two, and a leaf
  slot is at `32 + i*32` — aligned and cache-friendly.
* **Primary internal payload:** `(key u64, child page u32, pad u32)` = 16 B;
  254 children per page.
* **Index leaf:** `(value u64, node u64)` = 16 B for a non-unique index;
  `(value u64)` = 8 B with the node id in the value slot for a unique index.
  Index internal pages are the same shape as primary internal pages.
* **Fixed-size nodes, separate adjacency.** A flatgraph node is fixed-size (the
  32 B record above). Edges are a separate ordered map keyed by
  `(src u64, edge_kind u32, ordinal u32) → dst u64`, i.e. one more B+tree, or a
  per-node fixed-size edge block chained by page number. Keeping adjacency out
  of the node record means a counter update rewrites one 32 B record, not a
  variable-length neighbour list. This is the flatgraph idea (fixed-size nodes,
  offsets) inside a COW B+tree.
* **Why not struct-of-arrays?** `lib/Scry/Store.wiz` keeps relations as columns
  and indexes as `U64Map`s; that is excellent for scans. For a mutable store,
  a node update in SoA touches one slot in each of four arrays (four pages, four
  COW copies, four checksums). Slice 3 uses record-per-node; a columnar
  **read-only** projection can be an index/derived structure later, built by the
  same recompute path as an index.

### 2.3 Meta pages

Two 64-byte slots in page 0, written alternately:

```text
magic u64 | format u32 | flags u32 | txid u64 | root u64 | index_root u64
freelist_root u64 | log_end u64 | del_epoch u64 | min_gen u64
schema_gen u64 | page_count u64 | checksum u64
```

* `txid` is the generation/snapshot id, strictly increasing.
* `root` is the primary B+tree root page; `index_root` is the root of the index
  registry (or the first index tree; the registry is a small B+tree keyed by
  index id, value = root page).
* `freelist_root` is the free-page B+tree (empty in the never-reuse slice).
* `log_end` is the byte offset of the last committed log record (slice 2/audit).
* `del_epoch` is the generation of the last delete (§3).
* `min_gen` is the oldest retained snapshot (never-reuse: 0).
* `checksum` is over the slot with the field zeroed.

The writer reads both slots, ignores a bad magic/checksum, and takes the valid
slot with the larger `txid`. The newer slot is never the one being read.

### 2.4 A snapshot is a root pointer

```wiz
structure Snapshot where
  gen : U64          -- txid at getDb
  root : Root        -- production: { map : Map, page : U64 }; prototype: U64Map Node
  ws : WriteSet      -- the pending diff (empty after getDb)
```

`getDb` returns the current `(txid, root)` with an empty `ws`. `over` extends
`ws`. `putDb` validates `ws` against the current meta and, on success, publishes
a new root at `txid+1`. A snapshot's root is immutable: COW never overwrites a
page reachable from it.

In the production engine `Root` is `{ map : Map, page : U64 }` where `Map` is a
read-only `mmap` handle (an ω `foreign_type`). `Snapshot` is still a value; the
map is reference-counted, so a snapshot keeps its mapping alive. The handle maps
a configured maximum (or remaps when `page_count` passes the mapped length); an
old snapshot keeps the old map, so a growth never invalidates it. The prototype's
`Root` is a `U64Map Node`, so the API and the optics are identical and the mmap
move is invisible.

### 2.5 Free space: append, compact, or lease

Three policies, in order of increasing machinery:

1. **Never reuse (recommended for the first mmap slice).** Pages are appended;
   old roots and old snapshots are valid forever. File growth is the cost.
   **Compaction**: write a new file containing only live pages, `fsync`, `rename`
   over the path, `fsync` the directory. A reader with an open mapping keeps the
   old inode (POSIX), so its snapshot survives; new `getDb`s open the new file.
   This is sound with pure snapshot values and no finalisers.
2. **Keep the last K roots.** The meta stores `min_gen`; pages reachable from
   any of the last K roots are live; older pages go on the free list. A snapshot
   older than `min_gen` is invalid; `putDb` returns `Expired`, and a read through
   it is outside the contract. K is small (8–16) because a transaction holds a
   snapshot for its duration.
3. **Snapshot leases.** A `Snapshot` carries an ω `foreign_type` lease whose
   finaliser decrements a reader count; a page is reusable when no lease from
   before its death is alive. This is the full solution, and it is compatible
   with the pure API (the value is still immutable; the lease is resource
   management). It needs the finaliser/RC behaviour in compiled code, which Wiz
   has for `foreign_type` (`File`, `Fd`).

Slice 3 starts with (1); (2) is a bounded optimisation; (3) is the end state.

### 2.6 Checksums

* Page checksum: FNV-1a-64 (prototype) or xxHash64/CRC32C (native) over the page
  with the checksum field zeroed.
* Meta checksum: the same over the 64-byte slot.
* Log record: a CRC over the record; a torn tail is discarded at `log_end`.
* Verify lazily on first touch of a page in a snapshot, cache the result per
  `(snapshot, page)`. A mismatch is `Corrupt(page)`, not silent data. A full
  tree verification on open is O(pages) and optional; the meta/root chain is
  verified on every open.

---

## 3. Snapshots and validation

### 3.1 What is compared

* Each key (node id) has a **version**: the generation of the last write that
  touched it. It is stored inline in the 32 B record and is not erased when the
  record is deleted (the prototype's `Root.versions` map is a tombstone by
  another name). After a delete, the key keeps its last version for the
  retention horizon, so a stale `set` can be told from a fresh one.
* A transaction's `Snapshot` records `gen` (its base) and `ws` (the diff). A
  slice-1 addition records the **read-set**: every key the transaction read,
  with the version observed. `getNode`/`nodeAt`/a cursor can add to it.
* The write-set is a map `key → Patch`, where

  ```wiz
  inductive Patch where
    | set (node : Node)      -- overwrite: computed from a read
    | addCount (d : U64)     -- delta: independent of the read
    | del                    -- non-commutative with everything
  ```

### 3.2 The rule, in one paragraph

> `putDb` commits a transaction iff **(i)** its base generation is not below the
> delete epoch (`tx.gen ≥ del_epoch`), so no delete committed after the
> transaction began; **(ii)** for every key it `set`s or `del`s, the key's
> current version equals the version recorded in the transaction's base (per-key
> first-committer-wins); and **(iii)** every `add`/`append` is a pure delta and
> is applied to the key's *current* value without a version test, so two `+1`s
> from the same base both commit and sum. A `set` whose value was computed from
> a stale read is rejected even when the concurrent changes were themselves
> commutative; a transaction consisting only of deltas never conflicts on an
existing key when no delete has intervened. With a
> read-set, a transaction that contains a `set`/`del` additionally requires
> every read key's version to be unchanged. A unique-index collision is a fourth
> rejection, not a merge. The check is one pure function, `firstError`, called
> once in the single-writer critical section of `putDb`.

The global delete epoch is the conservative reading of the owner's rule: a
transaction that started before *a delete anywhere* is rejected, even if it
touches other keys. It costs one word in the meta and one comparison. The
per-key refinement (a tombstone per key, no global epoch) is a later slice; it
lets unrelated transactions proceed through a delete. The epoch is kept in
slice 1 because it is cheap and it makes the "started before a delete" rejection
unconditional.

### 3.3 What the commutative monoid buys

* `+1` and `+1` commute: both are `addCount 1`; commit 1 writes the value, commit
  2 reads the current value and adds 1. The final value is the sum.
* `+1` and `set` do not: the `set` overwrites whatever the add produced (or the
  add lands on the set); the engine cannot know which the user meant, so it
  rejects the stale one.
* `+1` and `delete` do not: add-after-delete and delete-after-add differ.
* `append` and `append` commute; `set-union` and `set-union` commute; `max` and
  `max` commute. The engine's merge is the monoid action for these, and a
  version check for everything else.

**Important contract for `over (+1)`.** A generic `A → A` is not a delta. The
prototype's `Patch.ofChange` records `addCount (new − old)` when only the counter
grew, because the demo's update is a translation. That inference is sound only
for translations: `f x = 2*x` from 3 records `+3`, and a concurrent `+1` would
produce 7, not 8. The production rule should be explicit: **a delta is produced
only by a delta-aware combinator** (`overAdd`/`append`/`union`), and a generic
`over` records a `set` (always safe, never merged). The owner's `over (+1)` is a
translation and is safe; the note recommends spelling it `overAdd l 1` (or
documenting the translation invariant on the lens) so the engine never has to
guess. The prototype keeps `ofChange` to show the mechanism; §12's evals use it
only with translations.

### 3.4 Where the check lives

`putDb` is the only place. It does, in order:

1. acquire the single-writer lock;
2. read the current meta (validate both slots, take the max `txid`);
3. run the pure `firstError`/`validate` on `(current, tx)`;
4. derive the index delta and check unique keys;
5. write the new pages / log record, `fsync`;
6. write the inactive meta, `fsync`;
7. publish `txid` to readers, release the lock.

The pure function is shared by the in-memory prototype (`Db.commit`) and the
real engine; the IO shell is thin. A rejection returns `Outcome.rejected e`
(`stale`, `conflict`, `missing`, `duplicate`, `io`); the caller can re-read with
`getDb` and re-run its pure function, because a `Snapshot` is reusable.

### 3.5 Read-set correctness

A `set` computed from a *different* key's stale read is not caught by the
write-set version check. Example: read node B's `kind`, decide node A's `label`.
If B changes, A's set is stale. Fix: the transaction's read-set records
`(key, version)` for every read that influenced a non-delta op; `putDb` rejects
if any read version changed. Deltas do not need it: their value is independent
of the read (under the translation contract). The prototype omits the read-set
(the owner's example reads only the focus); slice 1 adds it. The cursor is the
natural place to collect it (the plan knows what it read).

---

## 4. Durability and atomicity

### 4.1 The commit protocol

```text
0. open + flock(LOCK_EX)                       (single writer)
1. read meta A/B; pick max valid (magic + checksum)
2. validate (pure)                              -> reject, or a plan
3. allocate pages: bump page_count, or pop freelist
4. build pages in memory; pwrite each at page*4096
5. pwrite the log/commit record (write-set + txid + base + checksum)
6. fdatasync(fd)                                (pages + log durable)
7. pwrite the inactive meta: txid+1, new roots, log_end', del_epoch'
8. fdatasync(fd)                                (commit point durable)
9. publish txid (seqlock/atomic), unlock
```

The **meta write is the commit point**. The log record is optional for
correctness (the tree is the state) but is the audit/replication record and the
slice-2 store. The two `fdatasync`s are deliberate: a filesystem may reorder
data and metadata; the first makes the pages durable before the root that
points at them, the second makes the switch durable.

### 4.2 Crash cases

| # | crash point | on-disk state | recovery | outcome |
|---|---|---|---|---|
| 1 | before step 4 | old meta, old pages | nothing | old state |
| 2 | during a page write (step 4) | torn page, unreachable | old meta; page leaked | old state |
| 3 | after pages, before log/meta | new pages, old meta | old meta; pages leaked | old state |
| 4 | during the log record (step 5) | CRC bad, `log_end` unchanged | truncate at `log_end` | old state |
| 5 | after log, before meta | complete record, old meta | `log_end` says not committed; ignore/truncate | old state |
| 6 | during the meta write (step 7) | one slot torn (checksum fails) | take the other valid slot | old or new, never mixed |
| 7 | after meta, before fsync (step 8) | old or new meta on disk | valid slot with max txid; a torn new slot fails checksum | old or new, never mixed |
| 8 | after step 8, before publish | new meta durable | open sees the new meta; a live reader still has the old root | new state; old reader unaffected |
| 9 | crash during freelist write | stale freelist | rebuild the freelist by scanning roots, or ignore and append | new state, space leaked |
| 10 | file growth / truncate | file shorter/longer | never shrink under a live map; `ftruncate` only grows | no SIGBUS |
| 11 | new file / rename | directory entry not durable | `fsync` the parent after create/rename | file exists or not, atomically |
| 12 | two writers | one loses the lock | `flock` is released on crash; re-read the meta inside the lock to detect a stale view | one commit wins (all writers must use the lock; a non-cooperating process is outside the contract) |

A torn page that was **published** (step 8 succeeded) can only be a later media
fault; the page checksum detects it and the snapshot is `Corrupt(page)`. Falling
back to the previous meta slot is possible if the previous root is still live;
otherwise the last checkpoint/backup is the recovery point. This is a stronger
contract than LMDB's (which trusts the filesystem's sector atomicity and does not
checksum pages), and it is cheap enough at 4 KiB.

### 4.3 Recovery

Open, map the header, read both metas, take the max valid `txid`, verify the
root page checksum, and (slice 2) replay the log from `log_end` if the tree is
behind. A torn log tail is truncated at `log_end`. The freelist is rebuilt if
its root/checksum is invalid. No `fsck` of the whole tree on the happy path.

### 4.4 Atomic root switch

Two slots, alternating by `txid % 2`; never overwrite the slot that was used to
read the current state. A slot is valid iff magic + checksum pass. Readers use a
seqlock around the 64-byte read (or an aligned 8-byte `txid` load plus a
re-read), so they never see a half-written root. The writer writes through
`pwrite`, not through the readers' map; page-cache coherence makes the new
bytes visible after the write.

### 4.5 What Wiz can express today

* `Fd.open` (`lib/Sys.wiz:715`), `Fd.seek` (`:805`), `Fd.readExactly` (`:776`),
  `Fd.write` (`:793`), `Fd.close` (`:723`), `Fd` is a `foreign_type` with a
  finaliser (`:641`). This is enough to **write and read an append-only file**.
* `FS.writeFile`/`FS.writeBytes` (`:255`, `:261`) truncate the whole file; not a
  page write. `File.flush` (`:314`) is `fflush`, not `fsync`; `Fd` has no
  durability op. `Bytes` has `push`/`get`/`slice`/`append` but **no `set`**
  (`lib/IO.wiz:245–271`); a page is built by appending, not by random writes.
* `U8Array`/`U32Array`/`U64Array` (`lib/WordArray.wiz:76`, `:144`, `:212`) are
  in-place when unique and have `set`; they are the natural page builder.
  `wiz_warray_of_c` (`runtime/rt_data.inc:496`) **copies** C memory into a new
  array; there is no non-owning view.
* There is no `mmap`, `msync`, `fsync`, `ftruncate`, `flock`, `pread`/`pwrite`,
  or raw atomic load/store. **`fsync` is the one that blocks a durable slice;
  `mmap` is the one that blocks the fast read path.**

---

## 5. The optic API

### 5.1 The premise, corrected

`lib/Optic.wiz` (train6) is a **store encoding**, not profunctor optics:

* `Store A S := A × (A → S)` (`:43`);
* `Lens S A := S → Store A S` (`:71`);
* `PLens S A := S → Result (Store A S)` (`:74`) — the `P` is **partial**, not
  profunctor;
* `ALens`/`Affine` for the 0-or-1 case (`:124`, `:129`);
* `zoom`, `zoomP`, `List.atL`, `List.headL`, `Lens.comp`, `Lens.over`,
  `Lens.toP`, `PLens.comp`, the law bundles (`:83`, `:87`, `:90`, `:93`, `:106`,
  `:373`).

There is no `Profunctor`, `Strong`, `Choice`, `Wandering`, `Traversal`, `Prism`,
`Iso`, or `Const`/`Tagged`/`Forget` in the library. There is one interpretation:
**apply the update**. `lib/OpticDerive.wiz` (`:88`, `:100`) derives field lenses
and their laws. This note does not describe the library as profunctor optics.

### 5.2 The chosen route: work inside the store encoding

The `Store` type already contains the one place a write can be recorded: the
backward function `A → S`. The store's lens for a node is a `Store` whose
backward function records a patch:

```wiz
inductive Patch where
  | set (node : Node)
  | addCount (d : U64)
  | del

def WriteSet : Type := U64Map Patch

structure Snapshot where
  gen : U64
  root : Root
  ws : WriteSet

def Snapshot.getNode (s : Snapshot) (id : U64) : Option Node :=
  match U64Map.find s.ws id with
  | .some p => Patch.apply p (U64Map.find s.root.pages id)
  | .none => U64Map.find s.root.pages id

def Snapshot.record (s : Snapshot) (id : U64) (p : Option Patch) : Snapshot :=
  match p with
  | .none => s
  | .some q => { s with ws := WriteSet.combine s.ws id q }

/-- The place of an existing node: a partial lens that records. -/
def nodeAt (id : U64) : PLens Snapshot Node := fun s =>
  match Snapshot.getNode s id with
  | .none => .err .outOfBounds
  | .some n => .ok (n, fun n' => Snapshot.record s id (Patch.ofChange n n'))

/-- A total lens with a default (create-on-first-write); lawful on existing nodes. -/
def nodeOr (id : U64) (d : Node) : Lens Snapshot Node := fun s => ...
```

`Lens.over` (`lib/Optic.wiz:83`) is unchanged:

```wiz
def Lens.over {S A : Type} (l : Lens S A) (f : A → A) (s : S) : S :=
  let st := l s;
  st.2 (f st.1)
```

so the owner's shape typechecks as

```wiz
def bumpCount (id : U64) (s : Snapshot) : Snapshot :=
  Lens.over (Lens.comp (nodeOr id (Node.mk 0 0 0)) Node.countL) (fun c => c + 1) s
```

`Lens.comp` composes the backward functions (`:87`), so a deep path records one
**record-level** patch at the outermost store lens, not one per field. For a
partial place, add the six-line `PLens.over` (the prototype does):

```wiz
def PLens.over {S A : Type} (l : PLens S A) (f : A → A) (s : S) : Result S :=
  match l s with
  | .ok st => .ok (st.2 (f st.1))
  | .err e => .err e
```

`Affine.over` (`lib/Optic.wiz:136`) already returns the lender unchanged on
`none`, so an optional update is a no-op without a `Result`.

**No second pass.** The write-set is accumulated *as the optics run*, in the
`Store`'s backward function; the engine never diffs the whole state. This is the
answer to "can `over` be recorded as an op": yes, because the store encoding's
backward function is the recording point. It does not need `Strong`/`Choice`; it
needs the snapshot to carry the writer monoid.

**Laws.** `nodeAt` preserves GetPut because `Patch.ofChange old old = none` and
`Snapshot.record` with `none` returns the snapshot unchanged; PutGet because
`getNode` applies the recorded patch; PutPut because `Patch.seq` composes
patches sequentially (`add` + `add`, `set` absorbs, `del` absorbs). The
prototype does not prove these; the tests in §11 are the check. `nodeOr` is
lawful on existing nodes; on a missing node it creates one, so it is a
create-on-write lens, not a lawful total lens for the empty case.

### 5.3 The new pieces this engine adds (not claims about the library)

The store encoding has no pure `Traversal` and no query cursor. The note adds
two small, engine-local types:

```wiz
/-- A read-and-update traversal over every focus matching a predicate. -/
structure Traversal (S A : Type) where
  view : S → List A
  overAll : (A → A) → S → S

/-- The nodes in an index bucket, as a traversal (index updates). -/
def indexTraversal (d : IndexDef) (v : U64) : Traversal Snapshot Node

/-- A linear query cursor (see §7). -/
inductive Cursor (a : Type) where
  | private mk (rest : List a)
```

`Traversal` is the ω update path (`overAll` records one patch per matched node);
`Cursor` is the 1 read path. They are deliberately separate: an update needs an
ω write-set that can be merged, a query needs a single consumer that can stop
early.

### 5.4 The profunctor layer, if the owner wants it later

A profunctor presentation (`Strong` for lenses, `Choice` for prisms,
`Wandering` for traversals) would buy one `over`/`view`/`toList` for every optic
shape and a uniform composition story. It is **new work**, not present:

* the classes and their laws (`Strong`/`Choice`/`Wandering` coherence);
* a second interpretation (`Forget`/`Const`) for `view`/`toList`, which the
  store encoding does not have;
* a conversion from the existing `Lens`/`PLens` values;
* for indexed traversals, the index algebra: a composite traversal's index is
  the *pair* of indices, and an arbitrary index-combining function cannot be
  inverted (the `IxTraverse` lesson in `wiz-notes/indexed-optics.md`).

`Wandering` is the piece the index query most plausibly wants ("every entry
matching a predicate"). Cost: `Traversal` is where the lens laws stop being
enough; the coherence obligation is that the traversal's membership is stable
under the update (otherwise the index must be re-derived), and composition must
pair indices. **Slice 1 does not need it**: the hand-rolled `Traversal` and the
linear `Cursor` cover the update and query halves. Slice 4 may promote them if a
second consumer appears. The note's recommendation is to keep the store
encoding and add the profunctor layer only with a measured second use.

---

## 6. Indices

### 6.1 Primary vs secondary

* **Primary:** B+tree keyed by node id; value = the 32 B node record. This is the
  table.
* **Secondary:** one B+tree per index. Non-unique key = `(value u64, node id
  u64)`; unique key = `value u64`, value = node id. The index registry is a
  small B+tree `index id → root page`, in the meta/root.
* **Naming:** `IndexDef` is the schema entry; the optic takes the definition, not
  a string:

  ```wiz
  structure IndexDef where
    id : U32        -- schema number
    field : U32     -- 0 kind, 1 count, 2 label
    unique : Bool

  def indexTraversal (d : IndexDef) (v : U64) : Traversal Snapshot Node
  def Snapshot.indexNodes (d : IndexDef) (v : U64) (s : Snapshot) : Cursor Node
  ```

  A string name is parsed once by the schema loader and interned (`lib/Intern.wiz`
  is the precedent); the runtime uses the `U32`.

### 6.2 An index entry is a fact; a delete is a tombstone

**Log-only slice.** An index entry is an immutable fact

```text
(txid, op ∈ {add, remove}, index id, key, node id)
```

The live index at snapshot `T` is the fold of facts with `txid ≤ T`; a delete is
a `remove` fact (a tombstone), and `add`/`remove` are sets. `added`/`removed`
with set union is a commutative monoid, which is why the index can be replayed
and merged. This is the `IndexDelta` of the prototype:

```wiz
structure IndexDelta where
  added : List (U64 × U64 × U64)    -- (index, key, node)
  removed : List (U64 × U64 × U64)

def IndexDelta.empty : IndexDelta
def IndexDelta.combine (a b : IndexDelta) : IndexDelta
```

**COW slice.** The index B+tree at a root is the materialised fold. A commit
writes a new leaf without the removed entry; the old root keeps the old entry,
so an old snapshot still sees it. No in-place tombstone is needed in the tree;
the tombstone is the `-` fact in the log (and the deleted key's retained
version). This is the key difference from a mutable index: nothing is ever
overwritten.

### 6.3 Incremental vs recompute

* **Incremental** (the commit path): for every primary `set`/`del`/`add` whose
  indexed field changes, remove the old key and add the new one. O(changes ×
  log n), one write-set derivation, no scan.
* **Recompute** (the repair/schema path): scan the primary tree and rebuild one
  index. `Root.rebuildIndex` in the prototype. Use it at open after a crash, when
  an index is added, and in compaction; compare the recomputed index with the
  incremental one as a consistency check.

The index is **derived**: the primary write-set is the source of truth; the
index delta is a pure function of it and the old/new records. If the two ever
disagree, recompute wins and the incremental path has a bug.

### 6.4 Uniqueness

A unique index is a partial function `key → node`. At commit, for each changed
record, look up the target key's bucket excluding the same node; a hit is
`duplicate` and the commit is rejected. The prototype checks each op against the
current root only; a production check must also fold the transaction's own writes
into a temporary key set, so two nodes moving to the same unique key in one
transaction are caught. (Slice-1 test.) A unique index on a delta field (a
counter) is allowed, but a concurrent `+1` that would make two counters collide
is rejected rather than merged; that is the price of uniqueness. A unique index
on an immutable field (kind, label) is the easy case.

### 6.5 Index traversal and cursor

```wiz
-- ω update: every node in the bucket
def bumpOfKind (v : U64) (s : Snapshot) : Snapshot :=
  Traversal.overAll (indexTraversal kindIndex v)
    (fun n => { n with count := n.count + 1 }) s

-- 1 query: the same bucket as a streaming cursor
def Snapshot.indexNodes (d : IndexDef) (v : U64) (s : Snapshot) : Cursor Node :=
  Cursor.follow s (Snapshot.indexCursor d v s)
```

Within a transaction, primary reads see the write-set overlay; an index bucket
read still sees the base bucket, so a node whose indexed field changed is not
re-bucketed until commit. Slice 1 accepts this (read-your-writes for the
primary, not for the secondary); slice 4 can keep an in-transaction index
overlay or re-derive the bucket from the primary predicate.

`indexTraversal` materialises the bucket's node ids and folds; `indexNodes` is
the same `Cursor` type; the prototype materialises the bucket, while the
production plan streams index leaf pages. Both go through the same
`IndexDef`; the composite "index → primary" is `Cursor.follow`.

---

## 7. Queries as linear cursors

### 7.1 Why linear

A query plan has one consumer. If the cursor is a linear value, the type checker
enforces that: no duplicate reads, no use after the plan advanced, no silent
materialisation to serve a second consumer. That is what lets the engine commit
to a streaming plan, an index-only scan, predicate pushdown, and early exit
without defending against aliasing.

Wiz already has the style: linear pairs are taken apart with `let 1`
(`docs/stages/04-data.md:48–57`), a linear resource is threaded through a
continuation (`lib/MVar.wiz:54–69`), and an inductive with a private constructor
can be taken apart at 1 (`Uniq`/`Result1`, `lib/Region.wiz:102`, `:106`).

### 7.2 The types

```wiz
/-- A cursor over `a`: a linear handle around the plan's state. -/
inductive Cursor (a : Type) where
  | private mk (rest : List a)

/-- The end, or a value and the linear continuation. `Option` would not do:
its payload is unrestricted, so it could drop or duplicate the cursor. -/
inductive Step (a : Type) where
  | done
  | more (value : a) (1 next : Cursor a)

def Cursor.next {a : Type} (1 c : Cursor a) : Step a
def Cursor.close {a : Type} (1 c : Cursor a) : Unit

/-- Early exit: stop, or keep going. -/
inductive Control (b : Type) where
  | stop (b : b)
  | go (b : b)

def Cursor.foldUntil {a b : Type} (1 c : Cursor a)
  (k : b → a → Control b) (b0 : b) : b
```

`Cursor` is an inductive, not a structure: a structure held at 1 cannot be
projected or taken apart (`docs/stages/04-data.md:69–76`), while an inductive
can (`Uniq` is the precedent). The plan's state (`rest` here) is ordinary ω
data; the handle is what is linear.

### 7.3 Exactly one consumer, checked

`drafts/storage-engine/CursorReject.wiz` contains three bad definitions and one
good one. `wiz check` says:

```text
CursorReject.wiz:11:1: error: variable c declared with quantity 1 but used ω
  (a linear variable, of quantity 1, must be used exactly once, and c is used more than once)
CursorReject.wiz:15:1: error: variable c declared with quantity 1 but used ω
  (a linear variable, of quantity 1, must be used exactly once, and c is used more than once)
CursorReject.wiz:20:1: error: variable next declared with quantity 1 but used 0
  (a linear variable, of quantity 1, must be used exactly once, and next is not used)
CursorReject.wiz:32:1: error: cannot project p.1: a projection needs an unrestricted pair
  (it keeps one component and drops the other), but this one uses p, which has quantity 1;
  take the pair apart with `let 1 (x, y) := p; …` instead
```

The three bad cases are `badDup` (`Cursor.next c` twice), `badAfter` (use after
`next`), and `badDrop` (match `.more x _`, dropping the linear continuation).
The accepted `goodFirst` matches `.more x c'` and consumes `c'` once with
`Cursor.closeThen`. `goodPair` takes a linear pair apart with `let 1 (x, c) := p`
and is accepted; `badProj` (`p.1`) is rejected. The checker's message is exact:
`c is used more than once` / `next is not used`.

### 7.4 Pure

`Cursor.next` and `Cursor.foldUntil` are pure: the plan reads the snapshot's
immutable page state. With mmap, the read is a pure `Map.getU64` (a trusted
read of a read-only mapping, like `Bytes.get`); the map is created by `getDb`
and kept alive by the snapshot's ω `Map` handle. The only IO remains `getDb`
and `putDb`. Slice 1 is list-backed, so the same shape moves to mmap without
changing the API.

### 7.5 What linearity buys, and what is real now

| property | slice 1 (list-backed) | final (mmap) |
|---|---|---|
| exactly one consumer | **real** (checker rejects duplicates/drops) | real |
| early exit | **real** (`Control.stop`; `foldUntil` stops) | real |
| streaming | type-level only (the list is materialised) | real (page-by-page) |
| single pass, no result list | **real** (`foldUntil`) | real |
| index-only scan | aspiration (bucket materialised) | real if the index leaf carries the payload |
| predicate pushdown | aspiration (the plan has no predicate state yet) | real (predicate in the plan/state) |
| no clone on fork | **real** (a linear value cannot be copied) | real |

The linearity is not a performance claim by itself; it is the *permission* for
the engine to use an optimised plan. In slice 1 only the single-consumer and
early-exit guarantees are exercised; the streaming/index-only/pushdown wins are
slice 4.

### 7.6 Index and table are the same cursor

```wiz
def Snapshot.tableCursor (s : Snapshot) : Cursor Node
def Snapshot.indexCursor (d : IndexDef) (v : U64) (s : Snapshot) : Cursor U64
def Cursor.follow (s : Snapshot) (1 c : Cursor U64) : Cursor Node
def Snapshot.indexNodes (d : IndexDef) (v : U64) (s : Snapshot) : Cursor Node :=
  Cursor.follow s (Snapshot.indexCursor d v s)
```

* A table scan is `Cursor Node`.
* An index scan is `Cursor U64` (primary keys); `Cursor.follow` is the composite
  optic that turns it into `Cursor Node` (the index→primary lookup).
* An index-only scan is the same `Cursor U64` with the projection done in the
  plan, no `follow`; it is the same type, not a special case.

The update half is different on purpose: `Traversal` is an ω value with
`overAll`; `Cursor` is a 1 handle with `next`. A `Cursor` cannot be captured by
`over`/`zoom` (a function is ω; a linear value cannot be closed over by an ω
function). If a query must drive an update, use `Traversal.overAll` (ω) or a
linear fold whose state includes the write-set; the latter is new work.

### 7.7 `let 1`, `over`, `zoom`, and what is ω

* `Snapshot` is **ω**: it is an ordinary value and can be copied or dropped.
  `over` and `zoom` take ω lenses; the transaction is not linear.
* `Cursor` is **1**. `Snapshot.tableCursor s` creates a linear cursor from an ω
  snapshot; consuming the cursor does not consume the snapshot.
* `let 1 (x, c) := p; …` is how a linear pair is taken apart; `p.1` is rejected
  (see §7.3). `Step`/`Control` are bespoke because `Option`/`List` are ω.
* `zoom` (`lib/Optic.wiz:106`) runs a state transformer on a place of an ω
  lender; it is the right combinator for a pure update. It cannot thread a
  cursor. A linear `zoom` would be new work (`Uniq.zoom` exists for the linear
  handle case, `lib/Region.wiz`, but not for cursors).

### 7.8 What is missing for linear fields

* Structures at 1 cannot be taken apart (`docs/stages/04-data.md:69–76`); use an
  inductive (`Uniq`, `Result1`). Already supported; no addition.
* **Recursive consumers that thread the linear handle are rejected today.** A
  `partial def` that recurses on `c'` reports `c ... used 0`; the equation form
  reports `next ... used ω`. The workaround is to match the handle once into an
  ω plan state and recurse on that (`Cursor.fold`/`foldUntil`, §7.2). The
  smallest addition for user-written streaming loops is a **linear fixpoint
  rule** (a recursive call may consume a linear argument exactly once), or a
  built-in `Cursor.fold`/`foldUntil` in the storage library. Slice 1 does not
  need it; slice 4's engine should ship `fold`/`foldUntil` as the public loop.
* `Option`/`List` payloads are ω, so a linear element cannot live in them; use
  `Step`/`Control` or `Result1`/`ResultH`. A generic `LinearOption` would be a
  convenience, not a blocker.

---

## 8. The native surface

All of this is `runtime/` C plus `extern` declarations, following the
`foreign_type`/`implemented_by` pattern of `docs/stages/29-natives.md:12–20`.
The `Fd` handle is already a `foreign_type` (`lib/Sys.wiz:641`), so a new
`rt_storage.inc` can reuse its `wiz_sys_fdh` (`runtime/rt_sys.inc:957`).

### 8.1 The list

| native | why | size | blocks |
|---|---|---|---|
| `fsync`/`fdatasync` | durability of pages/log/meta | ~8 lines | **slice 2** |
| `mmap`/`munmap` | zero-copy read-only pages | ~40 lines | slice 3 read path |
| `get_u64` on a `Map` (optionally `get_u32`) | unaligned/wide reads | ~20 lines | slice 3 (with mmap) |
| `ftruncate` | reserve/grow the file before mapping | ~6 lines | optional (write grows) |
| `msync` | only if writing through the map | ~6 lines | optional (we `pwrite`) |
| `flock` | single writer across processes | ~8 lines | multi-process |
| `set_u64` on a `Map` | in-place page writes (if not `pwrite`) | ~15 lines | optional |
| `crc32c`/xxHash | fast page checksums | ~30 lines | optional (Wiz FNV works) |

The **one that blocks a durable store is `fsync`**. The **one that blocks the
fast read path is `mmap`** (with `get_u64`). `msync`/`ftruncate` are not needed
for the chosen `pwrite` commit path. `flock` is needed only for multi-process;
a single writer in one process can use a `MVar`/lock from `lib/Conc.wiz`, but a
crash-safe multi-process store should use `flock`.

### 8.2 C sketch

```c
/* runtime/rt_storage.inc -- the store's four primitives. */
typedef struct { void *addr; size_t len; } wiz_store_map;

WIZ_API uint64_t wiz_store_fsync(void *p) {
  wiz_sys_fdh *h = (wiz_sys_fdh *)p;
  if (h->fd < 0) { wiz_sys_err = EBADF; return 0; }
  return fsync(h->fd) == 0 ? 0 : (uint64_t)errno;        /* 0 or errno */
}
WIZ_API uint64_t wiz_store_ftruncate(void *p, uint64_t n) {
  wiz_sys_fdh *h = (wiz_sys_fdh *)p;
  return ftruncate(h->fd, (off_t)n) == 0 ? 0 : (uint64_t)errno;
}
WIZ_API void *wiz_store_mmap_ro(void *p, uint64_t len) {
  wiz_sys_fdh *h = (wiz_sys_fdh *)p;
  void *a = mmap(NULL, (size_t)len, PROT_READ, MAP_SHARED, h->fd, 0);
  if (a == MAP_FAILED) { wiz_sys_err = errno; return NULL; }
  wiz_store_map *m = (wiz_store_map *)wiz_xmalloc(sizeof *m);
  m->addr = a; m->len = (size_t)len;
  return m;
}
WIZ_API void wiz_store_map_free(void *p) {
  wiz_store_map *m = (wiz_store_map *)p;
  if (m->addr) munmap(m->addr, m->len);
  free(m);
}
WIZ_API uint64_t wiz_store_get_u64(void *p, uint64_t off) {
  wiz_store_map *m = (wiz_store_map *)p;
  uint64_t v; memcpy(&v, (char *)m->addr + off, 8);
  return le64toh(v);                                     /* format is little-endian */
}
/* optional: wiz_store_msync, wiz_store_set_u64, wiz_store_flock */
```

Wiz side:

```wiz
foreign_type Map (finalizer := "wiz_store_map_free")
extern "wiz_store_mmap_ro" Map.map : Fd → Nat → IO Map
extern "wiz_store_get_u64" Map.getU64 : Map → Nat → U64
extern "wiz_store_fsync" Fd.fsync : Fd → IO Nat
extern "wiz_store_ftruncate" Fd.truncate : Fd → Nat → IO Nat
```

`Map.getU64` is a pure read of a read-only mapping (trusted, like `Bytes.get`);
the map is created and destroyed in `IO`. `Fd.fsync` returns an errno status and
wraps in `Sys.status`/`Sys.lift` (`lib/Sys.wiz:49–55`).

### 8.3 What works today

* `Fd.open`/`seek`/`write`/`readExactly`/`close` write an append-only file.
* `U8Array`/`U32Array`/`U64Array` build pages in place when unique; `Bytes`
  appends. A page builder can use `U8Array.set` and convert to `Bytes` once.
* `FS.writeFile`/`writeBytes` replace a whole file (not a page); `File.flush` is
  `fflush` (not `fsync`); `wiz_warray_of_c` copies.
* `foreign_type` finalisers exist (`File`, `Fd`), so a `Map`/`Handle` can be
  closed; a pure `Snapshot` can carry a `Map` and stay a value.

---

## 9. What Wiz cannot do yet, and the smallest addition

| missing | consequence | smallest addition | blocker? |
|---|---|---|---|
| `mmap` | no zero-copy pages; reads are `Fd.read` + copy | `foreign_type Map` + 3 C functions (§8) | slice 3 read path |
| `fsync`/`fdatasync` | cannot promise crash durability; `flush` is `fflush` | one C function, ~8 lines | **slice 2** |
| `ftruncate` | cannot reserve/grow before mapping | one C function | optional (`write` grows) |
| `msync` | no explicit flush of a writable map | one C function | optional (`pwrite` path) |
| `flock` | no cross-process single writer | one C function or a lock file | multi-process |
| `pread`/`pwrite` | positional IO is `seek`+`read/write`; not thread-safe on one fd | two C functions | not single-threaded |
| wide/unaligned loads | `Bytes.get` is byte-at-a-time; a `U64` needs 8 gets + shifts | `Map.getU64`/`Bytes.getU64` | performance, not correctness |
| `Bytes.set` | a byte cannot be changed in place; a page is rebuilt | `Bytes.set` (copy-on-write) or `U8Array` | performance |
| non-owning `U8Array` view of C memory | `wiz_warray_of_c` copies (`runtime/rt_data.inc:496`) | a `Map` view, or a `warray_of_c_view` with a no-free flag | optional |
| raw atomic load/store | reader-visible `txid` needs a seqlock | a native atomic load or a syscall | not single-process |
| linear fixpoint | recursive consumers of a linear cursor are rejected | a linear fixpoint rule, or `Cursor.fold`/`foldUntil` | not slice 1 |
| structure at 1 | cannot project a linear structure | use an inductive (already supported) | no |
| `LinearOption` | `Option`/`List` cannot carry a linear element | use `Step`/`Control`/`Result1` | no |
| snapshot lease finaliser | a pure snapshot cannot be revoked | `foreign_type` lease + RC finaliser (§2.5) | no (retention policy) |

**Slice 1 (the in-memory prototype) has no blocker and typechecks today.**
Slice 2 (durable log) is blocked on `fsync`. Slice 3 (mmap pages) is blocked on
`mmap` + `getU64`. Multi-process is blocked on `flock`. Everything else is a
performance or convenience addition.

---

## 10. Prior art

* **LMDB** (Howard Chu, Symas). The direct model: a COW B+tree, two meta pages,
  one writer, many readers, snapshots as root pages, no WAL, `mmap`-backed
  reads. The page format here is not LMDB's, but the meta-page/COW discipline
  is. See the LMDB documentation and the comments in `mdb.c`/`lmdb.h`.
* **SQLite**: WAL mode (`sqlite.org/wal.html`) and the rollback journal
  (`sqlite.org/atomiccommit.html`); the locking ladder (SHARED/RESERVED/
  EXCLUSIVE). SQLite is the reference for "a commit is a log record + a
  checkpoint + a header switch"; this design uses the same commit-point idea
  with a COW tree instead of a WAL frame index.
* **Datomic** (Rich Hickey et al.). Immutable datoms `(E, A, V, T, op)`, a
  transactor that serialises writes, "the database is a value", and four
  indices (EAVT, AEVT, AVET, VAET). This design's snapshot/immutable-fact view
  and its "index is derived, not authoritative" rule follow Datomic; its
  per-key conflict rule is closer to MVCC than to Datomic's single transactor.
* **flatgraph / FlatBuffers**. FlatBuffers (Google) is the zero-copy,
  offset-based, `mmap`-friendly serialisation; mutation is limited to same-size
  in-place fields. flatgraph (the FlatBuffers-based graph store) shows the
  fixed-size node/offset layout and the read-only adjacency access. This design
  takes the fixed-size node and offset idea, but puts it in a COW B+tree so it
  can be updated; a flatgraph-style read-only projection can be a derived
  structure.
* **Event sourcing / monoid caches**. Martin Fowler, "Event Sourcing" (2005);
  Greg Young's event-store work. The log-only slice is event sourcing; the
  write-set monoid and the derived index are the "fold of facts" view. The
  commutative part is the CRDT line: Shapiro, Preguiça, Baquero, Zawirski,
  "Conflict-free Replicated Data Types" (SSS 2011) and "A comprehensive study of
  convergent and commutative replicated data types" (INRIA RR-7506, 2011).
* **STM / MVCC validation**. First-committer-wins: Dice, Shalev, Shavit,
  "Transactional Locking II" (DISC 2006). Per-key conflict detection under
  snapshot isolation: Cahill, Röhm, Fekete, "Serializable Isolation for
  Snapshot Databases" (SIGMOD 2008) and PostgreSQL's SSI. Isolation-level
  background: Berenson et al., "A Critique of ANSI SQL Isolation Levels"
  (SIGMOD 1995). The rule here is per-key first-committer-wins with a delta
  exemption, plus a global delete epoch.
* **Wiz in-tree**: `lib/Optic.wiz` (store encoding, laws, `zoom`),
  `lib/OpticDerive.wiz` (`deriving Lens`), `wiz-notes/indexed-optics.md`
  (index pairing, `IxTraverse`, the composition obligation),
  `wiz-notes/analysis-optics-decisions.md` (O1 explicit records, O2 index the
  focus, O3 quantities, O13 no coend), `docs/stages/11-tooling.md:47–48` (the
  host already writes an mmap'able `.olean`-style region — the precedent for a
  Wiz-produced mmap image), `docs/stages/29-natives.md:12–20` (model/native/
  laws/trust), `docs/stages/04-data.md:48–76` (linear pairs, structures at 1),
  `lib/MVar.wiz:54–69` (linear hole), `lib/Region.wiz:102–117` (`Uniq`,
  `Result1`, `ResultH`), `lib/WordArray.wiz` (in-place word arrays),
  `lib/WordMap.wiz` (`U64Map`), `lib/Intern.wiz` (string ids),
  `lib/Scry/Store.wiz:20–48` (derived indexes, `indexThreshold`).

---

## 11. Staged implementation plan

**Slice 0 — design + prototype (this note).** Done: the pure types, the
in-memory engine, the validation, the index, the linear cursor, the rejection
file. Acceptance: `wiz check` green on the three good files, expected errors on
the reject file (§12). No natives, no build.

**Slice 1 — in-memory, no IO.**
- Replace the prototype's `U64Map` root with the same `Root`/`Snapshot` types
  but a `U64Map`-backed B+tree model; add the read-set to `Snapshot`.
- Prove/test the lens laws for `nodeAt`/`nodeOr` and the `Traversal` laws
  (conditional on the indexed field).
- Random differential: a sequence of ops (including `set`, `del`, `+1`, index
  updates) against a reference map/index; every accepted commit equals the fold;
  every rejected commit leaves the state unchanged.
- Add `=storage` to the test groups. Acceptance: `wiz check` + the group.
- No blocker.

**Slice 2 — single file with a log (durable store).**
- `Handle` = `Fd` + the current `Db`; `getDb` returns the in-memory snapshot;
  `putDb` appends a commit record (write-set + txid + base + CRC), `fsync`, and
  updates the in-memory state.
- Open: scan the log, stop at the last valid CRC, fold. A checkpoint record can
  compact the log.
- Crash harness: truncate the file at every record/byte boundary, reopen, assert
  the last committed `txid` survives and no partial record is applied.
- Native: `fsync` (**blocker**); `ftruncate` optional. One `heavy --queue` job
  for the native build, one at a time.
- Acceptance: the crash matrix passes; the commit latency with/without `fsync`
  is measured.

**Slice 3 — COW pages + mmap reads.**
- Page builder (`U8Array`), leaf/internal B+trees, two meta slots, page
  checksums, root switch, `mmap` read-only snapshots, `Map.getU64`.
- Never-reuse pages + offline compaction (or K-root retention).
- Crash matrix with torn page/meta writes; recovery picks the max valid meta.
- Natives: `mmap`, `munmap`, `getU64`, `fsync`, `ftruncate`.
- Acceptance: `mmap` reads match the log-only store; a crash at every step
  leaves the last committed root; no page is overwritten while reachable.

**Slice 4 — index traversal + linear cursor in the engine.**
- Index B+trees, `indexTraversal`, `indexNodes`, `Cursor.follow`; unique
  conflicts; index-only scan; predicate pushdown in the plan.
- `Cursor.fold`/`foldUntil` as the public loop; a `Wandering`/`Traversal` class
  only if a second consumer appears.
- Acceptance: index equals recompute after every commit; a cursor early-exit
  does not read the rest (a plan counter); a duplicated cursor is a compile
  error (the reject file).

**Slice 5 — the optics-driven write-set in the real engine.**
- `Snapshot` overlay backed by pages; `Lens`/`PLens`/`Affine` + `Traversal` +
  `Cursor`; `lib/Storage.wiz` with `getDb`/`putDb`; the owner's snippet compiles.
- Benchmarks: mmap vs `Fd.read` page reads; commit latency; two-writer counter
  throughput; a `set`/`delete` conflict rate.
- Acceptance: the API is exactly §5.2/§7.2; the owner's example runs; the
  immutable-snapshot property is tested (a snapshot held across commits does not
  change).

**Build discipline.** No unbounded builds. `wiz check` probes go through
`light`; any native/compiler build is one `heavy --queue` job at a time. The
prototype needs neither.

---

## 12. The prototype, and what typechecked

Base: branch `storage-engine-design` at `66398557` (= `integration/train6`
HEAD); train6 is untouched; no PR. The checks used a `wiz` built from train6,
via `light`. The command is:

```text
wiz check -I drafts/storage-engine drafts/storage-engine/Storage.wiz
```

`-I drafts/storage-engine` is only for the local `Cursor` module; `lib/` is the
toolchain's own (a `-I lib` would be ignored for toolchain modules, which is why
the train6-built binary is the right checker).

**Files.**

* `drafts/storage-engine/Storage.wiz` — `Node` (`deriving Lens`), `Patch`,
  `WriteSet`, `Root`/`Snapshot`, `nodeAt`/`nodeOr`/`PLens.over`, `IndexDef`,
  index add/remove/rebuild, `IndexDelta`, `Traversal`/`indexTraversal`,
  `Db.commit`/validation, and the toy scenario.
* `drafts/storage-engine/Cursor.wiz` — `Cursor`, `Step`, `Control`,
  `next`/`close`/`fold`/`foldUntil`/`toList`/`filterMap`.
* `drafts/storage-engine/StorageCursor.wiz` — `tableCursor`, `indexCursor`,
  `Cursor.follow`, `indexNodes`; the index and table scans are both `Cursor`.
* `drafts/storage-engine/CursorReject.wiz` — the rejected duplications/drops
  (expected `wiz check` errors).

**`Storage.wiz` (rc=0, 13 `#eval` lines):**

```text
Storage.wiz:417:1: info: 1      -- one +1: count = 1
Storage.wiz:418:1: info: 1      -- committed
Storage.wiz:423:1: info: 1      -- second +1 from the same base: committed
Storage.wiz:424:1: info: 2      -- and the count is 2 (they commuted)
Storage.wiz:430:1: info: 1      -- a stale `set` (label) is rejected
Storage.wiz:433:1: info: 1      -- a unique-index duplicate is rejected
Storage.wiz:439:1: info: 1      -- a tx that began before a delete is rejected
Storage.wiz:442:1: info: 1      -- index bucket kind=1 has 1 node
Storage.wiz:443:1: info: 0      -- bucket kind=9 is empty
Storage.wiz:446:1: info: 1      -- the index traversal sees 1 node
Storage.wiz:448:1: info: 1      -- bumpOfKind 1 bumps that node to 1
Storage.wiz:449:1: info: 0      -- node 2 (kind 2) is untouched
Storage.wiz:450:1: info: 1      -- and the bucket is still 1
```

**`StorageCursor.wiz` (rc=0, 5 lines):**

```text
StorageCursor.wiz:33:1: info: 2   -- table scan: 2 nodes
StorageCursor.wiz:34:1: info: 1   -- index kind=1: 1 node
StorageCursor.wiz:35:1: info: 1   -- index kind=2: 1 node
StorageCursor.wiz:36:1: info: 2   -- foldUntil counts 2
StorageCursor.wiz:37:1: info: 0   -- early exit stops at 0
```

**`Cursor.wiz`:** rc=0, no output.

**`CursorReject.wiz`:** rc=1 with exactly the four errors quoted in §7.3
(`badDup`, `badAfter`, `badDrop`, `badProj`); `goodFirst` and `goodPair` are
accepted. The non-zero exit is the point of the file.

What is *not* proved: the lens/traversal laws, the crash cases, the mmap path,
and the native code. The prototype is a type-level and semantic model; the
staged plan says where the tests and the natives go.

---

## 13. Open decisions for the owner

1. **`getDb`/`putDb` return types.** The sketch says `IO Snapshot` / `IO
   Result`. A production API should not hide I/O errors: `EIO Snapshot` /
   `EIO Outcome` (`EIO A = IO (Except String A)`, `lib/Sys.wiz:67`), with
   `Outcome = committed gen | rejected (stale | conflict | missing | duplicate |
   io)`. The sketch's `IO` can be the happy-path wrapper. Recommended: `EIO`.
2. **`Result` vs `Outcome`.** `lib/Result.wiz`'s `Result`/`Error` is the panic
   monad (`panic`, `overflow`, `outOfBounds`, …); a commit conflict is not a
   panic. Use `Outcome` and keep `Result` for real panics.
3. **`over (+1)` vs `overAdd`.** A generic `A → A` is not a delta. Recommended:
   an explicit `overAdd`/`append` combinator for commutative fields, and a
   generic `over` that records a `set` (safe, not merged), so the engine never
   infers commutativity from a diff. The prototype's `ofChange` is the
   demonstration, not the final contract.
4. **Delete barrier: global or per key.** Slice 1's global `del_epoch` is the
   conservative reading of "started before a delete". Per-key tombstones are
   more concurrent; recommend keeping the global epoch until the per-key path
   is tested.
5. **Snapshot retention.** Never-reuse + compaction is sound and simple; K-root
   retention is bounded; leases are the end state. Recommend never-reuse for the
   first mmap slice.
6. **Profunctor layer.** Keep the store encoding and the hand-rolled
   `Traversal`/`Cursor` for slice 1; add `Wandering` only with a measured second
   use. If the owner wants one optic for update and query, that is the new work
   in §5.4, and its coherence obligations should be priced first.
7. **Cursor recursion.** The current checker rejects recursive consumers of a
   linear handle. Ship `Cursor.fold`/`foldUntil` as the public loop; a linear
   fixpoint rule is a language addition, not a storage-engine requirement.

---

## 14. Slice 2 implemented: the durable single-file store

Status: branch `store-durable` off `integration/train6` (`66398557`), no PR. The
prototype above is unchanged; the slice-2 files are additions in
`drafts/storage-engine/`:

* `Durable.wiz` — the file format, recovery, commit protocol, and the public
  `Handle`/`getDb`/`putDb`/`closeDb`;
* `DurableTest.wiz` — a compiled program that runs the §12 scenarios against a real
  file, plus the crash-ish cases;
* `test-durable.sh` — the three `wiz check`s and the `wiz run`.

The native is in the ordinary `Sys`/`Fd` family, not a storage-specific one:

* `runtime/rt_sys.inc`: `wiz_sys_fd_fsync` (`fsync(2)`) and
  `wiz_sys_fd_fdatasync` (`fdatasync(2)`, `fsync` under Emscripten), each returning
  `0` or `errno`; `runtime/wiz_rt.h` has the prototypes;
* `lib/Sys.wiz`: `Fd.syncRaw`/`Fd.dataSyncRaw` and `Fd.sync`/`Fd.dataSync` (EIO);
* `.github/trust-baseline.tsv`: the four rows (axiom + `builtin extern:`) for the
  two externs.

### 14.1 The format actually implemented

One file, little-endian, 4 KiB pages. Page 0 holds meta slot A and page 1 meta slot
B (the §2.2 diagram, not both slots in page 0 as §2.3 says): the slots are then in
different pages, so a torn write to one cannot take the other with it. Data pages
start at page 2.

* **Meta slot, 96 B** (the §2.3 field list is 96 B, not 64 B):
  `magic u64 | format u32 | flags u32 | txid u64 | root u64 | index_root u64 |
  freelist_root u64 | log_end u64 | del_epoch u64 | min_gen u64 | schema_gen u64 |
  page_count u64 | checksum u64`. Only `txid`, `root`, `del_epoch` and `page_count`
  are used in this slice; the rest are zero.
* **Data page:** a 32 B header (`kind u16 | n u16 | free u16 | flags u16 | txid u64 |
  checksum u64 | right u32 | reserved u32`) and 127 fixed 32 B records. The records
  are `key u64 | kind u32 | label u32 | count u64 | version u64`, exactly §2.2.
  `right` chains the leaves; `root` is the first page (0 for an empty map).
* **Checksums:** FNV-1a-64 over the page (or slot) with the checksum field zeroed.
  The Wiz checksum folds the page in 512-byte blocks: one 4096-deep recursion
  overflows the compiled program's stack, while the blocked fold gives the same
  hash.
* **This slice's tree** is one leaf chain, not a B+tree with internal pages. The
  page/record format and the COW discipline are the ones an internal level will
  use; a commit rewrites the whole map into fresh pages. That is enough for the
  API and the crash cases, and it keeps `mmap` (slice 3) a read-path change only.

### 14.2 Commit protocol as implemented

`putDb` takes the handle's `MVar` (the single-writer critical section), runs the
pure `Db.commit`, and only then touches the file:

```
1. pure Db.commit: validate (delete epoch, per-key first-committer-wins, unique
   index) and materialise the new map             -> rejected, or a plan
2. append fresh pages at page_count                (pwrite through Fd.seek/Fd.write)
3. fdatasync(fd)                                   pages durable
4. write the inactive meta slot (txid mod 2)
5. fsync(fd)                                       the commit point is durable
6. publish the new Db in the MVar
```

A rejection writes nothing. An I/O error leaves the old `Db` published, abandons
the pages it wrote, and moves a **generation floor** past the attempt; the next
commit uses `max(db.gen, genFloor) + 1`. That is what keeps a fallback safe: after
a torn last commit the chosen state is older than the torn slot's `txid`, and a
retry must not reuse that `txid` (a stale slot could otherwise point at pages the
retry overwrites).

`genFloor` and `page_count` are kept out of the pure `Db`: `Db.gen` is the honest
generation a snapshot reports, `genFloor` only bounds the next commit.

### 14.3 Recovery on open

`openDb` reads both 96 B slots. A slot is valid iff magic, format and checksum
pass. The valid slots are tried newest `txid` first; a slot is *chosen* only when
its whole page chain verifies:

* every page is 4 KiB, kind 1, `n ≤ 127`, its header `txid` equals the slot's
  `txid`, and its checksum matches;
* every page number is below the slot's `page_count`; `right` chains to 0; the
  walk is fuelled by `page_count`, so a cycle is corrupt, not a loop.

If the newest slot's chain fails (the last commit's pages were truncated or torn),
the next slot is tried. The chosen state gets `db.gen = chosen.txid` and a
`genFloor` equal to the greatest `txid` among *all checksum-valid* slots, so the
next commit is above the torn one. `page_count` starts after every page any valid
slot names, so recovery never overwrites a page a stale slot might still reach.
A file with no valid slot opens as an empty store; its bytes are unreachable pages
from a crash before the first commit.

The index roots are not stored: the index is derived state, so `dbOf` rebuilds it
from the primary records with `Root.rebuildIndex` (the same recompute path §6.3
keeps for repair). Deleted keys keep no tombstone on disk; the global delete epoch
is enough to reject a transaction that began before a delete. Per-key tombstones
arrive with the per-key refinement (§3.2, §13.4).

### 14.4 What ran

All through `light` with the worktree's `wiz` (built by one `heavy lake build wiz
tests`, 555 jobs, rc=0), except the build itself.

```text
wiz check -I drafts/storage-engine drafts/storage-engine/Durable.wiz      rc=0
wiz check -I drafts/storage-engine drafts/storage-engine/DurableTest.wiz  rc=0
wiz check lib/Sys.wiz                                                      rc=0

wiz check -I drafts/storage-engine drafts/storage-engine/Storage.wiz      rc=0
  (the same 13 #eval lines as §12)
wiz check -I drafts/storage-engine drafts/storage-engine/Cursor.wiz       rc=0
wiz check -I drafts/storage-engine drafts/storage-engine/StorageCursor.wiz rc=0
  (the same 5 lines as §12)
wiz check -I drafts/storage-engine drafts/storage-engine/CursorReject.wiz rc=1
  (the same 4 expected errors as §7.3)
```

The compiled test (a C build with the gmp flags from `grail.local.wiz`) prints:

```text
durable: in /tmp/wiz-…
durable: clean reopen ok
durable: truncated tail ignored
durable: all checks passed
```

It covers, against a real file: seed; two `+1`s from one base both commit and sum
(count 2, generation 3); a stale `set` is rejected; a unique-index duplicate is
rejected; a delete commits (generation 4) and a transaction begun before it is
rejected by the epoch; close and reopen sees generation 4, count 2, node 2 gone;
a commit after the reopen is generation 5 and survives another reopen. The torn
case writes three commits, copies the file with the last 4 KiB removed
(`Bytes.slice` is the by-hand truncation), opens the copy at generation 2 / count
1, commits again at generation 4, and reopens it at generation 4 / count 2.

`strace -e fsync,fdatasync` on the final binary shows **9 commits, 9
`fdatasync(3)` and 9 `fsync(3)`**: the native really reaches the kernel, and the
two phases are distinct.

Not run: the trust-ledger gate. `scripts/trust-ledger.sh --lib-only` on this
train6 checkout stops before the ledger on pre-existing errors in `lib/Scope.wiz`
(quantity 0 used ω) and `lib/Scry/EgraphExtract.wiz` (unknown identifiers), which
are unrelated to `lib/Sys.wiz`; `scripts/trust-ffi-audit.sh Sys` does show both new
externs as `reviewed` with the expected `Fd → Nat` signature. No PR and no CI.

---

## 15. Slice 3 implemented: retention, compaction, space accounting

Status: branch `store-compact` off `integration/train6`, merging `store-durable` and
`store-mmap` (both off `66398557`). No PR. The slice-2 format and commit protocol are
unchanged; this slice adds the registry, the live-page walk, the two-file compaction, and
`stats`, plus one native (`ftruncate`).

### 15.1 What the format already gave, and what it did not

`store-durable` writes one append-only chain: a commit appends the whole node map as 32 B
records in kind-1 pages linked by `right`, then switches a 96-byte meta slot. Two slots
hold the current and the previous root. Nothing is ever reused, so every generation's
pages stay on disk until something removes them.

* **Retained.** `min_gen` (present in the meta since slice 2, always 0) is now the oldest
  live generation. `page_count` keeps its meaning (first free page = file length in
  pages). The two-slot alternation, the 32 B header/record, FNV-1a-64 and the
  `pages → fdatasync → meta → fsync` commit order are untouched.
* **Assumed, not changed.** The format names exactly **two** roots, one per meta slot.
  Therefore retention across a restart is at most two roots: `openDb` verifies both
  slots' chains and registers both. A larger K is in-process history (each commit adds a
  `RootRef` in the handle); the format does not name those roots, so after a restart they
  are gone. Persisting K > 2 across restarts would need a registry page (a kind-2 chain
  named by a meta field) — that is a format extension, not what this slice does.
* **Added native.** `Fd.truncate` (`wiz_sys_fd_ftruncate`, 0/errno, `EINVAL` above
  `INT64_MAX`), two trust-baseline rows. It is used twice, both on the tail: on open, a
  commit that appended pages and crashed before the meta switch leaves a tail no valid
  slot names, and `openDb` truncates to `max(page_count over valid slots)`; when building
  the compacted image, `ftruncate` sets its exact length (`2 + live` pages), which is a
  no-op on the `pwrite` path but is the invariant an empty store (meta only) and a future
  preallocating writer rely on.

### 15.2 Retention (`drafts/storage-engine/Registry.wiz`)

A `RootRef` is `gen | root | pages | del_epoch | pins`; a `Registry` is
`refs (newest first) | keep (K)`.

* **Policy.** `Registry.live` = the newest K roots **union** every root with `pins > 0`.
  `lease`/`release` move the pin counter; a pinned root outlives the count policy. (The
  design's end state attaches this counter to a `Snapshot` finaliser; the counter is the
  bookkeeping, and the pure `Snapshot` value stays pure.)
* **Exact admission, not a floor.** `Registry.retained (gen)` is membership in the live
  set. Count-based retention can drop generation 5 while 4 is pinned, so a floor alone
  would admit a snapshot whose pages are gone. `Registry.min_gen` is still written to the
  meta as the horizon; `putDb` uses `retained` and returns `CommitError.expired`
  (`base`, `floor`). Reads through an evicted snapshot value are outside the contract,
  as §2.5 says.
* **Trimming.** Every commit re-applies the policy to the handle's history, so the
  registry is bounded by K + pins.

### 15.3 The live set and the plan (`Compact.wiz`)

`StoreView` is `page_count` plus each data page's `right` link, read from the file's
headers. `compact : StoreView → List RootRef → Plan` is pure:

1. walk every retained root's chain with a visited set shared across roots and a fuel
   bound of that root's `pages` (a corrupt cycle stops at the bound);
2. sort the union ascending and number it densely from page 2 (`newOf`);
3. map each root to its new first page, and report `totalPages` (the file before).

`Plan.stats` = `livePages`, `totalPages`, `metaPages = 2`,
`wastedPages = total − live − 2`, `wastedBytes = 4096 × wasted`; `Plan.after` is the same
accounting for the rewritten file (`total = live + 2`, waste 0). `statsOf` runs the same
walk against the live file, so the policy can decide *when* to compact from
`wastedPages`.

### 15.4 The compaction protocol, and why it is a second file

The format is append-only. A "fresh region of the same file" can only be at the end, so
an in-place compaction makes the file **larger**; to reclaim, the image must be moved
down over the old pages, and that cannot be crash-safe: a crash between the move and the
second meta switch leaves both slots naming overwritten pages, and a live read-only
mapping of the old inode `SIGBUS`es once the file is truncated below its pages. Neither
has a fallback. So the switch is the design's §2.5 swap:

```
1. read the view (every data page's right link) and the registry
2. plan := compact view (Registry.roots registry)          -- pure
3. create <path>.compact, write the live pages densely from page 2,
   relinking `right` and recomputing each page checksum
4. write the newest root's meta into its parity slot, and the newest
   retained root of the opposite parity into the other slot; min_gen
5. fsync(<path>.compact)                                    -- the image is complete
6. rename(<path>.compact, <path>)                           -- the single switch
7. fsync(parent(<path>))                                    -- the switch is durable
8. publish: the handle writes to the new descriptor, the registry is
   remapped, page_count := 2 + live
```

`rename` is the single atomic operation (the analogue of the meta write); the new file's
meta slots and pages are already durable, so there is no state where the name and the
contents disagree. A reader that mapped the old file keeps the old inode (POSIX), so a
`MappedSnapshot` taken before compaction still reads; new `getDb`s read the new file.

**Crash states.** (1) crash while writing the image: the store is untouched; the temp is
overwritten next time. (2) crash before the temp `fsync`: the store is untouched; a torn
temp is never a valid store. (3) after the temp `fsync`, before `rename`: the store is
untouched; the temp is a leaked inode. (4) during `rename`: old or new name, both complete
images (the pair is atomic). (5) after `rename`, before the directory `fsync`: either name
after power loss, both complete. (6) after the directory `fsync`: the new file. The old
root is valid in 1–3 (and in 4–5 if the old name survives), which is the case the brief
asks to test.

### 15.5 Integration of `store-mmap` (the merged read path)

`store-mmap` was written before the writer existed and assumed a B+tree. The writer's
actual page is a chained kind-1 leaf, so the merge makes three changes to `Mmap.wiz`,
without changing the format:

* `Store.metaMagic` is `store-durable`'s `0x57495a53544f5245` (the decoder still accepts
  any nonzero magic with a valid checksum);
* a leaf lookup that misses follows `right` (`Store.findInChain`), so the decoder reads
  the writer's chained records;
* the mapped snapshot types are renamed `MapRoot`/`MappedSnapshot` so a test can import
  both halves (Wiz has no namespaces); `Snapshot.open` also treats `root = 0` as the
  empty store rather than checksumming the meta page.

`CompactTest`'s last check maps the compacted file and reads every node through the
decoder, which is the "compaction preserves reads" check with the real read path.

### 15.6 Tests

`CompactPure.wiz` (`wiz check` + `#eval`) — a hand-built view with two chains (2→3→4,
5→6) and 12 pages: the union counts each page once (including a shared suffix); K = 1
keeps 3 pages, K = 2 keeps 5, a lease on the old root under K = 1 keeps 5;
`wastedPages` 7/5 before and 0 after; the mapping is dense from page 2; `retained` is
false for an evicted generation and true for a pinned one; lease/release move the
counter; `otherRoot` picks the opposite-parity slot.

`CompactTest.wiz` (`wiz run`) — seed plus 20 commits (never-reuse: one page each),
`stats` shows waste, then `prepareCompaction`: the old file still opens with the same
generation and content, and the prepared image is a complete store with the same
generation and content. `finishCompaction`: same generation, same nodes and versions,
`wastedPages = 0`, `total = live + 2`, the total fell by exactly the old waste, the
plan's after-stats equal the measured ones, the **mmap decoder** reads the compacted
file, a reopen reads it, both meta slots name roots, and a commit past it is durable.
`retentionTest`: K = 1, lease generation 1, six commits, compact — the leased chain is
still live (2 pages) and its records still load; release, compact — 1 page and a smaller
file; a commit from the evicted base is `expired`, from the current base it commits.
`crashTest`: prepare and abandon (complete image, then a garbage temp) leaves the path's
store exactly as it was. `tailTest`: two garbage pages appended with no meta naming them
(the crash-before-switch case) are truncated away on open, `stats` shows no waste, and the
generation is unchanged; an empty store compacts to its two meta pages (the
`ftruncate`-grows case) and still commits.

Results with the worktree's `wiz` (`heavy lake build wiz tests`, rc=0; checks and runs via
`light`):

* `CompactPure.wiz`: rc=0, 24 `#eval` lines, all matching the comments (live 5/3/5/3 for
  K=2/K=1/pinned/shared, waste 5 and 7, after 7 pages, 0 waste, dense mapping, retention
  predicates, remap 2/1, other slot 1, total 12 → 7).
* `CompactTest.wiz`: `compact: all checks passed (70)` — compaction 40, retention 16 more,
  crash 6 more, tail/empty 8 more (cumulative count).
* `DurableTest.wiz` and `MmapTest.wiz` still pass unchanged after the merge (the latter's
  group `storage-mmap` expected output is unchanged).
* `strace -f -e ftruncate,rename` on the run shows `ftruncate(3, 12288)` for the tail trim,
  `ftruncate(4, 16384)` for the image length, and
  `rename("…/compact.db.compact", "…/compact.db")` for each switch.
* `scripts/trust-ffi-audit.sh --check Sys` (under `heavy`): 69 externs, 0 legacy,
  signatures match, `Fd.truncateRaw wiz_sys_fd_ftruncate` reviewed.

Not run: the trust-ledger gate (same pre-existing `lib/Scope.wiz` /
`lib/Scry/EgraphExtract.wiz` errors as §14). No PR and no CI.
