# Storage engine — the pure half

A pure (no IO) companion to `wiz-notes/storage-engine.md`: recording optics,
secondary indices, and linear streaming cursors. This is slice 1 of the note's
staged plan, extended with the pieces slice 4 needs: a plan-backed cursor (fusing
`filter`/`filterMap`), index-only scans, predicate pushdown, early exit through
`follow`, and read-count shape checks (`indexTraversal`/`indexNodes`, `Cursor.follow`,
`fold`/`foldUntil`, the rejection cases).

Checked with a shipped `wiz` (no build needed; the pure half imports only `lib/`):

```text
wiz check -I drafts/storage-engine drafts/storage-engine/Core.wiz
wiz check -I drafts/storage-engine drafts/storage-engine/Cursor.wiz
wiz check -I drafts/storage-engine drafts/storage-engine/Storage.wiz
wiz check -I drafts/storage-engine drafts/storage-engine/StorageCursor.wiz
wiz check -I drafts/storage-engine drafts/storage-engine/Tests.wiz
```

`CursorReject.wiz` and `CursorRecursive.wiz` are expected to **fail**: they are the
checker's rejection cases. `wiz check` exits 1 on each; the messages are in the
files and in the note.

## Files

| file | contents |
|---|---|
| `Core.wiz` | `Node` (+ `field`/`beq`), `Cost` (the read-path counter), `Entry`, `KeyRange`/`KeyPred`, `Source`, `Projection`, `Rerange` (the pushdown hook) |
| `Cursor.wiz` | the linear `Cursor`/`Step`/`Control` over a `Plan`; `next`/`close`, `fold`/`foldUntil` (and `…With` cost variants), `map`/`filter`/`filterMap`, `first`/`firstWith`, `filterKey`/`filterOnNode` pushdown, `followKeys`, `info`/`Info.show` |
| `Storage.wiz` | `Patch`/`WriteSet`, `Root`/`Snapshot`, `Snapshot.fetch` (the counted read), `nodeAt`/`nodeOr`, `PLens.over`, `IndexDef`, `IndexFact`/`IndexDelta` (facts and tombstones), `Root.rebuildIndex`, `Traversal`/`indexTraversal`, `Db.commit` and validation |
| `StorageCursor.wiz` | `tableCursor`, `indexCursor` (primary keys), `indexOnlyRange`/`indexOnlyWhere` (the indexed field, no node), `Cursor.follow`, `indexNodes`, `filterOnNode` |
| `Tests.wiz` | the `#eval` cases (recording, commits/validation, index deltas, scans, early exit, and the plan: fusion, index-only, pushdown equivalence, read counts) |
| `CursorReject.wiz` | the four rejected cursor programs (expected errors) |
| `CursorRecursive.wiz` | the linear-recursion gap (expected error) and what a fix would need |

## Recording optics

`nodeAt`/`nodeOr` are store-encoding optics (`Store A S = A × (A → S)`): their
backward function records one `Patch` into the snapshot's write-set, so `Lens.over`
and `PLens.over` produce the diff *as they run*. `Lens.comp` composes the backward
functions, so a deep path records one record-level patch at the outer lens. There is
no second pass and no diff of the maps. This is the store encoding in
`lib/Optic.wiz`, **not** profunctor optics: there is no `Strong`/`Wandering`, and the
note's new `Traversal` is engine-local.

## Indices

An index entry is a fact `(index, key, node)`; a delete is a `remove` fact (a
tombstone); `IndexDelta.combine` is set union (commutative, associative, idempotent),
so a transaction's delta does not depend on write-set order. `Db.commit` derives the
delta from the primary write-set and applies it incrementally; `Root.rebuildIndex`
recomputes an index from the primary map for repair. The tests check that the
incremental index equals the rebuild after commits, that a unique collision is
rejected (including two nodes moving to one key in one transaction), and that the
delta's fold applied to the base root is the committed index.

Known slice-1 limits (from the note, not fixed here): the index is not
read-your-writes inside a transaction (the primary is); a unique check runs on the
whole resulting primary map rather than incrementally.

## Plans, index-only scans, pushdown, read counts

The cursor's old "rest list" is now a `Plan a` (`Cursor.wiz`):

```text
source : Source                 literal | table | index(field, unique)
state  : State a                remaining items (literal) or entries (scan)
pre    : List (Entry → Bool)    predicates that run before a primary fetch
post   : List (a → Bool)        predicates on the projected value
project: Entry → Option Node → Option a
fetch  : U64 → Option Node × Cost   the counted read path (Snapshot.fetch)
needNode, indexOnly, projection : metadata (which read path, which field)
rerange: Option Rerange        key range + a rebuild closure (pushdown hook)
cost   : Cost                  nodes = primary reads, keys = entries consumed
```

`filter` appends to `post` (nothing is walked), `filterMap` composes `project` (one
function, no data walk), and `next`/`first` advance the plan by one entry at a time.
`Cost` counts reads, never time.

An index entry carries both the indexed key and the primary id, so an index scan can
project either without touching the primary node:

* `indexCursor`/`indexNodes` keep the prototype's `Cursor U64` of **primary keys**
  (the index→primary composite is `Cursor.follow`);
* `indexOnlyRange`/`indexOnlyWhere` yield the **indexed field** and record
  `indexOnly = true`, `projection = key`; `Cost.nodes` is zero.

`filterKey`/`filterOnNode` take an inspectable `KeyPred` (`eq`, `between`). If the
plan's source is an index on that field, the predicate tightens `KeyRange` and the
entry walk is rebuilt for the narrower range; otherwise it stays a post-filter.
Opaque `a → Bool` predicates (`filter`) are never pushed. Pushdown is applied before
the plan advances (after that it falls back to a post-filter).

Read counts on the fixed three-node store (`Tests.wiz`, §10), where the kind index
has two nodes under key 1 and one under key 2:

| query | `Cost.nodes` (primary reads) | `Cost.keys` (entries) |
|---|---|---|
| full table scan | 3 | 3 |
| index scan, all keys, `follow` | 3 | 3 |
| one index bucket (key 1), `follow` | 2 | 2 |
| index-only, key = 1 | 0 | 2 |
| pushed equality, key = 1 | 2 | 2 |
| pushed range on the label index (7..8) | 2 | 2 |
| `first` on the all-keys index scan | 1 | 1 |

`first`/`foldUntil` stop the plan: one entry and one node read, not the remaining
bucket. The pushed and unfiltered-then-filtered paths are compared by value in the
tests, not just by count.

Not pushed down (still post-filters or not expressible): opaque predicates, a
conjunction of fields (no `and` in `KeyPred`), predicates on non-indexed fields,
`!=`/`not`/`or`, ordering/`limit` as plan operators, and a range on an index that is
not ordered (the prototype's `U64Map` index is ordered; the plan records the range but
the list-backed slice stream does not prune pages).

## The linear-recursion gap

`CursorRecursive.wiz` is the minimal failing consumer. The rejection with this
checker is:

```text
error: variable c declared with quantity 1 but used 0
  (a linear variable, of quantity 1, must be used exactly once, and c is not used)
```

It is `partial def` with a linear parameter, not recursion: even a non-recursive
`partial def` fails, because the inferred witness for the partial declaration ignores
the linear argument. With an explicit linear witness
(`partial (default := fun c _ => Cursor.closeThen c 0) …`) the same recursive body
typechecks, and the equation form (structural recursion on an ω measure) already
checks the handle. The engine keeps `fold`/`foldUntil` as the supported loop; the
file says what a linear-fixpoint rule would need to allow.

## Quire (the page-backed store and the page cursor)

`Quire.wiz` is the constant-page durable engine: version 2 of the file format (a
two-level radix directory over 32-byte records, index-fact chains, a 96-byte meta slot).
A commit copies the touched leaf, the two directory pages, the index root and prepends
one fact page per touched `(index, value)`; an open is a `stat` + `mmap` + meta pick
(no map materialisation, no index rebuild). `putMany` is the group commit: a list of
independent transactions validated in order, written as one page run, and published by
one meta switch (one `fdatasync`, one `fsync`), so a one-record-at-a-time writer amortises
the durability point without changing the snapshot contract. `QuireCursor.wiz` is the
page-backed query plan: `indexOnlyRange`/`indexCursorRange`/`indexNodesRange`,
`filterKey`/`filterOnNode` pushdown, `fold`/`foldUntil`, and `Cost.pages` (the mapped
pages touched). `QuireTest.wiz` covers a batched seed, an update through the lens, a
delete, stale and unique rejection, reopen, the page-read counts, and the group commit
(one generation, the crash between pages and commit record, per-record rejection).
`test-quire.sh` checks and runs it; `bench/` is the findings-store benchmark against
`lib/Json` (see `bench/README.md`). `Quire.wiz` also has `compactQ`: the live records and
recomputed indices are written to a fresh image and renamed over the path, which is what
reclaims a never-reuse file.
