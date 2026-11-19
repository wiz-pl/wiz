# Storage engine — the pure half

A pure (no IO) companion to `wiz-notes/storage-engine.md`: recording optics,
secondary indices, and linear streaming cursors. This is slice 1 of the note's
staged plan, extended with the pieces slice 4 needs (`indexTraversal`/`indexNodes`,
`Cursor.follow`, `fold`/`foldUntil`, early exit, the rejection cases).

Checked with a shipped `wiz` (no build needed; the pure half imports only `lib/`):

```text
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
| `Cursor.wiz` | the linear `Cursor`/`Step`/`Control`, `next`/`close`, `fold`/`foldUntil`, `map`/`filter`/`filterMap`, `first` |
| `Storage.wiz` | `Node`, `Patch`/`WriteSet`, `Root`/`Snapshot`, `nodeAt`/`nodeOr`, `PLens.over`, `IndexDef`, `IndexFact`/`IndexDelta` (facts and tombstones), `Root.rebuildIndex`, `Traversal`/`indexTraversal`, `Db.commit` and validation |
| `StorageCursor.wiz` | `tableCursor`, `indexCursor`, `Cursor.follow`, `indexNodes`: table and index scans are the same `Cursor` type |
| `Tests.wiz` | the `#eval` cases (recorded patch, two `+1`s, stale `set`, unique duplicate, index delta fold, incremental = rebuild, index scan via `follow`, `foldUntil` early exit, snapshot ω) |
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
