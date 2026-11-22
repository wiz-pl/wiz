# storage-engine: the draft-only half

The engine itself is promoted. The durable store, its page format, the page cursor and
the compaction policy are now library modules, so a package can `import` them:

| module | file |
|---|---|
| `Scry.Quire` | `lib/Scry/Quire.wiz` (the page-backed engine, `putQ`/`putMany`, `compactQ`) |
| `Scry.QuireCursor` | `lib/Scry/QuireCursor.wiz` (the page cursor, `Cost.pages`) |
| `Scry.Quire.Storage` | `lib/Scry/Quire/Storage.wiz` (the pure half: records, patches, indices, `Db.commit`) |
| `Scry.Quire.Core` | `lib/Scry/Quire/Core.wiz` (`Cost`, `Entry`, `KeyRange`, `Control`, …) |
| `Scry.Quire.Registry` | `lib/Scry/Quire/Registry.wiz` (the retention registry) |
| `Scry.Quire.Mmap` | `lib/Scry/Quire/Mmap.wiz` (the mapping, page header, meta pick) |
| `Scry.Quire.Durable` | `lib/Scry/Quire/Durable.wiz` (slice 2, the whole-chain predecessor) |
| `Scry.Quire.Compact` | `lib/Scry/Quire/Compact.wiz` (the two-file compaction) |

The page seal is `lib/Scry/quire_seal.c` (linked by `Scry.Quire` from its own directory;
the C name has no `wiz_` prefix, so the compiler emits its prototype and there is no
header).

**Why `lib/` and not `scry/src/`:** the test suite's loader and the toolchain's module
roots serve `lib/`, and `Scry.Registry` already exists under `scry/src/Scry/`, so the
engine's registry cannot live at that name. The engine is library-level, not part of the
scry package; the one consumer is `scry/src/Scry/ProjectCache.wiz` (the project findings
index).

What stays in this directory:

* `QuireTest.wiz`, `DurableTest.wiz`, `CompactTest.wiz`, `RegistryTest.wiz`,
  `MultiprocTest.wiz`, `MmapTest.wiz` — the runtime tests, now importing the `Scry.Quire.*`
  modules;
* `Cursor.wiz`, `StorageCursor.wiz`, `CursorLoop.wiz`, `CursorRecursive.wiz`,
  `CursorReject.wiz`, `Tests.wiz`, `CompactPure.wiz` — the draft-only pure cursor and its
  `#eval` cases;
* `Multiproc.wiz`, `CompatSeed.wiz`, `CompatRead.wiz`, `CrashHarness.wiz` and the shell
  harnesses;
* `bench/` — the JSON-vs-Quire findings benchmark (see `bench/README.md`).

Design and measurements: `wiz-notes/storage-engine.md` (the layout and the commit
protocol), `wiz-notes/quire-perf.md` (the benchmark and group commit),
`wiz-notes/scry-quire.md` (the index-vs-evidence split the project cache follows).

The pipeline is unchanged: a commit copies the touched leaf, the directory path and the
index root, then prepends one fact page per touched `(index, value)`; `putMany` amortises
one `fdatasync` plus one meta `fsync` over a group of independent transactions; `openQ`
is a `stat`, an `mmap` and a meta pick. `compactQ` rewrites the live image and renames it
over the path, which is what reclaims a never-reuse file.
