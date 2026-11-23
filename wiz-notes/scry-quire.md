# Scry on Quire: the workflow store, a prototype, and a migration

Status: investigation + opt-in prototype, 2026-11-19. Base: `integration/train7` at
`7365f7d1` (branch `scry-quire`, no PR; train7 is untouched). The prototype is
`drafts/scry-quire/` and runs against the composed engine in `drafts/storage-engine/`
(`Durable`, `Registry`, `Cursor`, `Compact`, `Multiproc`). Scry's default behaviour is
unchanged: nothing in `scry/src/` or `lib/Scry/` imports the prototype.

The short answer:

* **The finding index is the right first Quire user.** It is append-mostly, its records
  are a handful of fixed-width columns, it needs per-key first-committer-wins for
  triage, snapshots so a report reads a stable view while a scan appends, and it is
  queried by rule/state/file — which is exactly a secondary index.
* **The evidence documents stay JSON.** `static.json`, `dynamic.json`, `verify.json`,
  `candidate.json`, `finding.json`, the SARIF output, the REPL config and the bench
  baselines are variable-length documents written once and read by humans and other
  tools. Quire's record is 32 fixed bytes; putting blobs in it is not a schema change,
  it is a different engine.
* **The migration is not a format flip.** The prototype stores the *index*; the
  record's fields (function, line, history, timestamps, candidate, the finding blob)
  stay in the artifact JSON. A real migration needs an intern table for rule/file ids,
  a schema version and a migration command, `flock` (which `Multiproc.wiz` already has),
  compaction, and an export path so `findings.json` remains producible for tools that
  read it.

## 1. What the JSON stores are

### 1.1 `scry-workflow/findings.json` — the workflow store

Schema `scry-workflow-store/1` (`lib/Scry/Workflow.wiz:621–632`): one object with a
`findings` array. Each element is a `scry-workflow-record/1`:

| field | type | notes |
|---|---|---|
| `id` | string | `f_<16 hex>` semantic id; excludes line/column |
| `key` | string | the id's input string (debug/reproduction) |
| `lineHash` | string | GitHub-compatible alert identity |
| `state` | string | `new/triaged/confirmed/false-positive/fixed` |
| `history` | array | `{state, at, by, reason}`; grows on every triage |
| `source` | string | the source file |
| `rules` | string/null | the rule pack path |
| `allowErrors` | bool | the scan's mode |
| `finding` | object | the `scry taint` finding JSON (path, derivation, …) — the big field |
| `artifacts` | string | `scry-workflow/<id>` |
| `static`/`dynamic`/`verify` | string/null | artifact filenames |
| `candidate` | object/null | stage, rank, verdict, reasons, source, plan |
| `candidateFile` | string/null | `candidate.json` |
| `firstSeen`/`lastSeen` | nat | wall-clock nanoseconds |

**Write pattern: rewritten whole.** `wfLoadStore` reads and parses the whole file;
`wfUpsert` replaces or appends one record in the in-memory list
(`lib/Scry/Workflow.wiz:638`); `wfSaveStore` renders the whole store and
`FS.writeFile`s it (`scry/src/Scry/WorkflowCmd.wiz:87`); every `scan` (one save after
all files, `:496`), `triage`, `refine`, `repro` and `verify` uses the same path. So
*logically* the store is append-mostly, but physically every command is an O(n) rewrite.

**Queries.** `list` loads the whole store and linearly filters on `state`; `show`,
`repro` and `verify` linearly find one `id`; `refine` walks every record. There is no
rule/file/function query in the CLI, but those are the natural ones for a larger store
(and are all fields of the record or its `finding` blob).

### 1.2 Per-finding evidence

Each finding has a directory `scry-workflow/<id>/`:

* `static.json` (`scry-workflow-static/1`): tool/pipeline identity, source path and
  FNV hash, rule pack path/hash/count, analysis counts and limits, the finding, the
  path, the derivation certificate (`status`, `verified`, `root`, `nodes`, `text`,
  `axioms`, `assumptions`), boundary/memory assumptions, the SMT model status, run
  timestamps, and the environment.
* `dynamic.json` (`scry-workflow-dynamic/1`): sanitizer/compiler identity, the compile
  command and result, the harness and input hashes, the run command/stdout/stderr/status,
  the plan marker, and native frames.
* `verify.json` (`scry-workflow-verify/1`), `candidate.json`
  (`scry-workflow-candidate/1`), `finding.json` (the root bundle) and
  `environment.json`.

These are written by `Repro.wiz` and `WorkflowCmd.wiz`, read back by `show`/`verify`
and by the bundle export (`wfRootBundle`), and are the documents a human or another
tool opens. They are variable-length, written once (or replaced on a re-run), never
queried by structure.

### 1.3 Exports and other state

* **SARIF.** `Scry.renderSarif`, `Scry.renderProjectSarif`, `Scry.dynSarifText` render
  a SARIF 2.1.0 document; `TaintCmd`, `DynamicCmd` and `ProjectIO` `FS.writeFile` it.
  It is an external contract, not a store.
* **`.scry-repl/`** (`scry/src/Scry/Repl.wiz:49–53`): `state.json` (the loaded units and
  their `uN.cst` names), `config.json` (JSON mode/diff settings, hand-editable),
  `findings.json` (the same workflow store), `taint.json` and `diff.json` (last
  results), and the `uN.cst` column files (`Scry.CstStore.render`'s spill format).
* **`.scry-project-cache/`** (`scry/src/Scry/ProjectCache.wiz`): one
  `scry-cst 1` entry per translation unit, keyed by path+text+flags and validated by a
  digest of the preprocessed text; written through a sibling `.tmp` and renamed. Large
  values, immutable, content-addressed.
* **Bench/corpus fixtures** (`scry/bench/baseline.json`, truth files): checked-in test
  data, not runtime state.
* **The e-graph.** There is no persisted e-graph and no persisted digest. The "digest"
  is the test-only differential between `Scry.Egraph` and `Scry.EgraphNative`
  (`lib/Scry/EgraphNative.wiz:60–72`); the e-graph is derived state, rebuilt per run by
  `scry egraph`. It is not a storage candidate.

## 2. Which of them fit Quire's guarantees

| store | write pattern | needs delete / epoch | needs query | verdict |
|---|---|---|---|---|
| finding **index** (id, rule, state, file) | append-mostly; triage is one `set`; history appends | not today (`fixed` is a state); a future `forget`/retention does | by id, state, rule, file | **Quire** — the first candidate |
| `findings.json` record body (finding, history, timestamps, candidate) | rewritten with the record | n/a | rendered, not indexed | stay JSON (artifact) |
| `static.json`/`dynamic.json`/`verify.json`/`candidate.json`/`finding.json` | write-once, replace on re-run | no | read by id | stay JSON |
| SARIF | write-once per export | no | no | stay JSON |
| `.scry-repl/state.json`, `config.json`, `taint.json`, `diff.json` | whole rewrite, tiny | no | no | stay JSON (config is hand-edited) |
| `.scry-repl/uN.cst`, `.scry-project-cache/*.tu` | immutable, content-addressed | no | exact key | stay files (large values) |
| bench baselines / corpus truth | checked in | no | no | stay JSON |
| e-graph / its digest | in-memory, derived | no | no | not persisted; no change |

**Why the finding index fits.**

* **Append/commutative writes.** A scan creates findings under fresh ids; two scans that
  discover different findings are two `set`s of different keys and commute. Re-scanning
  an existing id from a base that saw the old version is a `set` on a key it read, so it
  is rejected (per-key first-committer-wins) — the caller re-reads and retries, which is
  exactly what a scan can do.
* **Triage is the non-commutative edit.** Two humans triaging the same finding are a
  conflict, not a merge; the store must reject the stale one. Quire's `set` rule is the
  right semantics; a `+1`-style CRDT would be wrong for a state machine.
* **Deletes.** The workflow state machine has no hard delete today, so the epoch rule is
  unused in the first migration. A `forget` (or a retention policy for fixed findings)
  would be a Quire `del`; the prototype demonstrates the rule.
* **Snapshots.** `scry findings list --json` or a report can hold one snapshot while a
  scan appends; Quire's snapshot is a root pointer, so the report sees a stable view
  without copying the store. The current whole-file store cannot do that: a scan's
  rewrite can be observed half-written by a concurrent reader (and a crash can truncate
  it).
* **Indices replace the in-memory filters.** Today `list --state` parses the whole file
  and filters a list. With Quire, the state index yields exactly the bucket; the rule,
  file and id indices are the same shape. The prototype's cursor costs show the
  difference (Section 3).

**Why the rest should stay JSON.** They are evidence, not a database: variable-length,
written once, read by other tools and humans, and (for `config.json`) hand-edited. A
32-byte fixed record cannot hold them, and adding a generic blob store to Quire is a
separate design (Section 4.1).

## 3. The prototype

`drafts/scry-quire/FindingsQuire.wiz` — the schema and the pure API (check-clean):
interning, the record mapping, `create`/`createAll`, `setState`, `forget`, and the
rule/state/file/rule∧state cursors with a counted fold.

`drafts/scry-quire/FindingsQuireTest.wiz` — the compiled driver (`wiz run`), which
creates `N = 500` findings through `Durable`, reopens, queries, exercises the stale
writer and the delete epoch, and runs the same workload on the JSON path with
`Scry.wfStoreText`/`wfStoreOfText`. `drafts/scry-quire/test.sh` checks and runs it.

The mapping (see the module header):

| Quire | findings |
|---|---|
| key `id` | FNV-1a-64 of the semantic id (`f_<16 hex>`) |
| `kind` | rule id (0–3 in the fixture; a real schema interns the rule pack) |
| `label` | state 0 `new`, 1 `triaged`, 2 `confirmed`, 3 `false-positive`, 4 `fixed` |
| `count` | file id (0–7 in the fixture; a real schema interns the normalized path) |
| `version` | the commit generation |

The indices are `ruleIndex` (`kind`), `fileIndex` (`count`) and `stateIndex` (`label`),
all non-unique.

### 3.1 What the run proves (functional)

* A batch of 500 creates is **one commit** (a scan's write pattern), and the reopened
  table has 500 records.
* A reopen returns the same counts: 125 for rule 1, 100 for state `confirmed`, 25 for
  rule 1 ∧ state `confirmed`, 500 for the table.
* A triage `set` from a snapshot that another triage has superseded is rejected with
  `conflict`; a triage that began before a `forget` (a Quire delete) is rejected with
  `stale`; the committed triage and the delete survive a reopen. The first is the
  per-key rule; the second is the epoch rule.
* The JSON path and the Quire path see the same logical findings (same fixture), so the
  counts below compare the same work.

### 3.2 The numbers

Fixture: `N = 500` findings, 4 rules, 5 states, 8 files; one run on the same machine.
The JSON full store is the real `scry-workflow-store/1` shape (the record's `finding`
blob, candidate and history included); the JSON index is the like-for-like baseline
(`id, rule, state, file, line`, no blob); Quire stores the 32-byte record.

| measure | JSON `findings.json` (full) | JSON index | Quire, one batch commit | Quire, 500 one-record commits |
|---|---:|---:|---:|---:|
| final file bytes | TBD | TBD | TBD | TBD (TBD after compaction, K=8) |
| bytes written to append all 500 | TBD | TBD | TBD | TBD |
| bytes read on reopen | TBD | TBD | TBD | TBD |
| records parsed / decoded | 500 | 500 | 500 | 500 |
| query `state = confirmed`: result | 100 | 100 | 100 | 100 |
| …query work | TBD records examined | TBD records | TBD index entries + TBD node reads | same |
| query `rule = 1` | — | — | TBD entries + TBD nodes | same |
| query `rule = 1 ∧ state = confirmed` | — | — | TBD entries + TBD nodes (post-filter) | same |
| table scan | TBD | TBD | TBD entries + TBD nodes | same |

TBD interpretation.

The measurement is **counts**, not wall-clock time: bytes written, final file size,
bytes read on reopen, records/cursor entries touched. Timings need a `perf-run` window
and are deliberately not claimed here.

## 4. Gaps for a real migration

### 4.1 The record schema, and where the record body lives

Quire's record is fixed at 32 bytes (`drafts/storage-engine/Durable.wiz:163–170`), with
three indexed attributes plus the key. The prototype uses all three for rule/state/file,
which leaves no column for **function**, **line**, **history**, **timestamps** or the
finding blob. Three honest options:

1. **Index in Quire, evidence in JSON (the prototype).** The finding index answers
   id/rule/state/file; `show` reads the artifact directory for the body. This is the
   cheapest and matches how scry already writes `static.json`. It loses the ability to
   query by function without a post-filter.
2. **Widen the record** (a v3 format with, say, 64 bytes and a function id). That is a
   format change to the engine, not a scry change, and it costs page density.
3. **A blob page / value store.** A second table `id → (offset, length)` into an
   append-only blob file would let Quire hold the record body. That is the real
   "documents in Quire" design, and it is a new slice, not a migration.

Recommendation: option 1 for the first migration. Keep `findings.json`'s body fields in
`static.json`/`finding.json`, where they already are; do **not** duplicate the blob into
the Quire file.

**The body already exists, but the two writes are not atomic.** `scry findings triage`
already rewrites the per-finding bundle `finding.json` (`wfWriteBundle`), and that bundle
carries `state`, `history`, `candidate` and the finding (`wfRootBundle`,
`WorkflowCmd.wiz:293–330, 676–682`). So the migration can treat `finding.json` as the
authoritative body and the Quire table as the index. The catch is the pair: a triage would
commit the new state in Quire and then rewrite the bundle (or the reverse), and a crash
between them leaves the index state ahead of the bundle's history. Two honest fixes:

* a **repair on open** that compares the index state with the last `history` entry in the
  bundle and appends a synthetic "state set by the index" entry when they disagree;
* or an **append-only triage table** in Quire (`id, gen, state, actor, reason`) where the
  history is a set of facts and the current state is the last fact; strings are interned
  again (or the reason stays in the bundle). This is the more Quire-native shape, but it
  needs a string-value story, which is the same option-3 blob gap.

The first migration should take the repair-on-open route: it is one function, and the
bundle already has everything the repair needs.

**Interning.** Rule and file ids must be stable and reconstructible. Rule names are a
small closed set from the pack, so `FNV-1a-64(rule name)` is stable across packs and
needs no table. File ids can be `FNV-1a-64(normalized path)`; the path is in
`static.json`/`finding.json` for display. If a string table is wanted, it is a separate
append-only JSON (or a future blob table), not a Quire record.

**Schema evolution.** `Durable.formatVersion` is 2 and `open` refuses any other version
(`Durable.wiz:147, 262–318`); `Meta.schemaGen` exists but is written as 0. The findings
table needs its own `schemaGen` (a findings-schema version, not the page format) and a
migration command that reads `findings.json` and writes the `.quire` file. Unknown
findings schemas must be refused, not guessed; the engine already sets that precedent.

### 4.2 Where the file lives

`--db` is a file path today and defaults to `scry-workflow/findings.json`. A Quire file
is one file too, so the natural default is `.scry/findings.quire` (or
`scry-workflow/findings.quire`) with the artifact directory unchanged. Two practical
rules:

* keep `--db` meaning "the store path"; a `.quire` path selects Quire, a `.json` path
  selects the old path (or add `--store=quire|json` while both exist);
* do not put the Quire file inside `scry-workflow/<id>/` (that is per-finding evidence);
  one store for the project, like `findings.json`.

The REPL's store (`.scry-repl/findings.json`) can use the same module with
`.scry-repl/findings.quire`; its `state.json`/`config.json` stay JSON.

### 4.3 Concurrent `scry` runs

The current store has **no lock**: two `scry findings scan` processes each load the whole
file, append, and rewrite it; the later `FS.writeFile` wins and the other run's findings
are lost. Quire fixes the lost-update part by construction (a snapshot + a validated
commit), but the prototype uses `Durable`, whose single-writer cell is an in-process
`MVar` only. The composed engine already has the missing piece:

* `Multiproc.wiz` takes `flock(LOCK_EX)` for the commit section and `flock(LOCK_SH)` for
  the reader handshake, then holds a snapshot lease; `Handle.getDb`/`Handle.putDb` are
  the multi-process API (`Multiproc.wiz:17–68, 243–310`);
* `Handle.tryPutDb` gives a non-blocking commit, so a `scry` run can report `busy`
  instead of waiting;
* compaction is offline and single-writer; a writer handle that spans a compaction must
  be reopened (`Multiproc.wiz:50–58`).

The migration should use `Multiproc`'s handle, not `Durable`'s, and add a test with two
processes. The prototype's stale test is the validation half (one process); the lock
half is already written and tested in `drafts/storage-engine/MultiprocTest.wiz`.

### 4.4 SARIF and JSON export

Other tools read `findings.json`, `finding.json` and SARIF; those contracts must not
change.

* `scry findings list --json`, `show --json` and `verify --json` keep their existing
  schemas; they are rendered from the index plus the artifact JSON.
* Add `scry findings export --format=findings-json` (or `--db old.json`) that writes a
  `scry-workflow-store/1` document from the Quire index and the artifacts. That is the
  compatibility path for tools that read the file directly.
* Keep the artifact paths in `static`/`dynamic`/`verify` (and the bundle export)
  unchanged; a Quire store changes where the *index* lives, not where the evidence
  lives.
* SARIF stays a rendered output (`Scry.renderSarif`), never a store.

### 4.5 Space, retention and compaction

The prototype's slice-2 writer rewrites the **whole node map** on every commit
(`Durable.wiz:685, 742–791`), so an incremental append is O(n) pages even though the
change is one record. That is a property of this slice, not of Quire: slice 3's COW
B+tree writes only the changed path. Until then:

* a scan's one-commit batch is cheap (Section 3.2);
* many one-record commits grow the file and need compaction (`Compact.wiz`), which
  rewrites only the live pages and keeps the newest `K` roots (`Registry.wiz`, default
  `K = 8`);
* a real `scry` writes in batches (one commit per command), so the prototype's
  incremental case is a stress test, not the expected workload.

The retention `K` is also the horizon for a long-running `show`/report; the design's
lease (a snapshot pins its root) is the end state, and `Registry` already counts pins.

### 4.6 Index build on open

`Durable` rebuilds the indices from the primary records on open
(`Durable.openDbWith` → `dbOf` → `Root.rebuildIndex`). That is O(n) per open, fine for
thousands of findings and a CLI invocation, but it is not a persisted index. Slice 3/4's
index pages remove it; until then a `scry findings show` pays the same O(n) that the
JSON parse pays, only with 32-byte records instead of a full document.

### 4.7 Function queries and multi-index plans

The prototype answers rule, state, file and rule∧state (the latter by scanning the rule
bucket and post-filtering the state, `Findings.ruleStateCursor`). A function query is
not a column; it would be a post-filter over a file/rule bucket, or a fourth attribute
in a wider record. Multi-index intersection (rule ∧ state ∧ file) needs either a
composite index or a plan that intersects two cursors; the design's `Cursor` is
single-source today (`drafts/storage-engine/StorageCursor.wiz`). Neither is a blocker
for the first migration because today's CLI only exposes `--state` and exact `id`.

## 5. A staged migration

**Stage 0 — the prototype (this note).** `drafts/scry-quire/`; nothing imports it;
`scry` is unchanged. Acceptance: `drafts/scry-quire/test.sh` is check-clean and the
driver's assertions pass (batch/reopen counts, conflict, stale, delete).

**Stage 1 — opt-in store.** Add `Scry.FindingsQuire` (or promote the prototype) and a
`--store=quire` / `SCRY_STORE=quire` flag (or a `.quire` `--db` path). On first use,
import an existing `findings.json` (read the whole store, create every record in one
commit, keep the artifact directories). Default remains JSON. Tests: the existing
`scry/tests/workflow-e2e.wiz` run twice, once per store, with `list --json` diffed.
Acceptance: identical `list`/`show` output; no change to the JSON default.

**Stage 2 — the JSON path becomes the export.** Flip the default to Quire; keep
`--store=json` for one release; add `scry findings export` that writes
`scry-workflow-store/1`. External readers use the export (or a documented `jq`-able
dump). Tests: export is byte-for-byte parseable by `wfStoreOfText`; a round-trip
Quire → export → JSON import preserves ids/states/history.

**Stage 3 — the REPL and the other workflow commands.** Point `Repl.findingsPath` at the
same module (`.scry-repl/findings.quire`), keeping `state.json`, `config.json`,
`taint.json` and `diff.json` as JSON. `triage`/`refine`/`repro`/`verify` already go
through the store API, so they switch with it. Acceptance: `scry tests repl.wiz` and
`workflow-e2e.wiz` green on both stores.

**Stage 4 — evaluate, do not assume.** Re-measure a real corpus (not the synthetic 500)
for file size, reopen and query cost; decide whether the project cache or any derived
cache wants a Quire table. Evidence documents, SARIF, the bench baselines and
`config.json` stay JSON by design.

**What would make me stop after Stage 1.** If the real store is dominated by the record
body (it is: the blob is most of the bytes), Quire only replaces the index, and the win
is query/snapshot correctness plus a much smaller working set — not a smaller
`scry-workflow/` directory, which is dominated by the artifacts. That is still a real
win (a scan cannot lose a concurrent triage; a report sees a stable view), but it should
be priced as "a correct index", not "a smaller store".

## 6. How to run it

```text
drafts/scry-quire/test.sh                  # uses .lake/build/bin/wiz
drafts/scry-quire/test.sh /path/to/wiz     # or an explicit build
```

The driver prints `key value` lines (`quire.batch.fileBytes`, `quire.query.rule.cost`,
`json.full.bytesWritten`, …). The numbers in Section 3.2 are copied from one run on the
same machine; the counts are deterministic for the fixture.

## 7. Prior art and in-tree references

* `wiz-notes/storage-engine.md` — Quire's design (snapshots, commutative writes, the
  delete epoch, indices, `.expired`, the staged slices).
* `drafts/storage-engine/` — `Durable` (file format v2, commit protocol), `Registry`
  (retention/leases), `Cursor`/`StorageCursor` (linear query plans), `Compact` (offline
  compaction), `Multiproc` (`flock`), `Mmap` (read-only page decoder).
* `lib/Scry/Workflow.wiz` — the store schema, ids and triage machine;
  `scry/src/Scry/WorkflowCmd.wiz` — load/save and the commands;
  `scry/src/Scry/Repro.wiz` — dynamic evidence.
* `scry/src/Scry/ProjectCache.wiz` — a content-addressed file cache (the model for
  "large values stay files").
* `lib/Scry/EgraphNative.wiz` — why the e-graph digest is a test differential, not a
  store.
