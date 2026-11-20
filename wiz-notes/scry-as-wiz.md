# A scry analysis run is a Wiz file

Status: design + prototype, branch `scry-wiz` (base `integration/train7`), 2026-11-20.
The pure layer is `scry/src/Scry/AnalysisFile.wiz`; the Quire layer and the command are
`drafts/scry-analysis/Scry/QuireGraph.wiz`, with the worked file
`drafts/scry-analysis/analysis.wiz` and the effect test
`drafts/scry-analysis/tests/effect-test.wiz`. `scry-quire`'s note
(`wiz-notes/scry-quire.md` on that branch) is the findings-store prototype; this note uses
the same engine (`drafts/storage-engine/Quire.wiz`, `QuireCursor.wiz`) for the **graph**.

Verified on 2026-11-20: the Quire effect test passes all 39 checks (including the live
view/head query, stale/revision, no-op vs new commit, malformed store, writer lock and
`#ingest` line); `analysis.wiz` checks and runs fresh, printing the refuted claim and the
widget payload. The pure `scry-analysis` group is green on train8 (5/5).

**Two corrections from the owner, both applied here.**

1. **The "lock file" is a content identity, not a mutex.** It records the revision the
   ingested graph corresponds to — a hash over the ingested files, or a git commit —
   and the analysis checks it against the tree on disk, reporting **stale** with both
   values. An advisory `flock` is a separate, optional *writer lock* for concurrent
   ingests; it is never called the lock file.
2. **The graph store is Quire**, the page-backed engine in `drafts/storage-engine/`
   (snapshots, indices, the delete epoch, `.expired`), not `findings.json`/`static.json`.
   A re-ingest is a **new commit** (new generation and root) in the same file; the old
   snapshot stays readable to a reader that holds it.

## 1. The file's lifecycle

`drafts/scry-analysis/analysis.wiz`:

```wiz
import Scry.AnalysisFile
import Scry.QuireGraph

#ingest "fixtures" into "graph.quire"

def manifestText : String := include_str "graph.quire.manifest.json"
def manifest : Scry.Manifest :=
  match Scry.manifestOfText manifestText with
  | .ok m => m
  | .error _ => Scry.emptyManifest

def graphView : Scry.GraphView := manifest.view
def claim : Scry.ClaimResult := Scry.claimCalls graphView
def findings : List Scry.AnalysisFinding := claim.findings
def display : String := Scry.analysisDisplay claim graphView

def main : IO Unit := do
  -- check the revision, open Quire, re-query the view, print the claim and payload
  …
```

1. **Write the file.** Everything except `#ingest` is ordinary Wiz. The command macro
   checks the two string literals and expands to a `def scry_ingest_graph_quire :
   Scry.IngestSpec`; it performs no I/O. Relative paths resolve against the file's
   directory, like `include_str`, but only the command resolves them.
2. **Check / edit.** `wiz check` and the language server elaborate the file normally:
   hover on `manifest` shows `Scry.Manifest`, on `claim` `Scry.ClaimResult`, diagnostics
   are Wiz diagnostics, and `wiz/interactiveGoals`/`wiz/interactiveInfo` work on the
   terms. The file's types are the editor interface; there is no scry-specific request on
   the pure path.
3. **Ingest.** `scry-analysis --file analysis.wiz` (or the code action, §4) executes each
   `#ingest`: it hashes the source tree (or reads the git commit), merges the stores,
   encodes the graph, commits a new **Quire snapshot**, and writes
   `<graph>.manifest.json` after the commit. This is the only step that mutates shared
   state. It holds the separate writer lock.
4. **Read.** The manifest is embedded with `include_str`, so the file must be
   re-elaborated after an ingest; the manifest's `view` is the pure projection the claim
   uses. A production editor should re-elaborate on the command's completion; today it
   does not (§9).
5. **Run.** `main` computes the current revision, compares it with the manifest,
   refuses on **stale** (`exit 3`) with both revisions, opens the Quire snapshot, checks
   that its `gen` is the manifest's, re-queries the view and compares it with the
   manifest's view, then prints the claim and the `WIZ_WIDGET:` payload.

The claim is deliberately small: every `call_expression` node must be the head of a
`call` row. It is universal over the graph, can be `vacuous`, and a missing node is a
finding. `Scry.Prover`'s `noFlow` claim over the taint EDB is the next instantiation, not
a different interface (§10).

## 2. Pure and effectful

| piece | where | effects |
|---|---|---|
| `#ingest` declaration, scanner | `Scry.AnalysisFile` (command macro) | none |
| `Revision`, `Manifest`, `GraphView`, `claimCalls`, widget JSON | `Scry.AnalysisFile` | none |
| encoding a `Scry.Facts` into Quire records | `Scry.QuireGraph` (`Scry.G.encode`) | none |
| reading the tree, git, Quire open/commit, manifest write, writer lock | `Scry.QuireGraph` | file system, `mmap`, `flock`, `git` |
| the command | `drafts/scry-analysis/ingest-main.wiz` | calls the above |

The elaborator cannot write the graph: a `#eval` runs with `externImpls := false`, so
foreign calls (including `mmap`/`flock`) are unavailable. The file is checkable and
pure; the runner is compiled (`wiz run`) and effectful. That boundary is the design, not
an accident.

## 3. Ingestion: the command, the code action, the revision

**Command grammar.**

```
scry-analysis DIR --graph FILE [--git]     # the slice's command
scry-analysis --file analysis.wiz          # every #ingest line of a file
```

The production surface is `scry ingest DIR --graph FILE`; it is not wired into
`scry/src/Scry/Cli.wiz` in this slice because the engine is still in `drafts/` (§10).

**The code action.** `Scry.ingestCodeActionJson uri root dest start stop` returns:

```json
{
  "title": "Ingest fixtures into graph.quire",
  "kind": "refactor.rewrite",
  "data": {"uri": "file:///…/analysis.wiz", "start": 10, "end": 40},
  "command": {
    "title": "Ingest fixtures into graph.quire",
    "command": "wiz.scry.ingest",
    "arguments": ["fixtures", "graph.quire"]
  }
}
```

The server must advertise `executeCommandProvider` and handle `workspace/executeCommand`
by spawning the `scry-analysis` command (the Lean LSP cannot import a Wiz package
module); then publish the returned diagnostics at the `#ingest` range. Today the server
has neither, so the action is a tested payload, not a live editor action (§9).

**The revision is content identity.** The manifest's `revision` is one of:

| kind | value | when |
|---|---|---|
| `tree` | `t_<16 hex>`: FNV-1a-64 over the ingested files' `path|size|content-hash`, in name order | a plain directory (the slice's fixtures) |
| `git` | the `HEAD` commit (`git-sha1`), plus `dirty` and `dirtyHash = FNV(status + diff)` | a git checkout, clean or dirty |

FNV is not cryptographic; the manifest says `algorithm: fnv1a64` so nothing claims
otherwise. A git revision gets the commit's own identity; a dirty checkout is explicitly
not its commit (both the commit and the dirty hash are compared).

**Remote revisions.** A manifest may name a git revision that is not checked out here.
`Scry.G.remoteCheck root rev` runs `git cat-file -e <rev>^{commit}`; when it is absent,
ingest **refuses with "revision … is not present in this checkout; fetch it first"** and
writes nothing. The slice tests that refusal.

**Staleness, always with both values.** `Scry.revisionVerdict manifest current` is
`fresh` only when kind, value, dirty flag and dirty hash all match. Otherwise it is
`stale` with the manifest's revision, the current revision and a reason (kind changed,
tree changed, dirty state changed, or no manifest). `Scry.renderRevisionVerdict` prints
both, e.g.

```
revision: STALE (manifest tree:fnv1a64:t_9a…, source tree:fnv1a64:t_41…): the source tree differs from the ingested tree
```

The runner exits 3 on stale. It never analyses the new tree against the old graph.

**Updating is a new commit, not a mutation.** In `Scry.G.ingestTree`:

1. take the separate writer lock (`<graph>.writer`, `flock(LOCK_EX)`, §4);
2. read the old manifest sidecar (a malformed manifest is an error, not overwritten);
3. compute the new revision (tree or git);
4. if the revision *and* the store generation equal the old manifest's, return
   `committed = false` (no snapshot);
5. otherwise encode the merged facts, build one transaction: **delete every record id the
   old manifest named** (nodes `0…N-1` and rows `N…N+M-1`) and **set the new records**;
6. `putQ` publishes a new `gen` and root (Quire's copy-on-write); the old snapshot is
   still readable by a reader that holds it, and retention keeps its root until
   compaction (`.expired` / `Registry` K);
7. write the manifest (`<graph>.manifest.json`) **after** the commit, with the new `gen`.

A crash between 6 and 7 leaves `store.gen > manifest.gen`; the runner reports
"manifest behind store", never fresh. A crash before 6 leaves the old store and old
manifest — consistent. The manifest is written by sibling-plus-rename.

## 4. The separate writer lock

The revision manifest does not serialise writers. Two ingests can still open the same
Quire file and both allocate pages from the same `pageCount`; `putQ`'s `MVar` is
in-process only. The slice therefore has a **writer lock**:

* `<graph>.writer`, `open(O_CREAT)` + non-blocking `flock(LOCK_EX)` (`Fd.tryLock` in
  `lib/Sys.wiz`, backed by `wiz_sys_fd_flock`);
* a live holder → the second ingest fails with "another ingest is writing <graph>";
  there is no timeout and no pre-emption;
* the lock is released and the descriptor closed on every path, including an I/O error;
* a dead process leaves no lock (the kernel drops it). The file is never unlinked (the
  unlink race would let a waiter lock an old inode).

This is exactly the mechanism `drafts/storage-engine/Multiproc.wiz` documents for
Quire's commit section, reduced to the one writer `scry` needs. It is **not** the
revision check and is not called the lock file. `scry-quire`'s note reaches the same
conclusion for the findings store (`Multiproc.handle`, one writer, compaction offline).

## 5. The Quire graph

**API.** `Scry.QuireGraph` uses:

| Quire | use |
|---|---|
| `openQ path indices` | open/create the graph; an open is a meta pick plus `mmap` |
| `getQ h` | the latest committed `QSnapshot` (`gen`, `root`, `indexRoot`, empty `ws`) |
| `putQ h tx` | commit a `QSnapshot` write-set; returns `Outcome` (`committed gen` / `rejected`) |
| `QSnapshot.record tx id patch` | add a `set`/`del` to the transaction |
| `QSnapshot.getNode s id` | one primary read |
| `QSnapshot.indexCursorRange d kr s` | a `QCursor` over an index bucket, projecting **primary ids** (no primary read) |
| `QCursor.fold` | consume the cursor (the linear handle) |
| `closeQ h` | close the descriptor (outstanding snapshots keep their mapping) |

Indices (`IndexDef` id/field/unique; fields 0 kind, 1 count, 2 label):

```
kindIndex  = IndexDef.mk 0 0 false   -- node kind / relation id
countIndex = IndexDef.mk 1 1 false   -- column 0 / edge src
labelIndex = IndexDef.mk 2 2 false   -- column 1 / edge dst
```

**Record encoding.** A Quire record is 32 bytes `(id, kind: U32, count: U64, label: U32)`;
the graph is:

| record | id | kind | count | label |
|---|---|---|---|---|
| node | node id `0…N-1` | node-kind id (`kinds` table, base 1) | span start | span stop |
| edge row | `N + edge index` | `1000 + edge-label id` | source node | target node |
| relation row | `N + E + row index` | `2000 + relation id` | column 0 | column 1 |

`kinds`, `edgeLabels`, `relations` and `fileTable` are interned in the manifest; ids are
stable for that manifest. `tableOf` already applies the base (`1`/`1000`/`2000`), so the
record writers use the table's id **directly** (a first version added the base twice and
the live `call` query missed every row; the effect test catches that). Edges are rows too
(`child` etc.), so a graph query needs no separate edge table. `fileTable` is
`(path, file-node id)`: the `file_of` relation's second column is the synthetic
`file:<path>` node id, not a dense file index. **Arity 2 only**: the graph's `call`,
`file_of` and CST edges are arity 2; a higher-arity relation is refused with a diagnostic,
not truncated. Spans and column 1 must fit `U32` (spans under 4 GiB); the encoder refuses
otherwise.

**Queries.** `Scry.G.viewOf s m`:

* call sites: `indexCursorRange kindIndex (eq (kinds["call_expression"]))` → **node ids**
  `< N` → `getNode` for the span, and `fileOf` (below) for the path;
* call heads: `indexCursorRange kindIndex (eq (relations["call"]))` → **row ids** →
  `getNode` and take `count` (column 0);
* errors: the same with `kinds["ERROR"]`;
* `fileOf`: `indexCursorRange countIndex (eq nodeId)` → row ids → keep the one whose
  `kind` is `relations["file_of"]`; its `label` is a file-node id, and `fileTable` maps
  that id to the path. (`indexOnlyRange` projects the *index key*, not the primary id; the
  first version used it and returned the kind value as if it were a row id, which the
  effect test caught.)

The manifest also stores `view`, computed from the merged `Scry.Facts` at ingest. The
editor's claim uses that pure view; the runner re-queries Quire and compares
(`Scry.sameView`), and checks `store.gen == manifest.gen`. A stale view is reported, not
rendered as the new code.

**What Quire gives the design.** A reader holds a `QSnapshot` (a root pointer) while an
ingest commits; the report/view is stable without copying the store. Two ingests are
serialised by the writer lock; a stale transaction is rejected by the per-key rule and
the delete epoch, not merged. `QDoCompact`/`Registry` keep the last K roots and
`.expired` bounds a reader that outlives retention. The prototype does not compact; a
graph store needs a compaction policy once ingests are frequent.

## 6. The widget payload

`Scry.analysisDisplay claim view` returns `WIZ_WIDGET:` plus:

```json
{
  "schema": "wiz.widget/1",
  "html": "<div class=\"wiz-widgets\" …>…</div>",
  "widgets": [
    {"id":"claim","kind":"button","value":"refuted","label":"claim calls-recorded: refuted",…},
    {"id":"finding-a_7","kind":"button","value":"7","label":"node 7 … in beta.c",…},
    {"id":"paths","kind":"plot","data":"{…claim…}",…}
  ],
  "count": 3,
  "scry": {
    "schema": "scry.analysis/1",
    "claim": {"name":"calls-recorded","status":"refuted","summary":"1 of 2 …","findings":[…]},
    "findings": [{"id":"a_7","file":"beta.c","node":7,"span":[4,14],…}],
    "graph": {"nodes":9,"edges":5,"relationRows":8}
  }
}
```

The top level is what the Jupyter widget kernel and `Widget.parseDisplay` already
understand, so the payload renders today; the `scry` key is the extension an infoview
reads. Each finding button's **value** is the node id, so a click can jump to
`(file, span)` without parsing the label. `Scry.analysisNoop` is the default callback; a
file can supply its own.

The editor wiring is the gap: `lib/Infoview.wiz`/the web client have no widget channel.
Two additive options: recognise `WIZ_WIDGET:` in `#eval`/info output, or add a
`wiz/widget` request that evaluates the file's `display` definition. The payload tests
pin the shape either way.

## 7. Gap list against today's `scry` CLI

| today | the analysis file | gap |
|---|---|---|
| `scry taint FILE.c` runs parse → lower C → Wil → rule pack → findings | the file states a claim over a Quire graph | the Wil/EDB pipeline is not callable from the file; `Scry.Prover` is library-only |
| `scry project DIR --taint` (`Scry.Project`, `ProjectCache`) | `#ingest DIR` merges `*.facts.json`/`*.cst` | no `cc -E`, tree-sitter, `Scry.Lower` or project cache; the ingest is a merge, not a frontend |
| `scry findings scan/refine/repro/verify` on `findings.json` | claim findings are returned, not persisted | no `Scry.Workflow` upsert; the findings Quire store is `scry-quire`'s prototype |
| `scry report FILE` HTML | the widget is the report | the HTML report's evidence/limits are richer; link to it, don't replace it |
| `scry repl FILE` | the file + `main` is the surface | no prompt/`:load`; the REPL remains the quick path |
| `scry parse --stats`, `scry query` | `Scry.graphJson`, `Scry.queryKind` are ordinary calls | the S3 query language is still three traversals |
| `scry` has no graph store | Quire `graph.quire` + manifest | the engine is in `drafts/`, not the package; `scry ingest` is not wired |
| `findings.json` had a mutex-less whole-file rewrite | Quire snapshots + a separate writer lock | no compaction policy, no two-process test yet |
| no revision identity | `tree`/`git` manifest, stale check | no automatic re-elaboration after ingest; no remote fetch command |
| no widget/claim layer | `wiz.widget/1` + `scry.analysis/1` | infoview/LSP plumbing (§9) |

## 8. Tests

| file | checks |
|---|---|
| `Tests/Groups/ScryAnalysis.lean` (`scry-analysis`) | `#ingest` macro/scanner; merge → view → claim (refuted at beta.c/node 7); manifest JSON round-trip; fresh/stale (tree change, kind change, dirty change); diagnostics/code-action JSON; widget bundle (3 widgets, one finding, `scry.analysis/1`) |
| `drafts/scry-analysis/tests/effect-test.wiz` | real Quire: **39/39 PASS** — ingest → graph+manifest (9 nodes, 5 edge rows, 8 relation rows); live `gen`/view match; stale with both revisions; same-revision re-ingest is a no-op; changed revision commits a new snapshot (`gen+1`); malformed store fails closed; writer lock refuses a second ingest; absent git revision says "fetch first"; `#ingest` file form + line 3 diagnostic; widget payload |
| `drafts/scry-analysis/analysis.wiz` | the worked pure claim + the effectful runner (revision gate, Quire read, view comparison, display) |

Commands:

```sh
# pure group (needs `lake build wiz tests`; no tree-sitter)
lake test -- '=scry-analysis'

# the Quire slice (compiled: mmap, flock and quire_seal.c)
wiz --cflags "-Idrafts/storage-engine" \
    -I drafts/storage-engine -I drafts/scry-analysis -I scry/src \
    run drafts/scry-analysis/tests/effect-test.wiz

# the worked file (after an ingest has written graph.quire + manifest)
wiz -I drafts/storage-engine -I drafts/scry-analysis -I scry/src \
    run drafts/scry-analysis/analysis.wiz
```

## 9. What the editor still needs

1. **LSP execution.** `workspace/executeCommand` + `executeCommandProvider` and a
   subprocess bridge to `scry-analysis`/`scry ingest`; without it the code action is
   inert.
2. **Widget delivery.** A `wiz/widget` request or recognition of `WIZ_WIDGET:` in
   `#eval`/info output; the infoview has no widget node.
3. **Re-elaboration after ingest.** `include_str` is read on `didOpen`/`didChange`; the
   server has no file watcher. The command should send `wiz/elaborated` for the analysis
   file after a successful ingest.
4. **Finding navigation.** A request mapping `(file, start, stop)` to a
   `Location`/`showDocument`; the infoview currently selects tagged subterms only.
5. **Diagnostics.** The ingest diagnostic's range is the `#ingest` line; a load failure
   names the store. Merge the two channels and offer "open the store/run ingest".
6. **Quire promotion.** When the engine leaves `drafts/`, `scry ingest` imports it
   directly; the writer lock should then use the multi-process handle
   (`Multiproc.wiz`) rather than a second open.

## 10. Honest gaps

* **The editor path is not wired.** The code action and payload are shapes; the server
  has no `executeCommand`, widget channel, or re-elaboration notification.
* **The frontend is a merge.** Ingest lowers existing `*.facts.json`/`*.cst` stores,
  not C source. A real `#ingest` is `Scry.Project` + `cc -E` + tree-sitter +
  `Scry.Lower`; the fresh worktree lacks the native C# grammar, and the slice avoids the
  native link deliberately.
* **The Quire record schema is minimal.** Three numeric columns cannot hold a path, a
  parent and flags at once; the slice uses the manifest for names and `file_of`, arity 2
  only, and a `U32` span/column. A production graph needs a wider record or a blob table
  (`scry-quire` §4.1 reaches the same conclusion for evidence bodies).
* **No compaction policy.** Quire appends a commit per ingest; `QDoCompact`/`Registry`
  keep K roots, but the slice does not schedule compaction, and a long-lived reader can
  hit `.expired`.
* **The claim is graph-consistency, not taint.** `claimCalls` is universal over
  `call_expression`; it is not `noFlow` over the taint EDB. Wiring `Scry.Claim` to a
  Quire-backed EDB is the next slice.
* **FNV is not cryptographic.** A revision collision would be a false "fresh". A git
  commit is the strong identity when the source is a checkout; a remote-only revision is
  refused rather than approximated.
* **The writer lock is not the revision check.** It prevents two writers; it does not
  make a stale analysis fresh, and a reader of the graph (`include_str`) takes no lock.
  The manifest and the generation check are what protect the analysis.
* **`scry-quire`'s note is about the findings store**, not the graph; its schema lessons
  (index in Quire, evidence in JSON, intern tables, migration) are reused here, but a
  first-class graph schema is still this note's proposal, not a decided format.
