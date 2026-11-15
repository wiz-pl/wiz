# Stage 11: tooling

## 11a–b: queries and a language server

* **Queries** (`Wiz/Query.lean`): elaboration is a pure function of the text, so each
  command's result is memoised under a **content hash chained through every command
  before it**. After an edit, only the commands from the edit on are elaborated again;
  the same text gives the same result (deterministic builds). The elaborator records
  identifiers with their types and ranges, and each global's declaration site, for
  `hoverAt`, `definitionAt` and `completionsAt`.
* **`wiz lsp`** (`Wiz/LSP.lean`): the Language Server Protocol over stdio, with
  diagnostics as you type, hover types, go to definition (also into `lib/`), and
  completion of global names. Each open document has its own query engine. A document's
  `include_str` files are read from its own directory, as on the command line (see
  [13-language/include-str.md](13-language/include-str.md), "Language server").

## 11c: a shared, content-addressed cache

`wiz check`/`build`/`run` keep each command's **effect** (declarations, messages,
registrations, info trees) in the cache directory (`--cache DIR`, default `~/.cache/wiz`;
`--no-cache` turns it off), under the command's chained content hash. A shared directory is a shared cache,
since equal keys mean equal results. Imported modules are cached command by command
too. Commands that change the grammar or the macros rerun (they are cheap).
`Wiz/Cache.lean` serialises terms as S-expressions (quantities through the rig's
literal syntax). Every example gives the same output from the cache as without it.

The store is **layered**: one directory is read and written (`--cache DIR`), and any
number of further directories are read-only (`--cache-ro DIR`, repeatable). A lookup
tries the write cache first, then the read caches in the order given; a missing or
unparsable entry falls through to the next, and only a full miss is a miss. `put` and
the module marker (`markSeen`) write to the write cache alone; with no write cache the
marker stays in memory for the run. `binaryId`'s memo (`bin/`) also belongs to the write
cache: a `--cache-ro`-only run hashes the executable each time, so a read-only directory
is never created or modified. `--no-cache` clears both lists; flags parse left to right,
so a later `--cache`/`--cache-ro` adds one again. `grail` takes the same flags (and
`cache-ro` as a build-file setting) and forwards them to its jobs.

This is what a Nix package uses: its build ships a cache in `$out/share/wiz/cache`, and
a run is `wiz check --cache-ro $out/share/wiz/cache FILE` (or with a writable
`--cache ~/.cache/wiz` in front). For a run with *only* read caches, say
`--no-cache --cache-ro DIR`: `wiz` and `grail` default to a writable cache, and
`--no-cache` clears it (it clears both lists) before the later `--cache-ro` adds the
read-only one back. The read-only cache is shared by every user of the store path and
is never written.

**Module regions (`--region-cache`, experimental).** A module's effects are also written
as one `<cache>/<binary ⊕ module key>.wizr`, a `Lean.CompactedRegion` (the format of
`.olean`: an mmap'able image of the terms, saved at a base address derived from the module
name; `Wiz/Cache.lean`, "Module regions"). `--region-cache` serves a module's cached
commands from that region instead of decoding its `.wizc` entries. The text entries stay
the authority and the fallback: a missing, truncated, corrupt (bad checksum) or mistagged
region is a miss, and the next run rewrites it. The command loop (keys, imports, duplicate checks) is unchanged — it
still parses every command and only takes the effects from the region, so the result is
the same as the text path's. The artifact holds only `Effect`s, which have no closures, so
the loader applies them to the live state (`Effect.apply`): `loader`, `trustedModule`,
`pp.run` and the `Budget` stay live. `--region-stats` (a `wiz` flag) prints what came from
a region.

`grail` takes the same flag, as `--region-cache` or as the `region-cache` setting of
`grail.wiz`/`grail.local.wiz` (`Toolchain.regionCache`). It is part of the toolchain record,
so `grail config` shows it and `Toolchain.toFlags` passes it to every job: a job's
in-process elaboration reads and writes regions in the same layers as its `.wizc` entries,
and a warm `grail build --region-cache` takes the package modules' effects from `.wizr`
instead of decoding the text.

**Regions and layers together.** Regions live in the same directory layers as the text
entries: a lookup tries the write cache first, then the read-only caches in order (so a
region shipped in `--cache-ro DIR` is used, and a run with only read caches reads
regions), and a region is only ever written to the write cache. A `--region-cache` run
with `--cache-ro` therefore reads both kinds of artifact from both kinds of layer, never
modifies a read-only cache, and still falls back to the text entry of the same module
(or a later layer) when a region is missing or mistagged.

**Checksums (`regionFormat` 2).** A `.wizr` file comes with a sidecar, `<region>.wizs`: the
8-byte little-endian 64-bit hash of the `.wizr`'s bytes (`Wiz/Cache.lean`, `checksumFile`:
one read of the image and the runtime's `ByteArray.hash`). It is
checked *before* the image is mapped, so a same-size bit flip — even one in a pointer the
type-erased reader would follow — is an ordinary miss: the text entry answers, the write
cache rewrites the region, and a read-only layer is left alone. Truncation, and a region
whose sidecar is missing or the wrong size, are misses too. (Not a trailer: Lean's compacted
reader walks the image backwards from its end, so appended bytes shift the root and the read
fails; the sidecar keeps the image byte-identical and lets the raw bytes be hashed first.)
The cost is one sequential read (the pages are then mapped anyway) and a hash pass, not a
decode: a few milliseconds on a multi-megabyte region. The region format is disposable and
never migrated: a file of the wrong `format`/`magic` is a miss, and the writer always
produces the current one (`regionFormat` is bumped when `Effect`, `Decl`, `Term` or `Info`
change shape, or the framing does).

**Pruning.** `wiz cache prune [--days N] [--dry-run]` (default 30 days) and
`--cache-prune DAYS` on a run remove keyed files (`.wizc`, `.wizm`, `.wizr`, `.wizs`) whose
modification time is older than N days, recursively, **in the write cache only**:
`--cache-ro` layers are never passed to the pruner, and nothing but those four extensions
is touched (the `bin/` memo, a package's files and symlinks stay). `--cache-prune` runs
before the command, so this process has not mapped a region it deletes; `--dry-run` only
counts and prints (`cache prune: would remove 12 files (… .wizc, … .wizm, … .wizr,
… .wizs), 3 GiB older than 7 days in …`). A pruned entry is just a miss: the next run elaborates and rewrites it. N must
be at least 1, and a read-only layer cannot be pruned even if it is passed with `--cache-ro`
(the command says so).

**Output manifests (`--cache-verify`, integrity only).** A cache key is an *input* hash;
until this stage the bytes an entry returns (its *output*) were trusted because they were
in the cache. `wiz` now writes a manifest with a SHA-256 of each entry's bytes and checks
it before applying the effect: a truncated, rewritten or swapped entry is a **miss** (the
text entry, the next layer, or re-elaboration answers), never a wrong result. There is no
signature yet — see P3 below.

The layout is one manifest per module (the note's P2) plus a per-layer generation index
(P1):

```
<cache>/manifest.d/<binary ⊕ fast key>-<sha256 key>.wizmf   -- one module, or one root file
<cache>/manifest.sexpr                                      -- generation index for the layer
<cache>/<binary ⊕ fast key>-<sha256 key>.wizr               -- one module's region
```

**Strong cache keys.** The 64-bit `hash`/`mixHash` keys are indexes, not collision-resistant
digests. A `Cache.Key` therefore carries a fast half (the old key, used by in-memory
tables, `.wizc` names and Lean's maps) and a SHA-256 half (used by region and manifest names,
manifest entries and verification). The SHA-256 half is domain-separated and
length-prefixed (`Wiz.Smt.Sha256.framed`): `["ab", "c"]` and `["a", "bc"]`, or a module key
and a toolchain id, cannot share a preimage. Module keys hash the exact text, headers,
`include_str` contents (under an `includeKey-v1` domain), imports and trust flag; command
keys chain the previous SHA-256 key and the command text;
`Toolchain.tag` and `Toolchain.targetTag` are the strong toolchain and target namespaces
(the 64-bit `Toolchain.id` remains the build/job index). A manifest or region requires both
halves, so a 64-bit collision is a miss (the text path or elaboration answers), never a
wrong effect. Format 1 manifests and format 2 regions are ignored by the new names and
regenerated; no unmigrated file is read under a strong key.

A module manifest lists its `.wizc` entries and its `.wizr` region with `key`, `key-sha`,
`file`, `size`, `sha256` and `format` (`salt` for text, `regionFormat` for a region), plus
`module`, `binary` (`binaryId`), `toolchain` (SHA-256 of the executable), `toolchain-tag`,
`target-tag`, `rig`, `prev` (the previous manifest root) and `valid-until`. Its `root` is
an RFC 6962-style Merkle root over a metadata leaf and the entries, so editing
`prev`/`valid-until` breaks the root too. `manifest.sexpr` records the generation number,
the previous root, the optional expiry and one record per module (fast key, SHA-256 key,
name, file, digest), with its own root. Only the write cache is ever written; a
`--cache-ro` layer is read and byte-identical after a run. The `.wizr` sidecar (`.wizs`) is
still checked first: a corrupt region never reaches the type-erased reader even when no
manifest exists.

The policy is `--cache-verify off|warn|strict` (`--cache-verify=MODE` also works):

* `off` — no manifests are read or written; the cache is exactly as before.
* `warn` (default) — a manifested key is served only if its bytes match. A new key has a
  SHA-256 half, so an unlisted write-cache entry is a miss (nothing binds its bytes to the
  strong input key); an old fast-only key still falls through, and `--cache-verify off`
  restores the old lookup. An old local cache is one cold pass, then it is rewritten with
  manifests. A `--cache-ro` layer is **strict**: an entry there is used only through a
  manifest, so deleting a manifest cannot downgrade a read-only layer to unverified. When
  a read-only layer has bytes for a module but no manifest, `wiz` warns once per layer (an
  empty layer is silent).
* `strict` (alias `require`) — only manifested entries are used anywhere; an unlisted key
  is a miss. A cold run writes the manifests, so it becomes strict-warm in one pass.

A manifest whose root does not validate, whose `valid-until` (or whose layer generation's)
has passed, or whose entry digest does not match is a miss: it is not repaired in a
read-only layer. `wiz cache verify [--strict]` scans every layer's manifests against the
bytes (exit 1 on a mismatch, a missing file, an expired manifest, or — with
`--strict`/`--cache-ro` — an unmanifested keyed file); `wiz cache manifest [--valid-days N]` rebuilds the generation
index (`prev` chains it to the old one) and can set its expiry. `--cache-verify-stats`
prints the per-run counts (manifests, verified entries/regions, mismatches, unverified).

Compatibility default: with no manifest (or `--cache-verify off`) existing caches keep
their old behaviour; the write cache's old unverified path is still available in `warn`.
Manifests are additive files — `.wizc`, `.wizr` and `.wizs` keep their names and bytes,
so an unmanifested cache is byte-identical and no key or salt changes.

**Not signatures (P3).** An unsigned manifest detects corruption and a mirror that swaps
a listed entry, but a writer who controls the manifest can rewrite both it and the bytes,
and can delete it (in `warn`, for the write cache). The missing half is an external
signature over the manifest (DSSE/minisign/`ssh-keygen -Y sign`), a key-id policy with
revocation, and a witnessed log; the attestation prior-art note calls this E2/P3. So do
not read these manifests as provenance: they are integrity, not authenticity.

Next: finer dependencies (re-elaborate only what an edit affects, not everything
after it).

## 11d: the info tree, the infoview and code actions

* **The info tree** (`Elab/Basic.lean`, `Elab/Info.lean`): while elaborating, the
  elaborator records identifiers, the expected type of every checked term (and of every
  hole), the open goals before and after each tactic, `match`es and declarations. It
  keeps values and contexts as it goes (free) and quotes and zonks them at the end of the
  declaration, into `Term`s, not strings. An error carries the state it was thrown in,
  so a declaration that fails (unsolved goals, a hole) still has its tree. The tree is
  memoised and cached with its command; hovers and go to definition read it.
* **The infoview** (`Wiz/Infoview.lean`): `Term.prettyTagged` prints a term exactly as
  `Term.pretty` does, as tagged text: every subterm is a tag whose ref points into the
  document's session table (valid until the next edit). `wiz lsp` answers
  `wiz/plainGoal`, `wiz/plainTermGoal`, `wiz/interactiveGoals`,
  `wiz/interactiveTermGoal` and `wiz/subtermInfo` (a subterm's type, from the kernel,
  and where a constant was declared); the protocol is in
  `wiz-notes/infoview-protocol.md`.
* **Code actions** (`Wiz/Actions.lean`): diagnostics carry a code and data; the server
  offers *did you mean* (edit distance ≤ 2 over locals and globals), *add missing cases*
  (`| .c x y => ?c` per missing constructor) and *add type ascription* to a `def` without
  a type, with edits inline or through `codeAction/resolve`. The common errors have
  stable codes (`Wiz/Core/ErrorCode.lean`, listed in [error-codes.md](../error-codes.md)),
  and the quick fixes are keyed on them: also *did you mean* for fields, constructors and
  imports, *add the missing import*, and `@f` / dropping the `@` when the argument count
  is off by the implicit parameters.

```
def k : Nat → Bool → Nat := by
  intro n         -- wiz/plainGoal here:  n : Nat ⊢ Bool → Nat
  intro b
  exact n
def four : Nat := doubel 2    -- unknown identifier 'doubel'   [Did you mean 'double'?]
```

## 11l: the infoview socket

`wiz lsp --infoview SOCK` also listens on the Unix socket `SOCK`, for infoviews that run
beside the editor (the terminal infoview connects there). The editor never says where
its cursor is, so the server infers it from the editor's requests: any request with a
position (hover, `documentHighlight`, which the server now advertises so that editors
send it on every move, go to definition, completion, …) and code actions (at the
range's start). When the cursor moves, and after each elaboration of its document,
every connected infoview gets `wiz/infoview/cursor` (uri, position, session) and pulls
with the ordinary `wiz/*` requests on the socket; sessions and refs are the editor's.
Lean's library has no Unix sockets, so `c/sockets.c` (compiled into the executables by
the linker, `moreLinkObjs` in the lakefile) listens, accepts, and turns a connection
into two ordinary Lean handles. The server's state stays single-threaded: a reader
thread per connection feeds one channel, and one loop answers in order. Protocol §8 of
`wiz-notes/infoview-protocol.md`; tested in-process (the `lsp-server` group: the editor
on a socket pair, an infoview on the socket).

## 11m–n: the infoview, in a terminal and in a browser

```
wiz lsp --infoview /tmp/wiz.sock          # the editor's server (11l)
wiz-infoview /tmp/wiz.sock                # in a tmux split: the goals at the cursor
wiz-infoview --file t.wiz --at 4:5        # or on its own: starts `wiz lsp` itself
web/build.sh && web/bridge.sh             # the same infoview in a browser
```

Both clients are Wiz programs, and they share their logic:

* `lib/Json.wiz`: JSON values (mutual inductive types: Wiz has no nested ones), a
  parser and a printer. Strings are code points; `\uXXXX` escapes and surrogate pairs
  are decoded, and the printer escapes control characters (or everything non-ASCII,
  `Json.renderAscii`).
* `lib/Infoview.wiz`: the protocol's tagged text and goals; a **layout** that flattens
  tagged text into styled pieces (numbering the tags in reading order), word-wraps them
  to a width with hanging indents, and renders lines with SGR colours by kind; the same
  goals as **HTML** with a `data-ref` and `data-idx` on every subterm's `<span>`;
  navigation (next, previous, enclosing, first inside); `Content-Length` framing
  (counting UTF-8 bytes); and the decoding of terminal keys and SGR mouse reports.
* `infoview/Tui.wiz` (`infoview/build.sh`): the terminal program. The alternate screen,
  raw mode, `poll` over the keyboard, the socket and a `SIGWINCH` self-pipe, and Unix
  sockets are `infoview/term.c` (linked by `link_c`, 9f), bound with `extern` (Wiz has no callbacks or
  structs in its FFI, so the event loop is Wiz around a blocking `iv_wait`). ←/→ select
  a subterm, ↑/↓ go out of and into it, and the bottom line says what it is
  (`wiz/subtermInfo`); a mouse click selects too.
* `web/Web.wiz` (`web/build.sh`): the page's language client, compiled to C and then to
  WebAssembly by Emscripten (`wiz --cc emcc`, with `web/js.c` by `link_c`, 9f): wasm64 keeps the runtime's 62-bit small numbers, mini-gmp
  stands in for GMP. It is a library (09-ffi.md, 9g): the page calls its exported
  `wiz_web_step` (state, event → state) on every event, so nothing waits in Wasm. The page
  (`web/infoview.html`, `web/infoview.js`, about 100 lines of JavaScript) only moves events
  in and HTML out. It talks to `wiz lsp --ws PORT` (11o) directly; `web/bridge.sh`
  starts that server and serves the page.

Running it in tmux, next to an editor whose language server is `wiz lsp --infoview
/tmp/wiz.sock` (11l):

```
infoview/build.sh                                   # → .lake/build/bin/wiz-infoview
tmux split-window -h -l 60 '.lake/build/bin/wiz-infoview /tmp/wiz.sock'
```

The pane waits for the server, then follows the editor's cursor. Without an editor:
`wiz-infoview --file examples/tactics.wiz --at 6:3` (`[` and `]` move the line).
`infoview/test.sh` (in the `infoview` test group) runs the terminal infoview against
`infoview/stub_server.py` (canned goals; as text and in a pseudo-terminal) and against
the real `wiz lsp --infoview`, with `infoview/editor_stub.py` as the editor.
`web/test.sh` (needs nix: Emscripten, Chromium; not in CI) runs the Wasm module under
Node (against the stub), then the page in headless Chromium over the DevTools protocol,
against the real `wiz lsp --ws`.

### 11o: the infoview over a WebSocket

A browser can't open a Unix socket, so `wiz lsp --ws PORT` also listens on a WebSocket
(RFC 6455), on `127.0.0.1` only unless an address is given (`--ws ADDR:PORT`; with
`--no-stdio` there is no editor on stdin). `Wiz/WebSocket.lean` is the protocol: the
HTTP upgrade (the answer proves the server understood it: base64 of the SHA-1 of the
client's key and a fixed GUID, both written here), an `Origin` check (any web page may
open a WebSocket to `127.0.0.1`, so only local pages are let in), and frames (a length
in 7, 16 or 64 bits; the client's payload XORed with a mask; fragments; ping and close).
One JSON-RPC message travels per text frame. A WebSocket client is an infoview (it is
told where the cursor is and pulls goals) and may also edit documents of its own, so the
web infoview, which is its own editor, needs no bridge. `c/sockets.c` gained TCP
listen/accept/connect, with connections again as plain Lean handles; the server loop
(`serveWith`) handles messages from every connection in order, as before. Protocol §8.2;
tested in-process (the `lsp-server` group: frames of each length class, the handshake's
RFC example, foreign origins refused, an editor on a socket pair and two pages).

## 11p: a Neovim plugin

`editors/nvim/` is **wiz.nvim**, a Lua plugin for Neovim ≥ 0.10 modelled on lean.nvim
(installation, options, keymaps and the full abbreviation list are in its README):

* **The language server.** The `wiz` filetype (`*.wiz`), a syntax file for highlighting
  (no tree-sitter), and `wiz lsp` started with `vim.lsp.start` for each Wiz buffer, rooted
  at the nearest `grail.wiz`, `wiz-toolchain`, `lakefile.toml` or `.git`. `lsp/wiz.lua` is the same
  configuration for Neovim 0.11's `vim.lsp.enable 'wiz'`. The client asks for
  `wiz/elaborated` (protocol §1), so the infoview hears about every re-elaboration.
* **Unicode input like Lean's.** `\lam` → λ, `\r` → →, `\<` → ⟨, `\-1` → ⁻¹, … from
  Lean's own table (vscode-lean4's `abbreviations.json`, Apache-2.0, vendored) plus Wiz's
  additions: the nine letters Lean leaves free become Greek (`\f` φ, `\h` η, `\j` ξ, `\k`
  κ, `\q` θ, `\s` σ, `\w` ω, `\y` υ, `\z` ζ; Lean's `\l` ←, `\r` →, `\x` × stay), and the
  symbols the repository uses that Lean has no abbreviation for (`\++` ⧺, `\done`,
  `\cross` ✗). An abbreviation is an extmark from the leader to the cursor (so it
  survives edits around it); it is replaced as soon as the next character could not
  continue any abbreviation, when it is complete and nothing longer starts with it, on
  `<Tab>`/`<CR>`, or when insert mode ends. `InsertCharPre` can't edit the buffer, so
  the replacement is scheduled and checks that the text is still there. `:WizAbbrev`
  looks a symbol or an abbreviation up.
* **The infoview.** A split that follows the cursor (debounced) and shows
  `wiz/interactiveGoals` and `wiz/interactiveTermGoal`, sent through the editor's own
  LSP client (no socket: 11l is for infoviews outside the editor). Tagged text becomes
  lines plus a list of tag ranges (kind, ref, nesting depth); kinds get highlight groups
  as extmarks, the innermost tag under the infoview's cursor is highlighted, and `K`
  asks `wiz/subtermInfo` for it (its type and, for a constant, `gd` to its
  declaration). A stale session (`ContentModified`) refreshes the view.
* **Nix.** `packages.<system>.wiz-nvim` (`vimUtils.buildVimPlugin`) and `nix run
  .#nvim-wiz`: Neovim with the plugin and the packaged wiz on `PATH`. The dev shell has
  `neovim`, for the tests.

The `nvim` test group runs `editors/nvim/tests/run.sh`: headless Neovim types
abbreviations through insert mode (and one key at a time in an embedded Neovim, so the
scheduled replacements run between keys and the cursor must end up right), checks that
every non-ASCII character in `lib/*.wiz` has an abbreviation, and drives the infoview
against the real `wiz lsp` on `tests/fixture/Goals.wiz`: the goal after `intro n`, an
argument's expected type, constants highlighted, `K` on `Bool` giving `Bool : Type`,
the view following an edit. It is skipped without `nvim`.

The harness separates the two ways the case can fail. A test failure prints `N passed,
M failed` and the `✗` case; `run.sh` then exits 1 and names the case again on a
`harness: failed case(s): …` line. Neovim itself can also exit nonzero *after* a clean
summary (a libuv handle, job or language server still alive while it tears down); that
is an environment anomaly, not a test result, so `run.sh` prints
`harness: nvim exited N after P passed, 0 failed`, keeps the end of nvim's raw output
(progress lines included) and its `NVIM_LOG_FILE`, and exits 2. When that log says
`uv_loop_close() hang?` (libuv could not close its event loop within the 2 seconds nvim
allows, which is the known silent 0→1 exit), the harness adds
`harness: cause: nvim/libuv teardown could not close its event loop`. A future flake
therefore reads as a `harness:` anomaly rather than as a failing test. `editors/nvim/tests/run.sh
--self-check` pins all of these paths against fixture output, without nvim or a build;
the `nvim` group runs it as its second case.

## 11q: go to definition and the infoview for syntax, binders, imports and instances

Hovers, go to definition and the infoview used to know only about terms. Now (as in
Lean) they also know about syntax:

```
syntax (name := twice) "twice" term:max : term       -- declaration of `twice`
macro_rules
  | `(term| twice $x) => `(term| Nat.add $x $x)      -- definition of `twice`
def four : Nat := twice two
--                ^ hover: twice two : Nat
--                         syntax `term.twice` (this file, line 1)
--                         by macro rule (this file, line 3), expands to  Nat.add two two
```

* **Uses of syntax.** Each command the user wrote is walked once for nodes of declared
  kinds (`syntax`, `notation`, `infix…`; also in the patterns of `macro_rules`) and for
  the names of declared categories (`syntax … : c`, `c:prec`, `` `(c| …) ``); the
  elaborator records what expanded each node it met (the macro rule, a procedural macro
  `attribute [macro k] f`, a command macro, or the tactic function `attribute [tactic k]
  f`) and what it expanded to. **Go to definition** goes to what expanded it, **go to
  declaration** (`textDocument/declaration`, now advertised) to the `syntax` command;
  for `notation` and `infix…` both are the same command. Prelude notation (`+`, `do`,
  …) jumps into the toolchain's `lib/Prelude.wiz`. The hover shows the source with its
  type, the syntax and where it was declared, the rule and the expansion (one step), and
  the instance the notation needed (`Add Nat`). The declaring commands' ranges are kept
  by kind and category (`CommandState.kindSites`, `catSites`) and in each `MacroRule`.
* **Macro output is synthetic.** A template's ranges are those of the file that
  declared the rule, so before this an expansion of a Prelude macro recorded hovers and
  expected types at Prelude offsets in the user's file. `SourceInfo.synthetic` now marks
  a template's nodes (and a procedural macro's output, which has the call's range):
  nothing is recorded at them, and the local context keeps the nearest range the user
  wrote, so errors inside an expansion point at the macro call or at the argument the
  user wrote. What antiquotations bind keeps its ranges, so `twice two` still has a
  hover on `two`.
* **Binders and pattern variables** (of `def`, `fun`, `∀`/`→`, `×`, `let`, inductive
  and structure parameters and fields, and `match` arms) are recorded like identifiers
  (hover: `n : Nat`) and with their context, so the expected type request
  (`wiz/plainTermGoal`, the infoview's "Expected type") shows a pattern variable in the
  context of its arm.
* **`import M`**: hover shows the module's file, go to definition opens it.
* **Commands, instances and messages: `wiz/interactiveInfo`**, a new infoview request
  (protocol in `wiz-notes/infoview-protocol.md`, §4), lists what else is at the cursor:
  the syntax and expansion, the import, the instances found at the innermost
  application (`instance … : Mul Nat`, at `2 * 3`), the declarations of the command
  (a `structure`: its type, constructor and fields, with their types; an `inductive`:
  its constructors), and the messages there (`#check`, `#eval`). wiz.nvim shows them as
  sections under the goals, and `gd` on an item jumps to it. `#check`, `#eval`,
  `#reduce`, `#run`, `inductive` and `structure` now keep their info trees, so hovers
  work inside them too.

Not covered: hovers inside tactic arguments (a tactic gets its syntax without ranges),
a procedural macro's output (it has no ranges of the user's), the arguments of
`attribute`, and docstrings (Wiz has none). Design notes: `wiz-notes/info-syntax.md`.
Tested in the `lsp-server` group and by wiz.nvim's tests (`nvim`).

## 11r: printing notation (unexpanders)

Terms print as the notation they were written with: `#check`, `#reduce`, `#eval`,
messages (`type mismatch`, kernel errors), hovers and the infoview's goals.

```
#check fun (n : Nat) => n + 1        -- fun n => n + 1 : Nat → Nat
#check [1, 2, 3]                     -- [1, 2, 3] : List Nat
#check fun (b c : Bool) => b && !c   -- fun b c => b && !c : Bool → Bool → Bool
#check ∃ (n : Nat), n = n            -- ∃ n, n = n : Prop
```

Before, these printed the elaborated term: `Add.add Nat instAddNat n 1`,
`List.cons Nat 1 (List.cons Nat 2 (List.cons Nat 3 (List.nil Nat)))`, and a `match` on a
`Bool.casesOn`. The mechanism is Lean's: a delaborator and `app_unexpander`s
(`Core/Pretty.lean`, `Syntax/PPTable.lean`).

* **Unexpanders.** At an application of a constant `c`, its explicit arguments (the
  binder infos of `c`'s type say which) are turned into syntax, bottom-up, and `c`'s
  unexpanders are tried, latest first, on `c x₁ … xₙ` as syntax; the first that applies
  gives the notation (arguments beyond what it takes are applied to it). A subterm that
  isn't notation (or a variable, a constant, a numeral, a `fun`) stays a leaf, printed
  as before.
* **Three kinds.** (1) *Automatic*: every `notation`, `infixl`/`infixr`/`infix` and
  `macro_rules` rule whose template is a constant applied to the rule's variables is
  read backwards (`+ - * / %`, `++`, `!`, `-x`, `|>`, `∧ ∨ ¬ ↔`, `<$>`, user notation).
  So the notation declared last for a constant is the one printed (Logic declares its
  ASCII spellings `/\`, `\/`, `<->` first). (2) *Declared*:
  `app_unexpander c | `(term| $f $x …) => `(term| …)`, quotation rules over the
  application (`$f` is the head); the Prelude prints `Bool.casesOn` as `if`/`&&`/`||`
  this way, Logic `Ex (fun x => p)` as `∃ x, p`. (3) *Procedural*:
  `attribute [app_unexpander c] f` with `f : Macro` (`Syntax → MacroM Syntax`, failing
  when it doesn't apply), run by the interpreter: the Prelude's `ListLit.unexpandNil`
  and `ListLit.unexpandCons` print `List.nil` as `[]` and `List.cons x [ys,*]` as
  `[x, ys,*]`, collecting the spine from the last cell up. All three can be `local`; a
  module's local ones (and its local notation's automatic ones) end with it.
* **`match`.** A `match` elaborates to `(fun x => T.casesOn … x : …) scrutinee`; such a
  redex prints as its reduct when that has an unexpander, so `if` comes back.
* **Formatting.** The notation is printed by walking the grammar of each node's kind
  (the parser descriptors, built-in ones included): atoms, children at the precedence
  their position asks for, parentheses where a node's precedence is lower (a node whose
  grammar ends in an open `term p`, like `fun` or `if`, counts as precedence `p`).
  Spacing follows the atoms as declared (`" + "`, `"!"`, `"∃ "`); keywords get spaces,
  brackets none, separators `, `. A node that can't be formatted (a kind without a
  grammar, a shape the grammar doesn't fit) prints its subterm without notation, so an
  unexpander can make output prettier but never wrong.
* **Tags survive.** Every syntax node made from a subterm remembers it, so in the
  infoview the subterms of notation (`n`, `1` and the whole `n + 1`) are still tagged
  and hoverable. (A procedural unexpander's output keeps the tags of its leaves only.)
* **Options.** `wiz … --pp-all` prints without notation (and turns the cache off);
  `set_option pp.notation false` (or `pp.all true`) does so from that point of a file
  (a module's setting stays in the module). `Term.prettyPrec` (used where printed terms
  are parsed back, `Reflect.lean`) never uses notation.

Not covered (follow-ups): implicit arguments outside notation still print (Lean hides
them: `pp.explicit false`), data values from `#eval`/`#reduce` (`.cons 1 .nil`) are
constructor values, not applications, so lists print as before there; `do` notation;
`⟨a, b⟩` and structure literals; numerals of other types (`OfNat.ofNat`); goals passed
to tactics as text and `trace_state` print without notation. The self-hosted toolchain
has its own printer (selfhost/Frontend.wiz) and prints no notation. Design notes:
`wiz-notes/pp-unexpand.md`. Tested in the `language` group.

## 11s: scroll, the documentation generator (`wiz doc`)

Like Lean's doc-gen4: a static site from a set of modules. Design notes:
`wiz-notes/scroll.md`.

    wiz doc [MODULE|FILE|DIR …] -o OUT [--lib] [--source-url URL] [--title T] [--web DIR]
    grail doc [TARGET…] [-o OUT] [--source-url URL] [--title T]

`--lib` documents the toolchain's library; a directory, every module under it (it is a
module root too); a file or module name, that module. `grail doc` runs `wiz doc` on the
package's `lib` targets with its module roots (dependencies included), into
`.grail/doc`. Source links are `URL` + the file's path in its root + `#L<line>`
(without `--source-url`, the path as text). Flags only, no environment variables.

* **Doc comments.** `/-- … -/` right before a command (only whitespace between)
  documents the declarations it makes, as in Lean; before a constructor (`/-- … -/ | c`
  or `| /-- … -/ c`) or a `structure`/`class` field, that one. `/-! … -/` documents the
  module (without one, scroll takes the module's leading `--` comment block). To the
  lexer a doc comment is still a block comment: the grammar is unchanged, and the
  self-hosted frontend (selfhost/Lex.wiz) deliberately ignores doc comments (they are
  for tools; nothing it checks depends on them). The Lean frontend finds a command's doc
  comment from where the command starts (`docCommentBefore`,
  `Wiz/Parser/DocComment.lean`) and stores it with what the declaration is:
  `CommandState.declDocs : Name → DeclDoc` (`kind`: `def`, `partial def`, `inductive`,
  `structure`, `class`, `instance`, `constructor`, `field`, `auxiliary`, …; `doc`;
  `parent`), `CommandState.docOf?`. The cache replays them (`Effect.docs`; salt 15).
  Doc comments are Markdown (`Wiz/Doc/Markdown.lean`: paragraphs, headings, fences,
  lists, quotes, `code`, emphasis, links; HTML is escaped), and a name in backticks links
  to its declaration.
* **The site** (`Wiz/Doc/Site.lean`): `index.html` (the modules and their summaries),
  one page per module (`A.B.html`): every public declaration (private and auxiliary ones
  are left out) with its kind, its signature (the infoview's tagged printer,
  `Term.prettyTagged`, so notation-aware printing applies when it does), its doc, a
  source link, its constructors or fields, and the instances of a class or for a type;
  every constant in a signature links to where it is documented (the definition sites
  the language server's go to definition uses, `declSites`). `api.html` is the
  API/library index: every module with all its declarations, their kinds, signatures
  (with the same cross-links) and doc summaries, each linking to its anchor on the
  module page; `api.json` is the same index for tools. The header of every page links to
  it. `search.js` is the client-side index of every module and declaration (name,
  module, kind, doc summary, signature text and target), searched by `scroll-search.js`
  (`/` focuses the box): names first, then doc comments, then signatures, and a hit
  says which matched. The pages are complete HTML: they read without JS, and the
  search works from `file://`.
* **Interactive signatures, with the infoview's Wasm.** Each page carries its data as
  JSON (`<script id="wiz-doc-data">`, and `A.B.json`): per declaration the signature in
  the infoview protocol's tagged-text format and the table of its subterms, each a
  `wiz/subtermInfo` answer (`kind`, `name`, `text`, `type`, `definition` as a link),
  precomputed since there is no server. With the Wasm module (served over HTTP), the
  web infoview's module (`web/Web.wiz`, now also exporting `wiz_doc_init` and
  `wiz_doc_step`) renders each signature as it comes into view: hover a subterm for its
  type and where it is defined, click a constant to go to its definition, click anything
  else to select it (the arrows move the selection, as in the infoview). The tagged text
  both share is a library of its own, `lib/Tagged.wiz` (the JSON, flattening, numbering
  and navigating tags, the HTML, the subterm box `Tagged.infoHtml`, and the page's
  model `DocPage.step`), which `lib/Infoview.wiz` imports; the browser half they share is
  `web/tagged.js` (loading and stepping the module, the mouse and keys on `.tt`), used by
  `web/infoview.js` and `web/scroll.js`. `web/build.sh` builds the module as before and
  copies the site's scripts and `scroll.css`; `wiz doc` takes them from `share/wiz/web`
  of a release, `web/out` of a checkout, or `--web DIR`. Without them the pages are
  plain HTML (and `wiz doc` says so).
* **CI** builds the library's documentation on `master` and publishes it: the `docs` job
  runs `wiz doc --lib` on a push (never a pull request), with source links to the
  commit and the Wasm module, into `doc-site/docs`, assembles the landing page at the
  site root and the static playground (11ab) under `doc-site/playground`
  (`web/build-site.sh`), checks the tree (`web/check-site.sh`), and uploads it as the
  artifact `wiz-docs` (3 days, for debugging); `deploy-docs` deploys that artifact to
  GitHub Pages. The URLs are `/` (the landing page), `/docs/` (the docs pages:
  `index.html`, `api.html`, `api.json`, `A.B.html`, `A.B.json`, `search.js` and the Wasm
  files) and `/playground/`; every link is relative.
  A repository has one Pages site and each deployment replaces the whole tree, so a
  future performance site shares this deployment under `/perf/` rather than deploying
  separately. `docs/building.md`, "Documentation site", has the URL layout, the
  one-time Pages setting and the single-site rule.
* **Tests**: the group `doc` (`Tests/Doc.lean`): doc comments stored and replayed by the
  cache; Markdown; `wiz doc` on a small package with doc comments (kinds, docs, source
  links, instances, the index); every cross-link resolves; every declaration is in the
  search index, with its doc summary and signature; the API index and `api.json` list
  every module and declaration; the pages without JS; `grail doc`; and the page model of the Wasm module
  run natively on a page's JSON (hover, click, keys); and that the core library is
  documented (every public declaration of `Prelude`, `Std`, `Vec` and `Word` has a doc
  comment, and each has a module doc). The search box's ranking and result rendering
  have a browser-free test, `web/scroll-search_test.mjs`, run by `web/test.sh`.
* **The library's documentation.** Every module in `lib/` has a `/-! … -/` module doc
  (what it is for, its main definitions, an example) and a `/-- … -/` doc comment on each
  public declaration; `--` comments are left for implementation notes. `wiz doc --lib -o
  OUT` builds the pages (CI's `wiz-docs` artifact).

## 11w: hovers in tactic arguments, the other infoviews, `local instance`, the browser infoview

* **Ranges through reflected syntax.** A tactic or procedural macro gets the user's
  syntax as a Wiz `Syntax` value, which has no ranges, and its output used to get the
  call's range everywhere. Now `encodeSyntax` adds each node's range as two hidden
  trailing fields of its constructor value. Wiz code never reads them (`SyntaxF` has no
  such fields), so they survive exactly when a tactic hands back the value it was given
  (`exact $t` passes `t` through), and are absent from anything it builds;
  `relocate` (after the exercise `decodeSyntax`) puts them back, and everything else is
  synthetic (11q). So hovers, expected types and go to definition work inside `by`
  arguments, nested tactics (`first`, `repeat`, `( … ; … )`) record their goals at
  their own ranges, and a list literal's elements keep theirs.
* **The terminal and web infoviews** ask for `wiz/interactiveInfo` too and show its
  sections (Syntax, Import, Instances, Declarations, Messages) under the goals, with the
  same tags (`lib/Infoview.wiz`: `InfoItem`, `View.ofInfo`, `Infoview.htmlInfo`).
* **`local instance`** (13m's `local` for instances, as Lean has it): the instance is
  found in its module only; the importer doesn't see it (its definition, a name, stays).
* **The infoview in a browser from wiz.nvim**: `:WizInfoviewBrowser` (`<LocalLeader>b`)
  sends `wiz/browserInfoview` to the buffer's own server, which starts listening on a
  WebSocket (127.0.0.1, a free port) unless it already does, and answers with the page's
  URL; Neovim opens it (`vim.ui.open`). The same port serves the web infoview's four
  files over HTTP (`WebSocket.webAssets`: only those names, and only to local origins;
  anything else is `404`/`403`), from `share/wiz/web` of a release toolchain (the release
  job builds them with Emscripten) or `web/out` of a checkout (`web/build.sh`), or
  `wiz lsp --web DIR`. With `?follow=1` the page has no editor of its own: it follows
  the editor's cursor (`wiz/infoview/cursor`, §8.2). `wiz lsp` now always runs the
  multi-connection loop (`serveWith`), so this works without `--ws`.

## 11t: filling holes, and completion that knows the context

* **Completion** (`Wiz/Completion.lean`): `textDocument/completion` answers a
  `CompletionList` whose items replace the word at the cursor (a `textEdit`), with the
  type as `detail`:
  * `x.f…` where `x` is a value: the fields of its type (a structure or a Σ, with their
    types) and the functions `T.f` of its type's namespace whose first explicit argument
    is a `T` (generalised field notation, `p.norm` for `Point.norm p`); after a
    namespace (`Nat.ad`), the names in it;
  * the keywords the **parser** expects at the cursor. The command around the cursor is
    parsed with the input cut at the start of the word: the tokens of the failure at the
    cut are what may come next. So column 0 gives the command keywords, a line of a `by`
    block the tactic names, a keyword-scoped DSL (13j) its own keywords (`yes` after
    `run_calc when [0]`), and nothing is hard-coded;
  * where a term or an identifier may go: the locals in scope with their types, then the
    globals, those whose type ends in the expected type's head first;
  * after `import`: the modules the server can load.

  The text being typed rarely elaborates, so the locals and the expected type come from a
  **patched** copy: the word replaced by a hole `_` (the hole's goal), or for `x.f…` by
  `x` (its identifier's type). The copy stops at the end of the command around the
  cursor, and the query engine reuses the commands before it, so a completion request
  elaborates one command.
* **Fill a hole** (code action, `refactor.rewrite`): a hole `_` or `?x` whose expected
  type is known becomes a skeleton of it: one action per constructor of an inductive
  type (`(.c ?x ?y)`, in parentheses where it is an argument), the anonymous constructor
  of a structure or Σ type with a named hole per field (`⟨?px, ?py⟩`), or
  `fun x => ?body` for a function type. Names of the new holes avoid the locals.
* **wiz.nvim**: `lsp.completion` (default `'auto'`: on unless nvim-cmp or blink.cmp is
  loaded) turns on Neovim 0.11's own LSP completion (after `.`, and `<C-Space>` in insert
  mode); the README lists what completion and the code actions offer.

```
def foo (n : Nat) (pt : Point) : Nat := Nat.add n pt.‸   -- pt.px : Nat, pt.py : Nat, pt.norm
def p : Point := _                                     -- [Fill with an anonymous constructor] ⟨?px, ?py⟩
```

## 11u: signature help

`textDocument/signatureHelp` (`Wiz/Signature.lean`; triggered by a space or `(`) shows
the binders of the function being applied, `List.length {A : Type} (_ : List A) : Nat`,
with the explicit argument being typed highlighted. The application is found in the
text, since the document rarely elaborates mid-application: back from the cursor to the
nearest unclosed bracket, or `:=`, `=>`, `,`, `|`, `;` at bracket depth 0, or the
start of the command. Its first word is the function, and the complete arguments after
it (named arguments `(x := e)` aside) say which explicit binder comes next. A global's
binders come from its declaration; a local function's type from the info tree of the
text cut after it, with its open brackets closed. In Neovim 0.11, `<C-s>` in insert mode.

```
def b (xs : List Nat) : Nat := List.length ‸    -- List.length {A : Type} [(_ : List A)] : Nat
```

### Doc comments in the editor (11s, 11t, 11u)

The language server shows a declaration's doc comment (`/-- … -/`, `CommandState.docOf?`)
as Markdown: in a hover under the type (`double : Nat → Nat`, a rule, then the doc), as
a completion item's `documentation`, and as signature help's `documentation`. Locals have
none; the library's declarations are documented (`lib/`), so `Nat.add` explains itself.

## 11v: the outline, workspace symbols and folding

* **Document symbols** (`textDocument/documentSymbol`, `Wiz/Symbols.lean`): one symbol per
  command, named after the first declaration it makes, with the others it makes (a
  structure's fields and constructor, an inductive type's constructors) as children; a
  type is a `Struct`, a constructor a `Constructor`, the rest `Function`, with the type as
  `detail`. The elaborator's own names (`.desc`, `.casesOn`, `.rec`, …) are left out.
* **Workspace symbols** (`workspace/symbol`): the declarations of the open documents and
  of the modules they import whose name contains the query, ignoring case, at most 300,
  each where it was declared (library modules by their path).
* **Folding ranges** (`textDocument/foldingRange`): commands spanning several lines,
  `by` blocks, `match`es, and block comments (kind `comment`).
* wiz.nvim: `gO` (Neovim 0.11) lists the outline; `lsp.folding = true` folds with the
  server's ranges (`vim.lsp.foldexpr`).

## 11x: inlay hints

`textDocument/inlayHint` (`Wiz/Inlay.lean`) shows the type the elaborator gave a `fun`
or `let` binder written without one, `fun x : Nat => …`, from the info tree's binders
(`recordBinder`): a local identifier whose text is the binder's own name, with `fun`/`λ`
(past the other binders of its group) or `let` before it and `=>`/`↦`/`:=` or another
binder after it, not `:`. wiz.nvim: `lsp.inlay_hints = true` turns them on.
## 11z: semantic tokens for the file's own keywords

`textDocument/semanticTokens/full` (`Wiz/Semantic.lean`, one token type `keyword`)
marks what a fixed syntax file can't know: the words of declared syntax (`syntax`,
`notation`, the Prelude's tactics, a keyword-scoped DSL's `when … yes … no`) inside the
nodes of that kind the info tree saw (`syntaxRef`), and the words that declared `term`
and `command` rules reserve everywhere (`run_calc`, `done`). A DSL keyword used as a name
outside the DSL (`def no (yes : Nat)`) stays a name. Comments and strings are skipped.
Neovim shows them as `@lsp.type.keyword` (linked to `@keyword`) without configuration.

## 11y: references, highlights and rename

`Wiz/Refs.lean`, from the info tree's identifiers (each records what it resolved to):

* **References** (`textDocument/references`): for a global, its uses in every open
  document and in the package's other modules (the library modules that aren't the
  toolchain's, so under `grail lsp` the package's own and its dependencies'), each
  elaborated once per source and kept by the server, plus the name in its declaration.
  For a local, its binder and the uses that see that binder (the nearest binder of the
  name before the use, inside the declaration).
* **Document highlights** (`textDocument/documentHighlight`, also what tells the
  infoview where the cursor is): the same, in the document.
* **Rename** (`textDocument/prepareRename`, `textDocument/rename`): edits every place
  that spells the whole name, in all those documents; it refuses a declaration of the
  toolchain's library and a new name that isn't one. A use through generalised field
  notation (`p.norm` for `Point.norm`) is not edited.

## 11aa: `wiz fmt`, a formatter

    wiz fmt [FILE|-] [--check] [--width N] [--explain]

Reprints a file from its syntax tree: each command is parsed with the tables that are in
effect at it (imported `syntax` and `notation` included), printed from the tree with the
grammar of every node kind (`PPFormat`, the table 11r's printer walks, so declared
spacing like `" + "` and `noWs` are honoured), and laid out by a small pretty-printing
document (`Wiz/Format.lean`: `group`/`line`/`nest`, strictly pretty). `FILE` alone prints
to stdout, `-` (the default) reads stdin, `--check` changes nothing and exits 1 when the
file differs, `--width` is the column budget (default 100), `--explain` prints what a
refused command would have become.

* **Why reprint, not rewrite whitespace.** The parser is the single source of truth for
  the tokens and for precedence, so a reprint cannot disagree with it about `a + b` or
  `(fun x => b) c`; user-declared `syntax` formats from its own grammar; and the output
  can be **checked**: every command's reprint is parsed again with the same tables and
  must give the same tree (`toSExpr`), or the command keeps its original text and is
  reported (`line N: left as written (…)`, exit status 1). A token/whitespace rewriter
  keeps comments for free but can never reindent, join or split lines, or drop
  parentheses, and it has to reimplement every declared spacing rule anyway.
* **Comments.** The tree drops them (`Token.skipWs`), so they are recovered from the
  source: every leaf keeps its byte range, and the text between two leaves is a run of
  comments. One written after a token, on its line, stays there (`;  -- note`); the rest
  go on their own line before the token they precede. A comment makes a `def` body start
  on its own line (below).
* **Layout and the parser's columns.** `colGt`/`colGe` compare against a remembered
  position (`withPosition`), so the layout has to respect it: a `match`'s alternatives
  and a `by`'s tactics align with their construct's line (at 2 when it is inline, at the
  line's indent when it starts one, deeper for nested matches), and a `let` always starts
  a line — `withPosition` in `term.let` stays in force for the terms after it, so a
  `let` in the middle of a line would forbid its own body's continuation lines to its
  left. That is why `def f := let …` breaks after `:=` while `def f := match …` may stay
  on one line.
* **What is refused.** A kind with no grammar in the tables, something between tokens
  that is not a comment, or a reprint that does not parse back to the same tree. The
  check is what makes a prototype safe: across the library files tested (Prelude, Logic,
  BitBlast, Deriving, Eff, Vec, EffHeap, Word, Grail, Feral, HeapBorrow, OpticDerive,
  Trace, Text, Sat, Hdl/Sim and two examples) the formatter changes no command it
  accepts, is idempotent on every file (formatting twice gives the same text), and
  refuses one command (`Fe.specLin` in `lib/Feral.wiz`: a `match` inside a `let` value,
  see `wiz-notes/wiz-fmt.md`). 13 test cases in the `format` group.
* **Not done.** Signatures never break (a long header stays long: wrapping binder lists
  needs `fill`/alignment); a multi-line block comment keeps the indentation of its
  continuation lines; the self-hosted frontend has no formatter; and the LSP does not
  offer `textDocument/formatting` yet (`Wiz/Format.lean` is that plumbing's core).
## 11ab: a static playground

`web/playground.html`: a Wiz playground that runs entirely in the page. A text area
with a small program, a **Run** button (or Ctrl/⌘+Enter), one output line per command,
and a status line (`loading` / `running` / `done in N ms`, with error lines in red).
No server, no editor, no install: `web/build-playground.sh` compiles the program the
page runs.

* **The engine.** The self-hosted frontend and kernel (`selfhost/Lex.wiz`,
  `Parse.wiz`, `Kernel.wiz`, `Frontend.wiz`) are Wiz source, so the same pipeline as the
  infoview's module builds them: `wiz` writes C (with mini-gmp for bignums), Emscripten
  links it as a wasm64 ES module. The one addition is an export, not a compiler or
  runtime change: `web/playground-exports.wiz` exports
  `wiz_playground_eval : String → String`, the text in and `selfhost/Frontend.wiz`'s
  `checkFile` lines out. The page calls it, frees the returned string, and renders it.
  Its parser needs the parser's tables; `selfhost/Tables.wiz` holds them (the same
  checked-in file the self-hosted toolchain reads, generated by
  `scripts/GenSelfhostTables.lean`, 39 KB), so building the module needs no Lean step
  beyond the `lake build wiz` every checkout needs.
* **What it runs.** The self-hosted frontend's embedded Prelude (Nat, Bool, List,
  Option, Prod, arithmetic, `String`), definitions with patterns and `match`, inductive
  types, structures, `#check`, `#reduce`/`#eval`, and its error messages. `import` lines
  are accepted but only Prelude is available (there is no module loader in the page);
  without any import the page prepends `import Prelude`, so a bare `def two : Nat := 1 + 1`
  works. `#eval` prints the kernel's normal form (`con((#1, …))`); `web/playground-values.js`
  recognises the shapes of Nat, Bool and list values and shows `42`, `true`, `[1, 2]`,
  keeping the raw form in the line's tooltip. Anything else is shown as it comes.
* **Build and serve** (from a checkout after `lake build wiz`):

      web/build-playground.sh web/out             # → web/out/wiz-playground.mjs (+ the page)
      python3 -m http.server -d web/out 8000      # then http://127.0.0.1:8000/playground.html

  The published site puts it at `/playground/`: `web/build-site.sh doc-site web/out`
  copies the page (as `playground/index.html`), its scripts and the module there, beside
  the landing page at `/` and the documentation at `/docs/` (11s; docs/building.md,
  "Documentation site"). The page's own links to the rest of the site are relative, so
  serving `doc-site` (`python3 -m http.server -d doc-site 8000`) shows the whole tree.

  `WIZ=...` picks another toolchain; `--gmp-src` is `web/build.sh`'s option for builds
  without nix. The script writes `web/out/playground.wiz` (the assembled engine source)
  beside the module. The page needs HTTP (an ES module and a `.wasm` fetch; `file://`
  will not do). `web/build.sh` and its infoview are unchanged and can share `web/out`.
* **Tests.** `node web/playground_test.mjs web/out` loads the module under Node, runs a
  definition, a `#check`, `#eval twice 21` (the value renders as `42`), a Bool and an
  error. `web/test.sh` now builds both Wasm modules and runs this test beside the
  infoview's Node and Chromium tests.
* **Limits.** The evaluator has no fuel: a non-terminating `#eval` blocks the tab (the
  call into Wasm is synchronous). Only the embedded Prelude exists, not the library's
  modules or `IO`/`#run`; the page is a checker, not a REPL with a filesystem.
* **Why a second module.** The infoview's exports (`wiz_web_init`/`wiz_web_step`) are a
  language-server client: they can ask a server for goals and diagnostics but cannot
  evaluate a term. The playground's evaluator is the self-hosted checker, which is Wiz
  code; exporting it is the only missing piece, and it needs no server.
