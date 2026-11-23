# scry web, interactive: hover and definition from `wiz lsp` (lane `scry-web-ux`)

Status: implementation + tests, branch `agent/scry-web-ux`, green end-to-end at
`daf06385d`, restacked on `integration/train12` `b5eb50555`. The one merge conflict was
`.github/repo-subsets.json`, regenerated with `scripts/repo-subsets.py --write`.
The slice is the design note's P1 step, reduced to the one interaction it asks for:
**the source reader's own page, mounted with `?lsp=`, asks a running `wiz lsp --ws`
about the Wiz file it displays, and the answer lands in the reader's existing panels.**

## What the slice does

1. `scry web DIR --out BUNDLE --source lib/Web/Source/Facts.wiz --source
   lib/Web/Source/Span.wiz` adds the two Wiz files to the bundle verbatim, with no
   analysis (`--source` is repeatable; `Source.File.language` is `wiz`). The finding
   pipeline for the analysed C/C# target is untouched. Facts.wiz is the reader's fact
   table; its use of `Source.Span.contains` gives the cross-file definition in the demo.
2. `index.html` is the same static, complete, no-JavaScript page as before. `app.js`
   adds one branch: `?lsp=PORT` (or `?lsp=ws://HOST:PORT`, `?token=` for a
   `--token-file` server) loads `source-live.js`, which mounts **the same**
   `wiz-source-ui.mjs` bytes and the same bundle; without `?lsp=` the page is exactly
   the static reader.
3. On the Wiz file, pointer movement over a source line is hit-tested by the host with
   `caretRangeFromPoint`; the offset (line offset from the pane's `data-start`) becomes
   the runtime effect `hover-at fileId offset`. The mouseover is debounced by 160 ms.
4. The runtime publishes a `hover` request (the existing `Page.requests` seam). The live
   host converts the offset to an LSP position through the runtime
   (`wiz_loom_editor_position`, i.e. `Web.EditorBridge`/`Web.EditorModel` — the one line
   table), asks `textDocument/hover`, and sends the result back **raw** with the effect
   `hover-lsp payload raw`. `Web.Source.Model.lspHover` stores it and
   `Web.Source.View.hoverPane` renders it with `Web.Hover.card` — the playground's
   Markdown card, including its fence/rule handling and `wiz.hover/1` path. There is no
   second Markdown reader or card.
5. A click sends `definition-at`; the host asks `textDocument/definition`, parses the
   result with `Web.Hover.targetJson` (the editor's rule, exposed as
   `wiz_loom_hover_target`), and builds a `scry.source.answer/1` with
   `request: "definition"`. Its rows name every target (`target` = `file:line:col`,
   `uri`). For a target that is a bundle file, the host converts the range through
   `wiz_loom_editor_offset`; `Source.Page.answer` opens that file and records the range
   as `focus`, and the source pane draws `.src-mark.src-focus` over it. A target outside
   the bundle is still named in the info panel, never opened.
6. `#/def/<fileId>@L:C-L:C` is the shareable form of that focus (no request); `#/src/…`
   and `#/f/…` are unchanged.
7. The footer's provenance is `live` or `static` (`scry … · live reader`). A failed
   connection is a footer note and `data-lsp="failed"` on `#app`; it is never an error
   page: every later request takes the bundle's static path, and the SSR has already
   rendered the product.

The only model additions are data the existing view can draw: `Source.Page.focus`
(an optional span, outlined by the existing `Highlight` path), `Source.Answer.raw`
(the live hover JSON, rendered by `Web.Hover.card`), `Source.Msg.focusSpan` (a
definition row's jump), plus the `hover-at`/`definition-at`/`hover-lsp`/`note` effects.
No second renderer, model or host answer shape: a live and a static answer are both
`scry.source.answer/1`.

The highlight path was also fixed where the slice touched it: line marks are now sorted
and overlapping marks merged before `Highlight.nodeWithNode` validates them (two
findings on one line, or a definition range inside a finding, used to fail the
"ascending, disjoint" check and render the whole line plain).

## Protocol

* Transport: `wiz lsp --ws PORT` (one JSON-RPC 2.0 message per WebSocket text frame);
  `web/lsp-client.js` is the existing client, with `general.positionEncodings:
  ["utf-16"]`, so LSP `line`/`character` are UTF-16 units and the reader's offsets are
  the same units. `web/source-live.js` opens every `wiz` file in the bundle with
  `textDocument/didOpen` (the bundle's text), so the server's copy is what the page
  shows, not a disk re-read.
* Requests used: `initialize`/`initialized`, `textDocument/didOpen`,
  `textDocument/hover`, `textDocument/definition`. Nothing else.
* Effects used (`web/source-ui.wiz`): `bundle`, `answer`, `route`, `ack` (unchanged)
  and `hover-lsp`, `hover-at`, `definition-at`, `note` (new). Requests stay
  `[{"kind":"hover"|"info"|"definition","payload":"FILEID@START-STOP"}]`.
* Provenance: `?lspRoot=` names the directory the bundle's relative paths live under, so
  the host can form `file://` URIs and `wiz lsp` can resolve the file's `import`s. It is
  a page parameter, never a manifest field (a bundle must not publish the build
  machine's paths).
* `scry.source.answer/1` still has one shape; `raw` is an optional field (empty in
  static exports) and the definition answer uses the existing `rows`/`span`/`fileId`.

## What is stubbed, limited, or not done

* **The browser smoke's server.** `web/source_chrome_test.mjs` takes an optional
  `WIZ_BIN`; with it the test starts the real `wiz lsp --ws 0 --ws-insecure --no-stdio`
  and asserts real hover/definition text. Without it, it starts
  `web/mock_lsp_server.mjs` (the repository's stand-in for the same protocol) and says
  so. The page has no stub: it always speaks the real protocol to whatever is on the
  port.
* **`wiz lsp` has no `-I`.** Its `libs` are the toolchain's `lib/` (for a checkout
  binary, `<checkout>/lib`). A Wiz file under `scry/src/` imports `Scry.*`, which is
  not on that root, so its hover/definition would fail. The demo therefore displays
  `lib/Web/Source/Facts.wiz` (the reader's fact table) and `lib/Web/Source/Span.wiz`
  (its imported span type); both resolve. Making `scry/src` usable needs a toolchain
  search path for the server, not a page change.
* **No completion, no diagnostics panel, no editor.** Click/hover only; the reader is
  still not an editor. `wiz/interactiveInfo` is not used: the info view stays scry's
  fact/definition rows.
* **A definition target outside the bundle is a label**, not a jump (the reader does not
  fetch source it does not have).
* **Positions are UTF-16 in the reader and code points in today's `wiz lsp`**
  (`toPos`/`ofPos` in `Wiz/LSP.lean` count `String.toList` characters, whatever the
  client's `positionEncodings` says). For ASCII source — the demo's Wiz files, and every
  hover smoke here — the two coincide. An astral character before the cursor would drift
  by one per astral character, and fixing that belongs in the server, not the page.
* Only pointer positions on a rendered line are live: a file not currently open is not
  hit-testable, and a selection made with the keyboard has no live behaviour yet.
* **A single source string of about 50 KB breaks the Wasm runtime's bundle load.**
  `Json.parse` in `lib/Json.wiz` reads a string with a per-character recursion
  (`Json.strBody`/`Json.revApp`); the Wasm module's 32 MB stack is gone at that size.
  Measured: a bundle payload of 64 759 bytes (which included `lib/Web/EditorModel.wiz`,
  52 KB) threw `RangeError: Maximum call stack size exceeded` inside the module during
  the `bundle` effect, and the page stayed on "loading the bundle…"; the same bundle with
  that file removed (10 129 bytes) loaded and produced 3 patches. The demo therefore
  carries only `Facts.wiz` (2 KB) and `Span.wiz` (7 KB), and `scry web` now warns on
  stderr for any bundle file over 40 000 characters. This is a pre-existing limit of the
  static parser, not of the live interaction; it is the next thing to fix for real
  projects (an iterative/string-slice parser, or a smaller per-file payload).
* **The first live answer is slow.** `wiz lsp` elaborates a document with term info on
  `didOpen`; on this machine the first hover on the reader's Span.wiz took **51 s**
  (the definition after it, 60 ms). The page's request timeout is 180 s and its footer
  says "live: connecting…" meanwhile; documents are opened lazily, on the first request
  for each file, so the bundle's other Wiz files cost nothing until asked about. This is
  the server's elaboration cost, not the page's (the same `wiz check` of Model.wiz is
  52 s; Span.wiz is 3.6 s).
* The live adapter is not on the site's `/source/` page (no server there); it is the
  same bundle bytes plus `?lsp=`.

## How to run

```sh
# 1. The binaries (heavy; do not run lake directly on the controller)
heavy --rsync -- lake build wiz grail

# 2. The runtime + the two test bundles, in one heavy job on the same node that built
#    the binaries (a copied-back wiz/grail is linked against that node's store; see the
#    ledger note below). The store path and the scry binary are produced on the node;
#    the bundles land in the worktree.
heavy --sshfs --nodelist=win3 -- sh -c '
  grammar=$(nix build .#tree-sitter-c-sharp --no-link --print-out-paths)
  cp -a "$grammar" scry/native/tree-sitter-c-sharp
  ( cd scry && cp ../grail.local.wiz . && ../.lake/build/bin/grail build scry )
  gmp=$(nix build --inputs-from . --no-link --print-out-paths nixpkgs#gmp.src)
  WIZ=.lake/build/bin/wiz nix shell --inputs-from . nixpkgs#emscripten -c \
    sh web/build-source-ui.sh web/out/ui --gmp-src "$gmp"
  web/source-bundle.sh scry/.grail/bin/scry web/out/fixtures --ui web/out/ui
  web/source-bundle.sh scry/.grail/bin/scry web/out/live --ui web/out/ui \
    --source lib/Web/Source/Facts.wiz --source lib/Web/Source/Span.wiz
  node web/source_static_test.mjs web/out/fixtures
  node web/source_live_test.mjs web/out/live .lake/build/bin/wiz
  chrome=$(nix shell --inputs-from . nixpkgs#chromium -c sh -c "command -v chromium")
  node web/source_chrome_test.mjs "$chrome" web/out/live .lake/build/bin/wiz'

# 3. The Node acceptance tests
node web/source_static_test.mjs web/out/fixtures
node web/source_live_test.mjs web/out/live .lake/build/bin/wiz   # real LSP, Node only

# 4. The browser smoke, with the real server when the built wiz runs locally
node web/source_chrome_test.mjs "$(command -v chromium)" web/out/live .lake/build/bin/wiz
#    ... and with the mock (the fallback path)
node web/source_chrome_test.mjs "$(command -v chromium)" web/out/live
```

`web/out/` is gitignored. The smoke's `?lspRoot=` defaults to the current directory,
so run it from the checkout root.

## Results

* `wiz check` (the Wiz compiler from this branch, `lib/Web/...`): Model.wiz rc=0 (52 s),
  View.wiz rc=0 (17 s), `web/source-ui.wiz` rc=0, `scry/src/Scry/WebCmd.wiz` rc=0. The
  first two runs found a missing `mergeSpans` wrapper and an untyped `.false` in the
  focus match; both are fixed in the committed tree.
* A direct `wiz lsp --ws` probe (Node client, `lib/Web/Source/Span.wiz`): hover at
  `EditorModel.slice` returned
  `EditorModel.slice : EditorModel.PositionIndex → Nat → Nat → String` plus the doc
  comment after **51.4 s**; the definition 60 ms later was
  `file://…/lib/Web/EditorModel.wiz` range 168:0–173:62 (the whole declaration).
* Two bundle-job attempts failed on the *node's* environment before the code was reached:
  (a) the `scry` link failed with `cannot find -lgmp`, because a `grail.local.wiz` copied
  from the controller names controller store paths — `nix develop` on the node rewrites
  it; (b) the tree-sitter grammar copied from the store is read-only (`0555`
  directories), so replacing it needs `chmod -R u+w` first. Both are job-environment
  fixes, not code changes; the scry compile itself had checked all 66 modules.
* Why the check/probe used a repointed binary: the heavy build ran on `win3`, so the
  copied-back `.lake/build/bin/wiz` has `win3`'s glibc as its ELF interpreter
  (`glibc-2.44-25`), which this controller does not have. For local probes only, a copy
  under `/tmp/opencode/scry-ux/` was `patchelf`-ed to the controller's
  `glibc-2.44-57`/`gcc-16.2.0-lib` and run with the worktree as cwd (so its fallback
  library root is this checkout's `lib/`). The bundle job runs on `win3` and uses the
  unpatched binaries.

### Resume gate (2026-11-23): the full bundle and browser run

The first complete run of `.scratch/build-bundles.sh` (job 5293, `win3`) reached the
browser's live section and found two defects the Node tests cannot see:

* `scry web` copied `source-live.js` but not the `lsp-client.js` it imports, so a
  `?lsp=` page's dynamic import failed and the page stayed on the SSR (the browser
  smoke's `?lsp=` navigation never became live). Fixed in `Scry.WebCmd`;
  `source-bundle.sh` now checks the file and the smoke asserts it, so the packaging
  mistake is one named failure instead of a cascade.
* `source-live.js` took the file text from `meta.text`, but `files.json` is metadata
  only; the text is `data/f/<id>.json`'s `source`. `wiz_loom_editor_position`
  therefore got `undefined`, the host fell back to the bundle's static answer, and
  every live hover/definition rendered "no answer". Fixed by reading `perFile` for
  the position, `didOpen` and definition ranges.

Both fixes are in `c4aa5045`. The restack to `b5eb50555` is `94bf7388` (only
`.github/repo-subsets.json` conflicted). On that tree, job 5360 was cancelled by Slurm
before it ran; the rerun (job 5375) was green end-to-end. The pre-push companion check
then found that the 16 new Wiz forms had no `legacy-names.tsv` rows (a `docs_style`
failure); `scripts/gen-legacy-names.py --update-digest` added them and updated
`Wiz/LegacyNames.lean` (`daf06385`), and `check-companion-lists.py` is clean. The four
Wiz checks and the full gate were rerun at that head: Model 104 s, View 30 s,
source-ui 36 s, WebCmd 446 s, all rc=0; 66/66 static Node checks, 10/10 real-`wiz lsp`
Node checks, 47/47 browser assertions (real Chromium and real `wiz lsp`), 0 failures,
rc=0. The mock-server fallback smoke runs locally: 44/44, rc=0. Bundle sizes:
fixtures 1,017,425 B, live 1,084,960 B (`wiz-source-ui.wasm` 843,812 B,
`wiz-source-ui.mjs` 14,726 B, merged `lsp-client.js` 27,018 B, data 69,869 B).

### Restack onto current train12 with the UTF-16 host (2026-11-23)

`agent/scry-web-ux` (3b97605db) was based on the old train12 `b5eb50555`. The restack is
`agent/scry-web-ux-merge` (worktree `/workspace/wt/scry-web-ux-merge`), two merges on
current `integration/train12` `2ad8f0f8c`:

* `401987d38` merges `agent/lsp-host-h1-h3` (`540141a79`, H1 unknown request → -32601,
  H2 UTF-16 positions + `positionEncoding`, H3 `ofPos` clamp/`surrogate`/EOF). H2 is the
  reason for the merge: the reader's offsets are UTF-16 end to end (`data-start` and the
  bundle spans come from `Scry.WebCmd`/`EditorModel`, both UTF-16) and the host used to
  count code points, so anything after a non-BMP character drifted by one per character.
* `528ecb3a8` merges `agent/scry-web-ux`. Two conflicts, both generated:
  `.github/repo-subsets.json` (regenerated with `scripts/repo-subsets.py --write`) and
  `Wiz/LegacyNames.lean`'s digest (`legacy-names.tsv` auto-merged, then regenerated from
  the merged tree with `scripts/gen-legacy-names.py --update-digest`: 12,635 rows in 242
  files, digest `4b8e3d74…`). `gen-legacy-names.py --check`, `check-names.py` and
  `check-companion-lists.py` are clean (5 lists; test-shards skipped, no test driver in
  this worktree), so the companion fix from `daf06385` survives the restack.

**The UTF-16 fixture.** The demo's facts file now carries a non-BMP character on the line
the live tests hover: `lib/Web/Source/Facts.wiz`'s `factsAt` use of
`Source.Span.contains` starts with `/- 😀 UTF-16 fixture -/`, and the module doc says why.
Every offset after it is a real UTF-16 offset: the UTF-16 column is one greater than the
code-point column. The tests aim at the *last* UTF-16 unit of `contains` rather than its
first, because that is the boundary that tells the two counts apart (a code-point server
decodes one character to the right, past the name; one character of drift inside an
8-letter name would pass).

* `web/source_live_test.mjs` asserts the fixture is real (`character === codePointColumn
  + 1`), that the host advertises `positionEncoding: "utf-16"` (H2's visible contract;
  before it the capability was absent and the host counted code points whatever the
  client sent), and then asks the real `wiz lsp --ws` for a hover and a definition at
  that last unit.
* `web/source_chrome_test.mjs` puts the pointer on that last unit (`pointerAt`'s new
  `charIndex`), asserts the pointer's own offset is a UTF-16 offset
  (`over.start > over.codePoints`), and hovers/clicks there.
* The mock-server smoke runs locally on a copy of the previous live bundle whose
  `data/f/<facts>.json` source is patched to carry the character: 39/39, rc=0 (the
  mock's fixed card and the pointer/offset assertions).

Heavy is held behind train11 at the time of writing, so the built-host runs (the Node
live test and the browser smoke with `WIZ_BIN=<built wiz>`) are not yet claimed here.

## Honesty ledger

| what | how it ran | verdict |
|---|---|---|
| Wiz model/view compile (`Source.Page.focus`, `lspHover`, definition answer, marks) | `wiz check` with the merged win3 binary, final run at `daf06385` | Model 104 s rc=0, View 30 s rc=0, source-ui 36 s rc=0, WebCmd 446 s rc=0 (4/4) |
| `scry web --source` + bundle generation | `web/source-bundle.sh` inside `.scratch/build-bundles.sh` (jobs 5293/5326/5375 and the final run at `daf06385`, `win3`) | fixtures 3 files/2 findings; live 5 files/2 findings; runtime yes |
| `scry.source.answer/1` static answers + patch replay (`source_static_test.mjs`) | final run at `daf06385` | 66/66 ok |
| real `wiz lsp --ws` hover/definition on the bundled `Facts.wiz` → `Span.wiz` | `source_live_test.mjs`, final run at `daf06385` | 10/10 ok; hover on `contains`, definition on `Span.wiz`'s `def` line |
| browser: no-JS SSR, mount, static finding hover, `#/f/` | `source_chrome_test.mjs`, real Chromium, final run at `daf06385` | all ok (26 assertions before the live section) |
| browser: `?lsp=` live hover card on `Source.Span.contains` | final run at `daf06385`, real `wiz lsp` | ok: LSP signature and "LSP hover at" |
| browser: click → definition → info rows + `src-focus` jump | final run at `daf06385`, real `wiz lsp` | ok: target `Span.wiz`, bundled file opened, `59:` range outlined |
| browser: server dies mid-session (deliberate failure) | final run at `daf06385` | ok: "live: hover failed" note, files/findings kept, no `data-wiz-error` |
| browser: `?lsp=` with a closed port (deliberate failure) | final run at `daf06385` | ok: `data-lsp=failed`, "live: off", static reader complete, no console error |
| browser: mock-LSP fallback | `source_chrome_test.mjs` locally (`chromium 157`), final bundle | 44/44 ok, rc=0 |
| companion lists (`docs_style`'s early gate) | `scripts/check-companion-lists.py` after `gen-legacy-names.py --update-digest` | clean (5 lists; test-shards skipped: no test driver in this worktree) |
| browser console / network | smoke collects `Runtime.exceptionThrown` + `console.error`; a CDP probe also listened to `Network.loadingFailed` | 0 console errors on every JS load; no failed request in the probe (the smoke has no separate network assertion; the dead-server cases assert the UI effect) |

Not run / not claimed: no full test suite, no site build, no Cachix push, no PR, no
performance measurement.
