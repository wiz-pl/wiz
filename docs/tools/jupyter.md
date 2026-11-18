# Jupyter kernels for Wiz

`tools/jupyter/` is an **opt-in** Jupyter kernel for Wiz: a notebook or
`jupyter console` can run Wiz cells, keep their definitions, show `#eval`
output, report errors and render `%%scry` taint findings. It is not part of the
dev shell, not built by `lake` and not exercised by CI's default groups; it is
Python (standard library plus `pyzmq`), not Lean.

```
tools/jupyter/
  wiz_kernel/            the kernel (wire protocol, drivers, magics, progress, widget comms, exporter)
  wiz-kernel/kernel.json the kernelspec template
  static/                widget.js, loader.js, the headless-browser test and goldens
  tests/                 protocol tests (test_kernel.py, test_widgets.py, test_notebook.py)
                         and the exporter tests (test_export.py: fixtures, no kernel)
  run-tests.sh           the test entry point (protocol, self-test, widget)
  wiz-nb                 the exporter command (`wiz-nb export FILE.ipynb`)
  export.py              the same, runnable from a checkout (`python3 tools/jupyter/export.py`)
  README.md              a short pointer to this page
```

## Install

The kernel needs Python ≥ 3.10 and `pyzmq`; Jupyter itself is only needed to
*use* the notebook (`jupyter_client` is used by the tests). Nothing else is
installed: the kernel lives in this checkout.

```sh
python3 -m pip install pyzmq                 # or: nix shell nixpkgs#python3Packages.pyzmq
python3 -m wiz_kernel install --user         # from tools/jupyter, or with PYTHONPATH:
                                             # PYTHONPATH=tools/jupyter python3 -m wiz_kernel install --user
jupyter console --kernel wiz-kernel          # or a notebook: Kernel → Wiz
```

`install` writes `share/jupyter/kernels/wiz-kernel/kernel.json` under the user's
Jupyter data directory (`--sys-prefix` for a virtualenv, `--prefix DIR` for
another prefix), with `argv` = this Python, `-m wiz_kernel -f
{connection_file}`, and `PYTHONPATH` pointing at `tools/jupyter`, so a checkout
works without `pip install`. `--wiz PATH` pins the toolchain in `env.WIZ`;
`--backend repl|batch` pins the driver; `--dry-run` prints the spec instead of
writing it. `python3 -m wiz_kernel uninstall` removes it.

The kernel also runs without a kernelspec (as Jupyter starts it):

```sh
PYTHONPATH=tools/jupyter python3 -m wiz_kernel -f /path/to/connection.json \
    [--wiz PATH] [--backend auto|repl|batch] [--cwd DIR] \
    [--toolchain-arg=--no-cache]
```

The toolchain is found like this: `--wiz`, then `$WIZ`, then `wiz` on `PATH`,
then a checkout's `.lake/build/bin/wiz` next to `tools/`. If none is found the
kernel still starts and answers `kernel_info_request`; every cell then gets a
`BackendUnavailable` error that says what to set.

The kernel is a single-threaded ZeroMQ loop over the connection file's five
sockets — shell, iopub, control, stdin and heartbeat (the heartbeat on its own
thread) — with Jupyter's 5.3 messaging spec implemented here
(`wiz_kernel/wire.py`): multipart frames with the `<IDS|MSG>` delimiter, the
four JSON frames, and an HMAC-SHA256 signature over them from the connection
file's key. `pyzmq` is the only third-party import; nothing from `jupyter_client`
or `ipykernel` is imported by the kernel. Every request is bracketed by iopub
`status: busy`/`idle`, so a client that connects late still sees iopub traffic.

## The two drivers

The kernel chooses a driver at startup and says which one it is using in three
places: the `kernel_info_reply` banner and `metadata.wiz_backend`, a one-line
`stderr` notice before the first cell's output, and `%backend`.

* **`repl` — a persistent `wiz repl` process.** This is the stateful driver:
  definitions, `syntax`, `macro`s, `instance`s and `import`s stay in scope for
  later cells. Each cell is written to a temp file and elaborated with the
  REPL's `:load FILE`, so a definition may span lines and every message carries
  the cell's own line and column. If the installed `wiz` has no `repl`
  subcommand, this driver is unavailable and the kernel falls back.

* **`batch` — no process state.** Every cell writes *the whole notebook so far*
  plus the cell to a temp file and runs `wiz check` on it, reporting only the
  messages of the cell's line range. State is the accumulated source, not a
  live process: a notebook is rechecked from the top for every cell, so cell
  *n* costs a check of cells 1…*n*. (`wiz check`, not `wiz run`: `run` builds
  and executes `main` and prints none of a cell's `#eval`/`#check` messages.)

`auto` (the default) tries `repl` first and falls back to `batch`. The fallback
reason is reported in `%backend` and in the notice. `--backend` pins either
driver.

Both drivers add `-I <kernel cwd>` to the toolchain's module roots, so
`import Foo` resolves against the directory the kernel was started in (the
notebook's directory, when started from there). The batch driver prepends
`import Prelude` unless a cell imports it; the REPL imports the Prelude at
start, as it does for a terminal session.

### What a cell means

* One cell is one file. Definitions and commands on separate lines behave as in
  a file, and a definition may continue over lines (both drivers use a file).
* `#check`, `#eval` and `:type`-style messages become notebook output on
  `stdout` (`warning:` goes to `stderr`). `#eval` is a command, so its value is
  a stream, as in a file.
* The cell's **last line as a bare expression** (`20 + 22`) is the cell's
  result: when the elaborator answers `unexpected '…'; expected command` for
  that line, the kernel retries it as `#eval`, drops that one error and emits an
  `execute_result` with the value. This is a convenience, not new Wiz semantics:
  a Wiz file has no expression statements.
* A Wiz error is an iopub `error` message (`ename` `WizError`, `evalue` the
  first line of the diagnostic, `traceback` with `line:column: error: …`) and
  the `execute_reply` has `status: "error"`; the session goes on, as `wiz repl`
  does.
* `is_complete_request` answers with a bracket/trailing-token heuristic (not a
  parser), so a frontend can decide whether Enter submits.

## Widgets (interactive output)

`lib/Web/Widget.wiz` builds a widget fragment out of **descriptors** and `Widget.display`
returns it as a pure `String`. The kernel recognises the string, turns it into a
notebook MIME bundle and opens a Jupyter **comm**; the browser applies the VDOM patches
the kernel sends back. No Wasm is involved: the Wiz side runs in the kernel's native
toolchain process, and the browser half is `web/framework/runtime.js`.

The block below is a notebook cell, not a file: its last line is a bare expression whose
value the kernel displays, so it is not checked as a Wiz file.

<!-- no-check: a notebook cell whose last line is a bare expression, not a Wiz file -->
```wiz no-check
import Web.Widget

-- The callback is pure: it receives the event and the widget list as displayed last
-- time, and returns the next list. The kernel re-evaluates it in the session.
def onGain (e : Widget.Event) (ws : List Widget.Widget) : List Widget.Widget :=
  List.map (fun w => match String.eq w.id e.widget with
    | .true => Widget.setValue w e.value
    | .false => w) ws

Widget.display [
  Widget.sliderRange "gain" "input" "0.50" "onGain" "0" "1" "0.05",
  Widget.button "reset" "click" "Reset" "onGain",
  Widget.text "name" "input" "ada" "onGain",
  Widget.plot "trace" "click" "{\"points\":[1,2,3]}" "onGain"
]
```

The constructors are `slider` (0–100, step 1) / `sliderRange`, `button` / `buttonValue`,
`text` and `plot`; each takes an id, the DOM event it forwards, its initial
value/label/data, and a **callback expression** naming a `Widget.Callback`
(`Widget.Event → List Widget.Widget → List Widget.Widget`). A widget with an empty
callback is display-only. `Widget.display` must be the cell's last expression (the
kernel evaluates a bare final expression); `#eval Widget.display …` also works, and the
kernel finds the prefixed line in the stream.

The protocol, all of it on the shell/iopub sockets:

* **display** — the string is `WIZ_WIDGET:` plus a JSON bundle
  (`schema`, `html`, `widgets`, `count`). The kernel adds a `comm_id` and publishes
  `comm_open` (`target_name: "wiz.widgets"`, `data` = the bundle) before the
  `execute_result`. That result carries `application/vnd.wiz.widget+json` (the bundle),
  `text/html` (the SSR fragment wrapped in
  `<div class="wiz-widget-fragment" data-wiz-widget-comm="ID">`) and a `text/plain`
  summary.
* **event** — the front end sends a `comm_msg` with
  `{method: "event", widget_id, event, value}`. The kernel looks the widget's callback
  up in `comm_id -> widget id -> callback expression`, evaluates
  `#eval Widget.handle (<callback>) "<previous bundle>" "<id>" "<event>" "<value>"` in
  the notebook session, and publishes a `comm_msg` with
  `{method: "update", bundle, patches}`. `patches` is `React.patchesJson
  (React.Rendered.diff old new)`, so the browser applies it with the same patch applier
  as the React framework. A failed callback is `{method: "error", error}`.
* **close / info** — `comm_close` drops the registry entry (and is echoed on iopub);
  `comm_info_request` lists the open widget comms. Shutdown sends `comm_close` for
  each.

The callback is the only thing spliced into the session (it is the notebook author's
own code, with the authority of a cell); every value that comes back from the browser
is quoted as a Wiz string literal. One display per cell is shown (the last); the
bundle can hold any number of widgets.

**Include path.** `Web.Widget` lives in a checkout's `lib/`, not in the toolchain's
own library, so the kernel must be started with that directory as a module root:

```sh
PYTHONPATH=tools/jupyter python3 -m wiz_kernel -f connection.json \
    --toolchain-arg=-I --toolchain-arg="$PWD/lib"
```

The same flag goes into a kernelspec's `argv` when installing from a branch. The
tests pass it explicitly.

**Front end.** `tools/jupyter/static/widget.js` is an ES module that imports
`applyPatches`/`mount` from `web/framework/runtime.js` — there is no second renderer —
and adds only event extraction (`data-wiz-widget`, `data-wiz-widget-input`,
`data-wiz-widget-value`) and the comm binding. `loader.js` is the classic Notebook
glue: it registers the `wiz.widgets` comm target, adopts the SSR fragment (no
re-render flash) and scans output areas. Load it from `custom.js`:

```js
// custom.js (classic Notebook / nbclassic): the files are ES modules, so use import()
import("https://…/tools/jupyter/static/loader.js").then((loader) => loader.install());
```

JupyterLab needs a mime-renderer extension for `application/vnd.wiz.widget+json` that
calls `renderMime`; the extension is **not** included, so JupyterLab shows the SSR
HTML without events.

**What survives the split.** The keyed diff is computed in Wiz (`React.Rendered.diff`,
`React.patchesJson`) and applied in JS (`move`/`insert`/`remove`/`text`/…), so keyed
lists keep their identity and minimal moves. Lens state (`React.useState`/`setState`)
is Wiz-side: the callback recomputes the new widget list from the previous one on every
event. `React.Owned` is a Wiz typing property inside one evaluation; a linear token
cannot be held across two `#eval`s or cross the comm, so it does not model a
browser-held resource. The browser has **no local state and no hooks**: every event is
a kernel round trip (with the batch driver, a `wiz check` of the whole notebook), and
the front end adopts server-rendered DOM rather than hydrating state.

**Events carry the value.** The raw React path (`React.on` → `delegate` →
`React.App.event`) passes only `(event, handler index)`, so a slider's value is lost
there. Widgets deliberately do not use that path: the front end sends `value`
explicitly and `Widget.Callback` receives it in `Widget.Event`, so
`Widget.setValue w e.value` sees the number (the protocol test pins this). The
index-only gap remains for hand-written `React.on` handlers in `Web.React` apps; a
widget uses the descriptor/comm path instead.

**Front-end test.** `tools/jupyter/static/widget_test.mjs` runs the same scenario
twice: the Node fallback (`web/framework/minidom.mjs`) always, and headless
Chrome/Chromium when one is on `PATH` (or `--browser`/`$WIZ_WIDGET_BROWSER` names it).
It mounts the `Widget.display` bundle through `WidgetView`, dispatches a real click and
a range `input`, checks the comm payloads (`{method, widget_id, event, value}`), and
applies the patches `Widget.handle` produced. The goldens in `static/goldens/` are the
serialised DOM after the first render and each update plus the comm payloads;
`--update` rewrites them. The browser run is what catches a `setAttribute("value")`
only patch (the live DOM property); the Node test double cannot. `static/widget_gen.sh`
regenerates the fixture from `widget_gen.wiz` (needs a `wiz` binary; the test does
not). `web/widget/test.sh` is the Wiz-side golden (each widget kind, the display
bundle, keyed diff and removal) with no browser at all.

**Limits.** `plot` carries opaque JSON in `data-wiz-widget-data` and the front end
draws a placeholder until a `Plot` module exists. `runtime.js` mirrors a `value` patch
into the DOM property (so a live range/text control follows it), but `checked` is still
attribute-only. There is no `display_data` stream and no debugger.

## Magics

`%%scry` runs `scry taint --json` on the cell's **C source** and renders the
findings (plain text, an HTML table and the raw report as `application/json`):

```
%%scry
char *getenv(const char *name);
int system(const char *command);

int main(void) {
  char *cmd = getenv(0);
  system(cmd);
  return 0;
}
```

→

```
scry taint: 1 finding(s), 1 checked, 0 unchecked, 0 boundary warning(s)
- [error] command-injection at wiz-scry-…c:7:3 (checked): Attacker-controlled data reaches a command interpreter
```

It is **per-cell**: the C is written to a temp file, analysed and forgotten.
There is no project, no include path, no cross-cell state, and the file name in
the finding is the temp file's (the row keeps the line and column). Options
after `%%scry` are passed to `scry taint` (`%%scry --rules my.scry`,
`%%scry --sarif out.sarif`, `--allow-errors`, `--fail-on-finding`); `--json` is
always added. The executable is found from `$WIZ_SCRY` (a command line, e.g.
`WIZ_SCRY='grail run scry --'` from `scry/`), then `scry` on `PATH`, then a
checkout's `scry/.grail/bin/scry` (searched from the kernel's cwd and from the
`wiz` binary's directory upwards). The default rule pack is passed as
`--rules lib/Scry/rules/default.scry` when one is found the same way. Without
an executable the cell fails with `ename: ScryUnavailable` and an explanation.

`%backend` prints the driver in use (and why, when it fell back); `%%wiz` and
`%wiz CODE` force the Wiz driver for a cell whose first line would look like a
magic. Unknown magics are an `UnknownMagic` error.

### `%%wiz` and a plain cell

There is no difference in execution. A plain cell and the same text after
`%%wiz` reach the same driver through the same `execute` call, are written to the
same kind of temp file, and have the same line numbers, state and result. The
only difference is **dispatch**: a plain cell's first line is offered to the
magic table, so a cell that begins with `%%scry` (or any other magic name) runs
that magic. `%%wiz` skips that one check, which is how a cell whose first line
really is `%%…` is written as Wiz. Use it for disambiguation, not for a different
backend; `%backend` is what reports the driver.

### `%%sh`

`%%sh` runs the cell as a shell script, streaming both pipes and returning the
exit status:

```
%%sh
git status --short
wc -l lib/*.wiz
```

stdout and stderr are published as `stream` messages **as the lines arrive**, so
a slow command shows output while it runs. Each stream keeps its own order, but
the two are separate pipes, so a stderr line can be published before a stdout line
the script wrote first (use `2>&1` when the interleaving matters). A zero exit
becomes the cell's result (`exit status 0`); a non-zero one is an `error` with `ename: ShellError` and the
status in `evalue`, so `%%sh` is usable as a check (Jupyter marks the cell
failed). The interpreter is `/bin/sh`; arguments replace that command line, e.g.
`%%sh bash -e`. The timeout is `$WIZ_SHELL_TIMEOUT` seconds (default 300).

**Security: there is no sandbox.** `%%sh` and every other magic run as your user,
with your environment, in the kernel's working directory, on the machine that
runs the kernel. The kernel does not restrict commands, paths, network or
subprocesses, and it makes no claim that it does: a notebook is code, and a
notebook from someone else is their code running as you. The same is true of
`%%scry` (it executes the `scry` binary) and of ordinary Wiz cells. Run untrusted
notebooks in a container, VM or separate user account, not by trusting this
kernel to contain them.

### `%%time`

`%%time` runs the cell through the normal backend (the plain-cell path) and
appends one `stream` line *after* the cell's output, so it sits above the cell's
`execute_result`:

```
%%time
def slow : Nat := 6 * 7
```

→

```
[time] wall 0.412 s, peak RSS 54.2 MiB (sampled descendants (/proc))
```

The wall clock is `time.monotonic` around the cell. Peak RSS is sampled every
50 ms from `/proc` for the kernel's descendants (the `wiz repl` process, or the
`wiz check` that batch starts), so it is a lower bound and the line says
`sampled`; where `/proc` is absent it falls back to
`resource.getrusage(RUSAGE_CHILDREN)` and says `children peak`. Sampling is a
daemon thread of small `/proc` reads, cheap enough to be the default. `%%time`
does not time `%%sh` (put `time` in the script) or `%%scry`; it is a Wiz-cell
timer.

### Progress for long analyses

A two-minute `scry taint` run must not look like a frozen notebook. `%%scry
--progress` passes `--progress` to `scry` and forwards each stderr line **while
the cell runs**, in order, through a progress channel. There are two transports:

* **iopub stream** (the default on this kernel): each line is a `stdout`
  `stream` message, in order. It needs nothing from the front end, so it works in
  `jupyter console`, JupyterLab and any client that shows streams.
* **comm**: a kernel-initiated `comm_open` with target `wiz.progress` and one
  `comm_msg` per line (with a `fraction` when the line has `n/m` or `n%`). This
  is the channel for a front end that renders progress: a client opens the comm
  itself with that target, and the kernel then uses it. The widget front end
  (`static/widget.js`) registers only `wiz.widgets` and does not render
  `wiz.progress`, so the kernel does not open the progress comm on its own and
  the default stays the iopub stream; `%progress` says so.

`%progress` reports which transport is in use and why:

```
progress: iopub stream (the widget front end does not render wiz.progress comms); each line is a `stdout` stream message, in order
```

The contract with `scry` is deliberately loose while `--progress` is new: every
non-blank stderr line is forwarded, and a `3/12` or `25%` in it becomes a
fraction. A `scry` without `--progress` rejects the flag and the cell reports a
`ScryError`; use plain `%%scry` there.

## Exporting a notebook

A notebook is only useful outside Jupyter if its output survives the trip. The
exporter renders the file — markdown cells, code and the outputs already stored
in it — into **one self-contained HTML page** (small inline stylesheet, no
JavaScript, no CDN, no network) or a plain Markdown file:

```sh
tools/jupyter/wiz-nb export docs/notebooks/tour.ipynb            # → tour.html
tools/jupyter/wiz-nb export FILE.ipynb --to md --out notes.md
python3 -m wiz_kernel.export export FILE.ipynb                   # the same
```

`--to html|md` picks the format (default `html`, or inferred from `--out`'s
suffix); `--out FILE` names the output (default: the notebook's name with
`.html`/`.md`); `--out -` writes to stdout. The built-in `wiz` binary is Lean
and does not dispatch to `tools/jupyter/`, so the command is the wrapper above
(the alias `wiz nb export` is not installed).

The output is **deterministic**: no timestamps, no random ids and no absolute
paths are added, so an exported page can be committed and diffed. `--check`
renders the notebook in memory and exits 1 when the committed file differs
(printing a short unified diff); it is how the docs notebook is kept from
rotting:

```sh
tools/jupyter/wiz-nb export docs/notebooks/tour.ipynb --check
tools/jupyter/check-notebooks.sh          # every docs/notebooks/*.ipynb
```

The example is `docs/notebooks/tour.ipynb` with its page `tour.html`; both are
checked in, and the docs site copies the HTML to `/notebooks/` (see
`web/build-site.sh`). The fixture notebooks in `tools/jupyter/tests/fixtures/`
cover markdown, stdout, `execute_result`, errors, widgets and a cell with no
output.

### What is rendered

* Markdown cells become a small HTML subset (headings, paragraphs, emphasis,
  inline code, fenced code, lists, quotes, links, images). Tables, footnotes
  and math are not interpreted.
* Code cells keep their source and execution count (`In [n]:`) and every stored
  output: `stdout`/`stderr` streams (consecutive streams are merged), an
  `execute_result` (`text/html`, `text/markdown`, `text/plain`, `image/png`,
  `image/jpeg`, `image/gif`, `image/webp`, SVG or `application/json`; HTML is
  sanitised, images become `data:` URLs) and errors (`ename`, `evalue` and the
  traceback).
* Raw cells are shown verbatim.
* Output HTML is treated as untrusted, as a viewer treats a notebook: scripts,
  styles, frames, event handlers and active URLs are removed; an embedded frame
  with `srcdoc` is unwrapped and sanitised in place, so a widget does not become
  a broken frame.
* **Widgets.** An `application/vnd.wiz.widget+json` output (the infoview's
  `{title, html, goals}` protocol) becomes its static HTML plus the goal
  snapshot. A Jupyter widget view
  (`application/vnd.jupyter.widget-view+json`) becomes a note that it is
  interactive-only, unless the bundle carries a `text/html` fallback, which is
  exported. Widget state lives in the kernel and is never in the file.

### What is lost

* **Interactivity.** A widget, a live output or a kernel-driven display cannot
  be reproduced; at best its static HTML fallback is exported, and otherwise the
  page says so.
* **Kernel state.** Definitions, imports, `syntax`, `macro`s and `instance`s
  live in the kernel, not in the notebook's outputs. The exported page is a
  snapshot: its code is not run, and a reader must open the notebook and run the
  cells to get a session.
* **Freshness of outputs.** `--check` re-exports the stored outputs; it does not
  re-run the notebook. An output that was already stale in the `.ipynb` stays
  stale in the page. Re-run the notebook (Jupyter or the kernel's tests) before
  exporting when the code changed.
* **Nothing outside the file.** `display_data` keys the exporter does not know,
  widgets without a static fallback, `stderr` from the kernel itself and
  anything produced after the last saved output are not invented.
* Execution counts and output order are kept as stored; the exporter does not
  renumber cells.

## Limits

* **Completion and inspection are empty.** `complete_request` returns no
  matches and `inspect_request` answers `found: false`. The Wiz language server
  (stage 11, `wiz lsp`) knows both; connecting it to the kernel is future work.
* **Interrupt is not implemented (frozen).** The kernelspec sets
  `"interrupt_mode": "message"`, so Jupyter sends `interrupt_request` on the
  control channel instead of a signal (a signal would kill the kernel and its
  child). The reply is `ok`, but the running `wiz` process is **not** stopped;
  a warning is printed. This includes `%%sh` and `%%scry --progress`: the child
  runs to completion or its own timeout (`WIZ_SHELL_TIMEOUT`,
  `WIZ_SCRY_TIMEOUT`). A cell that loops forever must be stopped by restarting
  the kernel (which kills the child).
* **No stdin.** The kernel never sends `input_request`; `allow_stdin` is
  ignored. Programs that read stdin in the REPL's `:run` are not supported.
* **No `display_data` or debugger.** Output is streams, one `execute_result` (text,
  HTML or a widget bundle) and errors. Multiple displays per cell, the `display_data`
  stream, the debug protocol and `user_expressions` (always `{}`) are not
  implemented. Widgets are the one rich output; see above. The `wiz.progress`
  comm is transport only: the widget front end does not render it.
* **Batch is O(cells²).** The fallback rechecks the notebook per cell; a long
  notebook is slow, and deleting a definition means restarting. A failed cell is
  kept in that accumulated source (as it would be in a file): later cells still
  run, because `wiz check` elaborates every command and reports them all.
* **A dead `wiz repl` is not restarted.** If the REPL process exits (a panic, a
  signal), later cells fail with `ename: BackendError` until the kernel is
  restarted; restarting loses the definitions (nothing is silently replayed).
* **Cells share one working directory.** `link_c` paths in a cell are resolved
  relative to the kernel's cwd, not the temp file (the REPL has no file of its
  own); a `:load`-style path with spaces is not supported.
* **`%%scry` is one C file per cell**, with tree-sitter's recovery on request
  only (`--allow-errors`). It is the taint slice, not the whole scry platform
  (points-to, memory, multi-file analysis are not in the CLI yet).
* **Notebook code is not sandboxed.** Like any kernel, the process runs code you
  give it; `%%sh`, `%%scry` and the toolchain are ordinary local programs. Use it
  on sources and notebooks you would run locally (see the `%%sh` security note).

## Tests

```sh
# everything runnable here: protocol tests, kernel self-test, widget front end
sh tools/jupyter/run-tests.sh

# protocol-level: starts the kernel on a connection file and talks jupyter_client
python3 -m unittest discover -s tools/jupyter/tests -v

# the same, with a toolchain that has `wiz repl`
WIZ_TEST_WIZ=/path/to/wiz python3 -m unittest discover -s tools/jupyter/tests -v

# no Jupyter at all: wire + drivers + magics + a raw-ZeroMQ kernel session
PYTHONPATH=tools/jupyter python3 -m wiz_kernel --self-test [--wiz PATH]

# the widget VDOM and patches, no browser (Node + web/framework/minidom.mjs)
WIZ=wiz web/widget/test.sh

# the widget front end: Node fallback, then headless Chrome/Chromium if installed
node tools/jupyter/static/widget_test.mjs [--browser PATH] [--no-browser]

# the exporter alone (pure Python; fixtures plus the docs notebook's --check)
python3 -m unittest discover -s tools/jupyter/tests -p 'test_export.py' -v
```

`tests/test_kernel.py` covers the kernel protocol, `tests/test_widgets.py` the widget
comm round trip (display → `comm_open` → slider event → `comm_msg` with patches, plus
`comm_info`/`comm_close`), and `tests/test_notebook.py` a real `nbclient` run of a
notebook (skipped without `nbclient`/`nbformat`). `web/widget/test.sh` is the Wiz-side
golden: each widget kind's VDOM, the display bundle, and the patches applied to
minidom (a keyed rotation is moves; a slider change is a `text` patch on its output).

The unittest module skips cleanly when `pyzmq` or `jupyter_client` is missing or
no `wiz` is found. `$WIZ_TEST_BACKEND` pins `repl`/`batch` (default `auto`);
`$WIZ_SCRY` enables the `%%scry` cases. `ProgressTransportTest` starts a second
kernel with `WIZ_SCRY` pointing at a small script in its workspace, which emits
three `progress:` lines on stderr and a JSON report on stdout, so the ordered
forwarding is tested without a real `scry` (or a `--progress` implementation).

`--self-test` needs only `pyzmq` (and skips the live session without it); it
prints PASS/FAIL/SKIP per check and exits 1 on a failure. It covers, besides the
wire and the drivers: `%%sh` stream order and exit status (0 and non-zero), the
`%%time` line (present, plausible wall, RSS field), `%%wiz` against a plain cell,
`%%scry --progress` ordering, and the same four cells through a live kernel. `test_export.py` needs
neither `pyzmq` nor a toolchain: it renders the checked-in fixture notebooks and
runs `--check` on the example.

`run-tests.sh` prints a `skip:` line for each part whose dependency is absent and
still exits 0 if everything that ran passed; it passes `--no-browser`/`--browser`
through to the widget front-end test and runs `web/widget/test.sh` when a `wiz`
binary is available. The front-end test's Node fallback always runs, so the pure
patcher is checked on a machine with no browser at all; the headless-browser step
is skipped with a message when no Chrome/Chromium is on `PATH`. A skipped browser
run is not a failed one, but a golden mismatch under the Node fallback is always a
failure. `tools/jupyter/static/widget_gen.sh` regenerates `widget_fixture.json` and
the DOM goldens from `widget_gen.wiz` (it needs `wiz`; the test does not).

The kernel is not hooked into `lake test` or the CI workflows; it needs no Lean
build and only a `wiz` executable (whose `repl` subcommand is the stage 11 REPL,
`docs/stages/11-tooling.md`). The widget front end's Node fallback needs only Node;
its browser run needs a Chrome/Chromium binary and is skipped otherwise.
