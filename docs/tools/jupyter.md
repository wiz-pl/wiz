# Jupyter kernels for Wiz

`tools/jupyter/` is an **opt-in** Jupyter kernel for Wiz: a notebook or
`jupyter console` can run Wiz cells, keep their definitions, show `#eval`
output, report errors and render `%%scry` taint findings. It is not part of the
dev shell, not built by `lake` and not exercised by CI's default groups; it is
Python (standard library plus `pyzmq`), not Lean.

```
tools/jupyter/
  wiz_kernel/            the kernel (wire protocol, drivers, magics, widget comms)
  wiz-kernel/kernel.json the kernelspec template
  static/                widget.js (the front end) and loader.js (classic Notebook glue)
  tests/                 protocol tests (test_kernel.py, test_widgets.py, test_notebook.py)
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

```wiz
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

**Limits.** `plot` carries opaque JSON in `data-wiz-widget-data` and the front end
draws a placeholder until a `Plot` module exists. Text/range values are patched as
attributes, not DOM properties (React's documented limit), so a live input's property
may not follow an attribute patch. There is no `display_data` stream and no debugger.

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

## Limits

* **Completion and inspection are empty.** `complete_request` returns no
  matches and `inspect_request` answers `found: false`. The Wiz language server
  (stage 11, `wiz lsp`) knows both; connecting it to the kernel is future work.
* **Interrupt is not implemented.** The kernelspec sets
  `"interrupt_mode": "message"`, so Jupyter sends `interrupt_request` on the
  control channel instead of a signal (a signal would kill the kernel and its
  child). The reply is `ok`, but the running `wiz` process is **not** stopped;
  a warning is printed. A cell that loops forever must be stopped by restarting
  the kernel (which kills the child).
* **No stdin.** The kernel never sends `input_request`; `allow_stdin` is
  ignored. Programs that read stdin in the REPL's `:run` are not supported.
* **No `display_data` or debugger.** Output is streams, one `execute_result` (text,
  HTML or a widget bundle) and errors. Multiple displays per cell, the `display_data`
  stream, the debug protocol and `user_expressions` (always `{}`) are not
  implemented. Widgets are the one rich output; see above.
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
* Notebook `%%scry` analysis is not sandboxed: like any kernel, the process runs
  code you give it, and the toolchain and scry binaries are ordinary local
  programs. Use it on sources you would run locally.

## Tests

```sh
# protocol-level: starts the kernel on a connection file and talks jupyter_client
python3 -m unittest discover -s tools/jupyter/tests -v

# the same, with a toolchain that has `wiz repl`
WIZ_TEST_WIZ=/path/to/wiz python3 -m unittest discover -s tools/jupyter/tests -v

# no Jupyter at all: wire + drivers + a raw-ZeroMQ kernel session
PYTHONPATH=tools/jupyter python3 -m wiz_kernel --self-test [--wiz PATH]

# the widget VDOM and patches, no browser (Node + web/framework/minidom.mjs)
WIZ=wiz web/widget/test.sh
```

`tests/test_kernel.py` covers the kernel protocol, `tests/test_widgets.py` the widget
comm round trip (display → `comm_open` → slider event → `comm_msg` with patches, plus
`comm_info`/`comm_close`), and `tests/test_notebook.py` a real `nbclient` run of a
notebook (skipped without `nbclient`/`nbformat`). `web/widget/test.sh` is the Wiz-side
golden: each widget kind's VDOM, the display bundle, and the patches applied to
minidom (a keyed rotation is moves; a slider change is a `text` patch on its output).

The unittest module skips cleanly when `pyzmq` or `jupyter_client` is missing or
no `wiz` is found. `$WIZ_TEST_BACKEND` pins `repl`/`batch` (default `auto`);
`$WIZ_SCRY` enables the `%%scry` cases. `--self-test` needs only `pyzmq` (and
skips the live session without it); it prints PASS/FAIL/SKIP per check and exits
1 on a failure.

The kernel is not hooked into `lake test` or the CI workflows; it needs no Lean
build and only a `wiz` executable (whose `repl` subcommand is the stage 11 REPL,
`docs/stages/11-tooling.md`).
