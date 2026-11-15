# Jupyter kernels for Wiz

`tools/jupyter/` is an **opt-in** Jupyter kernel for Wiz: a notebook or
`jupyter console` can run Wiz cells, keep their definitions, show `#eval`
output, report errors and render `%%scry` taint findings. It is not part of the
dev shell, not built by `lake` and not exercised by CI's default groups; it is
Python (standard library plus `pyzmq`), not Lean.

```
tools/jupyter/
  wiz_kernel/            the kernel (wire protocol, drivers, magics, LSP client)
  wiz-kernel/kernel.json the kernelspec template
  tests/test_kernel.py   protocol-level tests (jupyter_client)
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
    [--toolchain-arg=--no-cache] [--lsp-command CMD | --no-lsp]
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
places: the `kernel_info_reply` banner and `metadata.wiz_backend`, a `stderr`
notice before the first cell's output, and `%backend`.

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

## Completion and inspection (the language server)

`complete_request` and `inspect_request` are answered by the Wiz language server
(`wiz lsp`), not by a second implementation of inference. The kernel starts one
`wiz lsp` child **lazily**, on the first completion or inspection, keeps it for
the session and sends `didClose`/`shutdown`/`exit` when the kernel shuts down. The
transport is stdio (`Content-Length`-framed JSON-RPC 2.0, the server's default);
there is one child per kernel, in the kernel's working directory.

```
complete_request  → textDocument/didOpen or didChange (full text)
                  → textDocument/completion
inspect_request   → textDocument/hover
```

The server is found the same way as the toolchain: `--wiz`, `$WIZ`, `wiz` on
`PATH`, then a checkout's `.lake/build/bin/wiz`. `--lsp-command CMD` (or
`$WIZ_KERNEL_LSP`) replaces the whole command line, for a wrapper or a mock;
`--no-lsp` turns completion and inspection into empty answers. The extra
`-I <cwd>` argument the driver adds is there too, so a cell can `import` a
module from the notebook's directory.

### What the server sees

The kernel keeps the executed cells (a `%%wiz`/`%wiz` cell contributes its body;
`%%scry` and unknown magics contribute nothing) and, for a request, composes the
document the batch driver would check:

```
import Prelude            ← unless some cell already imports Prelude
<cell 1>\n
<cell 2>\n
<current cell>            ← the one Jupyter sent in complete_request
```

The document has a `file://` URI in the kernel's working directory
(`.wiz-kernel-notebook.wiz`); it need not exist on disk, but its directory is
where `include_str` resolves. A cell that does not parse does not stop the
request: the server elaborates the commands it can and completion still sees
the earlier definitions (the self-test checks this).

### Positions: the cell's offset, in UTF-16

Jupyter's `cursor_pos` is an index into the cell (a Python code-point index in
the kernel). LSP wants 0-based lines and UTF-16 code units. The translation is
done once, in `wiz_kernel/lsp.py`:

1. Compose the document above and remember `start`, the **code-point** offset
   where the current cell begins.
2. Take `document[start + cursor_pos:]` as a prefix (Python slicing, so astral
   characters count one here).
3. Count `\n` in it for the line; convert the text after the last newline to
   UTF-16 code units for the character (`a😀b` is four units, so a cursor after
   `b` is at character 4).

Never add the widths of previous cells: a line starts at character 0 again, and
mixing UTF-16 widths with Python offsets misplaces the request. The reply's
`textEdit.range` is mapped back the same way (LSP position → document offset →
cell offset), so `cursor_start`/`cursor_end` replace exactly the word LSP meant.
The Lean server counts Unicode scalar values, which agrees with UTF-16 for
everything in the Basic Multilingual Plane (`docs/playground-lsp.md` has the
same caveat); astral characters are the only difference.

### The Jupyter shapes

`complete_request` maps each LSP `CompletionItem` to Jupyter's
`{text, type, signature, documentation}`:

| LSP `kind` | Jupyter `type` |
|---|---|
| function, constructor | `function` |
| method | `method` |
| field, property | `property` |
| class, interface, enum, struct | `class` |
| module | `module` |
| keyword | `keyword` |
| variable, value, text, … | `text` |

`text` is `textEdit.newText` (else `insertText`, else `label`), `signature` is
the item's `detail` (the type), and `documentation` is its Markdown/text.
`cursor_start`/`cursor_end` come from the edit range; a list with no edits falls
back to the word around the cursor. The server's `isIncomplete` is not lost: it
is reported as `metadata.isIncomplete` and `metadata.wiz_lsp.isIncomplete`, so a
frontend that understands metadata can re-ask; the list is never truncated by
the kernel.

`inspect_request` calls `textDocument/hover` and answers `found: true` with the
Markdown in `data['text/plain']` and, when the server sent Markdown (it does), a
`data['text/markdown']` copy. A `null` hover, or one whose contents are blank,
is `found: false` with `data: {}`. `detail_level` is ignored (the server has one
hover).

### Degrading, and what `%backend` says

No `wiz`, no `lsp` subcommand, an initialization failure or a timeout is not a
kernel error: the reply is still `status: ok` with no matches / `found: false`.
The reason is in `metadata.wiz_lsp` (`enabled`, `available`, `started`,
`transport`, `command` when running, and `reason` when not). The same state is
in `kernel_info_reply.metadata.wiz_lsp`, in the banner, in the stderr notice
before the first cell and in `%backend`:

```
backend: repl
lsp: connected (stdio; `wiz lsp`)
```

Before the first completion the line says `lsp: not started (starts on the first
completion or inspection)`; with `--no-lsp` it says `lsp: disabled (--no-lsp)`.
A single failed request (a timeout, a server that exited) is remembered as the
reason until the next request; it never turns into an `error` reply.

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

* **Signature help and code actions are not wired into Jupyter messages.**
  `wiz lsp` implements `textDocument/signatureHelp`, `textDocument/codeAction`
  and the infoview (`wiz/*`), but Jupyter's completion/inspection protocol has
  no place for them; a future rich-display or frontend extension would carry
  them. Diagnostics are received (the client keeps the connection's stream in
  order) but are not shown in a cell: the text is the accumulated source, so a
  stale range would point at the wrong notebook line.
* **Completion is against the accumulated source, not the REPL's live state.**
  Every request sends the document composed from the executed cells, and the
  server elaborates it from the top; editing an earlier cell after it ran does
  not change the document, because the kernel records what was executed (a
  `%%wiz` cell records its body). This is the same model as the batch driver,
  and it is what makes the cell offset well-defined.
* **A dead language server is not restarted.** If `wiz lsp` exits, later
  requests answer empty/found=false with the exit in metadata until the kernel
  is restarted (same policy as a dead `wiz repl`).
* **The first completion pays the server's startup.** Later requests reuse the
  child (and its query engine) and send `didChange` only when the document text
  changed; moving the cursor alone does not re-elaborate.
* **Interrupt is not implemented.** The kernelspec sets
  `"interrupt_mode": "message"`, so Jupyter sends `interrupt_request` on the
  control channel instead of a signal (a signal would kill the kernel and its
  child). The reply is `ok`, but the running `wiz` process is **not** stopped;
  a warning is printed. A cell that loops forever must be stopped by restarting
  the kernel (which kills the child).
* **No stdin.** The kernel never sends `input_request`; `allow_stdin` is
  ignored. Programs that read stdin in the REPL's `:run` are not supported.
* **No rich display or debugger.** Output is streams, `execute_result` text/HTML
  and errors. `display_data`, widgets, the debug protocol and `user_expressions`
  (always `{}`) are not implemented.
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

# no Jupyter at all: wire + positions + mock LSP + drivers + a raw-ZeroMQ session
PYTHONPATH=tools/jupyter python3 -m wiz_kernel --self-test [--wiz PATH]
```

The unittest module skips cleanly when `pyzmq` or `jupyter_client` is missing or
no `wiz` is found. `$WIZ_TEST_BACKEND` pins `repl`/`batch` (default `auto`);
`$WIZ_SCRY` enables the `%%scry` cases. The mock-LSP classes need no Wiz build:
they start the kernel with `--lsp-command` pointing at
`python -m wiz_kernel.mock_lsp`, and a `--no-lsp` class and a missing-command
class check the degraded answers.

`--self-test` has a **mock LSP** section (`wiz_kernel/mock_lsp.py` is a real
stdio server with fixed completions/hover and a JSON-lines request log): it
checks the UTF-16 rules, the cell offset in a multi-cell notebook, that the
exact position reached the server, the replacement range, the
`isIncomplete` flag, the empty completion/hover, and `shutdown`/`exit` on close.
Its **live LSP** section starts the real `wiz lsp` when a toolchain is found,
completes a name defined in an earlier cell with an unparsable cell in between,
and hovers a use; it skips cleanly when `wiz lsp` cannot start. `--self-test`
needs only `pyzmq` for the live kernel session (the LSP sections need no ZeroMQ)
and prints PASS/FAIL/SKIP per check and exits 1 on a failure.

The kernel is not hooked into `lake test` or the CI workflows; it needs no Lean
build and only a `wiz` executable (whose `repl` subcommand is the stage 11 REPL,
`docs/stages/11-tooling.md`).
