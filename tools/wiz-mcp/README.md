# wiz-mcp: Wiz tools for MCP clients

A small MCP (Model Context Protocol) server that gives an agent the Wiz
toolchain: type checking, formatting, parsing, building, and the language
server's diagnostics, hover and tactic state.

* **stdlib only.** Python 3.9+; no packages, no virtualenv, no build step.
* **One process per workspace.** The client starts it; it owns exactly one
  `wiz lsp` daemon for that worktree, started on demand.
* **Opt-in.** Nothing in `flake.nix`/`devenv.nix` references this tool, and it
  is not on the default dev shell's path. Add the MCP configuration to one
  worktree or to your global client config when you want it.

## Why MCP and not the `lsp` config

OpenCode **V2 does not run language servers**. In 2.2.5 the `lsp` config key is
still in the schema, is decoded by `config/normalize.ts`, and appears in the
settings UI, but no code consumes it: `packages/core/src` has no LSP client and
the V2 docs index has no LSP page (`/v2/docs/lsp` serves the V1 page). So

```jsonc
{ "lsp": { "wiz": { "command": ["wiz", "lsp"], "extensions": [".wiz"] } } }
```

is decoded and **inert** today. It is the right recipe for the day V2 restores
LSP (it would give push diagnostics for free), but it does not give an agent
anything now. **MCP is the route.**

OpenCode starts **one copy of every configured MCP server per loaded
location** (worktree), not one per server: two locations produce two bridges,
and `pool: true` does not pool a legacy stdio server. A location unloads after
`experimental.location_idle_timeout` (default 60 minutes), so the process count
follows the recently active worktrees. That is why this bridge is cheap at rest
and why it must not share its daemon across worktrees.

## Quick start

Build the toolchain in the worktree first (the bridge does not build anything):

```sh
lake build wiz
```

Then add a local MCP server to the OpenCode V2 config. The file below is
`tools/wiz-mcp/opencode.example.jsonc`:

```jsonc
{
  "$schema": "https://opencode.ai/config.json",
  "mcp": {
    "timeout": { "startup": 30000, "catalog": 30000, "execution": 330000 },
    "servers": {
      "wiz": {
        "type": "local",
        "command": [
          "python3", "tools/wiz-mcp/wiz_mcp.py",
          "--wiz", "./.lake/build/bin/wiz",
          "--idle", "600",
          "--timeout", "300"
        ],
        "cwd": ".",
        "timeout": { "startup": 20000, "catalog": 10000, "execution": 330000 },
        "codemode": true
      }
    }
  }
}
```

`cwd` defaults to the workspace directory, so the relative script, `--wiz` and
all tool paths resolve inside that worktree. If your client does not resolve a
relative `command` against `cwd`, use the absolute path to `wiz_mcp.py`.
`timeout.execution` must be **larger** than the bridge's `--timeout`
(330 s > 300 s) so a hung call returns the bridge's error instead of being cut
off by the MCP client.

Tool names are `<server>_<tool>`: the tools below are `wiz_check`, `wiz_fmt`,
and so on. With `codemode: true` the model calls `tools.wiz.check(...)` and the
per-tool schemas stay out of the prompt. A restrictive permission policy must
allow `wiz_*` (the action is `<server>_<tool>`); the default agent policy
allows `*`.

For another MCP client, run the same command over stdio; there is nothing
OpenCode-specific in the server.

### Claude Code and the launcher

The repository root has a project-scoped `.mcp.json` that starts the bridge
through `tools/wiz-mcp/wiz-mcp.sh`. The launcher picks the `wiz` executable so
that a worktree without its own build still works, and logs its choice to
stderr: `$WIZ_BIN`, then `./.lake/build/bin/wiz`, then `tower which wiz` (the
tower toolchain for the directory), then `wiz` on `PATH`. Claude Code lists a
project server as "pending approval" until you approve it once in `claude`
(or `/mcp`). The tools are then `mcp__wiz__check`, `mcp__wiz__goals`, and so
on. A one-shot check that needs no approval:

```sh
claude -p 'call mcp__wiz__version' --mcp-config .mcp.json --strict-mcp-config \
  --allowedTools mcp__wiz__version
```

## Tools

| MCP tool (OpenCode name) | arguments | backend |
| --- | --- | --- |
| `version` (`wiz_version`) | – | `wiz --version` |
| `check` (`wiz_check`) | `path`, `source?`, `text?` | `wiz check PATH` (or the daemon with `source: "lsp"`); structured diagnostics; the workhorse |
| `parse` (`wiz_parse`) | `path` | `wiz parse PATH` |
| `fmt` (`wiz_fmt`) | `path`, `check?`, `width?` | `wiz fmt PATH [--check] [--width N]` |
| `build` (`wiz_build`) | `path`, `out`, `lib?` | `wiz build PATH -o OUT [--lib]`; **only with `--allow-build`** |
| `diagnostics` (`wiz_diagnostics`) | `path`, `text?` | `didOpen` → `publishDiagnostics` → `didClose` |
| `hover` (`wiz_hover`) | `path`, `text?`, `line`, `character` | `textDocument/hover` |
| `goals` (`wiz_goals`) | `path`, `text?`, `line`, `character` | `wiz/interactiveGoals` |

`text` sends a buffer that is not saved to disk. When it is omitted the file is
read. Positions are 0-based; Wiz's LSP treats `character` as a Unicode code
point (its own clients convert from their wire encoding).

Use `check` after editing, `fmt --check` before committing, and
`diagnostics`/`hover`/`goals` when the language server's view is needed. There
is no `verify` or `lint` command in Wiz, so there are no such tools.

`check`, `parse`, `fmt` and the LSP tools only need the `wiz` executable (its
module roots are found beside the binary). `build` additionally needs the host
C toolchain (`cc`, GMP) on the environment the bridge inherits; start the MCP
client from the dev shell (`nix develop`) or an equivalent shell if you use it.
The bridge does not invent compiler flags.

## Safety

The default server is read-only: it reads files and writes nothing but the
content-addressed `wiz` cache. Every tool carries MCP `annotations`
(`readOnlyHint`, `destructiveHint`, `idempotentHint`, `openWorldHint: false`),
which clients use for their permission prompts.

* **Paths are confined.** A `path` is resolved against the workspace and then
  through every symlink; the real path must lie inside the workspace, the
  toolchain's library (`PREFIX/share/wiz` of a release or Nix toolchain, or
  `CHECKOUT/lib` of a checkout build) or an `--allow-root` directory. An
  absolute path elsewhere, a `..` escape and a symlink out of the workspace are
  refused with `error.kind = "path_denied"` before `wiz` runs or the daemon
  starts.
* **`build` is gated.** It writes a file and runs the host C toolchain, so it is
  not listed unless the server is started with `--allow-build`; a call without
  it returns `not_enabled`. Its `out` must resolve inside the workspace (never
  the toolchain or an `--allow-root` directory) and may not be a symlink.
* **Children get an allowlisted environment.** `wiz` and the daemon see `PATH`,
  `HOME`, the user and locale variables, temp and cache directories, the C
  compiler variables (`CC`, `CFLAGS`, `CPATH`, `LD_LIBRARY_PATH`, …) and every
  `WIZ_*`, `NIX_*` and `LC_*` variable, plus `--pass-env` names. A name that
  looks like a credential (`TOKEN`, `SECRET`, `PASSW`, `AUTH`, `API_KEY`,
  `PRIVATE`, `CREDENTIAL`, `COOKIE`, `SESSION`) never passes, even when named
  with `--pass-env`; that covers `GH_TOKEN`, `CACHIX_AUTH_TOKEN`,
  `WIZ_NTFY_TOKEN_FILE` and `SSH_AUTH_SOCK`.
* **No network, no socket.** No tool takes a URL, and the daemon speaks LSP
  on its own stdin/stdout: it listens on nothing, so no other process can
  reach it. (Until 2026-11-17 it was `wiz lsp --ws 127.0.0.1:0`, whose port had
  no authentication; `wiz lsp --infoview SOCK` was not an option because its
  clients may only pull, not open documents.)

What the bridge does not control: the files `wiz` itself opens while checking
(imports from its module roots, `import_c` headers) and the processes it starts
(an SMT solver, `cc -E`). The check happens before the call, so a symlink
swapped in between the check and the open is not caught; the workspace is the
agent's own, so this is a guard against mistakes, not a sandbox.

## Output shape

Every tool returns one compact JSON object with the same keys, success or
failure:

```json
{"ok":true,"tool":"check","path":"/w/probe.wiz","exit":1,"stdout":"","stderr":"probe.wiz:1:7: error: …","result":null,"truncated":false,"error":null}
```

* `ok` is true when the tool ran and `wiz` exited 0 (the LSP tools have no exit
  status). `exit` carries the command's status, so a `check` with type errors is
  `ok: false, exit: 1, error: null`, with the messages in `stdout`/`stderr`.
  `error` is non-null only for a bridge-level failure.
* `stdout` and `stderr` are clipped at 64 KiB each, and a JSON `result` at
  64 KiB. `truncated: true` and an explicit `… [truncated: N characters
  omitted]` marker say so. A clipped `result` becomes
  `{"_truncated": true, "bytes": N, "preview": "…"}`.
* MCP `isError` is true exactly when `ok` is false. The text content and
  `structuredContent` carry the same object.
* `error.kind` is one of `invalid_args`, `path_denied`, `not_enabled`,
  `wiz_not_found`, `io_error`, `timeout`, `lsp_startup`, `lsp_closed`,
  `lsp_error`, `internal`.

### `check`: structured diagnostics

`check` returns the raw `stdout`/`stderr` as before and, in `result`, every
message as data:

```json
{"source":"cli","counts":{"error":1,"warning":0,"info":1},"unparsed":[],
 "diagnostics":[{"file":"/w/a.wiz","line":4,"column":16,
   "range":{"start":{"line":3,"character":15},"end":{"line":3,"character":15}},
   "severity":"error","code":null,"message":"type mismatch\n  expected: Nat\n  inferred: Bool"}]}
```

* `line`/`column` are 1-based, as Wiz prints them; `range` is 0-based, as in
  LSP (the same numbers the `diagnostics`, `hover` and `goals` tools take).
  Columns count Unicode code points.
* `source: "cli"` (the default) parses `wiz check`'s output: a message is
  `PATH:LINE:COLUMN: SEVERITY: TEXT` and continues on the following lines (a
  type mismatch's expected/inferred lines, an import's indented error list).
  The CLI prints neither the end of a range (`end` equals `start`) nor the
  error code (`code` is null). Lines that belong to no message (another file's,
  `region cache:` statistics, a crash) go to `unparsed`.
* `source: "lsp"` asks this worktree's daemon instead and accepts unsaved
  `text`. It has the same messages and positions, plus each range's end and the
  stable error `code` (`type-mismatch`, `parse-error`, `unknown-identifier`, …;
  see `docs/error-codes.md`). `exit` is null and `ok` is "no errors".
* Messages are sorted by position. `counts` has every severity, zeros included.

No `wiz` in the workspace is a normal error envelope, not a broken server:
`initialize` still succeeds, the tools return `wiz_not_found` with the path it
looked for and the `lake build wiz` hint, and the bridge stays alive (OpenCode
does not restart a crashed local MCP server).

## One daemon per worktree

`diagnostics`, `hover` and `goals` share **one** lazily started process:

```sh
wiz lsp          # LSP on its stdin/stdout, Content-Length framing; no socket
```

* It starts on the first LSP-backed call, not at `initialize`, and is killed
  after `--idle` seconds without one (default **600**).
* Every call has a deadline (`--timeout`, default **300 s**), on reads *and*
  writes (a daemon that stops reading its input cannot block a call). On expiry the
  daemon is killed and the call returns `error.kind = "timeout"`; the next call
  starts a fresh daemon. This is the mitigation for `wiz lsp` having no request
  timeout of its own.
* On `shutdown`/`exit`, EOF, or SIGTERM/SIGINT/SIGHUP the bridge closes the
  daemon's stdin and terminates it (SIGTERM, then SIGKILL after 5 s). On
  Linux the daemon also gets `PR_SET_PDEATHSIG`, so even a SIGKILLed bridge
  cannot leave an orphan.
* Calls are handled one at a time. That is the queue bound: a burst of tool
  calls cannot start a herd of `wiz` processes, and the daemon (single event
  loop) is never asked to serve two callers.
* The daemon runs with the workspace as its cwd and with this worktree's
  `./.lake/build/bin/wiz` by default.

The daemon is **never shared between worktrees**, and there is deliberately no
`WIZ_LSP_URL` escape hatch:

* Its module roots and `lib/` are fixed when it starts. Two worktrees on
  different branches would silently check against one branch's library.
* Documents are keyed by URI only. Two worktrees opening the same path (or
  `grail.local.wiz` variants) would collide.
* It has one event loop, so one caller's large edit blocks every other caller.

One daemon per bridge, one bridge per workspace is the correctness boundary.
(If you start two bridges in the same worktree — two clients — you get two
daemons. They are isolated and safe, just redundant; the normal OpenCode shape
is one bridge per location.)

## Memory

These are measured (`/proc/<pid>/status`) on a developer machine with one
small document; a busy host will vary. The study's table has the 30-worktree
numbers.

| process | RSS |
| --- | --- |
| bridge, no daemon | ~27 MB |
| bridge with a daemon | ~28 MB |
| `wiz lsp` daemon, just started | ~70 MB |
| daemon with one small document (`import Prelude`) | ~90–113 MB |
| daemon with a handful of documents | ~120 MB |
| daemon with 30 documents | ~134 MB |

Re-measured 2026-11-15 on this tree (bridge on Python 3.14): nine smoke runs
put a daemon with one small document at 90–113 MB, and a direct
`wiz lsp --ws` at 93–96 MB with the document open and 69–72 MB just started;
on stdio (2026-11-17) the smoke test's daemon was 117 MB, the same range.
The study's 87–117 MB daemon range still holds; its 17 MB idle-bridge figure
does not reproduce here, so plan with 27 MB.

Plan on **~0.5 GB per active location** for capacity (bridge + daemon + a
`wiz check` running during a call, with headroom); the steady state is much
smaller. The study's **~0.5 GB figure is 30 idle bridges**, not one daemon —
do not read it as 0.5 GB per daemon. At 27 MB per bridge, 30 idle worktrees
are ~0.8 GB; with idle unload they cost that much of bridges plus 0–8 daemons
(0–1.6 GB), not 30 daemons.

## Tests

The unit tests need no `wiz` (they use tiny shell scripts, OS pipes and a
fake stdio language server):

```sh
python3 -m unittest discover -s tools/wiz-mcp/tests -p 'test_*.py' -v
```

The end-to-end smoke test needs a built toolchain. It starts the bridge, runs
`diagnostics` then `hover` (so the real daemon starts), records the daemon's
RSS, checks that it holds no socket, shuts down, and checks that the daemon is
gone:

```sh
python3 tools/wiz-mcp/tests/smoke.py --wiz ./.lake/build/bin/wiz
```

Exit status 0 is a pass, 1 a failure, and **2 a clean skip** because no `wiz`
was built. A skipped run is not a passing run.

Both at once, with the skip reported as a skip:

```sh
sh tools/wiz-mcp/run-tests.sh
```

## Options

```text
--workspace DIR   tool paths are relative to DIR (default: cwd, set by the client)
--wiz PATH        wiz executable; relative paths resolve against the workspace
                  (default: ./.lake/build/bin/wiz)
--cache DIR       --cache DIR for wiz calls and the daemon
                  (default: wiz's own ~/.cache/wiz)
--idle SECONDS    unload an idle daemon; 0 keeps it (default: 600)
--timeout SECONDS per-call deadline; also the daemon's startup budget (default: 300)
--allow-build     list and allow `build` (off by default)
--allow-root DIR  another directory tools may read (repeatable; never written)
--pass-env NAME   pass another variable to wiz (repeatable; credential-like names
                  are still dropped)
```

Environment: `WIZ_BIN` is the default for `--wiz`; `WIZ_MCP_CACHE` for `--cache`.
All logs go to stderr; stdout is the MCP transport.

## Troubleshooting

* **`wiz_not_found`** — the workspace has no `./.lake/build/bin/wiz`. Run
  `lake build wiz` there, or pass `--wiz` explicitly. A bare name is looked up
  on `PATH`; a path with a slash is relative to the workspace.
* **`lsp_startup`** — the daemon exited before answering `initialize`. The
  error includes its exit status and the tail of its stderr. Check that
  `wiz lsp` starts by hand in that worktree (it waits on stdin).
* **`path_denied`** — the path resolves outside the workspace and the
  toolchain library. Use a path inside the worktree, or start the server with
  `--allow-root DIR` for a read-only extra directory.
* **`not_enabled`** — `build` needs `--allow-build` on the server command.
* **`build` cannot find `cc` flags** — they come from the environment; a
  variable outside the allowlist needs `--pass-env NAME`.
* **First LSP call is slow** — the daemon elaborates imported modules. With a
  cold `~/.cache/wiz` this can take several seconds; later calls are fast.
* **A daemon lingers after a crashed test** — the bridge kills it on exit and
  `PR_SET_PDEATHSIG` covers a killed bridge. If an old one from a killed
  process group is still around, kill only that PID or a pattern scoped to your
  own worktree; never kill another agent's processes.
* **Diagnostics are stale after editing an included file** — `wiz lsp` has no
  file watcher and no pull-diagnostics request. Call `diagnostics` again with
  the buffer text, or edit and re-send the including document.

## Limitations

* No LSP pull diagnostics, no `workspace/didChangeWatchedFiles`, no
  `textDocument/formatting`: the bridge computes diagnostics on the text it is
  given and shells out to `wiz fmt`.
* Calls are sequential; MCP cancellation notifications cannot interrupt a call
  in flight. The per-call deadline is the bound.
* No resources or prompts; only the tools above (seven, eight with `--allow-build`).
* The daemon's cache is content-addressed and safe to share, but cold worktrees
  duplicate elaboration work. A warm `~/.cache/wiz` avoids most of it.
