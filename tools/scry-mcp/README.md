# scry-mcp: Scry for MCP clients

A stdio MCP server for [Scry](../../scry/README.md): it does taint analysis of C files and
projects, queries fact stores and reads the findings database. By default it is
read-only. Dynamic analysis, repro/verify and triage exist only behind flags
(see [Runners](#runners-opt-in)). It is separate from
`tools/wiz-mcp` (its own process and its own `.mcp.json` entry, `scry`). It reuses
that bridge's transport, its path confinement and its environment filter, so
`tools/wiz-mcp/wiz_mcp.py` must sit beside it, as it does in a checkout.

## Quick start

`.mcp.json` registers it for Claude Code as `scry`:
`sh tools/scry-mcp/scry-mcp.sh --timeout 300`. It needs a built `scry` (`grail
build` in `scry/`) that lives outside the workspace, or an explicit `--scry` /
`$SCRY_BIN`. The first of these that exists is used:

1. `--scry PATH`
2. `$SCRY_BIN`
3. `scry` on `PATH`

The workspace's own build (`scry/.grail/bin/scry`) is **not** found
automatically: the workspace is the tree under review, and a server whose first
tool call executes a program from that tree would run repository-controlled
code. Point `--scry` or `$SCRY_BIN` at it explicitly if that is what you want.
That is the one intentional trust decision in the server: everything else it
starts is `cc` (the host preprocessor), `git diff`, or `uname`.

The default rule pack is `--rules`, else `./lib/Scry/rules/default.scry`, else
the `default.scry` in the library of the `wiz` the workspace would use.

## Tools

| tool | arguments | runs |
| --- | --- | --- |
| `scry_version` | – | `scry --version` |
| `scry_taint` | `path`, `rules?`, `diff?`, `diff_context?`, `allow_errors?`, `timeout?`, `max_nodes?` | `scry taint FILE --json --sarif TMP` |
| `scry_project` | `path` (a directory), `compdb?`, `rules?`, `allow_errors?`, `skip_broken?` | `scry project DIR --compdb DB --taint --json --sarif TMP` |
| `scry_facts` | `path` | `scry facts STORE` |
| `scry_query` | `path`, one of `kind`, `edge`, `edge_src` or `rel` | `scry query STORE --kind …` |
| `scry_explain` | `path`, `node` | `scry explain STORE NODE` |
| `scry_findings` | `action` (`list` or `show`), `id?`, `state?`, `db?` | `scry findings list` or `show ID`, with `--db … --json` |

Results:

* `scry_taint` and `scry_project` return Scry's JSON report as `result`:
  * `findings`, each with `rule`, `severity`, `message`, `location` and the
    source-to-sink `path`;
  * `boundary` and `memory` notes, `counts`, and `truncated` with the `budget`.

  `result._run` names the run's resources: `sarif_uri` (`scry://runs/{id}/sarif`)
  and `json_uri`. `withheld` counts the findings dropped because they point
  outside the readable roots.
* `diff: "BASE"` keeps only the findings on lines changed since `BASE`. The
  others are counted under `result.diff.findings.suppressed`. The bridge runs
  `git diff --no-ext-diff --no-textconv -U0 BASE -- FILE` in the workspace and
  passes the saved diff to Scry. `BASE` must be a ref or commit, not an option or
  a range. Git runs with every config source pinned (`GIT_CONFIG_NOSYSTEM`,
  `GIT_CONFIG_GLOBAL=/dev/null`), `core.fsmonitor=false`,
  `core.hooksPath=/dev/null`, `protocol.allow=never` and `GIT_NO_LAZY_FETCH=1`,
  so the workspace's own `.git/config` cannot run a command or fetch objects.
  `diff: "all"` treats every line as changed.
* `scry_findings` reads `scry-workflow/findings.json` unless `db` names another
  file. A missing database lists as empty. Before `show`, the bridge parses the
  database itself (refusing one over 64 MiB or without the
  `scry-workflow-store/1` schema) and hands Scry a store containing only that
  record. If the record's `artifacts` + `static`/`dynamic`/`verify`/`repro.json`
  would resolve outside the readable roots, `artifacts` is pointed at an empty
  directory in the private run dir, so Scry reads nothing outside and the
  evidence payloads come back `null`. Evidence inside the roots is returned.

## Runners (opt-in)

| tool | flag | runs |
| --- | --- | --- |
| `scry_dynamic` | `--allow-scry-dynamic` | `scry dynamic FILE.c --json --sarif TMP --work-dir TMP --timeout N [--no-coverage]` under `heavy` |
| `scry_repro` | `--allow-scry-dynamic` | `scry findings repro ID --db DB --sanitize S --timeout N --json [--input F] [--witness F]` under `heavy` |
| `scry_verify` | `--allow-scry-dynamic` | `scry findings verify ID --db DB --json` under `heavy` |
| `scry_triage` | `--allow-scry-triage` | `scry findings triage ID --state S --reason R --by scry-mcp --db DB` under `light` |
| `job_status`, `job_cancel` | `--allow-scry-dynamic` | follow or stop a job |

They share wiz-mcp's runner machinery (`tools/wiz-mcp/wiz_runners.py`; see
its README, "Runners"):

* **Scheduling.** `heavy --mem MEM timeout -k 30 T` runs the job, with a
  declared `mem` (default 4G, at most `--max-mem`) and `timeout` (default 600
  s). Heavy's status is read first: a busy heavy is `heavy_busy` unless
  `queue: true`, and a measurement window is `measurement_window`. Calls return
  a job after `wait` seconds, and there is one job at a time.
* **The sandbox.** `bwrap` gives the job no network, a read-only root and
  workspace, a private `/tmp`, and a hidden home directory. Only the run's own
  temporary directory is writable, plus the findings database's directory for
  repro, verify and triage. `run_timeout` (default 10 s, at most 120) is the
  analysed program's own limit inside Scry.
* **No caller-chosen commands.** `--cc`, `--harness` and `--env` are never
  passed, and those arguments are refused as unknown. `input` and `witness`
  must be files in the readable roots.
* **The findings database must be a real file in the workspace.** It may not
  be in the toolchain, an `--allow-root` directory or behind a symlink. A
  missing database is `not_found`; `scry findings scan` is still not offered.
* **Outputs are confined.** `scry_dynamic` reports go through the same
  confinement as `scry_taint`, and the SARIF is kept as a run resource.
  A repro or verify record whose `source` is outside the roots is withheld.

A stored repro may name a harness that someone recorded earlier with the CLI.
`verify` replays it inside the same sandbox; the server never accepts one.

## Safety

Every tool except the runners is annotated `readOnlyHint: true`,
`destructiveHint: false` and `openWorldHint: false`. The runners are
`readOnlyHint: false`.

* **Not offered.** These commands are not offered, because they write files
  or run code outside the runners' sandbox: `findings scan`, `bench`, `repl`,
  `project --facts`/`--cache`/`--cc`, and `cst`. `scry dynamic`,
  `findings repro`, `verify` and `triage` exist only as the runners above.
* **Temporary-directory output only.** Each run gets a fresh directory inside
  the server's private (0700) temporary directory. That directory is the
  child's working directory, `HOME`, `XDG_CACHE_HOME` and `TMPDIR`, so anything
  Scry writes lands there.
  * The SARIF and JSON reports of the last 20 runs are kept there as
    resources.
  * The whole directory is removed when the server exits.
  * Nothing is written to the workspace. The smoke test checks that `git status`
    is unchanged.
* **Paths are confined.** Every `path`, `rules`, `compdb` and `db` must be
  inside the workspace, the rule pack's directory, or an `--allow-root DIR`.
  Real paths are compared, so an absolute path, `..` or a symlink out is
  `path_denied`.
* **The compile database is checked first.** The bridge parses the database once,
  refuses it over 64 MiB or 100 000 entries, and hands Scry a normalised copy
  (`directory`, `file`, `arguments`) in the run directory, so Scry never
  re-parses the original `command` or falls back to it when `arguments` is
  empty. Each entry's `directory`, `file`, and each `-I`, `-isystem`,
  `-include`, `-iquote` and `-idirafter` path must be inside those roots, and a
  `directory`/`file`/argument with a NUL or other control character is
  `invalid_args`. System include directories (`/usr/include`,
  `/usr/local/include`, `/nix/store`) are also allowed, by containment, not by
  string prefix.
* **The database's flags are on an allowlist.** Only the preprocessing flags
  Scry needs reach `cc -E`: `-I`, `-isystem`, `-iquote`, `-idirafter`,
  `-include`, `-D`, `-U` and `-std=`/`--std=`. The compile driver's own `-c`,
  `-o` and `-M…` structure is consumed (never forwarded, so `-o` cannot write a
  file and `-M` cannot replace the preprocessed text). **Every other word is
  refused by name**, not stripped: `-B<dir>` (with a committed `cc1`),
  `-fplugin=`, `-specs=`, `-wrapper`, `@file`, `-Xclang`, `-cc1`, `-Xlinker`,
  `-imacros`, `--sysroot` and any other `-f…`/`-m…` option could change which
  program runs or what it reads. The refusal is `invalid_args` and names the
  flag; Scry's own parser enforces the same list
  (`scry/src/Scry/Project.wiz`). `cc -E -ffreestanding` is the one host program
  the server can start besides `scry` and `git diff`.
* **Outputs are confined.** Findings, SARIF results and findings-database
  records whose file is outside the roots are withheld: counted, never named.
  `show` of such a finding is `path_denied`. Within a report, `skipped[].file`
  and `skipped[].reason` (cc's stderr, which names headers), `cache.dir`, and in
  a `show` bundle `environment.cwd`, `environment.uname` and
  `environment.tool.binary` are replaced with `(withheld)`.
* **Reports are capped.** A resource (`scry://runs/{id}/…`) over 64 MiB is
  refused instead of being read into memory.
* **The environment is filtered** as in wiz-mcp: an allowlist, and no name that
  looks like a credential (`TOKEN`, `SECRET`, `PASSW`, `AUTH`, `API_KEY`, …),
  even with `--pass-env`.

Error kinds:

* `invalid_args`
* `path_denied`
* `scry_not_found`
* `scry_error` (Scry failed; its first stderr line is the message, and `stderr`
  has the rest)
* `not_found`
* `timeout` (the process group is killed)
* `io_error`
* `internal`
* runners only: `not_enabled`, `heavy_busy`, `measurement_window`, `busy` (a
  job is already running), `scheduler_not_found`, `scheduler_error` and
  `sandbox_unavailable`

## Options

```text
--workspace DIR   paths are relative to DIR (default: cwd)
--scry PATH       the scry executable
--rules FILE      the default rule pack
--timeout SECS    per-call deadline, also the cap on Scry's own --timeout (default: 300)
--allow-root DIR  another directory tools may read (repeatable; never written)
--pass-env NAME   pass another environment variable (credential-like names are still dropped)
--allow-scry-dynamic  list and allow scry_dynamic, scry_repro, scry_verify (heavy, sandboxed)
--allow-scry-triage   list and allow scry_triage (writes the findings database; light, sandboxed)
--heavy PATH, --light PATH, --bwrap PATH, --max-mem SIZE, --max-runtime SECS
                  as in wiz-mcp
```

## Tests

```sh
python3 -m unittest discover -s tools/scry-mcp/tests -p 'test_*.py'   # a fake scry; no build needed
python3 tools/scry-mcp/tests/smoke.py --scry scry/.grail/bin/scry      # a real scry build
```

The unit tests use a fake `scry` that records its argv, working directory and
environment. They check:

* confinement of inputs and outputs, including symlinks;
* compile-database checks, including the `arguments`/`command` parser and the
  normalised copy Scry is handed;
* that the temporary directory is private and removed on exit;
* that secrets are filtered;
* `diff` validation, that `git diff` runs in the workspace, and that a
  workspace `.git/config` cannot run a command through `core.fsmonitor` or a
  hook;
* that a `scry` planted in the workspace is never executed;
* the limits, the retention of runs, and the size caps;
* that the findings database is never written, and that its records, a `show`
  bundle's host facts and a project report's skipped reasons are redacted;
* the runners, with stand-in `heavy`/`light`/`bwrap` scripts: the gating, the
  argument vectors (no `--cc`/`--harness`/`--env`), the sandbox's writable
  directories, the database checks, confinement of dynamic reports, and
  refusal when heavy is busy.

The `tools` workflow runs them on every change under `tools/`.
