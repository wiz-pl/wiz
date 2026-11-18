# scry-mcp: Scry for MCP clients, read-only

A stdio MCP server for [Scry](../../scry/README.md): it does taint analysis of C files and
projects, queries fact stores and reads the findings database. It is separate from
`tools/wiz-mcp` (its own process and its own `.mcp.json` entry, `scry`). It reuses
that bridge's transport, its path confinement and its environment filter, so
`tools/wiz-mcp/wiz_mcp.py` must sit beside it, as it does in a checkout.

## Quick start

`.mcp.json` registers it for Claude Code as `scry`:
`sh tools/scry-mcp/scry-mcp.sh --timeout 300`. It needs a built `scry` (`grail
build` in `scry/`). The first of these that exists is used:

1. `--scry PATH`
2. `$SCRY_BIN`
3. `./scry/.grail/bin/scry`
4. `scry` on `PATH`

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
  a range. `diff: "all"` treats every line as changed.
* `scry_findings` reads `scry-workflow/findings.json` unless `db` names another
  file. A missing database lists as empty.

## Safety

Every tool is annotated `readOnlyHint: true`, `destructiveHint: false` and
`openWorldHint: false`.

* **Not offered.** These commands are not offered, because they run code or
  write files: `scry dynamic` and `findings repro` (both compile and run
  code), `findings scan`, `triage` and `verify` (all three write the database),
  `bench`, `repl`, `project --facts`/`--cache`/`--cc`, and `cst`.
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
* **The compile database is checked first.** Before `scry_project` runs, each
  entry's `directory`, `file`, and each `-I`, `-isystem`, `-include`,
  `-iquote` and `-idirafter` path must be inside those roots. System include
  directories (`/usr/include`, `/usr/local/include`, `/nix/store`) are also
  allowed.
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
  `show` of such a finding is `path_denied`.
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

## Options

```text
--workspace DIR   paths are relative to DIR (default: cwd)
--scry PATH       the scry executable
--rules FILE      the default rule pack
--timeout SECS    per-call deadline, also the cap on Scry's own --timeout (default: 300)
--allow-root DIR  another directory tools may read (repeatable; never written)
--pass-env NAME   pass another environment variable (credential-like names are still dropped)
```

## Tests

```sh
python3 -m unittest discover -s tools/scry-mcp/tests -p 'test_*.py'   # a fake scry; no build needed
python3 tools/scry-mcp/tests/smoke.py --scry scry/.grail/bin/scry      # a real scry build
```

The unit tests use a fake `scry` that records its argv, working directory and
environment. They check:

* confinement of inputs and outputs, including symlinks;
* compile-database checks;
* that the temporary directory is private and removed on exit;
* that secrets are filtered;
* `diff` validation, and that `git diff` runs in the workspace;
* the limits, and the retention of runs;
* that the findings database is never written.

The `tools` workflow runs them on every change under `tools/`.
