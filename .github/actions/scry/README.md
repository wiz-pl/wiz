# scry — a GitHub Action for changed C

A composite action that runs the [scry](../../../scry) C taint analyser on the files a
pull request changes, uploads SARIF 2.1.0 to code scanning, and writes a job summary of
**introduced** and **suppressed** results.

## One-line use

With `actions/checkout` (`fetch-depth: 0`) and `security-events: write` already in the
job, the whole integration is:

```yaml
- uses: wiz-pl/wiz/.github/actions/scry@master
```

A complete consuming workflow is [`examples/scry-workflow.yml`](../../../examples/scry-workflow.yml).
Pin both `@master` refs to commit SHAs in a real repository.

## What the repository must set

* **Permissions** — `security-events: write` for the SARIF upload, plus `contents: read`.
  A fork pull request's token is read-only; gate the upload on the fork status (the
  example does) or set `upload-sarif: "false"`.
* **Checkout** — `fetch-depth: 0`, so the PR's base branch exists as
  `origin/<base>` for `diff: auto`. Without it the action uses the merge commit's first
  parent when there is one, and otherwise warns and analyses the whole tree.
* **A pinned revision** — `scry-version` (a wiz branch, tag or commit) and the action
  ref. The action builds scry from that revision and caches the binary; a moving branch
  reuses a cache entry that no longer matches its content.
* **A rule pack** — empty `rules` uses `lib/Scry/rules/default.scry` from the scry source
  tree, which the build path always has. With a prebuilt `scry-path` and no
  `scry-source`, pass `rules:` or scry's own default lookup is used.
* **GitHub Advanced Security** — required for code scanning on private repositories.
  Public repositories get it by default.

The C sources are analysed one translation unit at a time. `paths` is a
whitespace-separated list of files, directories or git pathspecs; only `.c` files are
analysed, so a change to a header alone reports "no C files" instead of a clean result.

## Inputs

| input | default | meaning |
|---|---|---|
| `paths` | `.` | files/directories/pathspecs to scan (whitespace-separated) |
| `diff` | `auto` | a git revision, `auto` (the PR base), or `all` (no filter) |
| `rules` | — | a `.scry` pack; empty uses the source tree's default pack |
| `fail-on-finding` | `false` | fail after the upload when the diff introduces a result |
| `sarif` | `scry.sarif` | merged SARIF path, relative to the repository root |
| `upload-sarif` | `true` | upload to code scanning |
| `category` | `scry` | the code-scanning category |
| `allow-errors` | `false` | analyse recovered trees with ERROR/MISSING nodes |
| `extra-args` | — | extra `scry taint` arguments (e.g. `--diff-context 3`) |
| `scry-path` | — | a prebuilt executable; skips the build |
| `scry-source` | — | a wiz checkout (contains `scry/grail.wiz`) |
| `scry-repo` | `wiz-pl/wiz` | where to clone scry from when it must be built |
| `scry-version` | `master` | the wiz revision to build from |
| `scry-cache` | `true` | cache the built binary by source content |
| `working-directory` | `.` | repository directory to run git and scry in |

Outputs: `sarif` (absolute path), `shown` (findings on changed lines), `suppressed`
(findings on unchanged lines), `gate` (findings plus lowering/memory warnings on changed
lines — the count `fail-on-finding` uses).

## What it runs

For every changed `.c` file:

```sh
scry taint FILE.c --diff <base> --rules <pack> --sarif <per-file> --json
```

`--diff` is scry's diff-aware mode: a result is shown when its sink line, or a path step,
is on a line the diff adds. The SARIF is written **complete** — suppressed results stay
in it with `baselineState: unchanged` — so the upload cannot claim an untouched finding
was fixed. `merge.py` unions the per-file results into one SARIF run and reports the
counts. The `fail-on-finding` gate runs *after* the upload, so a failing run still
publishes its report.

## Build and cache

A consuming repository normally has no wiz checkout. The action clones `scry-repo` at
`scry-version`, installs Nix, substitutes the `wiz`/`grail` build from the public
`badlydrawnwizards` Cachix cache, then runs `grail build scry`. The binary lands in
`~/.cache/scry/bin/scry` and is cached with a key built from the OS, architecture,
`scry-version` and a content hash of the scry sources. The first run on a new revision
is expensive; later pull requests restore the cache.

If the repository already builds scry (the dogfood workflow here does), pass
`scry-path` and no Nix or download is needed. If it vendors a wiz checkout, pass
`scry-source`.

## The honest limit

This action reports the findings a change **introduces**. It does not report absence:

* pre-existing findings are suppressed with a count and kept in the SARIF, so a green
  run means "nothing new landed on a changed line", not "this code is clean";
* a finding whose sink and path steps are all on unchanged lines is suppressed even when
  the change is what made it reachable — `--diff` is a line mapping, not a taint diff;
* an insertion that moves a vulnerable line without editing it does not mark the line as
  changed;
* scry is a may-analysis over a C subset (tree-sitter-c, no C++); lowering and external
  calls it cannot model are reported as warnings, not silently assumed safe;
* each `.c` file is analysed on its own. Cross-translation-unit findings need
  `scry project`, which this action does not run.

## Failure behaviour

Every analysis error is fatal (no partial SARIF is uploaded). The SARIF is validated
before the upload step: an empty, truncated or non-SARIF file fails the action instead
of silently closing every existing alert in the category. When the diff contains no C
files, the action writes an empty SARIF for inspection, reports `skip-upload=true`, and
does not upload it for the same reason.

See [`DRY-RUN.md`](DRY-RUN.md) for the local command-shape and tampered-SARIF checks.
