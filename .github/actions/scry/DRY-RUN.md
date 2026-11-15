# Local dry-run transcript

What ran locally on 2026-11-15, against a scry binary built from the merged scry stack
(`$SCRY`, `$RULES` below). Nothing was pushed and no GitHub upload was attempted.

## Static checks

```console
$ bash -n .github/actions/scry/resolve.sh \
      .github/actions/scry/build.sh .github/actions/scry/scan.sh
$ python3 -m py_compile .github/actions/scry/merge.py \
      .github/actions/scry/validate-sarif.py
$ python3 - <<'PY'
import yaml
for p in ['.github/actions/scry/action.yml',
          '.github/workflows/scry.yml', 'examples/scry-workflow.yml']:
    yaml.safe_load(open(p)); print(p, 'ok')
PY
.github/actions/scry/action.yml ok
.github/workflows/scry.yml ok
examples/scry-workflow.yml ok
```

## The fixture

Two commits; the second is unrelated, and the vulnerable line is a working-tree change,
so `--diff HEAD` is exactly the introduced finding:

```console
$ mkdir scry-head && cd scry-head && git init -q -b main
$ printf '#include <stdlib.h>\nint main(void){ return 0; }\n' > src/app.c   # after mkdir src
$ git add -A && git commit -qm 'base: clean'
$ printf '#include <stdlib.h>\nchar *run(char *arg){ return arg; }\n' > src/run.c
$ git add -A && git commit -qm 'second commit: helper'
$ printf '#include <stdlib.h>\n#include "run.h"\nint main(void){ char *c = getenv("C"); system(run(c)); return 0; }\n' > src/app.c
$ git log --oneline
01dff74 second commit: helper
6e08744 base: clean
$ git status --short
 M src/app.c
```

## The command shape

```console
$ $SCRY taint src/app.c --diff HEAD --rules "$RULES" --sarif raw.sarif
taint: src/app.c (6 rules)
parse: ok
diff: --diff HEAD; 1 hunk(s) in 1 file(s), 2 added line(s), 2 line(s) in scope, context 0
src/app.c:3:40: error: command-injection: Attacker-controlled data reaches a command interpreter [main] (checked)
  path: source@main:1 -> flow@main:2 -> flow@main:3 -> sink@main:4
  diff: sink line 3
src/app.c:3:40: warning: scry/lowering/boundary: call to undeclared function system (external) [main] (unchecked) [diff: sink line 3]
...
diff: 1 finding(s) shown, 0 suppressed on unchanged lines
diff: 5 boundary warning(s) shown, 0 suppressed on unchanged lines
diff: 1 memory warning(s) shown, 0 suppressed on unchanged lines
taint: 1 finding(s), 1 checked, 0 unchecked, 5 boundary warning(s), 1 memory warning(s)
wrote SARIF 2.1.0: raw.sarif (1 result(s), 5 boundary; diff: 1 shown, 0 unchanged)
```

## The action's scan step

`resolve.sh` is given `INPUT_SCRY_PATH=$SCRY` and `INPUT_SCRY_SOURCE=<wiz checkout>`;
`scan.sh` is given `INPUT_DIFF=HEAD INPUT_PATHS=src/app.c`.

```console
$ bash .github/actions/scry/scan.sh
scry: analysing 1 file(s) against HEAD
  wrote SARIF 2.1.0: /tmp/tmp.ePBVS4JwVi/0.sarif (1 result(s), 5 boundary; diff: 1 shown, 0 unchanged)
scry: SARIF ok (6502 bytes, 1 run(s), 7 result(s))
scry: 1 finding(s) on changed lines, 0 on unchanged lines, 7 SARIF result(s) in scry-diff-head.sarif
## Scry

1 C file(s) analysed, diff `HEAD`.

| | introduced (shown) | unchanged (suppressed) | no source line |
|---|---:|---:|---:|
| findings | 1 | 0 | 0 |
| lowering warnings | 5 | 0 | 0 |
| memory warnings | 1 | 0 | 0 |

**7 result(s) on changed lines**; 0 suppressed as pre-existing.

<details><summary>Files</summary>

| file | findings | warnings | suppressed |
|---|---:|---:|---:|
| `src/app.c` | 1 | 6 | 0 |

</details>

> scry reports **introduced** results: findings whose sink, or a path step, is on a line this diff changes. No introduced finding is not proof the analysed code has none: the suppressed count above is the rest of this run's results.

> The analysis is C only and one translation unit at a time; a changed header alone is not analysed.
```

`GITHUB_OUTPUT` received `shown=1`, `suppressed=0`, `gate=7`, `skip-upload=false`.

The gate is 7, not 1: `fail-on-finding` follows scry's own definition and counts the
lowering and memory warnings on changed lines too. The summary keeps them in separate
rows so the finding count is not hidden by the warnings.

## Pre-existing findings are suppressed, and stay in the SARIF

A second fixture has a vulnerable line committed, then a comment-only commit. Comparing
that commit with `HEAD~1` (its only change is a comment):

```console
$ bash .github/actions/scry/scan.sh          # INPUT_DIFF=HEAD~1
...
| findings | 0 | 1 | 0 |
| lowering warnings | 0 | 4 | 0 |
...
$ cat "$GITHUB_OUTPUT"
sarif=.../scry-head1.sarif
shown=0
suppressed=1
gate=0
skip-upload=false

$ python3 -c 'import json; d=json.load(open("scry-head1.sarif")); \
  print([(r["ruleId"], r.get("baselineState")) for r in d["runs"][0]["results"]])'
[('scry/c/command-injection', 'unchanged'), ('scry/lowering/boundary', 'unchanged'),
 ('scry/lowering/boundary', 'unchanged'), ('scry/lowering/boundary', 'unchanged'),
 ('scry/lowering/boundary', 'unchanged')]
```

No finding was shown, the pre-existing one was counted, and the upload still carries it
as `unchanged` so code scanning does not mark it fixed.

## Tampered SARIF is refused before the upload

The upload step is reached only after `validate-sarif.py` succeeds. An empty file (what
a failed redirect or a truncated write leaves), a truncated JSON prefix, a log with no
runs, and a foreign SARIF version all fail:

```console
$ : > empty.sarif; head -c 60 scry.sarif > truncated.sarif
$ python3 .github/actions/scry/validate-sarif.py empty.sarif
scry: refusing to upload SARIF: empty.sarif is empty          # exit 1
$ python3 .github/actions/scry/validate-sarif.py truncated.sarif
scry: refusing to upload SARIF: truncated.sarif is not JSON: Unterminated string starting at: line 1 column 12 (char 11)
$ python3 .github/actions/scry/validate-sarif.py noruns.sarif
scry: refusing to upload SARIF: noruns.sarif has no runs
$ python3 .github/actions/scry/validate-sarif.py oldver.sarif
scry: refusing to upload SARIF: oldver.sarif has version '2.0.0', not '2.1.0'
$ python3 .github/actions/scry/validate-sarif.py scry.sarif
scry: SARIF ok (5328 bytes, 1 run(s), 5 result(s))            # exit 0
```

A diff with no `.c` files writes a valid empty SARIF for inspection but sets
`skip-upload=true`; the upload step is skipped rather than sending a log that would
close every existing alert:

```console
$ bash .github/actions/scry/scan.sh          # INPUT_DIFF=HEAD~1, commit touched only NOTES.md
scry: SARIF ok (244 bytes, 1 run(s), 0 result(s))
scry: no C files to analyse (paths: .; base: HEAD~1)
## Scry

No C files to analyse against `HEAD~1`. Nothing was uploaded: an empty SARIF would mark
every existing alert as fixed.

$ cat "$GITHUB_OUTPUT"
sarif=.../scry-empty.sarif
shown=0
suppressed=0
gate=0
skip-upload=true
```

## Multi-file merge

Two changed `.c` files produce two per-file logs; the merged log has one run, the six
rule descriptors once, and both files' results:

```console
$ bash .github/actions/scry/scan.sh          # INPUT_DIFF=HEAD, two staged .c files
scry: analysing 2 file(s) against HEAD
scry: SARIF ok (8669 bytes, 1 run(s), 12 result(s))
$ python3 -c 'import json; d=json.load(open("scry2.sarif")); \
  print(len(d["runs"][0]["tool"]["driver"]["rules"]), len(d["runs"][0]["results"]))'
6 12
```

## Not run locally

* The `github/codeql-action/upload-sarif` step and the real code-scanning service: no
  GitHub token or network upload here. The action passes the merged file plus
  `category`; the guard above is the local substitute for a bad file.
* The Nix path (`build.sh`: install Nix, substitute `.#wiz`, `grail build scry`) and the
  dogfood workflow's cold build. The tests above use an already-built binary, which is
  the same command shape `build.sh` produces.
* Pull-request event plumbing (`GITHUB_BASE_REF`, `fetch-depth: 0`): `diff: auto` was
  exercised against a local `refs/remotes/origin/main`, which is the ref the workflow
  checkout provides.
