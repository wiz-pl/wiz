# Scry benchmark corpus

This directory is the checked-in S0/S2 corpus (48 cases on `agent/scry-models`) for `scry bench`:

* `manifest.json` — the cases: suite, CWE, file, `expect`, and the expected findings.
* `cwe78/` — CWE-78 command injection.
* `cwe120/`, `cwe121/` — unbounded `strcpy`/`strcat` (the default pack's forbidden
  calls).
* `cwe134/` — format strings.
* `cwe242/` — `gets`.
* `../../tests/fixtures/taint-*.c` — the S0 fixtures the taint test group already uses.
* `../../tests/fixtures/model-*.c` — the external-model cases: the `exec*` variadic
  argv, `sprintf`'s formatted destination and format argument, the `strcpy` copy, the
  `read`/`recv` buffer source, `realloc`, a policy sanitiser, and the explicit
  unmodelled-external warning. They are referenced from the manifest, not duplicated.
* `../../tests/fixtures/taint-*.c` — the S0 fixtures the taint test group already uses,
  including the `taint-exec-{unsafe,safe}.c` command-sink family and the
  `taint-entry-{unsafe,safe}.c` exported-C-ABI-entry controls.

The fixtures are deliberately small and hand-authored. They are a regression and
debugging corpus, not evidence of real-world precision; S1/S3/S4 are optional external
corpora (see below).

## Manifest

```json
{
  "id": "s2/cwe78/direct-unsafe",
  "suite": "S2",
  "cwe": "CWE-78",
  "file": "cwe78/direct-unsafe.c",
  "expect": "unsafe",
  "findings": [
    {"rule": "command-injection", "function": "main", "callee": "system",
     "argument": 0, "sinkLine": 7, "sourceLine": 6}
  ]
}
```

* `expect` is `unsafe`, `safe`, or `unknown`.
* An `unsafe` case lists every expected finding. Matching is one-to-one on
  `(rule, function, callee, argument)`; `sinkLine` and `sourceLine` are optional and,
  when present, must match the reported locations.
* A `safe` case expects no finding.
* An `unknown` case is a documented coverage probe. It is reported as `unknown` and is
  excluded from TPR/FPR; use it for a construct the frontend cannot model yet.

## Outcome rules

`scry bench` computes metrics from **cases**, not raw alerts:

| case | actual | outcome |
|---|---|---|
| unsafe | every expected finding matched, valid evidence, no extra finding | `tp` |
| unsafe | an expected finding missing or with invalid evidence | `fn` |
| safe | no finding, no blocking boundary | `tn` |
| safe | any finding | `fp` |
| safe | no finding, but a blocking lowering boundary | `unknown` |
| unknown | any | `unknown` |

A finding's evidence is valid when its path reaches the reported sink. For a taint
finding the path must also start at a `source`; for a forbidden-call finding the call
itself is the path. `sinkLine`/`sourceLine` are checked when the manifest gives them.

## Boundary policy

The C frontend in this slice lowers a deliberate subset and reports the rest as
`lowering-boundary` warnings. They are split into two classes:

* **Advisory** — an external call without a prototype, a string literal, an implicit
  conversion, a void implicit return, an external global such as `stdin`, or a call
  arity mismatch. These are counted in the report but do not turn a clean safe case
  into `unknown`, because they do not feed the taint rules.
* **Blocking** — the construct the taint layer cannot see through: arrays and
  declarators, struct fields, pointer operations, `switch`/`goto`/`do`/`else`, an
  unbound identifier, and other skipped statements. A safe case with one of these is
  `unknown`, not a verified negative.

This split is a measurement decision, not a soundness claim. `wiz-notes/scry-bench.md`
records the limitation and the cases that are `unknown` today.

## Dynamic evidence

`scry bench --dynamic` also runs the separate corpus in `../dynamic/` (ASan/UBSan/
coverage). It is reported in its own `dynamic` section and does not change the static
TPR/FPR metrics or the baseline comparison; a clean dynamic run is not a negative
static case. See `../dynamic/README.md`.

## External suites

Nothing from Juliet, OWASP Benchmark or SV-COMP is checked in (and none was present on
the machine when the baseline was made), because those corpora are large and have
their own licences. To add a subset without touching the checked-in manifest:

```sh
scry bench --extra /path/to/subset --json build/s3.json --markdown build/s3.md
```

`/path/to/subset/manifest.json` uses the same schema; `file` paths are relative to that
directory. A missing extra manifest is reported under `skipped_sources`, not treated as
an error. This is the hook for a later S3/S4 slice: put the selected cases and their
ground truth in a manifest, keep the corpus outside the repository, and run it beside
the checked-in S0/S2 baseline.

## Updating the baseline

After reviewing a change in findings or expectations:

```sh
cd scry
grail run scry -- bench --update-baseline bench/baseline.json
grail test
```

`tests/bench.wiz` fails when the corpus no longer matches the checked-in baseline; that
is the regression gate.
