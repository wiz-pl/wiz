# Dynamic corpus

A small checked-in corpus for `scry dynamic` and `scry bench --dynamic`. Each case is a
C file with a `dynamic` object in `manifest.json`:

```json
{
  "id": "dyn/t2/cwe416/uaf",
  "cwe": "CWE-416",
  "tier": "T2",
  "file": "uaf.c",
  "dynamic": {"expect": "event", "kind": "crash", "sanitizer": "address", "line": 5}
}
```

* `expect: "event"` — a **validated** event of `kind` (`crash`/`ub`/`leak`) must be
  observed, with a source frame at `line` when given.
* `expect: "clean"` — no validated event on this input. This is **not** a proof of
  absence; it is the observation for this seed/input only.
* Outcomes are `matched`, `missed`, `clean`, `unexpected`, `skipped`, `error`. A
  machine with no working compiler/sanitizer reports every case `skipped`; that is a
  clean skip, not a failure.

## Tiers

The tiers follow `wiz-notes/prior-art/symbolic-execution.md` §11.5:

| tier | CWEs | dynamic evidence here |
|---|---|---|
| T1 | CWE-78, CWE-134 | `exec-clean`, `exec-taint-clean`, `format-unreached` (clean runs; the static finding is not witnessed without an input) |
| T2 | CWE-416, CWE-476 | `uaf` (ASAN heap-use-after-free), `null-deref` (UBSAN null) |
| T3 | CWE-190, CWE-787, CWE-121 | `ub-overflow` (UBSAN signed overflow), `heap-oob` (ASAN heap OOB), `stack-oob` (ASAN stack OOB) |
| n/a | CWE-401 | `leak` (LSAN); collected, not a witness tier target |

CWE-120/242 are forbidden-call rules (the call is the bug, not a path condition) and
CWE-362 needs concurrency semantics Wil lacks; both are **out of scope** for a concolic
witness. The `stack-oob` case is CWE-121, not CWE-120: the dynamic event is an OOB write,
not a proof that every `strcpy` is exploitable.

## Reproduce

```sh
cd scry
export PATH="$(ls -d /nix/store/*clang-wrapper-*/bin | head -1):$PATH"
grail build scry
./.grail/bin/scry bench --dynamic --no-timing --json -
./.grail/bin/scry dynamic bench/dynamic/uaf.c
```
