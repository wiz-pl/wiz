# Machine-readable check results (`wiz check --json`)

`wiz check --json` prints **one JSON document** on stdout: the diagnostics an editor's
language server would show, in a stable order and with stable field names. It is meant
for CI, editors, MCP servers and other tools; it is not the human-readable text output.

```console
$ wiz check --json Main.wiz
{"version":1,"command":"check","tool":{"name":"wiz","version":"0.1.0","commit":"…"},
 "files":["Main.wiz"],"ok":false,"diagnostics":[…],"artifacts":[]}
```

`--json-version 1` selects the same format and lets a caller pin the version without
repeating `--json`. This build writes version `1` and rejects any other version with
exit status 2. `wiz build … --json` writes the same document with `"command":"build"`;
on success its `artifacts` lists the output file (and, for `--lib`, `OUT.h`).

The schema is [`docs/schema/check-json-v1.json`](schema/check-json-v1.json).

## Streams and exit status

* stdout carries **only** the JSON document (and its final newline). Nothing else is
  written there.
* stderr carries the usual `FILE:LINE:COL: severity: message` lines (for a person
  watching the run), plus any toolchain warnings not tied to a diagnostic.
* The exit status is the same as without `--json`: `0` when there is no error
  diagnostic (warnings alone are `0`), `1` when at least one diagnostic has severity
  `error`, and `2` for a usage error (no file, an unknown flag, an unsupported
  `--json-version`). A usage error writes nothing on stdout.
* `--json` may be combined with every other `wiz check` flag (`-I`, `--no-cache`, …).
  `wiz check` accepts several files in one run; `files` lists them in command-line
  order.

## Fields

| field | type | meaning |
|---|---|---|
| `version` | integer | the format version; always `1` for this document |
| `command` | `"check"` or `"build"` | the command that wrote the document |
| `tool.name` | string | `"wiz"` |
| `tool.version` | string | the toolchain's version (`0.1.0-dev` in a checkout) |
| `tool.commit` | string or null | the release commit, when the toolchain has a `REVISION`; `null` in a checkout |
| `files` | array of strings | the files named on the command line, as written |
| `ok` | boolean | true when no diagnostic has severity `error` |
| `diagnostics` | array | the messages, sorted (see below) |
| `artifacts` | array of strings | files `build` wrote (the output, and `OUT.h` for `--lib`); always `[]` for `check` |

A diagnostic:

| field | type | meaning |
|---|---|---|
| `severity` | `"error"`, `"warning"` or `"info"` | the message's severity |
| `code` | string or null | the stable error code (`docs/error-codes.md`), or `null` when the message has none |
| `message` | string | the message text (the wording may change; the code does not) |
| `span.file` | string | the file the span is in (the checked file, as named) |
| `span.start`, `span.end` | integer | character offsets; `end >= start`, and `end == start` for a point (a parse error) |
| `span.line`, `span.col` | integer | one-based line and column of `span.start` |
| `related` | array | related locations, `{message, span}` each; empty today (see below) |
| `notes` | array of strings | extra notes; empty today (see below) |
| `data` | object or null | the quick-fix payload the language server sends (for example `{"name":…,"suggestions":[…]}`), or `null` when there is none |
| `fixes` | array | code actions for this message's span: `{title, kind, edits:[{span, newText}]}`; the same actions `textDocument/codeAction` offers (quick fixes, and refactors such as filling a hole) |

### Positions are character offsets

`span.start` and `span.end` index **Unicode scalar values** (characters, as
`String.toList` returns them), not UTF-8 bytes and not UTF-16 code units. `span.line`
and `span.col` are one-based; `span.col` likewise counts characters. This is the
`SourceInfo` convention the whole frontend uses, so the offsets are the ones the LSP
conversion starts from: `😀` is one character here, while an LSP client counts it as two
UTF-16 code units. A tool that needs UTF-16 positions should convert from `start`.

### Order

Diagnostics are sorted by `(span.file, span.start, code)`; `span.end` and `message`
break the remaining ties, so the order is total and reproducible. `files` keeps the
command line's order; it is not sorted.

## `related` and `notes`

The language server's `publishDiagnostics` does not send `relatedInformation` today, and
a `Msg` has no separate note text (hints are part of `message`). The fields are in the
document now, always empty, so that a future version can populate them additively
without changing the shape consumers already handle.

Quick fixes and refactors are richer: `data` is the same object the LSP puts in a
diagnostic, and `fixes` are computed by the same `Wiz/Actions.lean` code that answers
`textDocument/codeAction` for the message's range. A message can have more than one
action; an edit's span may be empty (`start == end`) when it is an insertion. `fixes` is
computed for messages that carry a `code` (the families `Actions` knows); a message
without one has `[]`, and `data` is `null`.

## Compatibility

**Fields may be added in version 1. Never change the meaning of an existing field
without a version bump.** Removing a field, changing its type, changing the sort order,
or making an offset mean bytes or UTF-16 units is version 2. A consumer should ignore
fields it does not know. The schema has `"additionalProperties": true` for exactly this
reason; the golden test in `Tests/Groups/CheckJson.lean` fails when the shape changes
without the test (and this document) being updated.
