# The package lint ABI (`wiz-lint/1`)

A package contributes a lint set as a Wiz module. The set is **data plus one pure
function per rule**: the toolchain builds a stable view of the command, calls the
function in the interpreter, and reads findings back. A package set never runs host code
and never needs a compiler rebuild.

This is the Wiz-rule entry of the shared extension model (`wiz-notes/separate-repos.md`):
the interface is a total function over a stable view, not over kernel internals. The
registry builds exactly the declared capabilities, and a rule that asks for more than the
set declares is a registration error.

## Declaring a set

```
import Prelude
import Text

lint-set "scry" "wiz-lint/1" [decl, spans]

def noRawPath (view : String) : String := ...

lint W501 "no-raw-path" api warning declaration [decl, spans] noRawPath
```

* `lint-set NAME ABI [capabilities]` is the header. A set must declare at least one
  capability, and the ABI range records the toolchain it was written against.
* `lint CODE NAME CATEGORY SEVERITY SCOPE [requires] RUNNER` adds one rule. `CODE` is
  `W500`–`W999`; the core block `W001`–`W499` is the toolchain's. `CATEGORY` is
  `correctness`, `performance`, `api`, `maintainability` or `ecosystem`; `SEVERITY` is
  `off`, `hint`, `warning` or `error`; `SCOPE` is `declaration` or `module`.
* `RUNNER` is a Wiz function `String → String`, declared above the `lint` command. It is
  the rule's executable part.

A consumer enables the set by name (`wiz lint --set scry --package-lint path/to/Lints.wiz`).
A set runs **only** when the consumer enables it; a transitive dependency's set is not
enabled automatically, and the package cannot set the consumer's policy or silence a
core rule.

## The capability set

A package may declare only the **stable** capabilities:

| capability | the view contains |
|---|---|
| `decl` | one `decl` line per declaration the command added: name, kind, `isPublic`, `hasDoc` |
| `spans` | the command's `span` |
| `imports` | one `import` line per direct import: module name and span |
| `globals` | one `global` line per declaration in the elaborated module |
| `messages` | one `message` line per message: severity, code, span, text |
| `facts` | one `binder` line per binder: name, used, depth |

`info`, `tactics`, `kernelTerm` and `sourceText` are not part of the package ABI: they
are unstable host views. A set that asks for one is refused, naming the capability.

The registry checks, before any rule runs:

1. the code is `W` + three digits in `W500`–`W999`, and is unique in the enabled closure
   (a duplicate names both sets);
2. every rule's `requires` is declared by the set;
3. the runner's closure has **no trust source** (`Globals.axiomsOf`: an axiom, a foreign
   function, `implemented_by`, an untrusted `builtin`, a native representation) and **no
   `partial` definition** (the driver must terminate);
4. the runners compile in the interpreter.

A runner cannot perform IO: its argument is a `String`, and a foreign function in its
closure is rejected above. A rejection is a hard registration error; the set does not
"quietly do nothing".

## The view

The view is line-oriented text. Fields are separated by a tab, lines by a newline, and a
field never contains either (a field's tabs/newlines become spaces). The first two lines
are:

```
view	wiz-lint/1
caps	decl,spans
```

`caps` names exactly the sections present. Then, in this order:

```
module	<module>
path	<path>
command	<kind>	<name>
span	<start>	<stop>
decl	<name>	<kind>	<isPublic>	<hasDoc>
binder	<name>	<used>	<depth>
import	<name>	<start>	<stop>
global	<name>
message	<severity>	<code>	<start>	<stop>	<text>
```

A section the set did not declare is absent, so a rule cannot read an undeclared
capability by accident. `start`/`stop` are offsets in the target file.

## Findings

The runner returns one finding per line, four tab-separated fields:

```
<start>	<stop>	<anchor>	<text>
```

The host supplies the rule's code and severity from its metadata, so a runner cannot
spoof another rule's code. `anchor` is the stable baseline key (declaration name plus an
occurrence; never a line number). An empty string is no findings. The finding is an
ordinary `Msg` with `code := the rule id`, so the language server, `--json`, and per-site
`-- lint: allow Wxxx (reason)` suppression all work without a second wire format.

## What stays P2

The view is serialised as text in P1, so a runner parses the few fields it needs (the
fixture uses `String.splitOn`). A typed `lib/Lint.wiz` (a `Command`/`Finding` structure
and its parser) is the ergonomic wrapper, not a new ABI. The `--package-lint` / `--set`
flags are the P1 discovery path; a typed `Package.lint`/`Package.lintSet` manifest field
and the `lint.conf` reader are the next step. The remaining P2 work is quick fixes
(`Fix`), the stable projected `info` view, a step/fuel budget for the interpreter (so a
trusted-library `partial` helper cannot hang a run), the selfhost lint table, and the
baseline / `--diff` gate.
