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

## The typed wrapper (`lib/Lint.wiz`)

The view is text because that is the smallest stable interface, but a rule need not
split it by hand. `lib/Lint.wiz` mirrors the registry's vocabulary — `Capability`,
`Category`, `Severity`, `Scope` and their `key`/`ofKey` spellings, with
`Capability.stable` the same package/unstable split the registry enforces — and parses
the view into structures:

```wiz no-check
import Lint

def noRawName (view : String) : String :=
  let c := Lint.Command.parse view;
  if Lint.Command.has c .decl then
    List.foldr (fun (d : Lint.Decl) (acc : String) =>
        match String.startsWith d.name "raw" with
        | .true => String.append (Lint.Finding.render
            (Lint.Finding.mk 0 0 (String.append d.name "#raw") "a raw name")) acc
        | .false => acc)
      "" c.decls
  else ""
```

`Lint.Finding.parse`/`parseAll`/`render` are the four-field finding format, and
`Lint.packageCode`/`coreCode` are the `W500`–`W999` / `W001`–`W499` blocks. This is a
wrapper, not a second ABI: the host still builds the text, and a rule still returns
text. `Tests/fixtures/lint/TypedProbe.wiz` is compared with `Wiz/Lint/Basic.lean` in the
`wiz-lint` group, so the mirror cannot drift.

## The package manifest and `lint.conf`

A package declares its sets in `grail.wiz` (this is the package boundary, where the
dependency graph is):

```wiz no-check
def package : Package := Package.new "scry"
  |> Package.lib "scry" "src"
  |> Package.lintSet "scry" "lint/Lints.wiz"
```

Declaring a set does not run it. The repository enables sets it wants in `lint.conf`
at the repository root, a line-oriented file (`#` starts a comment, words are separated
by spaces or tabs):

```
# lint.conf
set scry
set scratch lint/Scratch.wiz
public-roots lib src
```

* `set NAME` enables a set the manifest declares; a name the manifest does not declare
  is an error that names the missing `Package.lintSet` line. A typo never silently
  enables nothing.
* `set NAME MODULE` declares and enables a set in the file itself, for a repository
  with no manifest.
* `public-roots DIR…` are the roots `W301` treats as public (`lib` by default).
* A dependency's `lint.conf` is never read, and a package cannot enable its own set in
  a consumer: policy stays with the repository that owns the code.

`grail lint FILE…` resolves the manifest and `lint.conf`, adds the package's module
roots, and runs `wiz lint` with the resulting `--package-lint`/`--set`/`--public-roots`
flags. `wiz lint` itself keeps the explicit `--package-lint FILE --set NAME` form for
CI and for a file outside a package. An unknown capability, a trust source or a
package-defined `partial` in a declared set is still the registry's refusal, reported
before any rule runs.

## Baselines and diff mode

`wiz lint --lint-baseline-write FILE` records the run's findings; `wiz lint
--lint-baseline FILE` reports only findings whose **stable key** the baseline does not
name, and exits 1 when there is one (0 when there is none). The key is the file path,
the rule code and the rule's anchor:

```
# wiz-lint baseline v1: one finding per line, TAB-separated path, rule, anchor
lib/Foo.wiz	W101	foo#2
```

The anchor is a declaration name plus an occurrence, never a line or a hash of one, so
a reindent or a line move does not churn the baseline and a rename is a stale row (a
signal to re-review, not a silent match). The file is sorted and deduplicated, so a
rewrite is byte-for-byte stable; blank lines and `#` comments are ignored. A finding the
per-site marker suppressed is already gone from the run, so a baseline never re-admits
it. A failed run (an elaboration error) is never written as a baseline.

`grail lint` spells the two flags `--baseline FILE` and `--baseline-write FILE` and
passes them through.

## What stays P2

The `--package-lint`/`--set` flags and the manifest field are the discovery paths; a
directory-wide default file set (the package's roots) and `--diff BASE` (changed lines
only) are not wired yet — for now a caller names the files and the baseline's keys are
not line-scoped, so a whole-file run is the safe form. The remaining work is quick
fixes (`Fix`), the stable projected `info` view (`termView`), a step/fuel budget for the
interpreter (so a trusted-library `partial` helper cannot hang a run), and the selfhost
lint table. `lint.conf`'s `deny`/severity gating is also still open: the flags
(`--deny`, `--rule`) are per invocation, not per repository.
