/-!
# The shared entry registry: the record

One declaration of an extension point: a *kind* (`backend` for `--target`, and the
elaboration kinds the toolchain already has), a *name* (the key is `(kind, name)`), the
ABI and schema the payload was written against, the capabilities it declares, and a
**reference** to the payload (host code, a Wiz declaration, a data document, or a
process). The payload is never a function value, so the same record describes a core
backend, a package lint set and a future manifest entry.

`Wiz/Ext/Resolve.lean` owns the table and the one resolver. This module is only the
vocabulary, so a test can build an entry without importing the toolchain and a future
kind does not grow a second record.

The names here are the ones `wiz-notes/registry-abi.md` fixes; `Kind.key` spells the
backend kind `target`, because `--target`'s existing diagnostics (`unknown-target`,
`duplicate-target`) are part of the CLI's contract.
-/

namespace Wiz
namespace Ext

/-- The kinds of entry the toolchain knows. A target is a `backend` entry in this model:
it is resolved by the driver before any module is read, while the elaboration kinds are
resolved while a module is open. That difference is a property of the *table*, not of
the record. -/
inductive Kind where
  | deriver
  | tactic
  | macro
  | lintSet
  | lintRule
  | backend
  | docLanguage
  | termElab
  deriving Repr, BEq, Inhabited

/-- The key component and the prefix of the kind's diagnostic codes. A backend is
spelled `target` so the existing `--target` messages and tests keep their vocabulary. -/
def Kind.key : Kind → String
  | .deriver => "deriver"
  | .tactic => "tactic"
  | .macro => "macro"
  | .lintSet => "lint-set"
  | .lintRule => "lint-rule"
  | .backend => "target"
  | .docLanguage => "doc-language"
  | .termElab => "term-elab"

def Kind.describe : Kind → String
  | .deriver => "deriver"
  | .tactic => "tactic"
  | .macro => "macro"
  | .lintSet => "lint set"
  | .lintRule => "lint rule"
  | .backend => "target"
  | .docLanguage => "documentation language"
  | .termElab => "term elaborator"

/-- What an entry may ask for. The first group is an operation a backend (or a driver)
performs; the second is the stable, text-shaped view a package lint rule reads
(`docs/lint-abi.md`). `info`, `tactics`, `kernelTerm` and `sourceText` are deliberately
absent: they are unstable host views (`Wiz/Lint/Basic.lean` refuses them for a package
set). An invocation declares what it needs; the resolver refuses a capability the entry
does not declare, before the payload runs. -/
inductive Capability where
  /-- write the artifact -/
  | emit
  /-- check the input without writing an artifact -/
  | check
  /-- link an executable (the C/LLVM link step) -/
  | link
  /-- run the built program -/
  | run
  /-- write a build attestation -/
  | attest
  /-- `--lib`/`--no-main`: export functions instead of a program -/
  | library
  /-- `--split N`: more than one compilation unit -/
  | split
  /-- a REPL over the entry's backend -/
  | repl
  /-- the stable lint view: declarations -/
  | decl
  /-- the stable lint view: spans -/
  | spans
  /-- the stable lint view: imports -/
  | imports
  /-- the stable lint view: globals -/
  | globals
  /-- the stable lint view: messages -/
  | messages
  /-- the stable lint view: facts -/
  | facts
  deriving Repr, BEq, Inhabited

def Capability.key : Capability → String
  | .emit => "emit"
  | .check => "check"
  | .link => "link"
  | .run => "run"
  | .attest => "attest"
  | .library => "library"
  | .split => "split"
  | .repl => "repl"
  | .decl => "decl"
  | .spans => "spans"
  | .imports => "imports"
  | .globals => "globals"
  | .messages => "messages"
  | .facts => "facts"

def Capability.describe : Capability → String
  | .emit => "emit an artifact"
  | .check => "check its input"
  | .link => "link an executable"
  | .run => "run a program"
  | .attest => "write a build attestation"
  | .library => "build a library (--lib/--no-main)"
  | .split => "split the build (--split)"
  | .repl => "run a REPL"
  | .decl => "read declarations"
  | .spans => "read spans"
  | .imports => "read imports"
  | .globals => "read globals"
  | .messages => "read messages"
  | .facts => "read facts"

/-- What a backend writes. This is the shared vocabulary; a target's full artifact list
and tool list are backend policy, not fields of this record: they live in a side table
keyed by `target/NAME` (`Wiz/Ext/Resolve.lean`'s `backendArtifacts`). -/
inductive ArtifactKind where
  /-- generated source text (C, LLVM IR, …) -/
  | src
  /-- an object file -/
  | object
  /-- a C header beside an object -/
  | header
  /-- a loadable module (WebAssembly, an ES module) -/
  | module
  /-- a linked executable -/
  | executable
  /-- a side document (the eBPF probe descriptor, an attestation) -/
  | descriptor
  deriving Repr, BEq, Inhabited

def ArtifactKind.key : ArtifactKind → String
  | .src => "src"
  | .object => "object"
  | .header => "header"
  | .module => "module"
  | .executable => "executable"
  | .descriptor => "descriptor"

/-- The in-process driver of a core entry. A core backend is host code, so this enum is
the one place an in-tree target extends; a manifest/package entry names a `.process` or
`.data` payload instead and never adds a constructor here. `Main.lean` matches this enum
exhaustively, with no `else` that means C (the fifth-target bug class). -/
inductive CoreDriver where
  | c
  | llvm
  | wasm
  | bpf
  | js
  deriving Repr, BEq, Inhabited

def CoreDriver.key : CoreDriver → String
  | .c => "c"
  | .llvm => "llvm"
  | .wasm => "wasm"
  | .bpf => "bpf"
  | .js => "js"

/-- Where the executable part lives. `core` is host code registered in-process (the core
table only); `wizRule` names a Wiz declaration the interpreter runs; `data` is a
validated document; `process` is a child process with a declared contract;
`unsupported` is this toolchain's face of an entry that exists but cannot be served
(the selfhost's table, or a manifest entry before its adapter is installed). -/
inductive Payload where
  | core (driver : CoreDriver)
  | wizRule (decl : String)
  | data
  | process (command : String)
  | unsupported (reason : String)
  deriving Repr, BEq, Inhabited

def Payload.describe : Payload → String
  | .core driver => s!"core driver '{driver.key}'"
  | .wizRule decl => s!"the Wiz declaration '{decl}'"
  | .data => "a data document"
  | .process command => s!"the process '{command}'"
  | .unsupported reason => s!"unsupported ({reason})"

/-- One entry. `provider` is `wiz-lang` for the toolchain's own table and a package name
otherwise; `set` is the enablement set (empty means always enabled, as every core entry
is). `override` is legal only for a doc language, whose existing registry allows
replacing a built-in by name (`Wiz/Doc/Registry.lean`); `wiz` is reserved there.

A backend's artifact list and tool list are *not* fields here: they are backend policy
and live in a side table keyed by `target/NAME` (`Wiz/Ext/Resolve.lean`'s
`backendArtifacts`), so a deriver or a lint rule does not pay for a target's list. -/
structure Entry where
  kind : Kind
  name : String
  /-- other spellings of this entry; a name and an alias share one namespace per kind -/
  aliases : List String := []
  provider : String := "wiz-lang"
  /-- the enablement set; empty for a core entry (always enabled) -/
  set : String := ""
  /-- the document the payload consumes (`bpf-core/1`, `wiz-lint/1`, …) -/
  schema : String := ""
  /-- the interface the payload was written against (`wiz-backend/1`, …) -/
  abi : String := ""
  /-- what this entry declares it can do -/
  caps : List Capability := []
  payload : Payload := .unsupported "no payload declared"
  /-- doc languages only: replace a built-in of the same name -/
  override : Bool := false
  deriving Repr, BEq, Inhabited

/-- The stable key, `kind/name` (e.g. `target/bpf`). -/
def Entry.key (e : Entry) : String := s!"{e.kind.key}/{e.name}"

/-- Is the entry enabled by these sets? A core entry (empty `set`) always is. -/
def Entry.enabledBy (e : Entry) (enabledSets : List String) : Bool :=
  e.set.isEmpty || enabledSets.contains e.set

/-- A refusal is data: a stable code and a message a driver prints verbatim. Codes are
`<kind>-<reason>`; payload failures and platform refusals use `entry-failed`,
`entry-budget` and `entry-unsupported`. `Wiz/Ext/Resolve.lean` is the only producer. -/
structure Diagnostic where
  code : String
  message : String
  deriving Repr, BEq, Inhabited

/-- `code: message`, for a log line that must carry the stable code. The `wiz` CLI prints
`message` for the legacy `--target` refusals (the selfhost uses the same sentence) and the
code where a new refusal has no legacy wording. -/
def Diagnostic.render (d : Diagnostic) : String := s!"{d.code}: {d.message}"

end Ext
end Wiz
