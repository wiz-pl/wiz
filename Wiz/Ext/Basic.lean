/-!
# The shared entry registry: one record, one key, one resolver

This is the prototype of the model in `wiz-notes/registry-abi.md`. It is deliberately
pure: no imports, no IO, no elaborator state. A registry entry is a *declaration* —
`(kind, name)` plus the ABI it was written against and the capabilities it claims. The
payload is a reference (a host key, a Wiz declaration, a data document, or a process),
never a function value, so the same record describes a core entry, a package rule and a
future manifest-declared backend.

Resolution is total and fail-closed: it returns the entry or a stable `Refusal`; there is
no default entry and no fallback to a neighbouring kind. A duplicate `(kind, name)` is a
refusal at registration, naming both providers, before any payload runs. The
`backend` kind (`target` in diagnostic codes, to keep the existing CLI vocabulary) is the
first user: `backendEntries` is the single declaration of `c`, `llvm`, `wasm`, `bpf` and
`js`.
-/

namespace Wiz
namespace Ext

/-- The kinds of entry the toolchain knows. `backend` is the `--target` kind; its
diagnostic prefix is `target` so existing messages and tests keep their spelling. -/
inductive Kind where
  | deriver
  | tactic
  | macro
  | lintSet
  | lintRule
  | backend
  | docLanguage
  | termElab
  deriving BEq, Repr, Inhabited

/-- The key component (the registry table is keyed by `(kind, name)`) and the prefix of
the kind's refusal codes. Most kinds use their own name; a backend is a `target`. -/
def Kind.key : Kind → String
  | .deriver => "deriver"
  | .tactic => "tactic"
  | .macro => "macro"
  | .lintSet => "lint-set"
  | .lintRule => "lint-rule"
  | .backend => "target"
  | .docLanguage => "doc-language"
  | .termElab => "term-elab"

/-- What an entry may ask for. The first group is a backend's; the second is a package
lint rule's stable view. A registry entry declares these, and the resolver refuses an
invocation that needs one the entry does not declare — the refusal is data, not prose in
a driver. `info`, `tactics`, `kernelTerm` and `sourceText` are deliberately absent: they
are unstable host views (`Wiz/Lint/Basic.lean:49-102`). -/
inductive Cap where
  | emit
  | check
  | link
  | run
  | attest
  | library
  | split
  | repl
  | decl
  | spans
  | imports
  | globals
  | messages
  | facts
  deriving BEq, Repr, Inhabited

def Cap.key : Cap → String
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

/-- Where the executable part lives. `core` is host code registered in-process (core
kinds only); `wizRule` names a Wiz declaration run by the interpreter; `data` is a
validated document; `process` is a child process with a declared contract. `unsupported`
is the selfhost/current-platform face of an entry that exists but cannot be served. -/
inductive Payload where
  | core (key : String)
  | wizRule (decl : String)
  | data
  | process (command : String)
  | unsupported (reason : String)
  deriving BEq, Repr, Inhabited

/-- One entry. `provider` is `wiz-lang` for the toolchain's own table and a package name
otherwise; `set` is the enablement set (empty for core). `override` is legal only for a
doc language, whose existing registry allows replacing a built-in by name
(`Wiz/Doc/Registry.lean:127-146`); `wiz` is reserved there. -/
structure Entry where
  kind : Kind
  name : String
  /-- other spellings of this entry; a name and an alias share one namespace per kind -/
  aliases : List String := []
  provider : String := "wiz-lang"
  set : String := ""
  schema : String := ""
  abi : String := ""
  caps : List Cap := []
  payload : Payload := .core ""
  override : Bool := false
  deriving Repr, Inhabited

/-- The stable key: `kind/name`. (The table stores the pair; this is for messages and
baselines.) -/
def Entry.key (e : Entry) : String := s!"{e.kind.key}/{e.name}"

/-- A refusal is data: a stable code and a message a driver prints verbatim. Codes are
`<kind>-<reason>`; payload failures use `entry-failed` and `entry-budget`. -/
structure Refusal where
  code : String
  message : String
  deriving Repr, Inhabited

/-- A registry table. One table per lifetime (the driver reads a target before any
module; the elaborator reads a deriver while a module is open), but one record and one
resolver. -/
structure Table where
  entries : List Entry := []
  deriving Repr, Inhabited

/-- A name is one path-free token (a backend is `[a-z][a-z0-9-]*` in practice; the exact
shape is checked per kind when that kind gets a package path). -/
def nameOk (n : String) : Bool :=
  !n.isEmpty && !n.any (fun c => c.isWhitespace || c == '/' || c == '\\')

/-- `a, b or c`: one spelling for the choices a refusal lists. -/
def choicesText (names : List String) : String :=
  match names.reverse with
  | [] => ""
  | [last] => last
  | last :: rest =>
    let head := ", ".intercalate rest.reverse
    s!"{head} or {last}"

/-- Register one entry. A duplicate `(kind, name)` is refused here, before anything runs,
and the message names both providers. `override` is refused for every kind except a doc
language. -/
def Table.register (t : Table) (e : Entry) : Except Refusal Table := do
  unless nameOk e.name do
    throw { code := s!"invalid-{e.kind.key}-name",
            message := s!"{e.kind.key}: '{e.name}' is not a valid entry name" }
  if e.abi.isEmpty then
    throw { code := s!"invalid-{e.kind.key}-abi",
            message := s!"{e.kind.key} {e.name}: the entry declares no ABI" }
  if e.override && e.kind != .docLanguage then
    throw { code := s!"invalid-{e.kind.key}-override",
            message := s!"{e.kind.key} {e.name}: only a doc language may override a built-in" }
  for a in e.aliases do
    unless nameOk a do
      throw { code := s!"invalid-{e.kind.key}-alias",
              message := s!"{e.kind.key} {e.name}: '{a}' is not a valid alias" }
    if a == e.name then
      throw { code := s!"invalid-{e.kind.key}-alias",
              message := s!"{e.kind.key} {e.name}: the name is repeated as an alias" }
    match t.entries.find? (fun x => x.kind == e.kind && (x.name == a || x.aliases.contains a)) with
    | some old =>
      throw { code := s!"duplicate-{e.kind.key}",
              message := s!"{e.kind.key} {a} is provided by both '{old.provider}' and '{e.provider}'" }
    | none => pure ()
  if e.aliases.eraseDups.length != e.aliases.length then
    throw { code := s!"invalid-{e.kind.key}-alias",
            message := s!"{e.kind.key} {e.name}: an alias is listed twice" }
  match t.entries.find? (fun x => x.kind == e.kind && (x.name == e.name || x.aliases.contains e.name)) with
  | some old =>
    throw { code := s!"duplicate-{e.kind.key}",
            message := s!"{e.kind.key} {e.name} is provided by both '{old.provider}' and '{e.provider}'" }
  | none => pure { entries := t.entries ++ [e] }

/-- Build a table from a list; the first duplicate or malformed entry refuses the whole
table (no partial table is ever returned). -/
def Table.ofEntries (es : List Entry) : Except Refusal Table :=
  es.foldlM (fun t e => t.register e) ({ entries := [] } : Table)

/-- The entry for `(kind, name)`, if any. An alias resolves to its entry; the alias and
the name occupy one namespace per kind. -/
def Table.find? (t : Table) (k : Kind) (n : String) : Option Entry :=
  t.entries.find? fun e => e.kind == k && (e.name == n || e.aliases.contains n)

/-- Resolve one name. There is no default: an unknown name is a refusal, and the message
lists the names of that kind (a typo must not silently build a different entry). -/
def Table.resolve (t : Table) (k : Kind) (n : String) : Except Refusal Entry :=
  match t.find? k n with
  | some e =>
    match e.payload with
    | .unsupported reason =>
      throw { code := "entry-unsupported", message := s!"{k.key} {e.name}: {reason}" }
    | _ => pure e
  | none =>
    let names := (t.entries.filter (·.kind == k)).map (·.name)
    let choices := if names.isEmpty then "" else s!" (choose {choicesText names})"
    throw { code := s!"unknown-{k.key}", message := s!"unknown {k.key} {n}{choices}" }

/-- Resolve and check the capabilities an invocation needs. Every missing capability is a
`<kind>-capability` refusal, before the payload is entered. -/
def Table.resolveWith (t : Table) (k : Kind) (n : String) (needs : List Cap) :
    Except Refusal Entry := do
  let e ← t.resolve k n
  for c in needs do
    unless e.caps.contains c do
      throw { code := s!"{k.key}-capability",
              message := s!"{k.key} {e.name} does not declare the capability '{c.key}'" }
  pure e

/-! ## The first user: `--target` -/

/-- The single declaration of the core backends. `schema` is the document the entry
consumes; empty means the in-process IR (there is no serialized IR yet, see
`wiz-notes/registry-abi.md` §4.5). `bpf` is the one core entry with a document input
(`bpf-core/1`). Capabilities are the operations the driver may ask for: the resolver,
not a `String` comparison in `Main.lean`, decides whether `--attest`, `--lib`, `--split`,
`run` or the REPL is legal. -/
def backendEntries : List Entry := [
  { kind := .backend, name := "c", schema := "", abi := "wiz-backend/1",
    caps := [.emit, .link, .run, .attest, .library, .split, .repl],
    payload := .core "Wiz.Compiler.Build.c" },
  { kind := .backend, name := "llvm", schema := "", abi := "wiz-backend/1",
    caps := [.emit, .link, .run, .attest, .library, .repl],
    payload := .core "Wiz.Compiler.Build.llvm" },
  { kind := .backend, name := "wasm", schema := "", abi := "wiz-backend/1",
    caps := [.emit, .run],
    payload := .core "Wiz.Compiler.Build.wasm" },
  { kind := .backend, name := "bpf", schema := "bpf-core/1", abi := "wiz-backend/1",
    caps := [.emit, .check],
    payload := .core "Wiz.Compiler.Bpf" },
  { kind := .backend, name := "js", schema := "", abi := "wiz-backend/1",
    caps := [.emit, .run],
    payload := .core "Wiz.Compiler.Build.js" }
]

/-- The core backend table. If a core entry is malformed or duplicated, every resolution
refuses; the toolchain does not start with a partial table. -/
def backendTable : Except Refusal Table := Table.ofEntries backendEntries

/-- The names the help text may list (the table is the source of truth). -/
def backendNames : List String := backendEntries.map (·.name)

/-- Resolve `--target NAME`. -/
def resolveBackend (name : String) : Except Refusal Entry := do
  let t ← backendTable
  t.resolve .backend name

/-- Resolve `--target NAME` for an invocation that needs `needs` capabilities. -/
def resolveBackendFor (name : String) (needs : List Cap) : Except Refusal Entry := do
  let t ← backendTable
  t.resolveWith .backend name needs

end Ext
end Wiz
