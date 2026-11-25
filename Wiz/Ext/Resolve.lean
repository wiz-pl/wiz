import Wiz.Ext.Basic

/-!
# The shared entry registry: the table and the one resolver

One table per lifetime (the driver's target table is read before any module; the
elaborator's table is read while a module is open), but one record and one resolver. The
resolver is total and fail-closed:

1. the name (or an alias) must be in the table, or `<kind>-unknown` refuses;
2. the provider's set must be enabled (core entries are always enabled), or
   `<kind>-not-enabled` refuses;
3. the entry's ABI must be the one this consumer reads, or `unsupported-<kind>` refuses;
4. an entry may declare only the capabilities its kind allows (`Kind.capabilities`), or
   `invalid-<kind>-capability` refuses — for example a lint rule cannot `emit` and a
   backend cannot read a lint view;
5. the invocation's needs must be a subset of the entry's declared capabilities, or
   `<kind>-capability` refuses;
6. a payload this toolchain cannot serve is `entry-unsupported`.

Nothing runs before the entry is returned, so a refusal cannot have written an artifact
and a duplicate cannot have silently replaced a provider. The codes are data
(`Wiz/Ext/Basic.lean`'s `Diagnostic`); `=ext` pins them.

The first user is `--target`: five core rows (`c`, `llvm`, `wasm`, `bpf`, `js`) and the
tree's sixth spelling `ebpf`, which is `bpf`'s alias (the CLI comment already called it
"the tracing-flavoured alias"). A new name is a row here, not a sixth `String` comparison
in `Main.lean`.
-/


namespace Wiz
namespace Ext

/-- A registry table. One table per lifetime, one record and one resolver. -/
structure Table where
  entries : List Entry := []
  deriving Repr, Inhabited

/-- A name is one path-free token. The exact per-kind shape is checked when that kind
gets a package path; a backend is `[a-z][a-z0-9-]*` in practice. -/
def nameOk (n : String) : Bool :=
  !n.isEmpty && !n.any (fun c => c.isWhitespace || c == '/' || c == '\\')

/-- Is any element of `xs` repeated? Sorts a copy and compares neighbours, so it is
O(n log n) rather than the O(n²) of `eraseDups.length != length` (the aliases list is
short, but the complexity check refuses the quadratic idiom on purpose). The order of
`xs` itself is never changed - only the presence of a duplicate matters here. -/
private def hasDuplicate (xs : List String) : Bool :=
  let rec adjacentEqual : List String → Bool
    | a :: b :: rest => a == b || adjacentEqual (b :: rest)
    | _ => false
  adjacentEqual (xs.mergeSort (· ≤ ·))

/-- `a, b or c`: one spelling for the choices a refusal lists. -/
def choicesText (names : List String) : String :=
  match names.reverse with
  | [] => ""
  | [last] => last
  | last :: rest =>
    let head := ", ".intercalate rest.reverse
    s!"{head} or {last}"

/-- The key's valid spellings: the names in table order, then every alias. Names come
first so `--target bogus` lists `c, llvm, wasm, bpf, js or ebpf` (the CLI contract), not
an order that depends on where an alias was declared. -/
def Table.spellings (t : Table) (k : Kind) : List String :=
  let es := t.entries.filter (·.kind == k)
  es.map (·.name) ++ es.flatMap (·.aliases)

/-- Register one entry. A duplicate `(kind, name)` (or alias) is refused here, before
anything runs, and the message names both providers. `override` is refused for every
kind except a doc language; a `.core` payload is core-table-only. -/
def Table.register (t : Table) (e : Entry) : Except Diagnostic Table := do
  let k := e.kind.key
  unless nameOk e.name do
    throw { code := s!"invalid-{k}-name", message := s!"{k}: '{e.name}' is not a valid entry name" }
  if e.abi.isEmpty then
    throw { code := s!"invalid-{k}-abi", message := s!"{k} {e.name}: the entry declares no ABI" }
  if let some c := e.invalidCapability? then
    throw { code := s!"invalid-{k}-capability",
            message := s!"{k} {e.name}: a {e.kind.describe} cannot declare the capability '{c.key}'" }
  if e.override && e.kind != .docLanguage then
    throw { code := s!"invalid-{k}-override",
            message := s!"{k} {e.name}: only a doc language may override a built-in" }
  match e.payload with
  | .core _ =>
    if e.provider != "wiz-lang" then
      throw { code := s!"invalid-{k}-payload",
              message := s!"{k} {e.name}: provider '{e.provider}' cannot register host code (a .core payload)" }
  | _ => pure ()
  if hasDuplicate e.aliases then
    throw { code := s!"invalid-{k}-alias", message := s!"{k} {e.name}: an alias is listed twice" }
  for a in e.aliases do
    unless nameOk a do
      throw { code := s!"invalid-{k}-alias", message := s!"{k} {e.name}: '{a}' is not a valid alias" }
    if a == e.name then
      throw { code := s!"invalid-{k}-alias",
              message := s!"{k} {e.name}: the name is repeated as an alias" }
    match t.entries.find? (fun x => x.kind == e.kind && (x.name == a || x.aliases.contains a)) with
    | some old =>
      throw { code := s!"duplicate-{k}",
              message := s!"{k} {a} is provided by both '{old.provider}' and '{e.provider}'" }
    | none => pure ()
  match t.entries.find? (fun x => x.kind == e.kind && (x.name == e.name || x.aliases.contains e.name)) with
  | some old =>
    throw { code := s!"duplicate-{k}",
            message := s!"{k} {e.name} is provided by both '{old.provider}' and '{e.provider}'" }
  | none => pure { entries := t.entries ++ [e] }

/-- Build a table from a list; the first duplicate or malformed entry refuses the whole
table (no partial table is ever returned). -/
def Table.ofEntries (es : List Entry) : Except Diagnostic Table :=
  es.foldlM (fun t e => t.register e) ({} : Table)

/-- The entry for `(kind, name)`, if any. An alias resolves to its entry; the alias and
the name occupy one namespace per kind. -/
def Table.find? (t : Table) (k : Kind) (n : String) : Option Entry :=
  t.entries.find? fun e => e.kind == k && (e.name == n || e.aliases.contains n)

/-- The one resolver. `needs` is what the invocation will use, `enabledSets` the package
sets this run selected (core entries have an empty `set` and need no set), and `abi` the
interface this consumer reads (empty: accept the entry's declared ABI). Every refusal is
a `Diagnostic` with a stable code; the entry is returned only when all checks pass. -/
def Table.resolve (t : Table) (k : Kind) (n : String) (needs : List Capability := [])
    (enabledSets : List String := []) (abi : String := "") : Except Diagnostic Entry :=
  match t.find? k n with
  | none =>
    let choices := t.spellings k
    let suffix := if choices.isEmpty then "" else s!" (choose {choicesText choices})"
    throw { code := s!"unknown-{k.key}", message := s!"unknown {k.key} {n}{suffix}" }
  | some e =>
    if !e.enabledBy enabledSets then
      throw { code := s!"{k.key}-not-enabled",
              message := s!"{k.key} {e.name} is provided by the set '{e.set}', which is not enabled" }
    else if !abi.isEmpty && e.abi != abi then
      throw { code := s!"unsupported-{k.key}",
              message := s!"{k.key} {e.name}: this toolchain reads {abi}, the entry declares {e.abi}" }
    else if let some c := e.invalidCapability? then
      throw { code := s!"invalid-{k.key}-capability",
              message := s!"{k.key} {e.name}: a {e.kind.describe} cannot declare the capability '{c.key}'" }
    else match needs.find? (fun c => !e.caps.contains c) with
      | some c =>
        throw { code := s!"{k.key}-capability",
                message := s!"{k.key} {e.name} does not declare the capability '{c.key}'" }
      | none =>
        match e.payload with
        | .unsupported reason =>
          throw { code := "entry-unsupported", message := s!"{k.key} {e.name}: {reason}" }
        | _ => pure e

/-- The in-process driver of a core entry, or the refusal for a payload this driver cannot
run. Dispatch is a second, separate step: resolution has already checked ABI, enablement
and capabilities. -/
def Entry.coreDriver? (e : Entry) : Except Diagnostic CoreDriver :=
  match e.payload with
  | .core d => pure d
  | .unsupported reason =>
    .error { code := "entry-unsupported", message := s!"{e.kind.key} {e.name}: {reason}" }
  | p =>
    .error { code := s!"unsupported-{e.kind.key}",
             message := s!"{e.kind.key} {e.name}: the {e.kind.describe} driver cannot run {p.describe}" }

/-! ## The first user: `--target` -/

/-- The ABI a target payload is written against. The field stays empty on an entry that
consumes a serialized document (there is no `wiz-ir/1` yet); `bpf` consumes `bpf-core/1`. -/
def backendAbi : String := "wiz-backend/1"

/-- The single declaration of the core backends. A target's shape refusals (`--lib`,
`--split`, `--attest`) are capabilities here, not `if target == …` arms in the driver.
`ebpf` is an alias of `bpf`, as it already was in `Main.lean`'s help text and the
selfhost's table. -/
def backendEntries : List Entry := [
  { kind := .backend, name := "c", abi := backendAbi,
    caps := [.emit, .link, .run, .attest, .library, .split, .repl],
    payload := .core .c },
  { kind := .backend, name := "llvm", abi := backendAbi,
    caps := [.emit, .link, .run, .attest, .library, .split, .repl],
    payload := .core .llvm },
  { kind := .backend, name := "wasm", abi := backendAbi,
    caps := [.emit, .run],
    payload := .core .wasm },
  { kind := .backend, name := "bpf", aliases := ["ebpf"], schema := "bpf-core/1", abi := backendAbi,
    caps := [.emit, .check],
    payload := .core .bpf },
  { kind := .backend, name := "js", abi := backendAbi,
    caps := [.emit, .run],
    payload := .core .js }
]

/-- A backend's artifact list: a side table keyed by `target/NAME`, as the registry note
asks (a deriver or a lint rule does not pay for a target's list). It is a description of
what the payload writes, not an enforcement; resolution never runs the payload. -/
structure BackendArtifacts where
  target : String
  files : List (String × ArtifactKind)
  deriving Repr, Inhabited

def backendArtifacts : List BackendArtifacts := [
  { target := "c", files := [("OUT", .executable), ("OUT.o", .object), ("OUT.h", .header)] },
  { target := "llvm", files := [("OUT", .executable), ("OUT.o", .object), ("OUT.h", .header)] },
  { target := "wasm", files := [("OUT.wasm", .module)] },
  { target := "bpf", files := [("OUT.c", .src), ("bpf_rt.h", .header), ("OUT.probe.json", .descriptor)] },
  { target := "js", files := [("OUT.mjs", .module)] }
]

/-- The artifacts a target declares (the canonical name; `ebpf` resolves to `bpf`). -/
def artifactsOf (name : String) : List (String × ArtifactKind) :=
  (backendArtifacts.find? (·.target == name)).map (·.files) |>.getD []

/-- The core target table. If a core entry is malformed or duplicated, every resolution
refuses; the toolchain does not start with a partial table. -/
def backendTable : Except Diagnostic Table := Table.ofEntries backendEntries

/-- The canonical names, in table order. -/
def backendNames : List String := backendEntries.map (·.name)

/-- Every accepted `--target` spelling (canonical names first, then the aliases). -/
def backendSpellings : List String :=
  backendEntries.map (·.name) ++ backendEntries.flatMap (·.aliases)

/-- `c, llvm, wasm, bpf, js or ebpf`: the one spelling of the target choices, used by
both the missing-value message and an unknown name. -/
def backendChoices : String := choicesText backendSpellings

/-- Resolve `--target NAME` through the core table. `ebpf` resolves to the `bpf` entry. -/
def resolveBackend (name : String) : Except Diagnostic Entry := do
  let t ← backendTable
  t.resolve .backend name (abi := backendAbi)

/-- Resolve `--target NAME` for an invocation that needs these capabilities. Every
missing capability is refused here, before the driver is entered. -/
def resolveBackendFor (name : String) (needs : List Capability)
    (enabledSets : List String := []) : Except Diagnostic Entry := do
  let t ← backendTable
  t.resolve .backend name needs enabledSets backendAbi

/-- Resolve an entry from a table that includes package rows (a manifest would build it;
no manifest reader is wired yet). This is the same resolver, not a second one. -/
def resolveBackendIn (t : Table) (name : String) (needs : List Capability := [])
    (enabledSets : List String := []) : Except Diagnostic Entry :=
  t.resolve .backend name needs enabledSets backendAbi

end Ext
end Wiz
