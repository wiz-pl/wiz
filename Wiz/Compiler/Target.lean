/-!
# The `--target` registry

A target name is read before any module is: `Main.takeTarget` and the self-hosted
driver's `parseOptsGo` (`selfhost/Cli.wiz`) both parse it out of argv. The two drivers
distinguish two refusals, because they mean different things to a user:

* **unknown** — the name is not a target at all (a typo): `unknown target X (choose …)`;
* **unsupported** — the name is a target, but this toolchain has no backend for it:
  `unsupported target X: …`.

`all` below is the *one* name table. The host implements every entry (`supported` is
`true` throughout). The self-hosted driver is compiled with the same spellings: the
`Wiz/Selfhost.lean` splice (`targetsSource`) renders `all` as Wiz definitions that
`selfhost/Cli.wiz` uses, so the driver has no second literal list. Its *capability* is
its own: it implements `c`/`llvm` (C5) and refuses the rest by name; that set is
`Wiz.Selfhost.selfhostImplemented`, not a second copy of the names.

`ebpf` is an alias of `bpf` (the tracing-flavoured spelling), so it occupies the same
`(kind, name)` slot: a name and its aliases are one entry. `choices` lists the canonical
names first, then the aliases — the spelling both drivers use in an unknown-target or
missing-value refusal.

`Tests/Groups/SelfhostCliDiff.lean` pins the names, the alias and the unknown-target
sentence; the selfhost's unsupported sentence legitimately differs (it names the C5
gap) and is pinned by `=selfhost-cli-diff` too.

## The `Wiz/Ext` seam

The full entry model and its resolver live on the `ext-registry` lane (`Wiz/Ext/Basic`,
`Wiz/Ext/Resolve`: `Entry`, `Capability`, `Table.resolve`, `resolveBackend`). They are
not in this tree yet. This module is deliberately the small adapter: a name, aliases and
the supported flag, which is the part `--target` reads today. When `Wiz/Ext` lands,
delete this module's table and call `Wiz.Ext.resolveBackend`; the mapping is

| here | `Wiz.Ext` |
|---|---|
| `Target.name`, `Target.aliases` | `Entry.name`, `Entry.aliases` (kind `backend`, key `target`) |
| `Target.supported = false`, `Target.reason` | `Payload.unsupported reason` (`entry-unsupported`) |
| `Target.choices` | `Wiz.Ext.backendChoices` |
| `Target.resolve all n` | `Wiz.Ext.resolveBackend n` |

The two outcomes this module cannot express — a row that is present but whose provider
set is not enabled (`target-not-enabled`), and a capability the row does not declare
(`target-capability`) — are `Wiz/Ext`'s, not this seam's. There is no `set` or `caps`
field here on purpose: adding them would be a second registry.

A target is not an extern implementation: the `(declaration, target)` rows for foreign
functions are `IR.ExternImpl` (`Wiz/Compiler/IR.lean`), selected after elaboration.
-/

namespace Wiz

/-- A `--target` name and whether this compiler has a backend that can emit it. -/
structure Target where
  /-- the canonical spelling `--target` takes -/
  name : String
  /-- other accepted spellings of the same entry (`ebpf` for `bpf`) -/
  aliases : List String := []
  /-- does this toolchain have a backend for it? -/
  supported : Bool := true
  /-- why not, when `supported` is false -/
  reason : String := ""
  deriving Repr, DecidableEq, Inhabited

namespace Target

/-- Every target entry, in the order the unknown-target refusal lists them. The host has
a backend for all five (`c`, `llvm`, `wasm`, `bpf`, `js`); `ebpf` is `bpf`'s alias. The
self-hosted driver is compiled with these spellings and implements the first two. -/
def all : List Target :=
  [ { name := "c" }, { name := "llvm" }, { name := "wasm" },
    { name := "bpf", aliases := ["ebpf"] }, { name := "js" } ]

/-- Every accepted spelling of `ts`: canonical names in table order, then their aliases.
This is the order `--target`'s refusals list (`c, llvm, wasm, bpf, js or ebpf`), not an
order that depends on where an alias was declared. -/
def spellings (ts : List Target) : List String :=
  ts.map (·.name) ++ ts.flatMap (·.aliases)

/-- `a, b or c`: one spelling for the choices a refusal lists. -/
def choicesText (names : List String) : String :=
  match names.reverse with
  | [] => ""
  | [last] => last
  | last :: rest =>
    let head := ", ".intercalate rest.reverse
    s!"{head} or {last}"

/-- The names as both drivers spell them in an unknown-target refusal. Derived from
`all`, so a name or alias added above cannot leave the refusal listing an old set. -/
def choices : String := choicesText (spellings all)

/-- The entry for `n` in `ts`; `none` is an unknown name. The table is an argument so a
test can add or drop an entry without changing the CLI's table. -/
def ofNameIn (ts : List Target) (n : String) : Option Target :=
  ts.find? fun t => t.name == n || t.aliases.contains n

/-- The entry for `n` in the host's table. -/
def ofName? (n : String) : Option Target := ofNameIn all n

/-- The canonical name `n` resolves to (`ebpf` is `bpf`), if any. -/
def canonicalIn (ts : List Target) (n : String) : Option String :=
  (ofNameIn ts n).map (·.name)

/-- The refusal of a name no table has. `ts` is the table that was searched, so a test's
table lists its own names (the CLI's table prints `c, llvm, wasm, bpf, js or ebpf`). -/
def unknownIn (ts : List Target) (n : String) : String :=
  let names := spellings ts
  let suffix := if names.isEmpty then "" else s!" (choose {choicesText names})"
  s!"unknown target {n}{suffix}"

/-- The refusal of a name the default table does not have. -/
def unknown (n : String) : String := unknownIn all n

/-- The refusal of a name the table knows but this toolchain cannot emit. -/
def unsupported (t : Target) : String :=
  let why := if t.reason.isEmpty then "this toolchain has no backend for it" else t.reason
  s!"unsupported target {t.name}: {why}"

/-- The entry for `n`, or the refusal: unknown names and known-but-unsupported names are
different errors. An alias resolves to its canonical entry (`ebpf` resolves to `bpf`). -/
def resolve (ts : List Target) (n : String) : Except String Target :=
  match ofNameIn ts n with
  | none => throw (unknownIn ts n)
  | some t => if t.supported then pure t else throw (unsupported t)

end Target
end Wiz
