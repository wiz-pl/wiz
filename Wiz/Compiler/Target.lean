/-!
# The `--target` registry

A target name is read before any module is: `Main.takeTarget` and the self-hosted
driver's `parseOptsGo` (`selfhost/Cli.wiz`) both parse it out of argv. The two drivers
distinguish two refusals, because they mean different things to a user:

* **unknown** — the name is not a target at all (a typo): `unknown target X (choose …)`;
* **unsupported** — the name is a target, but this toolchain has no backend for it:
  `unsupported target X: …`.

The host implements every name below, so every `supported` here is `true`. The
self-hosted driver knows the same five names and supports `c`/`llvm` (C5); its table is
in `selfhost/Cli.wiz` (`targetModes`, `targetOk`). The *names* and the unknown-target
sentence must agree between the two drivers — `Tests/Groups/SelfhostCliDiff.lean` pins
both — while the second sentence is where they legitimately differ.

A target is not an extern implementation: the `(declaration, target)` rows for foreign
functions are `IR.ExternImpl` (`Wiz/Compiler/IR.lean`), selected after elaboration.
-/

namespace Wiz

/-- A `--target` name and whether this compiler has a backend that can emit it. -/
structure Target where
  /-- the spelling `--target` takes -/
  name : String
  /-- does this toolchain have a backend for it? -/
  supported : Bool := true
  /-- why not, when `supported` is false -/
  reason : String := ""
  deriving Repr, DecidableEq, Inhabited

namespace Target

/-- Every target name, in the order the unknown-target refusal lists them. The host has
a backend for all five (`c`, `llvm`, `wasm`, `bpf`, `js`); the self-hosted driver knows
the same names and implements the first two. -/
def all : List Target :=
  [ { name := "c" }, { name := "llvm" }, { name := "wasm" }, { name := "bpf" },
    { name := "js" } ]

/-- The names as both drivers spell them in an unknown-target refusal. -/
def choices : String := "c, llvm, wasm, bpf or js"

/-- The entry for `n` in `ts`; `none` is an unknown name. The table is an argument so a
test can add or drop an entry without changing the CLI's table. -/
def ofNameIn (ts : List Target) (n : String) : Option Target :=
  ts.find? (·.name == n)

/-- The entry for `n` in the host's table. -/
def ofName? (n : String) : Option Target := ofNameIn all n

/-- The refusal of a name no table has. -/
def unknown (n : String) : String := s!"unknown target {n} (choose {choices})"

/-- The refusal of a name the table knows but this toolchain cannot emit. -/
def unsupported (t : Target) : String :=
  let why := if t.reason.isEmpty then "this toolchain has no backend for it" else t.reason
  s!"unsupported target {t.name}: {why}"

/-- The entry for `n`, or the refusal: unknown names and known-but-unsupported names are
different errors. -/
def resolve (ts : List Target) (n : String) : Except String Target :=
  match ofNameIn ts n with
  | none => throw (unknown n)
  | some t => if t.supported then pure t else throw (unsupported t)

end Target
end Wiz
