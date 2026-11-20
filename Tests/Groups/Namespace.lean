import Tests.Elab
import Tests.Reject

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-! (13t) `namespace` and `open`: declarations under a dotted prefix, unqualified use
from an `open`, prefix aliases (`open M as A`), the ambiguity error, and the interaction
with `private` and `end`.

The self-hosted frontend mirrors these commands (`selfhost/Frontend.wiz`); its cases are
in `Tests/Groups/SelfHost.lean`. -/

/-- No errors, and exactly these messages (the `#check` lines), from a program with the
given modules importable. -/
def nsOk (mods : List (Name × String)) (src : String) (infos : List String) : IO Unit := do
  let s := runFrontend (R := ZeroOneMany) src { loader := fun n => mods.lookup n }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  checkEq (repr infos).pretty (repr (s.messages.toList.map (·.text))).pretty

/-- Exactly one error, mentioning `fragment`, from a program with the given modules
importable. -/
def nsFails (mods : List (Name × String)) (src : String) (fragment : String) : IO Unit := do
  let s := runFrontend (R := ZeroOneMany) src { loader := fun n => mods.lookup n }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.size == 1 do throw (IO.userError s!"expected one error, got {errs.size}: {errs}")
  unless (errs[0]!.splitOn fragment).length > 1 do
    throw (IO.userError s!"error does not mention '{fragment}':\n{errs[0]!}")

/-- Exactly one error, with `code` and mentioning `fragment`, from a program with the
given modules importable. -/
def nsFailsCode (mods : List (Name × String)) (src : String) (code fragment : String) : IO Unit := do
  let s := runFrontend (R := ZeroOneMany) src { loader := fun n => mods.lookup n }
  let errs := s.messages.filter (·.severity == .error)
  unless errs.size == 1 do throw (IO.userError s!"expected one error, got {errs.size}: {errs.map (·.render src)}")
  let m := errs[0]!
  unless m.code == code do
    throw (IO.userError s!"expected code '{code}', got '{m.code}':\n{m.render src}")
  unless (m.text.splitOn fragment).length > 1 do
    throw (IO.userError s!"error does not mention '{fragment}':\n{m.render src}")

/-- The nested-namespace program: `A.B.x`, `A.y` (which uses `B.x` through `A`), and
`#check`s of the qualified names. -/
def nestedNs : String :=
  "namespace A\nnamespace B\ndef x : Unit := ()\ndef y : Unit := x\nend B\n" ++
  "def z : Unit := B.x\nend A\n#check A.B.x\n#check A.B.y\n#check A.z\n"

def openUse : String :=
  "namespace A\ndef x : Unit := ()\ndef y : Unit := x\nend A\n" ++
  "open A\ndef use : Unit := x\n#check x\n#check use\n"

def twoOpens : String :=
  "namespace A\ndef x : Unit := ()\nend A\nnamespace B\ndef x : Unit := ()\nend B\n" ++
  "open A\nopen B\ndef use : Unit := x\n"

def openAndDecl : String :=
  "namespace A\ndef x : Unit := ()\nend A\ndef x : Unit := ()\nopen A\ndef use : Unit := x\n"

def openedTwice : String :=
  "namespace A\ndef x : Unit := ()\nend A\nopen A\nopen A\ndef use : Unit := x\n#check use\n"

def aliasPrefix : String :=
  "namespace A\ndef x : Unit := ()\nend A\n" ++
  "open A as Al\ndef use : Unit := Al.x\n#check Al.x\n"

def aliasNotOpen : String :=
  "namespace A\ndef x : Unit := ()\nend A\n" ++
  "open A as Al\ndef use : Unit := x\n"

/-- A module with a private and a public declaration in a namespace. -/
def privMod : String :=
  "namespace Secret\nprivate def hidden : Unit := ()\ndef shown : Unit := ()\nend Secret\n"

def privThroughOpen : String :=
  "import Priv\nopen Secret\ndef a : Unit := shown\ndef b : Unit := hidden\n"

def privThroughAlias : String :=
  "import Priv\nopen Secret as S\ndef a : Unit := S.shown\ndef b : Unit := S.hidden\n"

/-- A qualified name needs no `open`, and `secret` is usable in its own module. -/
def privQualified : String :=
  "import Priv\ndef a : Unit := Secret.shown\n"

def openOutlivesNamespace : String :=
  "namespace A\ndef x : Unit := ()\nend A\nnamespace B\nopen A\nend B\n" ++
  "def use : Unit := x\n#check use\n"

/-- `open` in a module is file-scoped: it does not reach an importer. -/
def openerMod : String :=
  "namespace A\ndef x : Unit := ()\nend A\nopen A\ndef y : Unit := x\n"

def importedOpenDoesNotLeak : String :=
  "import Op\ndef z : Unit := x\n"

def missingEnd : String := "namespace A\ndef x : Unit := ()\n"

def strayEnd : String := "def x : Unit := ()\nend\n"

def wrongEnd : String := "namespace A\ndef x : Unit := ()\nend B\n"

/-- (13v) `namespace __root__` opens the root for a block: the declarations in it keep
their written (global) names, and `end __root__` closes it. -/
def rootBlock : String :=
  "namespace __root__\ndef r : Unit := ()\ndef A.x : Unit := ()\nend __root__\n" ++
  "#check r\n#check A.x\n"

/-- (13v) `namespace __root__.P` opens the root-level `P`, and a nested namespace inside a
root block is root-level too. -/
def rootDotted : String :=
  "namespace __root__.Shared\ndef g : Unit := ()\nend Shared\n" ++
  "open __root__.Shared\ndef use : Unit := g\n" ++
  "namespace __root__\nnamespace Inner\ndef h : Unit := ()\nend Inner\nend\n" ++
  "#check Shared.g\n#check Inner.h\n#check use\n"

/-- (13v) `def __root__.x` declares the true global `x`, and `__root__.x` names it. -/
def rootDecl : String :=
  "namespace N\ndef __root__.x : Unit := ()\nend N\n#check x\n#check __root__.x\n"

/-- (13v) `__root__` is a leading segment only. -/
def rootMisplaced : String := "namespace N\ndef A.__root__.x : Unit := ()\nend N\n"

def rootBare : String := "def __root__ : Unit := ()\n"

def mutualNs : String :=
  "namespace N\nmutual\ninductive A where\n  | mk (b : B)\ninductive B where\n  | mk (a : A)\nend\n" ++
  "def a (b : B) : A := A.mk b\nend N\n#check N.A\n#check N.B\n"

/-- A module with a namespace that another file opens. -/
def mathMod : String :=
  "namespace M\ndef double (n : Unit) : Unit := n\nend M\n"

def openAcrossModules : String :=
  "import Math\nopen M\ndef use : Unit := double ()\n#check use\n"

/-- `open` is not transitive: `Outer` opens `I`, but opening `Outer` does not open `I`. -/
def innerMod : String := "namespace I\ndef x : Unit := ()\nend I\n"

def outerMod : String :=
  "import Inner\nnamespace Outer\nopen I\ndef y : Unit := x\nend Outer\n"

def openNotTransitive : String := "import Outer\nopen Outer\ndef z : Unit := x\n"

/-- A module's name is not a namespace: its declarations are named as written in it. -/
def plainMod : String := "def double (n : Unit) : Unit := n\n"

def moduleNameNotNamespace : String := "import Plain\nopen Plain\n"

/-- `open B as A` shadows a real namespace `A` for qualified names. -/
def aliasShadows : String :=
  "namespace A\ndef x : Unit := ()\nend A\nnamespace B\ndef x : Unit := ()\nend B\n" ++
  "open B as A\ndef use : Unit := A.x\n#check A.x\n"

/-- A local binder shadows the opened `A.x`, and the bound name is the binder's (a `Type`
global would not typecheck as a `Unit`); outside the binder the open still applies. -/
def localShadows : String :=
  "namespace A\ndef x : Type := Unit\nend A\nopen A\n" ++
  "def f (x : Unit) : Unit := x\ndef g : Type := x\n#check g\n"

/-- A module whose namespace holds only a private name: opening it there makes the
private name unqualified, and `shown` proves it. -/
def privOnlyMod : String :=
  "namespace Secret\nprivate def hidden : Unit := ()\nend Secret\nopen Secret\n" ++
  "def shown : Unit := hidden\n"

def privOnlyOpen : String := "import PrivOnly\ndef a : Unit := shown\n#check a\n"

def namespaceGroup : Group where
  name := "namespace"
  exercise := "Stage 13t"
  cases := [
    { name := "nested namespaces: A.B.x, a member used through the enclosing namespace, #check shows the qualified name", run := fun _ =>
        nsOk [] nestedNs ["A.B.x : Unit", "A.B.y : Unit", "A.z : Unit"] },
    { name := "a qualified name works with no `open`", run := fun _ =>
        nsOk [] "namespace A\ndef x : Unit := ()\nend A\ndef use : Unit := A.x\n#check use\n" ["use : Unit"] },
    { name := "`open A` then an unqualified use; #check shows A.x", run := fun _ =>
        nsOk [] openUse ["A.x : Unit", "use : Unit"] },
    { name := "two opens with the same name: the use is ambiguous, naming both", run := fun _ =>
        nsFailsCode [] twoOpens "ambiguous-name" "'x' is ambiguous: it refers to 'A.x', 'B.x'; qualify it with a namespace" },
    { name := "an open and a declaration with the same name: the use is ambiguous", run := fun _ =>
        nsFailsCode [] openAndDecl "ambiguous-name" "'x' is ambiguous: it refers to 'A.x', 'x'; qualify it with a namespace" },
    { name := "opening the same namespace twice is one candidate, not an ambiguity", run := fun _ =>
        nsOk [] openedTwice ["use : Unit"] },
    { name := "`open A as Al` makes Al.x a spelling of A.x", run := fun _ =>
        nsOk [] aliasPrefix ["A.x : Unit"] },
    { name := "`open A as Al` does not open A unqualified", run := fun _ =>
        nsFails [] aliasNotOpen "unknown identifier 'x'" },
    { name := "a private name is not reachable through an open", run := fun _ =>
        nsFails [("Priv", privMod)] privThroughOpen "unknown identifier 'hidden'" },
    { name := "a private name is not reachable through an alias: the private error names the module", run := fun _ =>
        nsFails [("Priv", privMod)] privThroughAlias "'Secret.hidden' is private to module Priv" },
    { name := "a qualified public name works without an open", run := fun _ =>
        nsOk [("Priv", privMod)] privQualified [] },
    { name := "a namespace with only this module's private names opens in that module", run := fun _ =>
        nsOk [("PrivOnly", privOnlyMod)] privOnlyOpen ["a : Unit"] },
    { name := "`open` a namespace declared in another module", run := fun _ =>
        nsOk [("Math", mathMod)] openAcrossModules ["use : Unit"] },
    { name := "`open` is not transitive: an importer's `open` does not open what it opened", run := fun _ =>
        nsFails [("Inner", innerMod), ("Outer", outerMod)] openNotTransitive "unknown identifier 'x'" },
    { name := "an `open` names a namespace, not a module: a module's name opens nothing", run := fun _ =>
        nsFails [("Plain", plainMod)] moduleNameNotNamespace "unknown namespace 'Plain'" },
    { name := "an `open … as` alias shadows a real namespace of the same prefix", run := fun _ =>
        nsOk [] aliasShadows ["B.x : Unit"] },
    { name := "a local binder shadows a name the `open` provides", run := fun _ =>
        nsOk [] localShadows ["g : Type"] },
    { name := "wiz check: an `open` across two modules", run := fun _ =>
        Tests.Reject.cliCheck openAcrossModules [("Math", mathMod)] false },
    { name := "wiz check: an ambiguous name is a command-line error", run := fun _ =>
        Tests.Reject.cliCheck twoOpens [] true },
    { name := "an `open` is file-scoped: it outlives its namespace's `end`", run := fun _ =>
        nsOk [] openOutlivesNamespace ["use : Unit"] },
    { name := "an `open` in a module does not reach the files that import it", run := fun _ =>
        nsFails [("Op", openerMod)] importedOpenDoesNotLeak "unknown identifier 'x'" },
    { name := "a namespace with no `end` is reported at its own line", run := fun _ =>
        nsFailsCode [] missingEnd "unclosed-namespace" "namespace A is not closed: add `end` (or `end A`)" },
    { name := "a stray `end` is an error at its own line", run := fun _ =>
        nsFails [] strayEnd "`end` without an open `namespace`" },
    { name := "`end B` that does not close `A` is an error", run := fun _ =>
        nsFails [] wrongEnd "`end B` does not close the namespace `A`" },
    { name := "mutual inductive types under a namespace", run := fun _ =>
        nsOk [] mutualNs ["N.A : Type", "N.B : Type"] },
    { name := "(13v) `namespace __root__` keeps the block's declarations global; `end __root__` closes it", run := fun _ =>
        nsOk [] rootBlock ["r : Unit", "A.x : Unit"] },
    { name := "(13v) `namespace __root__.P` is the root-level P; a namespace nested in a root block is root-level", run := fun _ =>
        nsOk [] rootDotted ["Shared.g : Unit", "Inner.h : Unit", "use : Unit"] },
    { name := "(13v) `def __root__.x` declares the true global x, reachable as x and as __root__.x", run := fun _ =>
        nsOk [] rootDecl ["x : Unit", "x : Unit"] },
    { name := "(13v) `__root__` not as the first segment of a name is an error", run := fun _ =>
        nsFailsCode [] rootMisplaced "root-name" "only meaningful as the first segment" },
    { name := "(13v) a declaration named exactly `__root__` is an error", run := fun _ =>
        nsFailsCode [] rootBare "root-name" "only meaningful as the first segment" }
  ]

builtin_initialize registerGroup namespaceGroup

end Tests.Elab
