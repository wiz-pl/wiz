import Wiz
import Wiz.Actions
import Tests.Harness
import Tests.Reject

/-!
# `diagnostics`: one root error, and the fix named

The three structural defects of `wiz-notes/diagnostics-quality.md` (2026-11-22), each as a
program with its expected output:

* a failed declaration is poisoned: later references say `'broken' failed to elaborate`
  with the root error as a *related* diagnostic, never `unknown identifier`;
* a missing import is named (a `deriving` class, an unknown module, `Array`, `Inhabited`)
  from a loader-aware index, and the quick fix adds one `import M` per file;
* a mismatch is classified before unification (`wrong-argument-count` for a missing
  argument, for a tuple pattern's arity), a field of a hole is `unsolved-hole` at the
  `_`, and the mismatch carries a path to the first differing subterm.
-/

namespace Tests.DiagnosticsGroup

open Wiz
open Tests.Reject

def run (src : String) : IO (CommandState ZeroOneMany) := do
  pure (runFrontend (R := ZeroOneMany) src (← stateFor []))

def errors (src : String) : IO (Array Msg) := do
  let s ← run src
  pure (s.messages.filter (·.severity == .error))

def findErr (errs : Array Msg) (frag : String) : IO Msg := do
  match errs.find? (fun m => m.text.contains frag) with
  | some m => pure m
  | none => throw (IO.userError s!"no error mentions {repr frag}:\n{"\n".intercalate (errs.toList.map (·.text))}")

def moduleSources (s : CommandState ZeroOneMany) : List (Name × String) :=
  s.modules.toList.filterMap fun m => (s.loader m).map fun src => (m, src)

def importActions (s : CommandState ZeroOneMany) (src : String) (m : Name) : Array Actions.Action :=
  (Actions.actionsAt s src 0 src.length (moduleSources s)).filter fun a => a.title == s!"Add `import {m}`"

-- Fix 1: a failed declaration is poisoned, not an unknown name
def poisoned : Case where
  name := "a failed declaration is poisoned: one root error, references say so (no unknown-identifier cascade)"
  run := fun _ => do
    let src := "import Prelude\ndef broken : Nat := Bool.true\ndef uses : Nat := broken\ndef uses2 : Nat := Nat.succ uses\n"
    let errs ← errors src
    checkEq 3 errs.size
    let root ← findErr errs "type mismatch"
    check (root.code == ErrorCode.typeMismatch) s!"root code: {root.code}"
    check ((spanText src root).contains "Bool.true") s!"root span: {repr (spanText src root)}"
    let uses ← findErr errs "'broken' failed to elaborate"
    check (uses.code == ErrorCode.failedDeclaration) s!"uses code: {uses.code}"
    checkEq 1 uses.related.size
    check (uses.related[0]!.info.start == root.info.start && uses.related[0]!.info.stop == root.info.stop)
      "the related diagnostic is not the root error's span"
    check (uses.related[0]!.code == ErrorCode.typeMismatch) s!"related code: {uses.related[0]!.code}"
    let uses2 ← findErr errs "'uses' failed to elaborate"
    check (uses2.code == ErrorCode.failedDeclaration) s!"uses2 code: {uses2.code}"
    check (!uses2.related.isEmpty) "uses2 has no related diagnostic"
    check (!errs.any fun m => m.text.contains "unknown identifier") "a fictional unknown identifier remains"

-- Fix 2: loader-aware import repair
def derivingImport : Case where
  name := "deriving Repr, BEq without `import Deriving`: one missing-import, one deduped fix"
  run := fun _ => do
    let src := "import Prelude\ninductive X where\n  | x\n  deriving Repr, BEq\n"
    let s ← run src
    let errs := s.messages.filter (·.severity == .error)
    checkEq 1 errs.size
    let e := errs[0]!
    check (e.code == ErrorCode.missingImport) s!"code: {e.code}"
    check (e.text.contains "`Repr` and `BEq` are derived by module `Deriving`") e.text
    check ((spanText src e).contains "deriving") s!"span: {repr (spanText src e)}"
    checkEq 1 (importActions s src "Deriving").size
    check (!errs.any fun m => m.text.contains "no deriver") "the deriver registration message remains"

def moduleSpelling : Case where
  name := "import Prelud: unknown-module names the closest module"
  run := fun _ => do
    let errs ← errors "import Prelud\ndef x : Nat := 1\n"
    checkEq 1 errs.size
    let e := errs[0]!
    check (e.code == ErrorCode.unknownModule) s!"code: {e.code}"
    check (e.text.contains "did you mean 'Prelude'?") e.text

def arrayImport : Case where
  name := "Array without `import Std`: the missing import is named, and offered once for the file"
  run := fun _ => do
    let src := "import Prelude\ndef x : Array Nat := Array.empty\n"
    let s ← run src
    let errs := s.messages.filter (·.severity == .error)
    check (!errs.isEmpty) "accepted Array without Std"
    check (errs.any fun m => m.text.contains "declared in module `Std`" && m.text.contains "add `import Std`")
      s!"errors:\n{"\n".intercalate (errs.toList.map (·.text))}"
    checkEq 1 (importActions s src "Std").size

def inhabitedImport : Case where
  name := "Inhabited without `import Text`: the class's module is named"
  run := fun _ => do
    let src := "import Prelude\ndef n : Nat := Inhabited.default\n"
    let errs ← errors src
    check (!errs.isEmpty) "accepted Inhabited without Text"
    check (errs.any fun m => m.text.contains "declared in module `Text`" &&
      m.text.contains "add `import Text`") s!"errors:\n{"\n".intercalate (errs.toList.map (·.text))}"

-- Fix 3: classify before unifying, hole at `_`, a structured diff
def arityAndHole : Case where
  name := "missing argument, tuple arity and a field of a hole: classified, not type mismatches"
  run := fun _ => do
    let src := "import Prelude\ndef add1 : Nat := Nat.add 1\ndef badTuple (p : Nat × Bool) : Nat :=\n  match p with\n  | (a, b, c) => a\ndef badField (p : _) : Nat := p.x\n"
    let errs ← errors src
    let add1 ← findErr errs "is missing 1 argument"
    check (add1.code == ErrorCode.wrongArgumentCount) s!"add1 code: {add1.code}"
    check (add1.text.contains "`Nat.add`") add1.text
    check (add1.text.contains "(2 explicit parameters, 1 given)") add1.text
    let tuple ← findErr errs "this pattern has 3 components"
    check (tuple.code == ErrorCode.wrongArgumentCount) s!"tuple code: {tuple.code}"
    check (tuple.text.contains "has 2") tuple.text
    check ((spanText src tuple).contains "a, b, c") s!"tuple span: {repr (spanText src tuple)}"
    let hole ← findErr errs "the type of p is not known"
    check (hole.code == ErrorCode.unsolvedHole) s!"hole code: {hole.code}"
    check (!hole.text.contains "?m0") "the internal meta name leaked"
    check ((spanText src hole) == "_") s!"hole span: {repr (spanText src hole)}"
    check (!errs.any fun m => m.text.contains "a tuple pattern needs a pair") "the tuple message remains"
    check (!errs.any fun m => m.text.contains "no field 'x'") "the field message remains"

def mismatchDiff : Case where
  name := "a type mismatch carries a structured diff with a path to the first differing subterm"
  run := fun _ => do
    let src := "import Prelude\ndef f : Nat → Nat → Nat := Nat.add 1\n"
    let errs ← errors src
    let e ← findErr errs "type mismatch"
    check (e.code == ErrorCode.typeMismatch) s!"code: {e.code}"
    let some d := e.mismatch | throw (IO.userError "the message has no mismatch diff")
    check (d.kind == "argument") s!"kind: {d.kind}"
    check (d.path == [1]) s!"path: {repr d.path}"
    check (d.expectedAt == "Nat" && d.inferredAt == "Nat → Nat")
      s!"diff at: {repr (d.expectedAt, d.inferredAt)}"

/-- The group: the three fixtures, the no-cascade assertion, the suggestions. -/
def group : Group where
  name := "diagnostics"
  exercise := "diagnostics quality: poison, import repair, structured mismatch"
  shard := "library"
  cases := [
    poisoned,
    derivingImport,
    moduleSpelling,
    arrayImport,
    inhabitedImport,
    arityAndHole,
    mismatchDiff
  ]

builtin_initialize registerGroup group

end Tests.DiagnosticsGroup
