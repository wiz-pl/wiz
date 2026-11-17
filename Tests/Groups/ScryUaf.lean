import Wiz
import Tests.Harness

/-!
# Tests for the CWE-416 lifetime rule (`Scry.Lifetime`)

The Wil corpus is `lib/Scry/UafExamples.wiz`; the C end-to-end fixtures are
`scry/tests/fixtures/uaf-*.c`, driven by `scry/tests/uaf.wiz` (grail). Here we test the
engine directly: the `kind memory` rule pack, the alloc -> free -> use path, the
may-branch case, and the false-positive kills (free-then-null, realloc reassignment, a
reassigned alias).

Cases:

1. the pack has one `memory` rule with `check use-after-free`;
2. a load after free is one finding with path `alloc,free,sink`;
3. an alias after free is one finding;
4. a second free is one finding;
5. a free on one branch and a use after the merge is one finding (may);
6. free-then-null is silent;
7. `p = realloc(p, n)` reassignment is silent;
8. a reassigned alias is silent;
9. a free in a callee followed by a caller use is one finding whose free node is in
   the callee;
10. the default taint pack has no memory rule, so the lifetime rule is opt-in.
-/

open Wiz

namespace Tests.ScryUaf

def libLoader : IO (Name → Option String) := do
  let mut m : List (Name × String) := []
  for e in ← System.FilePath.readDir "lib" do
    if e.path.extension == some "wiz" then
      m := (e.path.fileStem.getD "", ← IO.FS.readFile e.path) :: m
    else if ← e.path.isDir then
      for f in ← System.FilePath.readDir e.path do
        if f.path.extension == some "wiz" then
          m := (e.fileName ++ "." ++ f.path.fileStem.getD "", ← IO.FS.readFile f.path) :: m
  for e in ← System.FilePath.readDir "scry/src/Scry" do
    if e.path.extension == some "wiz" then
      m := ("Scry." ++ e.path.fileStem.getD "", ← IO.FS.readFile e.path) :: m
  pure fun n => m.lookup n

def imports : String :=
  "import Scry.UafExamples\n" ++
  "import Scry.Rules\n" ++
  "import Scry.RuleExamples\n" ++
  "import Scry.Interproc\n" ++
  "import Scry.Lifetime\n"

def runProbe (body : String) : IO (List String) := do
  let src := imports ++ body ++ "\n"
  let loader ← libLoader
  let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do
    throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  pure (s.messages.toList.map (·.text))

def evalTexts (body : String) (expected : List String) : IO Unit := do
  checkEq expected (← runProbe body)

def prelude : String :=
  "def pKinds (p : List Scry.PathNode) : String :=\n" ++
  "  String.intercalate \",\" (List.map (fun n => Scry.PathKind.show n.kind) p)\n" ++
  "def nthF : List Scry.PathNode → Nat → String\n" ++
  "  | .nil, _ => \"\"\n" ++
  "  | .cons p _, .zero => p.func\n" ++
  "  | .cons _ ps, .succ k => nthF ps k\n" ++
  "def findings (prog : Wil.Program) : List Scry.RuleFinding :=\n" ++
  "  Scry.programFindings (Scry.analyze prog Scry.uafRules)\n" ++
  "def count (prog : Wil.Program) : Nat := List.length (findings prog)\n" ++
  "def firstPath (prog : Wil.Program) : List Scry.PathNode :=\n" ++
  "  match findings prog with | .cons f _ => f.path | .nil => []\n" ++
  "def demoCount (prog : Wil.Program) : Nat :=\n" ++
  "  List.length (Scry.programFindings (Scry.analyze prog Scry.demoRules))\n"

/-- The `#eval`s of `body` are `expected`, in order. -/
def evalNats (body : String) (expected : List Nat) : IO Unit := do
  checkEq (expected.map toString) (← runProbe (prelude ++ body))

/-- Path and function expectations are strings; the body prints `String`s. -/
def evalStrings (body : String) (expected : List String) : IO Unit := do
  checkEq expected (← runProbe (prelude ++ body))

def group : Group :=
  { name := "scry-uaf"
    exercise := "Scry CWE-416 (lifetime rule: alloc -> free -> use paths and false-positive kills)"
    parallel := true
    cases := [
      { name := "pack: one memory rule, check use-after-free"
        run := fun _ => evalStrings
          ("#eval match Scry.RulePack.memoryRuleFor Scry.uafRules \"use-after-free\" with\n" ++
           "  | .some r => r.check\n" ++
           "  | .none => \"missing\"\n" ++
           "#eval match Scry.RulePack.memoryRuleFor Scry.uafRules \"use-after-free\" with\n" ++
           "  | .some r => Scry.FindingKind.show (Scry.PackRule.kind (.memory r))\n" ++
           "  | .none => \"missing\"\n")
          [ "\"use-after-free\"", "\"memory\"" ] },
      { name := "dangling load: one finding, alloc -> free -> sink"
        run := fun _ => evalStrings
          "#eval count Scry.uafDangling\n#eval pKinds (firstPath Scry.uafDangling)\n"
          [ "1", "\"alloc,free,sink\"" ] },
      { name := "alias after free: one finding"
        run := fun _ => evalNats "#eval count Scry.uafAlias\n" [1] },
      { name := "double free: one finding"
        run := fun _ => evalNats "#eval count Scry.uafDoubleFree\n" [1] },
      { name := "conditional free then merge use: one may finding"
        run := fun _ => evalNats "#eval count Scry.uafConditional\n" [1] },
      { name := "free-then-null: silent"
        run := fun _ => evalNats "#eval count Scry.uafSafeNull\n" [0] },
      { name := "realloc reassignment: silent"
        run := fun _ => evalNats "#eval count Scry.uafSafeRealloc\n" [0] },
      { name := "reassigned alias: silent"
        run := fun _ => evalNats "#eval count Scry.uafSafeReassignAlias\n" [0] },
      { name := "interprocedural free: one finding, free in release"
        run := fun _ => evalStrings
          "#eval count Scry.uafInterproc\n#eval nthF (firstPath Scry.uafInterproc) 1\n"
          [ "1", "\"release\"" ] },
      { name := "default pack has no memory rule (opt-in)"
        run := fun _ => evalNats
          ("#eval List.length (Scry.RulePack.memoryRules Scry.demoRules)\n" ++
           "#eval demoCount Scry.uafDangling\n")
          [0, 0] }
    ] }

builtin_initialize registerGroup group

end Tests.ScryUaf
