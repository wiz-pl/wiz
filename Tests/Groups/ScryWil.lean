import Wiz
import Tests.Harness

/-!
# Tests for `Scry.Wil` (the IR and its concrete semantics)

The programs are hand-built in `lib/Scry/WilExamples.wiz`; each case evaluates a property
of `Wil.runFunction` with `#eval` (so no C toolchain is needed) and compares the `Nat`
it evaluates to with the expected list. The differential cases compare the IR's result
with a direct Wiz computation of the same function: when the C frontend lands, the same
shape of test adds a third computation (compiled C).
-/

open Wiz

namespace Tests.ScryWil

/-- Every `lib/*.wiz` and `lib/D/*.wiz` (as `D.X`), by module name. -/
def libLoader : IO (Name → Option String) := do
  let mut m : List (Name × String) := []
  for e in ← System.FilePath.readDir "lib" do
    if e.path.extension == some "wiz" then
      m := (e.path.fileStem.getD "", ← IO.FS.readFile e.path) :: m
    else if ← e.path.isDir then
      for f in ← System.FilePath.readDir e.path do
        if f.path.extension == some "wiz" then
          m := (e.fileName ++ "." ++ f.path.fileStem.getD "", ← IO.FS.readFile f.path) :: m
  pure fun n => m.lookup n

/-- `body` (which imports the libraries) has no errors, and its `#eval` messages are
`expected`, in order (each a `Nat`). -/
def evalNats (body : String) (expected : List Nat) : IO Unit := do
  let src := "import Scry.Wil\nimport Scry.WilExamples\nimport Text\n" ++ body ++ "\n"
  let loader ← libLoader
  let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do
    throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  checkEq (expected.map toString) (s.messages.toList.map (·.text))

def group : Group where
  name := "scry-wil"
  exercise := "Scry S2 (Wil)"
  cases := [
    { name := "arithmetic: three-address add and multiply",
      run := fun _ => evalNats
        "#eval match Wil.runFunction Scry.arith 100 \"main\" [] with\n  | .ok v => Wil.Val.bitsAt 32 v\n  | _ => 0" [14] },
    { name := "branch: max of (10, 3)",
      run := fun _ => evalNats
        "#eval match Wil.runFunction Scry.maxOf 100 \"max\" [Scry.i32 10, Scry.i32 3] with\n  | .ok v => Wil.Val.bitsAt 32 v\n  | _ => 0" [10] },
    { name := "branch (other arm): max of (3, 10)",
      run := fun _ => evalNats
        "#eval match Wil.runFunction Scry.maxOf 100 \"max\" [Scry.i32 3, Scry.i32 10] with\n  | .ok v => Wil.Val.bitsAt 32 v\n  | _ => 0" [10] },
    { name := "direct calls: inc twice, 2 -> 4",
      run := fun _ => evalNats
        "#eval match Wil.runFunction Scry.incTwice 100 \"main\" [] with\n  | .ok v => Wil.Val.bitsAt 32 v\n  | _ => 0" [4] },
    { name := "recursive direct call: sumTo 10",
      run := fun _ => evalNats
        "#eval match Wil.runFunction Scry.sumTo 500 \"sum\" [Scry.i32 10] with\n  | .ok v => Wil.Val.bitsAt 32 v\n  | _ => 0" [55] },
    { name := "a back edge that terminates: 5!",
      run := fun _ => evalNats
        "#eval match Wil.runFunction Scry.facLoop 1000 \"fac\" [] with\n  | .ok v => Wil.Val.bitsAt 32 v\n  | _ => 0" [120] },
    { name := "signed arithmetic: (-7) / 2 = -3",
      run := fun _ => evalNats
        "#eval match Wil.runFunction Scry.signedDiv 100 \"main\" [] with\n  | .ok v => Wil.Val.bitsAt 32 v\n  | _ => 0" [4294967293] },
    { name := "signed arithmetic: (-7) % 2 = -1",
      run := fun _ => evalNats
        "#eval match Wil.runFunction Scry.signedRem 100 \"main\" [] with\n  | .ok v => Wil.Val.bitsAt 32 v\n  | _ => 0" [4294967295] },
    { name := "unsigned arithmetic wraps at the width",
      run := fun _ => evalNats
        "#eval match Wil.runFunction Scry.wrapAdd 100 \"main\" [] with\n  | .ok v => Wil.Val.bitsAt 32 v\n  | _ => 0" [1] },
    { name := "memory: alloc, store, load",
      run := fun _ => evalNats
        "#eval match Wil.runFunction Scry.storeLoad 100 \"main\" [] with\n  | .ok v => Wil.Val.bitsAt 32 v\n  | _ => 0" [7] },
    { name := "memory: a pointer computed by gep",
      run := fun _ => evalNats
        "#eval match Wil.runFunction Scry.gepLoad 100 \"main\" [] with\n  | .ok v => Wil.Val.bitsAt 32 v\n  | _ => 0" [5] },
    { name := "memory: a load one past the end faults",
      run := fun _ => evalNats
        "#eval match Wil.runFunction Scry.oobLoad 100 \"main\" [] with\n  | .fault m => match String.eq m \"load: out of bounds at 0+4\" with\n    | .true => 1\n    | .false => 0\n  | _ => 0" [1] },
    { name := "memory: a load after free faults",
      run := fun _ => evalNats
        "#eval match Wil.runFunction Scry.danglingLoad 100 \"main\" [] with\n  | .fault m => match String.eq m \"load: freed block 0\" with\n    | .true => 1\n    | .false => 0\n  | _ => 0" [1] },
    { name := "an assume that is false faults",
      run := fun _ => evalNats
        "#eval match Wil.runFunction Scry.assumeFalse 100 \"main\" [] with\n  | .fault m => match String.eq m \"infeasible: assumption is false\" with\n    | .true => 1\n    | .false => 0\n  | _ => 0" [1] },
    { name := "an infinite loop runs out of fuel (and only fuel stops it)",
      run := fun _ => evalNats
        "#eval match Wil.runFunction Scry.spin 20 \"main\" [] with\n  | .outOfFuel => 1\n  | _ => 0" [1] },
    { name := "the step relation: an entry configuration has a successor",
      run := fun _ => evalNats
        "#eval match Wil.entry Scry.arith \"main\" [] with\n  | .ok c => match Wil.step c with\n    | .next _ => 1\n    | _ => 0\n  | .error _ => 0" [1] },
    { name := "differential: Wil arithmetic agrees with Wiz arithmetic",
      run := fun _ => evalNats
        "#eval match Wil.runFunction Scry.arith 100 \"main\" [] with\n  | .ok v => match Nat.beq (Wil.Val.bitsAt 32 v) (2 + 3 * 4) with\n    | .true => 1\n    | .false => 0\n  | _ => 0" [1] },
    { name := "differential: Wil's recursive sum agrees with a direct Wiz recursion",
      run := fun _ => evalNats
        "def sumRef : Nat → Nat\n  | .zero => 0\n  | .succ n => Nat.add (.succ n) (sumRef n)\n#eval match Wil.runFunction Scry.sumTo 500 \"sum\" [Scry.i32 10] with\n  | .ok v => match Nat.beq (Wil.Val.bitsAt 32 v) (sumRef 10) with\n    | .true => 1\n    | .false => 0\n  | _ => 0" [1] },
    { name := "differential: Wil's iterative factorial agrees with a Wiz recursion",
      run := fun _ => evalNats
        "def factRef : Nat → Nat\n  | .zero => 1\n  | .succ n => Nat.mul (.succ n) (factRef n)\n#eval match Wil.runFunction Scry.facLoop 1000 \"fac\" [] with\n  | .ok v => match Nat.beq (Wil.Val.bitsAt 32 v) (factRef 5) with\n    | .true => 1\n    | .false => 0\n  | _ => 0" [1] }
  ]

builtin_initialize registerGroup group

end Tests.ScryWil
