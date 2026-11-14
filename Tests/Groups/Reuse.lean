import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- Programs for the reuse tests: functions that take a cell apart and rebuild it after one
or two `case`s on a `Bool` returned by a call; a zipper insertion into a binary tree;
and a structure updated through calls (`record`, as `drafts/feral/lowered/07`). -/
def reuseSrc : String := "import Prelude
inductive T where
  | a (x : Nat) (y : Nat)
  | b (x : Nat) (y : Nat)
def small : Nat → Bool
  | .zero => .true
  | .succ _ => .false
def f (t : T) : T := match t with
  | .a x y => (match small x with
    | .true => T.b y x
    | .false => T.a y x)
  | .b x y => T.b y x
def g (t : T) : T := match t with
  | .a x y => (match small x with
    | .true => (match small y with
      | .true => T.b y x
      | .false => T.a x x)
    | .false => T.a y x)
  | .b x y => T.b y x
def h (t u : T) : T := match t with
  | .a x y => (match small x with
    | .true => u
    | .false => T.a y x)
  | .b x y => T.b y x
structure Stats where
  hits : Nat
  misses : Nat
def step (n : Nat) : Option Nat := match small n with
  | .true => .none
  | .false => .some (Nat.succ n)
def bump2 (a b : Nat) : Option (Nat × Nat) := match step a with
  | .some a => .some (a, Nat.succ (Nat.succ b))
  | .none => .none
def record (s : Stats) : Option Stats := match s with
  | (h, m, _) => match step h with
    | .some h => (match bump2 h m with
      | .some r => .some (Stats.mk r.1 r.2)
      | .none => .none)
    | .none => .none
inductive Tree where
  | leaf
  | node (key : Nat) (left : Tree) (right : Tree)
inductive Path where
  | top
  | inLeft (key : Nat) (right : Tree) (up : Path)
  | inRight (key : Nat) (left : Tree) (up : Path)
def Path.plug : Path → Tree → Tree
  | .top, t => t
  | .inLeft key right up, t => Path.plug up (Tree.node key t right)
  | .inRight key left up, t => Path.plug up (Tree.node key left t)
def Tree.insert (k : Nat) : Tree → Path → Tree
  | .node key left right, path => (match Nat.lt k key with
    | .true => Tree.insert k left (Path.inLeft key right path)
    | .false => match Nat.lt key k with
      | .true => Tree.insert k right (Path.inRight key left path)
      | .false => Path.plug path (Tree.node key left right))
  | .leaf, path => Path.plug path (Tree.node k .leaf .leaf)
def spine : Nat → Nat → Tree
  | i, .zero => Tree.leaf
  | i, .succ m => Tree.node i Tree.leaf (spine (Nat.succ i) m)
def ta : T := T.a 1 2
def fa : T := f (T.a 1 2)
def fb : T := f (T.a 0 2)
def ga : T := g (T.a 0 0)
def gb : T := g (T.a 0 1)
def gc : T := g (T.a 1 1)
def ha : T := h (T.a 0 5) (T.b 1 1)
def hb : T := h (T.a 1 5) (T.b 1 1)
def s0 : Stats := Stats.mk 1 2
def r0 : Option Stats := record (Stats.mk 1 2)
def t10 : Tree := spine 1 10
def t20 : Tree := spine 1 20
def z10 : Tree := Tree.insert 11 (spine 1 10) Path.top
def z20 : Tree := Tree.insert 21 (spine 1 20) Path.top
"

def reuseState : IO (CommandState ZeroOneMany) := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let s := runFrontend (R := ZeroOneMany) reuseSrc { trustedModule := Tests.libModule, loader := fun m => if m == "Prelude" then some prelude else none }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render reuseSrc
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  pure s

/-- Run each entry point of `reuseSrc` through the optimised IR on the checked heap: the
objects allocated (a leak, or using a freed object, is an error). -/
def reuseAllocs (entries : List Name) : IO (List Nat) := do
  let s ← reuseState
  entries.mapM fun n => do
    let r : Except String Nat := do
      let code ← (compileReachable s.globals s.builtins [n]).mapError toString
      let decls ← IR.lowerProgram code (.global n)
      let (_, a) ← IR.runProgram (IR.optimizeProgram decls)
      pure a
    match r with
    | .ok a => pure a
    | .error e => throw (IO.userError s!"{n}: {e}")

/-- The optimised IR of a function of `reuseSrc`, as lines. -/
def reuseIR (n : Name) : IO (List String) := do
  let s ← reuseState
  match (do
      let code ← (compileReachable s.globals s.builtins [n]).mapError toString
      IR.lowerProgram code (.global n) : Except String (Array IR.Decl)) with
  | .ok decls =>
    let d := ((IR.optimizeProgram decls).find? (·.name == n)).get!
    pure ((d.toString.splitOn "\n").map (·.trimAscii.toString))
  | .error e => throw (IO.userError e)

/-- Only the parameter `x0` is reset (a `Bool` returned by `small` is never paired). -/
def onlyParamReset (n : Name) : IO Unit := do
  let ls ← reuseIR n
  let resets := ls.filter fun l => (l.splitOn ":= reset").length > 1
  check (!resets.isEmpty && resets.all (·.endsWith ":= reset x0")) s!"resets: {resets}\n{"\n".intercalate ls}"

def reuseGroup : Group where
  name := "reuse"
  exercise := "Stage 8c"
  cases := [
    { name := "across one case: the cell is rebuilt in both branches, no allocation", run := fun _ => do
        checkEq [1, 1, 1] (← reuseAllocs ["ta", "fa", "fb"])
        onlyParamReset "f" },
    { name := "across nested cases", run := fun _ => do
        checkEq [1, 1, 1] (← reuseAllocs ["ga", "gb", "gc"])
        onlyParamReset "g" },
    { name := "a branch that doesn't rebuild frees the token (no leak)", run := fun _ => do
        checkEq [2, 2] (← reuseAllocs ["ha", "hb"])
        let ls ← reuseIR "h"
        check (ls.any fun l => l.endsWith ":= reuse x1000000 in ctor 0") s!"no freed token:\n{"\n".intercalate ls}" },
    { name := "a Bool returned by a call is never reset", run := fun _ => do
        onlyParamReset "f"; onlyParamReset "g"; onlyParamReset "h" },
    { name := "a zipper insertion allocates nothing per level", run := fun _ => do
        let [t10, t20, z10, z20] ← reuseAllocs ["t10", "t20", "z10", "z20"] | throw (IO.userError "?")
        -- the tree, and the new node
        checkEq (t10 + 1, t20 + 1) (z10, z20) },
    { name := "a structure updated through calls reuses its own cells, in place", run := fun _ => do
        let [s0, r0] ← reuseAllocs ["s0", "r0"] | throw (IO.userError "?")
        let ls ← reuseIR "record"
        -- `Stats` is one pair since 22i (its last field is unboxed): the parameter's cell
        -- holds the new one
        check (ls.any fun l => (l.splitOn ":= reuse x1000000 in ctor 0 ").length > 1 &&
            ((l.splitOn ":= reuse x1000000 in ctor 0 ")[1]!.splitOn " ").length == 2)
          s!"the parameter's cell is not rebuilt in place:\n{"\n".intercalate ls}"
        -- the two `step`s' options and bump2's result (an option and a pair) are the only
        -- allocations: the new `Stats` takes the parameter's cell
        checkEq (s0 + 4) r0 },
    { name := "renaming a body renames reset and reuse", run := fun _ => do
        let b : IR.Body := .vdecl 5 (.reset 1) (.vdecl 6 (.reuse 5 0 #[2, 3]) (.ret 6))
        let σ : Std.HashMap IR.Var IR.Var := ({} : Std.HashMap _ _).insert 1 10 |>.insert 2 20 |>.insert 3 30
        let ls := ((IR.Body.rename σ b).toString.splitOn "\n").map (·.trimAscii.toString)
        checkEq ["let x5 := reset x10", "let x6 := reuse x5 in ctor 0 x20 x30", "ret x6"] ls }
  ]

builtin_initialize registerGroup reuseGroup

end Tests.Elab
