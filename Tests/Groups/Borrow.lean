import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- Programs for the borrowing tests (stage 8e): functions that only look at their
argument, a closure over one, and a pair taken apart at once. -/
def borrowSrc : String := "import Prelude
def len : List Nat → Nat
  | .nil => 0
  | .cons _ xs => Nat.succ (len xs)
def sumAcc : Nat → List Nat → Nat
  | acc, .nil => acc
  | acc, .cons x xs => sumAcc (Nat.add acc x) xs
inductive Tree where
  | leaf
  | node (key : Nat) (left : Tree) (right : Tree)
def Tree.mem (k : Nat) : Tree → Bool
  | .leaf => .false
  | .node key l r => match Nat.lt k key with
    | .true => Tree.mem k l
    | .false => match Nat.lt key k with
      | .true => Tree.mem k r
      | .false => .true
def mapL (f : List Nat → Nat) : List (List Nat) → List Nat
  | .nil => .nil
  | .cons x xs => .cons (f x) (mapL f xs)
-- (not a bare constructor: that would be inlined, and the match on it folded away, 15c)
def split (xs : List Nat) : List Nat × List Nat := (xs, List.append xs .nil)
def both (xs : List Nat) : Nat := match split xs with
  | (a, b) => Nat.add (len a) (len b)
def t3 : Tree := Tree.node 2 (Tree.node 1 .leaf .leaf) (Tree.node 3 .leaf .leaf)
"

/-- The optimised IR of a function of `borrowSrc`, as lines. -/
def borrowIR (n : Name) : IO (List String) := do
  let s := runFrontend (R := ZeroOneMany) borrowSrc { trustedModule := Tests.libModule, loader := ← preludeLoader }
  match (do
      let code ← (compileReachable s.globals s.builtins [n]).mapError toString
      IR.lowerProgram code (.global n) : Except String (Array IR.Decl)) with
  | .ok decls =>
    let d := ((IR.optimizeProgram decls).find? (·.name == n)).get!
    pure ((d.toString.splitOn "\n").map (·.trimAscii.toString))
  | .error e => throw (IO.userError e)

/-- Parameter `x{i}` of `n` is borrowed and never counted. -/
def borrowedUncounted (n : Name) (i : Nat) : IO Unit := do
  let ls ← borrowIR n
  let hdr := ls.headD ""
  check ((hdr.splitOn s!"@&x{i} ").length > 1 || hdr.endsWith s!"@&x{i} :=") s!"x{i} not borrowed:\n{"\n".intercalate ls}"
  check (!ls.any fun l => l == s!"dup x{i}" || l == s!"drop x{i}") s!"x{i} counted:\n{"\n".intercalate ls}"

/-- A program that projects field 1 of a number (the old unary-view fallback: since
`proj` is borrowed, the objects it made would leak). Lowering never emits this. -/
def projOfNumber : Array IR.Decl :=
  #[{ name := "wiz.entry", params := #[],
      body := .vdecl 0 (.lit 5) (.vdecl 1 (.proj 1 0) (.ret 1)) }]

def borrowGroup : Group where
  name := "borrow"
  exercise := "Stage 8e"
  cases := [
    { name := "the length of a list borrows it", run := fun _ => borrowedUncounted "len" 0 },
    { name := "a left fold borrows the list (and its tail call is a loop)", run := fun _ => do
        borrowedUncounted "sumAcc" 1
        let ls ← borrowIR "sumAcc"
        -- (a self tail call is a jump to a loop, 15f)
        check (ls.any fun l => l.startsWith "jmp ") s!"no loop:\n{"\n".intercalate ls}" },
    { name := "a lookup in a tree borrows the tree", run := fun _ => borrowedUncounted "Tree.mem" 1 },
    { name := "comparisons borrow: the key and the keys it meets are not counted", run := fun _ => do
        borrowedUncounted "Tree.mem" 0
        let ls ← borrowIR "Tree.mem"
        check (!ls.any fun l => l.startsWith "dup " || l.startsWith "drop ") s!"counted:\n{"\n".intercalate ls}"
        -- big numbers are objects: a borrowing comparison must neither free nor leak them
        let big := "1180591620717411303424"
        cRun (borrowSrc ++ s!"def tb : Tree := Tree.node (Nat.add {big} 2) (Tree.node {big} .leaf .leaf) .leaf\n" ++
          s!"def b2n : Bool → Nat\n  | .true => 1\n  | .false => 0\n" ++
          s!"def main : Nat := Nat.add (b2n (Tree.mem {big} tb)) (Nat.add (b2n (Tree.mem (Nat.add {big} 1) tb)) (b2n (Tree.mem (Nat.add {big} 2) tb)))\n") "2" },
    { name := "borrowing functions run without leaks", run := fun _ =>
        okLib (borrowSrc ++ "#run len (.cons 1 (.cons 2 .nil))\n#run sumAcc 0 (.cons 1 (.cons 2 .nil))\n#run Tree.mem 3 t3\n#run Tree.mem 4 t3")
          ["2", "3", ".true", ".false"] },
    { name := "a closure over a borrowing function goes through an owned wrapper", run := fun _ => do
        okLib (borrowSrc ++ "#run mapL len (.cons (.cons 1 .nil) (.cons .nil .nil))") [".cons 1 (.cons 0 .nil)"]
        let s := runFrontend (R := ZeroOneMany) (borrowSrc ++ "def lens : List Nat := mapL len (.cons .nil .nil)\n") { trustedModule := Tests.libModule, loader := ← preludeLoader }
        match (do
            let code ← (compileReachable s.globals s.builtins ["lens"]).mapError toString
            IR.lowerProgram code (.global "lens") : Except String (Array IR.Decl)) with
        | .ok decls =>
          let ds := IR.optimizeProgram decls
          check (ds.any (·.name == "len._owned")) "no wrapper"
          check (ds.all fun d => (d.toString.splitOn "pap len ").length == 1) "len partially applied directly"
        | .error e => throw (IO.userError e) },
    { name := "drop specialisation: a unique pair taken apart moves its fields", run := fun _ => do
        let ls ← borrowIR "both"
        check (ls.any fun l => (l.splitOn "prim dropMoved").length > 1) s!"no specialised drop:\n{"\n".intercalate ls}"
        okLib (borrowSrc ++ "#run both (.cons 1 (.cons 2 .nil))") ["4"] },
    { name := "proj of a field of a number stops the IR interpreter and the C runtime", run := fun _ => do
        match IR.runProgram projOfNumber with
        | .ok _ => throw (IO.userError "the IR interpreter projected a number")
        | .error e => check ((e.splitOn "internal error: proj 1 of the number 5").length > 1) e
        let dir ← IO.FS.createTempDir
        let exe := dir / "proj"
        match ← Build.compileC (← toolchain) (C.program projOfNumber) exe with
        | .error e =>
          if (e.splitOn "gmp.h").length > 1 then skip "no toolchain" else throw (IO.userError e)
        | .ok () =>
          let out ← IO.Process.output { cmd := exe.toString }
          checkEq 3 out.exitCode
          check ((out.stderr.splitOn "internal error: proj").length > 1) out.stderr },
    { name := "borrowing and drop specialisation in C", run := fun _ =>
        cRun (borrowSrc ++ "def main : Nat := Nat.add (both (.cons 1 (.cons 2 .nil))) (len (mapL len (.cons .nil .nil)))\n") "5" }
  ]

builtin_initialize registerGroup borrowGroup

end Tests.Elab
