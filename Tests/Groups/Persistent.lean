import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- A user file that declares its own `Tree` and imports `PMap`: the library's internal
tree is namespaced (`PMap.Tree`), so the two do not clash. The file also exercises the
public map and set operations, a user `Compare` instance, and duplicate replacement. -/
def userTreeSrc : String :=
  "import PMap\n" ++
  "inductive Tree (A : Type) where\n  | leaf\n  | node (l : Tree A) (x : A) (r : Tree A)\n" ++
  "def Tree.size {A : Type} : Tree A → Nat\n  | .leaf => 0\n  | .node l _ r => Nat.succ (Nat.add (Tree.size l) (Tree.size r))\n" ++
  "def t : Tree Nat := .node (.node .leaf 1 .leaf) 2 (.node .leaf 3 .leaf)\n" ++
  "inductive Key where\n  | mk (a : Nat) (b : Nat)\n" ++
  "def Key.a : Key → Nat\n  | .mk a _ => a\n" ++
  "def Key.b : Key → Nat\n  | .mk _ b => b\n" ++
  "def Key.cmp (x y : Key) : Ordering :=\n" ++
  "  Ordering.andThen (Nat.cmp (Key.a x) (Key.a y)) (Nat.cmp (Key.b x) (Key.b y))\n" ++
  "instance : Compare Key := Compare.mk Key.cmp\n" ++
  "def m : PMap Key Nat :=\n" ++
  "  PMap.fromList [(Key.mk 2 1, 21), (Key.mk 1 2, 12), (Key.mk 1 1, 11), (Key.mk 2 1, 22)]\n" ++
  "def s : PSet Nat := PSet.fromList [3, 1, 2, 1]\n" ++
  "#eval Tree.size t\n" ++
  "#eval PMap.size m\n" ++
  "#eval PMap.findD m (Key.mk 1 2) 0\n" ++
  "#eval PMap.findD m (Key.mk 2 1) 0\n" ++
  "#eval PMap.size (PMap.erase m (Key.mk 1 1))\n" ++
  "#eval PSet.toList s\n" ++
  "#eval PSet.contains s 2\n"

/-- Persistent maps and sets (`lib/PMap.wiz`): `examples/persistent.wiz` checks
persistence, the BST invariant, sorted `toList`, round trips, a differential test against
`U64Map`, the expected laws, structural sharing, sets and a generic key type, returning 0
when all hold. `examples/persistent-bench.wiz` with no arguments prints the checksums of
its three modes (the persistent tree, `U64Map`'s list model and the native `U64Map`),
which must agree. -/
def persistentGroup : Group where
  name := "persistent"
  exercise := "persistent data structures: lib/PMap.wiz (PMap, PSet), examples/persistent.wiz"
  cases := [
    { name := "the model (#eval) passes every check", run := fun _ => do
        let src ← IO.FS.readFile "examples/persistent.wiz"
        okLibs (src ++ "\n#eval main\n") ["0"] },
    { name := "compiled (C) passes every check", run := fun _ => do
        let src ← IO.FS.readFile "examples/persistent.wiz"
        cRunLibs src "0" },
    { name := "compiled (LLVM) passes every check", run := fun _ => do
        let src ← IO.FS.readFile "examples/persistent.wiz"
        cRunLibs src "0" (llvm := true) },
    { name := "a user Tree does not clash with the library's PMap.Tree", run := fun _ => do
        okLibs userTreeSrc ["3", "3", "12", "22", "2", ".cons 1 (.cons 2 (.cons 3 .nil))", ".true"] },
    { name := "the benchmark: the tree, U64Map's model and the native U64Map agree", run := fun _ => do
        let src ← IO.FS.readFile "examples/persistent-bench.wiz"
        cRunLibs src "86477693 86477693 86477693\n" }
  ]

builtin_initialize registerGroup persistentGroup

end Tests.Elab
