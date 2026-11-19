import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- `lib/FingerTree.wiz`: the level-indexed finger tree, the `Monoid`/`Measure`
interface, the size and measure laws, and the deque laws. The last case also pins the
kernel restriction that forced the level index (the textbook non-uniform tree is
rejected). -/
def fingerTreeGroup : Group where
  name := "finger-tree"
  exercise := "stdlib: lib/FingerTree.wiz"
  parallel := true
  cases := [
    { name := "the tree checks: push, pushFront, append, get and ofList read back", run := fun _ =>
        okLibs ("import FingerTree\n" ++
          "def q : Seq Nat := Seq.push (Seq.push (Seq.push Seq.empty 1) 2) 3\n" ++
          "#eval Seq.toList q\n" ++
          "#eval Seq.size q\n" ++
          "#eval Seq.get q 1\n" ++
          "#eval Seq.get q 9\n" ++
          "#eval Seq.toList (Seq.ofList [1, 2, 3, 4, 5])\n" ++
          "#eval Seq.toList (Seq.pushFront q 0)\n" ++
          "#eval Seq.toList (Seq.append q (Seq.ofList [4, 5]))\n")
          [
            ".cons 1 (.cons 2 (.cons 3 .nil))",
            "3",
            ".some 2",
            ".none",
            ".cons 1 (.cons 2 (.cons 3 (.cons 4 (.cons 5 .nil))))",
            ".cons 0 (.cons 1 (.cons 2 (.cons 3 .nil)))",
            ".cons 1 (.cons 2 (.cons 3 (.cons 4 (.cons 5 .nil))))"
          ] },
    { name := "the size and measure laws, over Nat and over a non-commutative monoid", run := fun _ =>
        okLibs ("import FingerTree\n" ++
          "def natLaw : Monoid.Lawful (Monoid.mk 0 Nat.add) :=\n" ++
          "  (Nat.add_assoc, (fun a => rfl, Nat.add_zero))\n" ++
          "instance : Measure Nat Nat := Measure.mk (fun n => n)\n" ++
          "instance : Monoid (List Nat) := Monoid.mk List.nil List.append\n" ++
          "def listLaw : Monoid.Lawful (Monoid.mk List.nil List.append) :=\n" ++
          "  (List.append_assoc (A := Nat), (fun a => rfl, List.append_nil))\n" ++
          "instance : Measure Nat (List Nat) := Measure.mk (fun n => List.cons n List.nil)\n" ++
          "def q : Seq Nat := Seq.ofList [1, 2, 3]\n" ++
          "def sizeLaw : Seq.size q = List.length (Seq.toList q) := FT.size_eq q\n" ++
          "def measureLaw : (Seq.measure q : Nat) = (listMeasure (Seq.toList q) : Nat) :=\n" ++
          "  FT.measure_eq natLaw q\n" ++
          "def listMeasureLaw : (Seq.measure q : List Nat) = (listMeasure (Seq.toList q) : List Nat) :=\n" ++
          "  FT.measure_eq listLaw q\n" ++
          "def mq : Nat := Seq.measure q\n" ++
          "def lq : List Nat := Seq.measure q\n" ++
          "#eval mq\n" ++
          "#eval lq\n" ++
          "#eval Nat.beq (Seq.size q) 3\n")
          [
            "6",
            ".cons 1 (.cons 2 (.cons 3 .nil))",
            ".true"
          ] },
    { name := "the deque laws: push, pushFront, catenate, pop, popFront", run := fun _ =>
        okLibs ("import FingerTree\n" ++
          "def q : Seq Nat := Seq.ofList [1, 2, 3]\n" ++
          "def r : Seq Nat := Seq.ofList [4, 5]\n" ++
          "def pushLaw : Seq.toList (Seq.push q 4) = List.append (Seq.toList q) [4] :=\n" ++
          "  FT.toList_push q (.base 4)\n" ++
          "def pushFrontLaw : Seq.toList (Seq.pushFront q 0) = List.append [0] (Seq.toList q) :=\n" ++
          "  FT.toList_pushFront q (.base 0)\n" ++
          "def appendLaw : Seq.toList (Seq.append q r) =\n" ++
          "    List.append (Seq.toList q) (Seq.toList r) := Seq.toList_append q r\n" ++
          "def ofListLaw : Seq.toList q = [1, 2, 3] :=\n" ++
          "  Seq.toList_ofList (A := Nat) [1, 2, 3]\n" ++
          "def appendSizeLaw : Seq.size (Seq.append q r) =\n" ++
          "    Nat.add (Seq.size q) (Seq.size r) := Seq.size_append q r\n" ++
          "def popQ : Option (List Nat × Nat) :=\n" ++
          "  match Seq.pop q with\n" ++
          "  | .some (t, x) => .some (Seq.toList t, x)\n" ++
          "  | .none => .none\n" ++
          "def popFrontQ : Option (List Nat × Nat) :=\n" ++
          "  match Seq.popFront q with\n" ++
          "  | .some (t, x) => .some (Seq.toList t, x)\n" ++
          "  | .none => .none\n" ++
          "#eval popQ\n" ++
          "#eval popFrontQ\n")
          [
            ".some (.cons 1 (.cons 2 .nil), 3)",
            ".some (.cons 2 (.cons 3 .nil), 1)"
          ] },
    { name := "ten elements across the levels: four pops and popFronts rebuild the middle", run := fun _ =>
        okLibs ("import FingerTree\n" ++
          "def q5 : Seq Nat := Seq.ofList [0, 1, 2, 3, 4]\n" ++
          "def q : Seq Nat := Seq.push (Seq.push (Seq.push (Seq.push (Seq.push q5 5) 6) 7) 8) 9\n" ++
          "def popN : Nat → Seq Nat → Option (Seq Nat × Nat)\n" ++
          "  | .zero, _ => .none\n" ++
          "  | .succ k, s => match Seq.pop s with\n" ++
          "    | .none => .none\n" ++
          "    | .some (t, x) => match k with\n" ++
          "      | .zero => .some (t, x)\n" ++
          "      | .succ _ => popN k t\n" ++
          "def popFrontN : Nat → Seq Nat → Option (Seq Nat × Nat)\n" ++
          "  | .zero, _ => .none\n" ++
          "  | .succ k, s => match Seq.popFront s with\n" ++
          "    | .none => .none\n" ++
          "    | .some (t, x) => match k with\n" ++
          "      | .zero => .some (t, x)\n" ++
          "      | .succ _ => popFrontN k t\n" ++
          "def pop4List : Option (List Nat × Nat) :=\n" ++
          "  match popN 4 q with\n" ++
          "  | .some (t, x) => .some (Seq.toList t, x)\n" ++
          "  | .none => .none\n" ++
          "def front4List : Option (List Nat × Nat) :=\n" ++
          "  match popFrontN 4 q with\n" ++
          "  | .some (t, x) => .some (Seq.toList t, x)\n" ++
          "  | .none => .none\n" ++
          "#eval pop4List\n" ++
          "#eval front4List\n" ++
          "#eval Seq.get q 9\n" ++
          "#eval Seq.get q 10\n" ++
          "#eval Seq.size q\n" ++
          "#eval Seq.toList (Seq.pushFront q 100)\n")
          [
            ".some (.cons 0 (.cons 1 (.cons 2 (.cons 3 (.cons 4 (.cons 5 .nil))))), 6)",
            ".some (.cons 4 (.cons 5 (.cons 6 (.cons 7 (.cons 8 (.cons 9 .nil))))), 3)",
            ".some 9",
            ".none",
            "10",
            ".cons 100 (.cons 0 (.cons 1 (.cons 2 (.cons 3 (.cons 4 (.cons 5 (.cons 6 (.cons 7 (.cons 8 (.cons 9 .nil))))))))))"
          ] },
    { name := "the textbook non-uniform tree is what the kernel rejects (the design note)", run := fun _ =>
        failsLibs ("import FingerTree\n" ++
          "inductive NonUniform (A : Type) where\n" ++
          "  | empty\n" ++
          "  | deep (middle : NonUniform (List A))\n")
          "must use the same parameters" }
  ]

builtin_initialize registerGroup fingerTreeGroup

end Tests.Elab
