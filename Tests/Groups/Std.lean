import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

def stdGroup : Group where
  name := "std"
  exercise := "Stage 12a"
  cases := [
    -- (7e) integers
    { name := "integers: arithmetic, literals, printing", run := fun _ =>
        okLibs ("import Int\n#eval (-3 : Int) * 4 + 2\n#eval (5 : Int) - 8\n#eval (-7 : Int) / 2\n#eval (-7 : Int) % 2\n" ++
          "def t : (-3 : Int) * 4 + 2 = -10 := rfl\ndef u (a : Int) : 0 + a = a := Int.zero_add a\n#run (2 : Int) - 3 * 4\n#eval Int.natAbs (-5)\n" ++
          "#eval Int.lt (-2) 1\n#eval Int.toNat (-4)")
          ["-10", "-3", "-3", "-1", "-10", "5", ".true", "0"] },
    { name := "integers: lemmas, and printing needs no axiom", run := fun _ =>
        okLibs ("import Int\n#check Int.neg_neg\n#check Int.add_zero\n#print axioms Int.add_zero")
          ["Int.neg_neg : (a : Int) → - -a = a",
           "Int.add_zero : (a : Int) → a + 0 = a",
           "'Int.add_zero' does not depend on any axioms"] },
    { name := "integers: compiled (C)", run := fun _ =>
        cRunLibs "import Int\ndef main : Int := (-3 : Int) * 4 + 2" "-10" },
    { name := "7f: x + 1 and 1 + x at words, Int and BitVec: the numeral takes the operand's type", run := fun _ =>
        okLibs ("import Word\nimport Int\nimport BitVec\ndef a (x : U8) : U8 := x + 1\ndef b (x : U8) : U8 := 1 + x\n" ++
          "def c (x : Int) : Int := 1 - x * 2\ndef d (x : BitVec 8) : BitVec 8 := x + 1\ndef e (x : U32) : U32 := x + (1 + 2) * 3\n" ++
          "def f (xs : List U8) : List U8 := List.cons 1 xs\n#eval (a 255).toNat\n#eval (b 1).toNat\n#eval c 5\n#eval (d 7).toNat\n#eval (e 1).toNat\n" ++
          "def g (x : I16) := 2 * x - 1\n#eval (g 3).toNat")
          ["0", "2", "-9", "8", "10", "5"] },
    { name := "order notation: ≤, < and ≈ are classes (lib/Order.wiz)", run := fun _ =>
        okLibs ("import Order\ndef Bool.Le (a b : Bool) : Prop := Bool.or (Bool.not a) b = .true\n" ++
          "instance : LE Bool := LE.mk Bool.Le\ninstance : Equiv Bool := Equiv.mk (fun a b => a = b)\n" ++
          "def t : Bool.false ≤ Bool.true := rfl\ndef u : Bool.true ≈ Bool.true := rfl\n#check Bool.false ≤ Bool.true")
          ["Bool.false ≤ Bool.true : Prop"] },
    -- arithmetic library: lib/Nat.wiz, Ring.wiz, IntRing.wiz, IntOrder.wiz, Rat.wiz
    { name := "naturals: semiring laws, the order as a proposition, ≤ notation", run := fun _ =>
        okLibs ("import Nat\n#check Nat.mul_add\n#check Nat.le_trans\n" ++
          "def a (n : Nat) : n ≤ n + 1 := Nat.le_add_right n 1\ndef b : Nat.Le 2 5 := rfl\ndef c : (3 : Nat) < 4 := rfl\n" ++
          "def d (m n : Nat) (h : m ≤ n) (h' : n ≤ m) : m = n := Nat.le_antisymm m n h h'\n#print axioms Nat.mul_assoc")
          ["Nat.mul_add : (a : Nat) → (b : Nat) → (c : Nat) → a * (b + c) = a * b + a * c",
           "Nat.le_trans : (a : Nat) → (b : Nat) → (c : Nat) → Nat.Le a b → Nat.Le b c → Nat.Le a c",
           "'Nat.mul_assoc' does not depend on any axioms"] },
    { name := "nat_ring! proves semiring identities by reflection", run := fun _ =>
        okLibs ("import Ring\ndef t (a b c : Nat) : (a + b) * (a + c) = a * a + a * c + b * a + b * c :=\n" ++
          "  nat_ring! (a + b) * (a + c) = a * a + a * c + b * a + b * c\n" ++
          "def u (n : Nat) : Nat.succ n * 2 = n + n + 2 := nat_ring! Nat.succ n * 2 = n + n + 2\n" ++
          "def v (f : Nat → Nat) (x : Nat) : f x * (x + 1) = x * f x + f x := nat_ring! f x * (x + 1) = x * f x + f x\n" ++
          "#print axioms t") ["'t' does not depend on any axioms"] },
    { name := "nat_ring! rejects an equation that is not an identity", run := fun _ =>
        failsLibs "import Ring\ndef bad (a b : Nat) : a + b = a * b := nat_ring! a + b = a * b" "not definitionally equal" },
    { name := "int_ring! and the ring laws of Int", run := fun _ =>
        okLibs ("import IntRing\ndef t (a b : Int) : (a - b) * (a + b) = a * a - b * b := int_ring! (a - b) * (a + b) = a * a - b * b\n" ++
          "def u (a b c : Int) : -(a - b) * c + a * c = b * c := int_ring! -(a - b) * c + a * c = b * c\n" ++
          "#check Int.mul_comm\n#check Int.neg_mul\n#print axioms Int.mul_add")
          ["Int.mul_comm : (a : Int) → (b : Int) → a * b = b * a",
           "Int.neg_mul : (a : Int) → (b : Int) → -a * b = - (a * b)",
           "'Int.mul_add' does not depend on any axioms"] },
    { name := "int_ring! rejects an equation that is not an identity", run := fun _ =>
        failsLibs "import IntRing\ndef bad (a b : Int) : a - b = b - a := int_ring! a - b = b - a" "not definitionally equal" },
    { name := "the order of Int, absolute value, the triangle inequality", run := fun _ =>
        okLibs ("import IntOrder\ndef a (x y : Int) (h : x ≤ y) : x + 1 ≤ y + 1 := Int.add_le_add_right 1 x y h\n" ++
          "def b : (-2 : Int) < 3 := rfl\ndef c (x y : Int) : Int.abs (x + y) ≤ Int.abs x + Int.abs y := Int.abs_add x y\n" ++
          "#check Int.abs_sub_le\n#print axioms Int.abs_sub_le")
          ["Int.abs_sub_le : (a : Int) → (b : Int) → (c : Int) → Int.Le (Int.abs (a - c)) (Int.abs (a - b) + Int.abs (b - c))",
           "'Int.abs_sub_le' does not depend on any axioms"] },
    { name := "rationals: an ordered field up to ≈, and q_ring!", run := fun _ =>
        okLibs ("import Rat\ndef half : Q := Q.mk 1 2 rfl\ndef a : half + half ≈ 1 := rfl\ndef b : half < 1 := rfl\n" ++
          "def c (p q : Q) : (p + q) * (p + q) ≈ p * p + 2 * p * q + q * q := q_ring! (p + q) * (p + q) ≈ p * p + 2 * p * q + q * q\n" ++
          "def d (p q r : Q) (h : p ≤ q) (h' : q < r) : p < r := Q.lt_of_le_of_lt h h'\n" ++
          "#eval (Q.div 1 half).num\n#check Q.mul_inv\n#check Q.abs_sub_le\n#print axioms Q.lt_ceil")
          ["2", "Q.mul_inv : (p : Q) → ¬p.1 = 0 → p * Q.inv p ≈ 1",
           "Q.abs_sub_le : (p : Q) → (q : Q) → (r : Q) → Q.abs (p - r) ≤ Q.abs (p - q) + Q.abs (q - r)",
           "'Q.lt_ceil' does not depend on any axioms"] },
    { name := "ring: the tactic reads the goal (Nat, Int, ≈ at Q; binders introduced)", run := fun _ =>
        okLibs ("import RingTactic\ndef a (x y : Int) : (x - y) * (x + y) = x * x - y * y := by ring\n" ++
          "def b : (m n : Nat) → Nat.succ m * n = n + m * n := by ring\n" ++
          "def c (p q : Q) : (p + q) * (p - q) ≈ p * p - q * q := by ring\n" ++
          "def d (f : Int → Int) (x : Int) : f x * (x + 1) - f (x) = x * f x := by ring\n" ++
          "def e (x : Int) : (x + 2) * (x - 3) = x * x - x - 6 := by ring\n#print axioms c")
          ["'c' does not depend on any axioms"] },
    { name := "ring: a false identity is reported with both sides", run := fun _ =>
        failsLibs "import RingTactic\ndef bad (a b : Int) : a - b = b - a := by ring" "ring: not an identity of commutative rings" },
    { name := "ring: a goal that is not an equation of a ring", run := fun _ =>
        failsLibs "import RingTactic\ndef bad (x : Bool) : x = x := by ring" "ring: the goal is an equation, but not at Nat or Int" },
    { name := "machine types: operators at UInt64 and Float64", run := fun _ =>
        okLibs "import IO\ndef f (a b : UInt64) : UInt64 := a * b + 1\ndef g (x : Float64) : Float64 := x * x - 2 / 3" },
    { name := "arrays, updated in place", run := fun _ =>
        ioRun ("import Std\ndef fill : Nat → Array Nat → Array Nat\n  | .zero, a => a\n  | .succ n, a => Array.push (fill n a) (n * n)\n" ++
          "def main : IO Unit := do\n  let a := fill 10 Array.empty;\n  IO.println (Nat.toString (Array.getD a 9 0));\n" ++
          "  IO.println (Nat.toString (Array.getD (Array.set a 9 5) 9 0));\n  IO.println (Nat.toString (Array.getD a 9 0))")
          "81\n5\n81\n" },
    { name := "native text", run := fun _ =>
        ioRun ("import Std\ndef main : IO Unit := do\n  let t := Str.append (Str.ofString \"hello, \") (Str.ofString \"world\");\n" ++
          "  IO.println (Str.toString (Str.slice t 7 12));\n  IO.println (Nat.toString (Str.size t))") "world\n12\n" },
    { name := "maps from text", run := fun _ =>
        ioRun ("import Std\ndef count : List String → StrMap Nat → StrMap Nat\n  | .nil, m => m\n" ++
          "  | .cons w ws, m => count ws (StrMap.insert m (Str.ofString w) (StrMap.findD m (Str.ofString w) 0 + 1))\n" ++
          "def main : IO Unit := do\n  let m := count (.cons \"a\" (.cons \"b\" (.cons \"a\" .nil))) StrMap.empty;\n" ++
          "  IO.println (Nat.toString (StrMap.findD m (Str.ofString \"a\") 0));\n  IO.println (Nat.toString (StrMap.size m))") "2\n2\n" }
  ]

builtin_initialize registerGroup stdGroup

end Tests.Elab
