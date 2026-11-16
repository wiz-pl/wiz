import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- `norm_num` (closed arithmetic by the kernel's `rfl`) and `linarith` (linear
`Nat`/`Int`/`Q` goals), with their certificate boundary: every theorem mentions no
axiom, and false/nonlinear goals are refused with a message. -/
def arithTacticsGroup : Group where
  name := "arith-tactics"
  exercise := "the `norm_num` and `linarith` tactics (lib/NormNum.wiz, lib/Linarith.wiz)"
  cases := [
    { name := "norm_num: closed Nat, Int and Q arithmetic, and closed subterms of a symbolic goal", run := fun _ =>
        okLibs ("import NormNum\ndef a : 2 + 2 = 4 := by norm_num\n" ++
          "def b : (3 : Int) * 4 - 5 = 7 := by norm_num\n" ++
          "def c : Q.mk 1 2 rfl + Q.mk 1 3 rfl ≈ Q.mk 5 6 rfl := by norm_num\n" ++
          "def d (x : Nat) : x + (2 + 3) = x + 5 := by norm_num\n" ++
          "#print axioms a\n#print axioms b\n#print axioms c")
          ["'a' does not depend on any axioms",
           "'b' does not depend on any axioms",
           "'c' does not depend on any axioms"] },
    { name := "norm_num: a false closed Nat proposition is refused", run := fun _ =>
        failsLibs "import NormNum\ndef bad : (2 : Nat) + 2 = 5 := by norm_num"
          "norm_num: the closed arithmetic proposition is false" },
    { name := "norm_num: a false closed Int proposition is refused", run := fun _ =>
        failsLibs "import NormNum\ndef bad : (2 : Int) * 3 = 7 := by norm_num"
          "norm_num: the closed arithmetic proposition is false" },
    { name := "norm_num: a false closed Q proposition is refused", run := fun _ =>
        failsLibs "import NormNum\ndef bad : Q.mk 1 2 rfl ≈ Q.mk 2 3 rfl := by norm_num"
          "norm_num: the closed arithmetic proposition is false" },
    { name := "linarith: Nat, Int and Q inequalities, strict goals, and equality from two inequalities", run := fun _ =>
        okLibs ("import Linarith\ndef a (x y z : Int) (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by linarith\n" ++
          "def b (x y : Int) (h : x < y) : x + 1 ≤ y := by linarith\n" ++
          "def c (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a + 1 ≤ c + 1 := by linarith\n" ++
          "def d (a b : Nat) (h : a < b) : a + 1 ≤ b := by linarith\n" ++
          "def e (p q r : Q) (h1 : p ≤ q) (h2 : q < r) : p < r := by linarith\n" ++
          "def f (p q : Q) (h : 2 * p ≤ 2 * q) : p ≤ q := by linarith\n" ++
          "def g (x y : Int) (h1 : x ≤ y) (h2 : y ≤ x) : x = y := by linarith\n" ++
          "def h (x y : Int) (e : x = y) : y ≤ x := by linarith\n" ++
          "def i (x : Int) (h : False) : x ≤ x + 1 := by linarith\n" ++
          "#print axioms a\n#print axioms c\n#print axioms e\n#print axioms f")
          ["'a' does not depend on any axioms",
           "'c' does not depend on any axioms",
           "'e' does not depend on any axioms",
           "'f' does not depend on any axioms"] },
    { name := "linarith: a symbolic goal (an application is one atom) still closes", run := fun _ =>
        okLibs ("import Linarith\ndef a (f : Int → Int) (x : Int) : f x ≤ f x + 1 := by linarith\n" ++
          "def b (f : Nat → Nat) (x y : Nat) (h : f x ≤ f y) : f x + 2 ≤ f y + 2 := by linarith\n" ++
          "def c (f : Q → Q) (x y : Q) (h : f x < f y) : f x < f y + 1 := by linarith\n" ++
          "#print axioms a")
          ["'a' does not depend on any axioms"] },
    { name := "linarith: a false Nat goal is refused", run := fun _ =>
        failsLibs "import Linarith\ndef bad (a b : Nat) (h : a ≤ b) : b ≤ a := by linarith"
          "linarith: the goal does not follow" },
    { name := "linarith: a false Int goal is refused", run := fun _ =>
        failsLibs "import Linarith\ndef bad (x y : Int) (h : x < y) : y < x := by linarith"
          "linarith: the goal does not follow" },
    { name := "linarith: a false Q goal is refused", run := fun _ =>
        failsLibs "import Linarith\ndef bad (x y : Q) (h : x < y) : y ≤ x := by linarith"
          "linarith: the goal does not follow" },
    { name := "linarith: a nonlinear goal is refused", run := fun _ =>
        failsLibs "import Linarith\ndef bad (x y : Int) : x * y ≤ y * x := by linarith"
          "linarith: nonlinear term" },
    { name := "linarith: a nonlinear hypothesis is refused", run := fun _ =>
        failsLibs "import Linarith\ndef bad (x y : Int) (h : x * y ≤ 3) : x * y ≤ 4 := by linarith"
          "linarith: nonlinear term" },
    { name := "linarith: a Nat goal that needs a division is refused", run := fun _ =>
        failsLibs "import Linarith\ndef bad (a b : Nat) (h : 2 * a ≤ 2 * b) : a ≤ b := by linarith"
          "linarith: a Nat goal that needs a division" }
  ]

builtin_initialize registerGroup arithTacticsGroup

end Tests.Elab
