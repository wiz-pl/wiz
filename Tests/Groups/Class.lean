import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- (7e) A type with numeric instances: `Z3` is the integers mod 3. -/
def numClassSrc : String := "import Prelude
inductive Z3 where
  | a
  | b
  | c
def Z3.ofNat (n : Nat) : Z3 := match Nat.mod n 3 with
  | .zero => .a
  | .succ .zero => .b
  | _ => .c
def Z3.toNat : Z3 → Nat
  | .a => 0
  | .b => 1
  | .c => 2
instance {ω n : Nat} : OfNat Z3 n := OfNat.mk (Z3.ofNat n)
instance : Add Z3 := Add.mk (fun x y => Z3.ofNat (Z3.toNat x + Z3.toNat y))
instance : Mul Z3 := Mul.mk (fun x y => Z3.ofNat (Z3.toNat x * Z3.toNat y))
instance : Neg Z3 := Neg.mk (fun x => Z3.ofNat (3 - Z3.toNat x))
instance : Sub Z3 := Sub.mk (fun x y => Z3.ofNat (Z3.toNat x + (3 - Z3.toNat y)))
"

def classGroup : Group where
  name := "classes"
  exercise := "Exercise 7.1"
  cases := [
    { name := "methods take the instance as an instance-implicit argument", run := fun _ =>
        okLib (classPrelude ++ "#check Inhabited.default") ["Inhabited.default : {A : Type} → [self : Inhabited A] → A"] },
    { name := "an instance is found", run := fun _ =>
        okLib (classPrelude ++ "#eval (Inhabited.default : Bool)") [".true"] },
    { name := "instances with instance arguments chain", run := fun _ =>
        okLib (classPrelude ++ "#eval (Inhabited.default : List (List Nat))") [".cons (.cons 0 .nil) .nil"] },
    { name := "local instances", run := fun _ =>
        okLib (classPrelude ++ "def orDefault {A : Type} [Inhabited A] : Option A → A\n  | .some a => a\n  | .none => Inhabited.default\n" ++
          "#eval orDefault (Option.none : Option Bool)") [".true"] },
    { name := "a missing instance is an error", run := fun _ =>
        failsLib (classPrelude ++ "#eval (Inhabited.default : String)") "failed to synthesize an instance of Inhabited String" },
    { name := "output parameters are determined by the instance", run := fun _ =>
        okLib ("import Prelude\nclass MixAdd (A B : Type) (C : outParam Type) where\n  hadd : A → B → C\n" ++
          "instance : MixAdd Nat Bool Nat where\n  hadd := fun n b => n\n#check MixAdd.hadd (3 : Nat) Bool.true")
          ["MixAdd.hadd Nat Bool Nat instMixAddNatBoolNat (3 : Nat) Bool.true : Nat"] },
    { name := "later instances win", run := fun _ =>
        okLib (classPrelude ++ "instance : Inhabited Nat := Inhabited.mk 7\n#eval (Inhabited.default : Nat)") ["7"] },
    { name := "priorities", run := fun _ =>
        okLib (classPrelude ++ "instance (priority := 2000) : Inhabited Nat := Inhabited.mk 5\n" ++
          "instance : Inhabited Nat := Inhabited.mk 7\n#eval (Inhabited.default : Nat)") ["5"] },
    { name := "tabling: a cyclic instance fails instead of looping", run := fun _ =>
        failsLib ("import Prelude\nclass Loop (A : Type) where\n  x : A\ninstance {A : Type} [Loop A] : Loop A := Loop.mk Loop.x\n" ++
          "#eval (Loop.x : Nat)") "failed to synthesize an instance of Loop Nat" },
    { name := "do notation for any Monad", run := fun _ =>
        okLib ("import Prelude\ninstance : Monad Option where\n  pure := fun a => Option.some a\n" ++
          "  bind := fun x f => match x with\n    | .none => Option.none\n    | .some a => f a\n" ++
          "def addOpt (x y : Option Nat) : Option Nat := do\n  a ← x;\n  b ← y;\n  Monad.pure (a + b)\n" ++
          "#eval addOpt (.some 1) (.some 2)\n#eval addOpt (.some 1) .none") [".some 3", ".none"] },
    { name := "a class's universe is inferred from its fields", run := fun _ =>
        okLib "import Prelude\nclass Functor (f : Type → Type) where\n  map : {A B : Type} → (A → B) → f A → f B\n#check Functor" ["Functor : (Type → Type) → Type 1"] },
    -- (7e) numeric classes
    { name := "arithmetic at Nat goes through the classes and still computes", run := fun _ =>
        okLib ("import Prelude\n#eval 2 + 3 * 4 - 1\n#eval 17 / 5 + 17 % 5\ndef t : 2 + 3 = 5 := rfl\n" ++
          "def z (n : Nat) : 0 + n = n := rfl\ndef s (n : Nat) : 1 + n = Nat.succ n := rfl\n#check fun (n : Nat) => n + 1\n" ++
          "set_option pp.notation false\n#check fun (n : Nat) => n + 1")
          ["13", "5", "fun n => n + 1 : Nat → Nat", "fun n => HAdd.hAdd Nat Nat Nat (instHAdd Nat instAddNat) n 1 : Nat → Nat"] },
    { name := "numerals and operators at a type with instances", run := fun _ =>
        okLib (numClassSrc ++ "#eval (5 : Z3) + 2\ndef inc (x : Z3) : Z3 := x + 1\n#eval inc 2\n#eval -(1 : Z3)\n#eval (2 : Z3) * 2 - 1")
          [".b", ".a", ".c", ".a"] },
    { name := "an instance can look at the numeral", run := fun _ =>
        okLib (numClassSrc ++ "#check (7 : Z3)\ndef seven : (7 : Z3) = Z3.b := rfl")
          ["7 : Z3"] },
    { name := "a numeral at a type without OfNat is an error", run := fun _ =>
        failsLib "import Prelude\ninductive Z3 where\n  | a\n  | b\n  | c\n#eval (1 : Z3)" "failed to synthesize an instance of OfNat Z3 1" },
    { name := "an operator without an instance is an error", run := fun _ =>
        failsLib "import Prelude\n#eval \"a\" + 1" "it needs an instance of Add String, through instHAdd" },
    { name := "prefix minus needs Neg", run := fun _ =>
        failsLib "import Prelude\ndef m : Nat := -1" "failed to synthesize an instance of Neg Nat" },
    { name := "operators in inductive indices and equation types", run := fun _ =>
        okLib ("import Prelude\ninductive V (A : Type) : Nat → Type where\n  | nil : V A 0\n  | cons {n : Nat} (x : A) (v : V A n) : V A (n + 1)\n" ++
          "def add0 : (n : Nat) → 0 + n = n\n  | _ => rfl\ndef two : V Nat (1 + 1) := .cons 1 (.cons 2 .nil)") },
    { name := "every native Nat operation computes through the classes, in proofs and #reduce", run := fun _ =>
        okLib ("import Prelude\ndef a : Nat := Nat.pow 2 70\ndef t1 : a + 5 = 1180591620717411303429 := refl 1180591620717411303429\ndef t2 : a - 5 = 1180591620717411303419 := refl 1180591620717411303419\ndef t3 : a * 3 = 3541774862152233910272 := refl 3541774862152233910272\ndef t4 : a / 1024 = 1152921504606846976 := refl 1152921504606846976\ndef t5 : (a + 7) % 1024 = 7 := refl 7\ndef t6 : Nat.land a (a + 5) = a := refl a\ndef t7 : Nat.lor a 5 = a + 5 := refl (a + 5)\ndef t8 : Nat.xor (a + 5) 5 = a := refl a\ndef t9 : Nat.shiftLeft 1 70 = a := refl a\ndef t10 : Nat.shiftRight (a * 4) 72 = 1 := refl 1\ndef t11 : Nat.log2 (a + 1) = 70 := refl 70\ndef t12 : Nat.beq (a + 1) (1 + a) = .true := refl Bool.true\ndef t13 : Nat.lt a (a + 1) = .true := refl Bool.true\ndef t14 : Nat.testBit (a + 4) 2 = .true := refl Bool.true\ndef t15 : 2 + 3 * 4 - 1 = 13 := rfl\n#reduce (a * 3 - 1) / 7 % 1000\n#eval Nat.xor (a + 5) 5")
          ["38", "1180591620717411303424"] },
    { name := "compiled: a + b at Nat is the native addition", run := fun _ =>
        okLib "import Prelude\ndef f (a b : Nat) : Nat := a * b + a\n#ir f"
          ["def f x0 x1 :=\n  dup x0\n  let x2 := prim nat.mul x0 x1\n  let x3 := prim nat.add x2 x0\n  ret x3"] },
    { name := "compiled: a method of a class with several methods", run := fun _ =>
        okLib ("import Prelude\nclass Ring (A : Type) where\n  zero : A\n  plus : A → A → A\n" ++
          "instance : Ring Nat where\n  zero := 0\n  plus := Nat.add\ndef f (a : Nat) : Nat := Ring.plus a Ring.zero\n#ir f\n#run f 4")
          ["def f x0 :=\n  let x1 := 0\n  let x2 := prim nat.add x0 x1\n  ret x2", "4"] },
    -- 7f: heterogeneous operators, default instances
    { name := "7f: a numeral that meets no type is a Nat (default instances), in types too", run := fun _ =>
        okLib ("import Prelude\n#check fun x => x + 1\ndef t : 1 + 1 = 2 := rfl\ndef u := (rfl : 2 * 3 = 6)\n" ++
          "def p := (1, 2 ^ 3)\n#check p\n#eval 2 ^ 10\n#eval (2 + 3).succ\ndef m (n : Nat) : Nat := n * .succ n\n#eval m 3\n" ++
          "#check [1, 2] ++ [3]\ndef xs : List Nat := List.cons 1 (List.cons 2 List.nil)\ndef s (n : Nat) : 2 + n = Nat.add 2 n := rfl")
          ["fun x => x + 1 : Nat → Nat", "p : Nat × Nat", "1024", "6", "12", "[1, 2] ++ [3] : List Nat"] },
    { name := "7f: a heterogeneous instance (scalar × structure)", run := fun _ =>
        okLib ("import Prelude\nstructure V where\n  x : Nat\n  y : Nat\n" ++
          "instance : HMul Nat V V := HMul.mk (fun k v => V.mk (k * v.x) (k * v.y))\n" ++
          "def scale (k : Nat) (v : V) : V := k * v\n#eval (scale 3 (V.mk 1 2)).y\n#check scale")
          ["6", "scale : Nat → V → V"] },
    { name := "7f: a user default instance, tried before the latest instance", run := fun _ =>
        okLib ("import Prelude\nclass Default (A : Type) where\n  val : A\n" ++
          "instance instDefaultNat : Default Nat := Default.mk 7\ninstance : Default Bool := Default.mk Bool.true\n" ++
          "attribute [default_instance] instDefaultNat\n#eval Default.val + 1")
          ["8"] },
    { name := "7f: attribute [default_instance] and [binop] need an instance and a method", run := fun _ => do
        failsLib "import Prelude\nattribute [default_instance] Nat.add" "Nat.add is not an instance"
        failsLib "import Prelude\nattribute [binop] Nat.add" "Nat.add is not a method of a class"
        failsLib "import Prelude\ninstance instHAdd : Add Bool := Add.mk Bool.and" "'instHAdd' is declared by both" },
    { name := "7f: compiled: operators with defaulted numerals are native", run := fun _ =>
        okLib "import Prelude\ndef g := fun x => x * 2 + 1\n#ir g\ndef h (x : Nat) : Nat := x ^ 2 + 1\n#run h 5"
          ["def g x0 :=\n  let x1 := 2\n  let x2 := prim nat.mul x0 x1\n  let x3 := 1\n  let x4 := prim nat.add x2 x3\n  ret x4", "26"] }
  ]

builtin_initialize registerGroup classGroup

end Tests.Elab
