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
    { name := "order notation: ≤, < and ≈ are classes (lib/Data/Order.wiz)", run := fun _ =>
        okLibs ("import Data.Order\ndef Bool.Le (a b : Bool) : Prop := Bool.or (Bool.not a) b = .true\n" ++
          "instance : LE Bool := LE.mk Bool.Le\ninstance : Equiv Bool := Equiv.mk (fun a b => a = b)\n" ++
          "def t : Bool.false ≤ Bool.true := rfl\ndef u : Bool.true ≈ Bool.true := rfl\n#check Bool.false ≤ Bool.true")
          ["Bool.false ≤ Bool.true : Prop"] },
    -- arithmetic library: lib/Nat.wiz, Ring.wiz, IntRing.wiz, IntOrder.wiz, Rat.wiz
    { name := "naturals: semiring laws, the order as a proposition, ≤ notation", run := fun _ =>
        okLibs ("import Nat\n#check Nat.mul_add\n#check Nat.le_trans\n" ++
          "def a (n : Nat) : n ≤ n + 1 := Nat.le_add_right n 1\ndef b : Nat.Le 2 5 := rfl\ndef c : (3 : Nat) < 4 := rfl\n" ++
          "def d (m n : Nat) (h : m ≤ n) (h' : n ≤ m) : m = n := Nat.le_antisymm m n h h'\n#check Nat.mul_assoc\n#print axioms Nat.mul_assoc")
          ["Nat.mul_add : (a : Nat) → (b : Nat) → (c : Nat) → a * (b + c) = a * b + a * c",
           "Nat.le_trans : (a : Nat) → (b : Nat) → (c : Nat) → Nat.Le a b → Nat.Le b c → Nat.Le a c",
           "Nat.mul_assoc : (a : Nat) → (b : Nat) → (c : Nat) → a * b * c = a * (b * c)",
           "'Nat.mul_assoc' does not depend on any axioms"] },
    { name := "simp lemmas: normal forms and explicit rw chains (lib/SimpLemmas.wiz)", run := fun _ =>
        okLibs ("import SimpLemmas\n" ++
          "-- equations stuck on a variable: `rw` sees them\n" ++
          "def r1 (n : Nat) : (n + 0) * 1 = n := by\n  rw (Nat.mul_one (n + 0))\n  rw (Nat.add_zero n)\n  rfl\n" ++
          "def r2 (n : Nat) : n * 0 = 0 := by\n  rw (Nat.mul_zero n)\n  rfl\n" ++
          "def r3 (n : Nat) : 1 * n = n := by\n  rw (Nat.one_mul n)\n  rfl\n" ++
          "def r4 (b : Bool) (n : Nat) : (if !(!b) then n else 0) = (if b then n else 0) := by\n  rw (Bool.not_not b)\n  rfl\n" ++
          "def r5 (b : Bool) : (b && Bool.true) = b := by\n  rw (Bool.and_true b)\n  rfl\n" ++
          "def r6 (b : Bool) : (b && Bool.false) = Bool.false := by\n  rw (Bool.and_false b)\n  rfl\n" ++
          "def r7 (b : Bool) : (b || Bool.false) = b := by\n  rw (Bool.or_false b)\n  rfl\n" ++
          "def r8 {A : Type} (xs : List A) : List.append xs .nil = xs := by\n  rw (List.append_nil xs)\n  rfl\n" ++
          "def r9 {A : Type} (xs ys : List A) : List.length (List.append xs ys) = List.length xs + List.length ys := by\n  rw (List.length_append_eq xs ys)\n  rfl\n" ++
          "def r10 (f : Nat → Nat) (g : Nat → Nat) (xs : List Nat) :\n    List.map f (List.map g xs) = List.map (fun x => f (g x)) xs := by\n  rw (List.map_map f g xs)\n  rfl\n" ++
          "def r11 (a : Int) : a * 1 = a := by\n  rw (Int.mul_one a)\n  rfl\n" ++
          "def r12 (a : Int) : 1 * a = a := by\n  rw (Int.one_mul a)\n  rfl\n" ++
          "def r13 (a : Int) : 0 * a = 0 := by\n  rw (Int.zero_mul a)\n  rfl\n" ++
          "def r14 (a : Int) : a - 0 = a := by\n  rw (Int.sub_zero a)\n  rfl\n" ++
          "def r15 (a : Int) : a + 0 = a := by\n  rw (Int.add_zero a)\n  rfl\n" ++
          "-- definitional equations: checked by application (their type computes to True, so `rw` cannot use them)\n" ++
          "def d1 (b : Nat) : b ^ 0 = 1 := Nat.pow_zero b\n" ++
          "def d2 (b n : Nat) : b ^ Nat.succ n = b * b ^ n := Nat.pow_succ b n\n" ++
          "def d3 (n : Nat) : 0 + n = n := Nat.zero_add n\n" ++
          "def d4 (n : Nat) : 0 * n = 0 := Nat.zero_mul n\n" ++
          "def d5 (a b : Nat) : (if Bool.true then a else b) = a := Bool.if_true a b\n" ++
          "def d6 (a b : Nat) : (if Bool.false then a else b) = b := Bool.if_false a b\n" ++
          "def d7 {A : Type} (xs : List A) : .nil ++ xs = xs := List.nil_append xs\n" ++
          "def d8 {A B : Type} (f : A → B) : List.map f .nil = .nil := List.map_nil f\n" ++
          "def d9 {A B : Type} (f : A → B) (x : A) (xs : List A) :\n    List.map f (.cons x xs) = .cons (f x) (List.map f xs) := List.map_cons f x xs\n" ++
          "def d10 {A B : Type} (f : A → B) : Option.map f .none = .none := Option.map_none f\n" ++
          "def d11 {A B : Type} (f : A → B) (a : A) : Option.map f (.some a) = .some (f a) := Option.map_some f a\n" ++
          "def d12 (a b : Nat) : ((a, b) : Nat × Nat).1 = a := Prod.fst_mk a b\n" ++
          "def d13 (a b : Nat) : ((a, b) : Nat × Nat).2 = b := Prod.snd_mk a b\n" ++
          "def d14 (a : Int) : 0 + a = a := Int.zero_add a\n") },
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
          "#check Int.mul_comm\n#check Int.neg_mul\n#check Int.mul_add\n#print axioms Int.mul_add")
          ["Int.mul_comm : (a : Int) → (b : Int) → a * b = b * a",
           "Int.neg_mul : (a : Int) → (b : Int) → -a * b = - (a * b)",
           "Int.mul_add : (a : Int) → (b : Int) → (c : Int) → a * (b + c) = a * b + a * c",
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
          "#eval (Q.div 1 half).num\n#check Q.mul_inv\n#check Q.abs_sub_le\n#check Q.lt_ceil\n#print axioms Q.lt_ceil")
          ["2", "Q.mul_inv : (p : Q) → ¬p.1 = 0 → p * Q.inv p ≈ 1",
           "Q.abs_sub_le : (p : Q) → (q : Q) → (r : Q) → Q.abs (p - r) ≤ Q.abs (p - q) + Q.abs (q - r)",
           "Q.lt_ceil : (p : Q) → p < Q.ofNat (Q.ceil p)",
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
    { name := "Compose: `∘` is a class (its laws hold at functions), and printing round-trips", run := fun _ =>
        okLibs ("import Compose\n#eval (Nat.succ ∘ Nat.succ) 0\n" ++
          "#check fun (n : Nat) => (Nat.succ ∘ Nat.succ) n\n" ++
          "#check Compose.id_left\n#print axioms Compose.assoc\n#print axioms Compose.id_left\n#print axioms Compose.id_right\n" ++
          "instance : Compose Bool Bool Bool := Compose.mk (fun g f x => Bool.not (g (f x)))\n" ++
          "#eval (Bool.not ∘ Bool.not) Bool.true\n")
          ["2", "fun n => (Nat.succ ∘ Nat.succ) n : Nat → Nat",
           "Compose.id_left : {α : Type} → {β : Type} → (f : α → β) → (0 x : α) → id β (f x) = f x",
           "'Compose.assoc' does not depend on any axioms",
           "'Compose.id_left' does not depend on any axioms",
           "'Compose.id_right' does not depend on any axioms", ".false"] },
    { name := "native text", run := fun _ =>
        ioRun ("import Std\ndef main : IO Unit := do\n  let t := Str.append (Str.ofString \"hello, \") (Str.ofString \"world\");\n" ++
          "  IO.println (Str.toString (Str.slice t 7 12));\n  IO.println (Nat.toString (Str.size t))") "world\n12\n" },
    { name := "native text: self-append and a shared value copy (no mutation)", run := fun _ =>
        ioRun ("import Std\ndef both (s : Str) : Str × Str := (s, Str.append s (Str.ofString \"x\"))\n" ++
          "def main : IO Unit := do\n  let s := Str.ofString \"abc\";\n  let t := Str.append s s;\n" ++
          "  IO.println (Str.toString t);\n  IO.println (Str.toString s);\n" ++
          "  let p := both (Str.ofString \"abc\");\n  IO.println (Str.toString p.1);\n  IO.println (Str.toString p.2);\n" ++
          "  let b := Str.push (Str.push (Str.ofString \"\") 65) 66;\n  IO.println (Str.toString b);\n" ++
          "  IO.println (Str.toString (Str.join (.cons (Str.ofString \"a\") (.cons (Str.ofString \"b\") (.cons (Str.ofString \"c\") .nil)))))")
          "abcabc\nabc\nabc\nabcx\nAB\nabc\n" },
    { name := "native text: aliasing fixtures (compiled; the original is never mutated)", run := fun _ => do
        for f in ["self-append", "shared-receiver", "shared-push", "shared-join"] do
          let src ← IO.FS.readFile ("Tests/fixtures/std-aliasing/" ++ f ++ ".wiz")
          let want ← IO.FS.readFile ("Tests/fixtures/std-aliasing/" ++ f ++ ".expected")
          ioRun src want },
    -- (audit F19) `Str.append` grows the receiver in place when it is unique, so the
    -- builder loop is linear; `Str.join` and a `Str.push` loop must build the same bytes.
    { name := "native text: append, join and push build the same bytes", run := fun _ =>
        ioRun ("import Std\ndef piece : Str := Str.ofString \"ab\"\n" ++
          "def appendN : Nat → Str → Str\n  | .zero, s => s\n  | .succ k, s => appendN k (Str.append s piece)\n" ++
          "def piecesN : Nat → List Str → List Str\n  | .zero, acc => acc\n  | .succ k, acc => piecesN k (.cons piece acc)\n" ++
          "def pushN : Nat → Nat → Str → Str\n  | .zero, _, s => s\n  | .succ k, b, s => pushN k (Nat.sub 1 b) (Str.push s (Nat.add 97 b))\n" ++
          "def main : IO Unit := do\n  let a := appendN 2000 Str.empty;\n" ++
          "  let j := Str.join (piecesN 2000 .nil);\n  let p := pushN 4000 0 Str.empty;\n" ++
          "  IO.println (Nat.toString (Str.size a));\n  IO.println (Nat.toString (Str.size j));\n" ++
          "  IO.println (Nat.toString (Str.size p));\n  IO.println (Str.toString (Str.slice p 0 6));\n" ++
          "  IO.println (Nat.toString (match Str.eq a j with\n    | .true => 1\n    | .false => 0));\n" ++
          "  IO.println (Nat.toString (match Str.eq j p with\n    | .true => 1\n    | .false => 0))")
          "4000\n4000\n4000\nababab\n1\n1\n" },
    { name := "native text: append under the address sanitiser", run := fun _ => do
        -- The in-place path reallocs the receiver and the copy path reads both
        -- operands; a use-after-free there is invisible to an output comparison, so
        -- the same shapes run under AddressSanitizer. LeakSanitizer is off for the run:
        -- the runtime keeps two process-lifetime scratch buffers (`wiz_scratch` and the
        -- free worklist) that its own exit check does not count as objects, and it is
        -- those, not a Str, that LSan reports.
        let tc ← toolchain
        let src := "import Std\ndef piece : Str := Str.ofString \"ab\"\n" ++
          "def appendN : Nat → Str → Str\n  | .zero, s => s\n  | .succ k, s => appendN k (Str.append s piece)\n" ++
          "def piecesN : Nat → List Str → List Str\n  | .zero, acc => acc\n  | .succ k, acc => piecesN k (.cons piece acc)\n" ++
          "def pushN : Nat → Nat → Str → Str\n  | .zero, _, s => s\n  | .succ k, b, s => pushN k (Nat.sub 1 b) (Str.push s (Nat.add 97 b))\n" ++
          "def main : IO Unit := do\n  let a := appendN 500 Str.empty;\n" ++
          "  let j := Str.join (piecesN 500 .nil);\n  let p := pushN 1000 0 Str.empty;\n" ++
          "  let shared := Str.ofString \"ab\";\n  let x := Str.append shared (Str.ofString \"cd\");\n" ++
          "  let y := Str.append shared shared;\n" ++
          "  IO.println (Nat.toString (Str.size a));\n" ++
          "  IO.println (Nat.toString (match Str.eq a j with\n    | .true => 1\n    | .false => 0));\n" ++
          "  IO.println (Nat.toString (match Str.eq j p with\n    | .true => 1\n    | .false => 0));\n" ++
          "  IO.println (Str.toString shared);\n  IO.println (Str.toString x);\n" ++
          "  IO.println (Str.toString y)"
        let dir ← IO.FS.createTempDir
        IO.FS.writeFile (dir / "main.wiz") src
        let exe := dir / "main"
        let wiz ← IO.FS.realPath ".lake/build/bin/wiz"
        let args := ["build", (dir / "main.wiz").toString, "-o", exe.toString,
          "--cc", tc.cc,
          "--cflags", String.intercalate " " (tc.cflags ++ ["-O1", "-g", "-fsanitize=address"]),
          "--ldflags", String.intercalate " " (tc.ldflags ++ ["-fsanitize=address"]),
          "--libs", String.intercalate " " tc.libs,
          "--gmp", String.intercalate " " tc.gmp]
        let b ← IO.Process.output { cmd := wiz.toString, args := args.toArray, cwd := some dir }
        if b.exitCode != 0 then
          if (b.stderr.splitOn "gmp.h").length > 1 then skip "no toolchain"
          else throw (IO.userError s!"the asan probe did not build:\n{b.stderr}")
        let spawn : IO.Process.SpawnArgs := { cmd := exe.toString }
        let spawn := { spawn with env := #[("ASAN_OPTIONS", some "detect_leaks=0:abort_on_error=1")] }
        let r ← IO.Process.output spawn
        checkEq "1000\n1\n1\nab\nabcd\nabab\n" r.stdout },
    { name := "maps from text", run := fun _ =>
        ioRun ("import Std\ndef count : List String → StrMap Nat → StrMap Nat\n  | .nil, m => m\n" ++
          "  | .cons w ws, m => count ws (StrMap.insert m (Str.ofString w) (StrMap.findD m (Str.ofString w) 0 + 1))\n" ++
          "def main : IO Unit := do\n  let m := count (.cons \"a\" (.cons \"b\" (.cons \"a\" .nil))) StrMap.empty;\n" ++
          "  IO.println (Nat.toString (StrMap.findD m (Str.ofString \"a\") 0));\n  IO.println (Nat.toString (StrMap.size m))") "2\n2\n" }
  ]

builtin_initialize registerGroup stdGroup

end Tests.Elab
