import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

def vecPrelude : String := "import Vec
def v3 : Vec Nat 3 := .cons 10 (.cons 20 (.cons 30 .nil))
def w3 : Vec Nat 3 := .cons 1 (.cons 2 (.cons 3 .nil))
"

def bvPrelude : String := "import BitVec
def b8 (x : Nat) : BitVec 8 := BitVec.ofNat 8 x
"

/-- Index-refining matches on a self-contained `Vec` (no lib/Vec.wiz): the solution rule
casts a function, which erasure used to fail on, and `#eval` then ran a stub. -/
def refinePrelude : String := "import Prelude
inductive V (A : Type) : Nat → Type where
  | nil : V A 0
  | cons {0 n : Nat} (x : A) (xs : V A n) : V A (Nat.succ n)
def V.head {A : Type} {0 n : Nat} : V A (Nat.succ n) → A
  | .cons x _ => x
def V.zipWith {A B C : Type} (f : A → B → C) {0 n : Nat} : V A n → V B n → V C n
  | .nil, .nil => .nil
  | .cons a as, .cons b bs => .cons (f a b) (V.zipWith f as bs)
def V.sum {0 n : Nat} : V Nat n → Nat
  | .nil => 0
  | .cons x xs => x + V.sum xs
def v3 : V Nat 3 := .cons 10 (.cons 20 (.cons 30 .nil))
def w3 : V Nat 3 := .cons 1 (.cons 2 (.cons 3 .nil))
"

def vecGroup : Group where
  name := "vec"
  exercise := "Stage H0c"
  cases := [
    { name := "index-refining matches run: #eval, #run and C (regression: erasing a cast)", run := fun _ => do
        okLib (refinePrelude ++ "#eval V.head v3\n#run V.head v3\n#eval V.sum (V.zipWith Nat.mul v3 w3)\n#run V.sum (V.zipWith Nat.mul v3 w3)")
          ["10", "10", "140", "140"]
        cRun (refinePrelude ++ "def main : Nat := V.head v3 + V.sum (V.zipWith Nat.mul v3 w3)") "150" },
    { name := "the libraries check, theorems included", run := fun _ =>
        okLibs "import Vec\nimport BitVec" },
    { name := "access by Fin, and update", run := fun _ =>
        okLibs (vecPrelude ++ "#eval Vec.get v3 (Fin.of 3 2 rfl)\n#eval Vec.toList (Vec.set v3 (Fin.of 3 1 rfl) 99)\n" ++
          "#eval Vec.head v3\n#eval Vec.toList (Vec.tail v3)\n#eval Vec.last v3\n#eval Vec.toList (Vec.init v3)")
          ["30", ".cons 10 (.cons 99 (.cons 30 .nil))", "10", ".cons 20 (.cons 30 .nil)", "30", ".cons 10 (.cons 20 .nil)"] },
    { name := "an index out of range is rejected", run := fun _ =>
        -- (13b) the elaborator compares the two sides of `rfl` itself (`3 < 3` is `.false`)
        failsLibs (vecPrelude ++ "def bad : Nat := Vec.get v3 (Fin.of 3 3 rfl)") "rfl: the two sides are not definitionally equal" },
    { name := "maps, zips and folds", run := fun _ =>
        okLibs (vecPrelude ++ "#eval Vec.toList (Vec.map Nat.succ v3)\n#eval Vec.toList (Vec.zipWith Nat.add v3 w3)\n" ++
          "#eval Vec.foldr Nat.add 0 v3\n#eval Vec.foldl (fun acc x => acc * 10 + x) 0 w3\n#eval Vec.toList (Vec.zip v3 w3)")
          [".cons 11 (.cons 21 (.cons 31 .nil))", ".cons 11 (.cons 22 (.cons 33 .nil))", "60", "123",
           ".cons (10, 1) (.cons (20, 2) (.cons (30, 3) .nil))"] },
    { name := "building and reshaping", run := fun _ =>
        okLibs (vecPrelude ++ "#eval Vec.toList (Vec.append v3 w3)\n#eval Vec.toList (Vec.reverse v3)\n" ++
          "#eval Vec.toList (Vec.replicate 2 7)\n#eval Vec.toList (Vec.splitAt 1 v3).2\n#eval Vec.toList (Vec.ofFn 4 Fin.val)\n" ++
          "#eval Vec.toList (Vec.shiftIn 5 v3)\n#eval Vec.toList (Vec.fromList (.cons 4 (.cons 5 .nil)))")
          [".cons 10 (.cons 20 (.cons 30 (.cons 1 (.cons 2 (.cons 3 .nil)))))", ".cons 30 (.cons 20 (.cons 10 .nil))",
           ".cons 7 (.cons 7 .nil)", ".cons 20 (.cons 30 .nil)", ".cons 0 (.cons 1 (.cons 2 (.cons 3 .nil)))",
           ".cons 5 (.cons 10 (.cons 20 .nil))", ".cons 4 (.cons 5 .nil)"] },
    { name := "the length is erased; Vec.length counts", run := fun _ =>
        okLibs (vecPrelude ++ "#erase Vec.cons\n#eval Vec.length (Vec.append v3 w3)\n" ++
          "def lenMap (n : Nat) (v : Vec Nat n) : Vec.length (Vec.map Nat.succ v) = n := Vec.length_eq (Vec.map Nat.succ v)")
          ["Vec.cons := (λA. (λn. (λx. (λxs. ⟨1 ◾ #1 #0⟩))))", "6"] },
    { name := "the kernel computes on literal lengths", run := fun _ =>
        okLibs (vecPrelude ++ "def t1 : Vec.foldr Nat.add 0 (Vec.replicate 4 5) = 20 := rfl\n" ++
          "def t2 : Vec.toList v3 = .cons 10 (.cons 20 (.cons 30 .nil)) := rfl\n" ++
          "#reduce Vec.foldr Nat.add 0 v3\n#reduce Vec.head v3") ["60", "10"] },
    { name := "rfl at a computed equation between a numeral and a constructor (was a known bug; fixed by equality at μ by constructor, D1)", run := fun _ =>
        okLibs (vecPrelude ++ "def t3 : Vec.length (Vec.map Nat.succ w3) = 3 := rfl") },
    { name := "a cast between Vec Nat (.succ 2) and Vec Nat 3 computes (numeral vs constructor index; elab-bugs 3)", run := fun _ =>
        okLibs (vecPrelude ++ "def u3 : Vec Nat (Nat.succ 2) := v3\n" ++
          "def c3 (e : Vec Nat (Nat.succ 2) = Vec Nat 3) : (cast e u3 : Vec Nat 3) = v3 := rfl\n" ++
          "#reduce fun (e : Vec Nat (Nat.succ 2) = Vec Nat 3) => Vec.toList (cast e u3 : Vec Nat 3)")
          ["fun e => .cons 10 (.cons 20 (.cons 30 .nil))"] },
    { name := "map_map, get_set and get_map, with the castRefl axiom (D1)", run := fun _ =>
        okLibs (vecPrelude ++ "def mm : Vec.map Nat.succ (Vec.map Nat.succ w3) = Vec.map (fun a => Nat.succ (Nat.succ a)) w3 := Vec.map_map Nat.succ Nat.succ w3\n" ++
          "def gs {A : Type} {0 n : Nat} (v : Vec A n) (i : Fin n) (x : A) : Vec.get (Vec.set v i x) i = x := Vec.get_set v i x\n" ++
          "def gm {A B : Type} (f : A → B) {0 n : Nat} (v : Vec A n) (i : Fin n) : Vec.get (Vec.map f v) i = f (Vec.get v i) := Vec.get_map f v i\n") },
    { name := "compiled, through the IR and C", run := fun _ => do
        okLibs (vecPrelude ++ "#run Vec.toList (Vec.reverse v3)\n#run Vec.get (Vec.set v3 (Fin.of 3 2 rfl) 7) (Fin.of 3 2 rfl)\n" ++
          "#run Vec.toList (Vec.zipWith Nat.mul v3 w3)")
          [".cons 30 (.cons 20 (.cons 10 .nil))", "7", ".cons 10 (.cons 40 (.cons 90 .nil))"]
        cRunLibs (vecPrelude ++ "def main : Nat := Vec.foldl Nat.add 0 (Vec.zipWith Nat.mul (Vec.reverse v3) (Vec.init (Vec.snoc w3 9)))") "100" },
    { name := "Nat division, powers and bits (the Prelude natives BitVec uses)", run := fun _ =>
        okLibs ("import Prelude\n#eval Nat.div 1000000007 13\n#eval Nat.mod 1000000007 13\n#eval Nat.pow 2 64\n" ++
          "#eval Nat.land 12 10\n#eval Nat.lor 12 10\n#eval Nat.xor 12 10\n#eval Nat.testBit 5 2\n#eval Nat.div 7 0\n" ++
          "def t : Nat.mod 300 256 = 44 := rfl\n#run Nat.shiftRight (Nat.pow 2 100) 98")
          ["76923077", "6", "18446744073709551616", "8", "14", "6", ".true", "0", "4"] },
    { name := "bit vectors: wrapping arithmetic", run := fun _ =>
        okLibs (bvPrelude ++ "#eval (b8 300).toNat\n#eval (BitVec.add (b8 200) (b8 100)).toNat\n#eval (BitVec.sub (b8 3) (b8 5)).toNat\n" ++
          "#eval (BitVec.neg (b8 1)).toNat\n#eval (BitVec.mul (b8 20) (b8 13)).toNat\n#eval (BitVec.udiv (b8 200) (b8 7)).toNat\n" ++
          "#eval (BitVec.umod (b8 200) (b8 7)).toNat\ndef t : (BitVec.add (b8 200) (b8 100)).toNat = 44 := rfl")
          ["44", "44", "254", "255", "4", "28", "4"] },
    { name := "bit vectors: bitwise, shifts, comparisons", run := fun _ =>
        okLibs (bvPrelude ++ "#eval (BitVec.and (b8 12) (b8 10)).toNat\n#eval (BitVec.or (b8 12) (b8 10)).toNat\n" ++
          "#eval (BitVec.xor (b8 12) (b8 10)).toNat\n#eval (BitVec.not (b8 12)).toNat\n#eval (BitVec.shl (b8 129) 1).toNat\n" ++
          "#eval (BitVec.lshr (b8 128) 3).toNat\n#eval (BitVec.ashr (b8 128) 3).toNat\n#eval BitVec.getBit (b8 5) 2\n" ++
          "#eval BitVec.msb (b8 128)\n#eval BitVec.slt (b8 255) (b8 0)\n#eval BitVec.ult (b8 255) (b8 0)")
          ["8", "14", "6", "243", "2", "16", "240", ".true", ".true", ".true", ".false"] },
    { name := "BitVecShift: barrel-shifter stages in toNat/low form (shl, lshr, high/low)", run := fun _ =>
        okLibs ("import BitVecShift\n" ++
          "def a (x : BitVec 8) (k : Nat) : (BitVec.shl x k).toNat = Bits.low 8 (Nat.mul x.toNat (Nat.pow 2 k)) := BitVec.shl_toNat 8 k x\n" ++
          "def b (x : BitVec 4) : (BitVec.shlStage 2 2 x).toNat = Bits.low 4 (Nat.mul x.toNat 4) := BitVec.shlStage_toNat 2 2 x\n" ++
          "def c (w j a : Nat) : Bits.low (Nat.add w j) (Nat.mul a (Nat.pow 2 j)) = Nat.mul (Bits.low w a) (Nat.pow 2 j) := Bits.low_shift w j a\n" ++
          "def d (x : BitVec 4) : Bits.low 2 (Bits.low 4 x.toNat) = Bits.low 2 x.toNat := Bits.low_low 2 4 x.toNat rfl\n" ++
          "def e (x : BitVec 8) (k : Nat) : (BitVec.lshr x k).toNat = Bits.high k x.toNat := BitVec.lshr_toNat 8 k x\n" ++
          "def f (x : BitVec 8) (k : Nat) : (BitVec.lshr x k).toNat = Bits.low 8 (Bits.high k x.toNat) := BitVec.lshr_low_toNat 8 k x\n" ++
          "def g (k j n : Nat) : Bits.high k (Bits.high j n) = Bits.high (Nat.add j k) n := Bits.high_high k j n\n" ++
          "def h (j m n : Nat) (hp : Nat.lt n (Nat.pow 2 (Nat.add j m)) = .true) : Nat.lt (Bits.high j n) (Nat.pow 2 m) = .true := Bits.high_lt j m n hp\n" ++
          "def i (k A B : Nat) : Nat.div (Nat.add (Nat.mul A (Nat.pow 2 k)) B) (Nat.pow 2 k) = Nat.add A (Nat.div B (Nat.pow 2 k)) := Bits.div_add_pow k A B\n" ++
          "def j (k A B : Nat) : Bits.high k (Nat.add (Nat.mul A (Nat.pow 2 k)) B) = Nat.add A (Bits.high k B) := Bits.high_add_pow k A B\n" ++
          "def k (w n : Nat) (hp : Nat.lt n (Nat.pow 2 w) = .true) : Bits.low w n = n := Bits.low_of_lt w n hp\n" ++
          "def l (w v n : Nat) (hp : Nat.le w v = .true) : Bits.low v (Bits.low w n) = Bits.low w n := Bits.low_low_rev w v n hp\n" ++
          "def m (b : BitVec 3) : BitVec.and (BitVec.ofNat 3 0) b = BitVec.ofNat 3 0 := BitVec.and_zero_left b\n" ++
          "def n (b : BitVec 1) : BitVec.and (BitVec.ofNat 1 1) b = b := BitVec.and_one_left b\n" ++
          "def o (w k a : Nat) (hk : Nat.le k w = .true) (ha : Nat.lt a (Nat.pow 2 w) = .true) : " ++
          "Nat.sub (Bits.dec (Nat.pow 2 w)) (Bits.high k (Nat.sub (Bits.dec (Nat.pow 2 w)) a)) = " ++
          "Nat.add (Nat.sub (Nat.pow 2 w) (Nat.pow 2 (Nat.sub w k))) (Bits.high k a) := Bits.sub_one_high w k a hk ha\n") },
    { name := "BitVecAdd: the 34-bit carry/borrow adder is add/sub (concatenation, slice)", run := fun _ =>
        okLibs ("import BitVecAdd\n" ++
          "def a (x y : BitVec 32) : BitVec.adc (BitVec.ofNat 1 0) x y = BitVec.add x y := BitVec.adc_zero x y\n" ++
          "def b (x y : BitVec 32) : BitVec.adc (BitVec.ofNat 1 1) x y = BitVec.sub x y := BitVec.adc_one x y\n" ++
          "def c (s : BitVec 1) (x y : BitVec 32) : BitVec.adc s x y = BitVec.muxBit s (BitVec.sub x y) (BitVec.add x y) := BitVec.adc_eq s x y\n" ++
          "def d (x : BitVec 32) : (BitVec.zext1 (BitVec.concat x (BitVec.ofNat 1 1))).toNat = Nat.add (Nat.mul x.toNat 2) 1 := BitVec.adcW1 x\n" ++
          "def e (A : Nat) (h : Nat.Lt A (Nat.pow 2 32)) : Bits.low 33 (Nat.add (Nat.mul A 2) 1) = Nat.add (Nat.mul A 2) 1 := Bits.low33_cat A h\n" ++
          "def f (w n : Nat) : Nat.div (Bits.low (Nat.succ w) n) 2 = Bits.low w (Nat.div n 2) := Bits.div_low_succ w n\n" ++
          "def g (x y : BitVec 32) : (BitVec.adc (BitVec.ofNat 1 0) x y).toNat = Bits.low 32 (Nat.add x.toNat y.toNat) := BitVec.adc_zero_toNat x y\n" ++
          "#eval BitVec.toNat (BitVec.adc (BitVec.ofNat 1 0) (BitVec.ofNat 32 4294967295) (BitVec.ofNat 32 2))\n" ++
          "#eval BitVec.toNat (BitVec.adc (BitVec.ofNat 1 1) (BitVec.ofNat 32 3) (BitVec.ofNat 32 5))")
          ["1", "4294967294"] },
    { name := "bit vectors: widths and bits as a Vec", run := fun _ =>
        okLibs (bvPrelude ++ "#eval (BitVec.concat (BitVec.ofNat 4 10) (BitVec.ofNat 4 3)).toNat\n" ++
          "#eval (BitVec.extract 5 2 (b8 60)).toNat\n#eval (BitVec.zeroExtend 16 (b8 200)).toNat\n" ++
          "#eval (BitVec.signExtend 16 (b8 200)).toNat\n#eval (BitVec.signExtend 4 (b8 200)).toNat\n" ++
          "#eval Vec.toList (BitVec.toVec (BitVec.ofNat 4 6))\n#eval (BitVec.ofVec (BitVec.toVec (b8 173))).toNat")
          ["163", "15", "200", "65480", "8", ".cons .false (.cons .true (.cons .true (.cons .false .nil)))", "173"] },
    { name := "bit vectors at 63, 64 and 65 bits, compiled", run := fun _ => do
        okLibs ("import BitVec\n#run (BitVec.mul (BitVec.ofNat 64 18446744073709551615) (BitVec.ofNat 64 3)).toNat\n" ++
          "#run (BitVec.add (BitVec.ofNat 65 36893488147419103231) (BitVec.ofNat 65 2)).toNat\n" ++
          "#run (BitVec.sub (BitVec.ofNat 63 0) (BitVec.ofNat 63 1)).toNat")
          ["18446744073709551613", "1", "9223372036854775807"]
        cRunLibs "import BitVec\ndef main : Nat := (BitVec.ashr (BitVec.ofNat 64 9223372036854775808) 63).toNat" "18446744073709551615" },
    { name := "one type family: a BitVec is a UIntN, both ways, and widths still count", run := fun _ => do
        okLibs ("import BitVec\ndef w (x : U32) : BitVec 32 := BitVec.add x (BitVec.ofNat 32 1)\n" ++
          "def u (x : BitVec 8) : U8 := UIntN.mul x x\n#eval (w (U32.ofNat 4294967295)).toNat\n#eval (u (BitVec.ofNat 8 20)).toNat\n" ++
          "def t : (UIntN.add (BitVec.ofNat 8 200) (U8.ofNat 100)).toNat = 44 := rfl")
          ["0", "144"]
        failsLibs "import BitVec\ndef bad (x : BitVec 8) : U16 := x" "mismatch" },
    { name := "a BitVec compiles to native words: no word object in the IR", run := fun _ => do
        let src := "import BitVec\ndef f (a b : BitVec 64) : BitVec 64 := BitVec.add (BitVec.xor a b) (BitVec.ashr a 3)\n" ++
          "def g (a : BitVec 64) : Bool := BitVec.slt a (BitVec.signExtend 64 (BitVec.extract 7 0 a))\n#ir f\n#ir g\n" ++
          "#ir BitVec.add\n#ir BitVec.ashr\n#ir BitVec.slt\n#ir BitVec.extract\n#ir BitVec.signExtend\n#ir BitVec.concat"
        let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := ← libLoader }
        let out := String.intercalate "\n" (s.messages.toList.map (·.text))
        check ((out.splitOn "ctor").length == 1 && (out.splitOn "proj").length == 1) s!"a word object in:\n{out}"
        check ((out.splitOn "wiz_word_ashr").length > 1 && (out.splitOn "wiz_word_slt").length > 1) s!"no natives in:\n{out}" },
    { name := "22l: the range is a theorem (toNat_lt, ext, cases1)", run := fun _ =>
        okLibs ("import BitVec\ndef r (x : UIntN 8) : Nat.lt x.toNat 256 = .true := UIntN.toNat_lt x\n" ++
          "def s (x : IntN 8) : Nat.lt x.toNat 256 = .true := IntN.toNat_lt x\n" ++
          "def c (x : UIntN 1) : x = 0 ∨ x = 1 := UIntN.cases1 x\n" ++
          "def e : (UIntN.lor (UIntN.max 8) (UIntN.ofNat 8 3) : UIntN 8) = UIntN.ofNat 8 255 := UIntN.ext _ _ rfl\n") },
    { name := "22l: closed words with the same bits are equal by rfl, however their range was proved", run := fun _ => do
        okLibs ("import BitVec\ndef t1 : BitVec.or (BitVec.ofNat 1 1) (BitVec.ofNat 1 0) = BitVec.ofNat 1 1 := rfl\n" ++
          "def t2 : BitVec.and (BitVec.ofNat 4 12) (BitVec.ofNat 4 10) = BitVec.ofNat 4 8 := rfl\n" ++
          "def t3 : BitVec.xor (BitVec.ofNat 4 12) (BitVec.ofNat 4 10) = BitVec.ofNat 4 6 := rfl\n" ++
          "def t4 : BitVec.not (BitVec.ofNat 4 12) = BitVec.ofNat 4 3 := rfl\n" ++
          "def t5 : BitVec.or (BitVec.ofNat 4 12) (BitVec.ofNat 4 10) = BitVec.ofNat 4 14 := rfl\n" ++
          "def t6 : UIntN.toIntN (UIntN.ofNat 1 1) = IntN.ofNat 1 1 := rfl\n" ++
          "def t7 : IntN.toUIntN (IntN.ofNeg 8 1) = UIntN.max 8 := rfl\n" ++
          "def t8 : BitVec.concat (BitVec.ofNat 4 15) (BitVec.ofNat 4 1) = BitVec.ofNat 8 241 := rfl\n" ++
          "def t9 : UIntN.zero 3 = UIntN.ofNat 3 0 := rfl\n")
        failsLibs "import BitVec\ndef bad : BitVec.or (BitVec.ofNat 1 1) (BitVec.ofNat 1 0) = BitVec.ofNat 1 0 := rfl\n" "not definitionally equal" },
    { name := "22l: concat and ofVec go through ofNat: interpreted and compiled agree", run := fun _ => do
        let src := "import BitVec\ndef main : Nat := (BitVec.concat (BitVec.ofNat 4 15) (BitVec.ofNat 4 1)).toNat + " ++
          "1000 * (BitVec.ofVec (Vec.cons Bool.true (Vec.cons Bool.false (Vec.cons Bool.true Vec.nil)))).toNat + " ++
          "10000 * (UIntN.xor (UIntN.max 3) (UIntN.ofNat 3 2)).toNat\n"
        okLibs (src ++ "#eval main\n") ["55241"]
        cRunLibs src "55241" }
  ]

builtin_initialize registerGroup vecGroup

end Tests.Elab
