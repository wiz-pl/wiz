import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- Machine words (`lib/Word.wiz`): one table of operations at widths 8–100, signed and
unsigned, with its expected values. The kernel and the interpreters compute with the
definitions; compiled code calls the natives (`implemented_by`). -/
def wordTable : String := "import Word\ndef b2n : Bool → Nat\n  | .true => 1\n  | .false => 0\ndef m64 : Nat := 18446744073709551615\ndef main : List Nat :=\n  (.cons ((UIntN.add (U8.ofNat 200) (U8.ofNat 100)).toNat)\n    (.cons ((UIntN.sub (U8.ofNat 3) (U8.ofNat 5)).toNat)\n    (.cons ((UIntN.mul (U64.ofNat m64) (U64.ofNat m64)).toNat)\n    (.cons ((UIntN.add (U64.ofNat m64) (U64.ofNat 1)).toNat)\n    (.cons ((UIntN.mul (U64.ofNat m64) (U64.ofNat 3)).toNat)\n    (.cons ((UIntN.shiftLeft (U32.ofNat 5) 40).toNat)\n    (.cons ((UIntN.shiftLeft (U32.ofNat 5) 20).toNat)\n    (.cons ((UIntN.not (U64.ofNat 12345)).toNat)\n    (.cons ((UIntN.add (UIntN.ofNat 65 (Nat.pow 2 65 - 1)) (UIntN.ofNat 65 2)).toNat)\n    (.cons ((UIntN.mul (UIntN.ofNat 100 (Nat.pow 3 60)) (UIntN.ofNat 100 (Nat.pow 3 10))).toNat)\n    (.cons ((UIntN.div (U32.ofNat 1000) (U32.ofNat 7)).toNat)\n    (.cons ((UIntN.mod (U32.ofNat 1000) (U32.ofNat 7)).toNat)\n    (.cons ((UIntN.div (U32.ofNat 1000) (U32.ofNat 0)).toNat)\n    (.cons ((UIntN.mod (U32.ofNat 1000) (U32.ofNat 0)).toNat)\n    (.cons ((IntN.div (I8.ofNeg 7) (I8.ofNat 2)).toNat)\n    (.cons ((IntN.rem (I8.ofNeg 7) (I8.ofNat 2)).toNat)\n    (.cons ((IntN.div (I8.ofNeg 128) (I8.ofNeg 1)).toNat)\n    (.cons ((IntN.shiftRight (I8.ofNeg 100) 3).toNat)\n    (.cons ((IntN.resize 16 (I8.ofNeg 1)).toNat)\n    (.cons ((IntN.div (I64.ofNeg (Nat.pow 2 63)) (I64.ofNeg 1)).toNat)\n    (.cons ((IntN.div (I64.ofNeg 1000000000000) (I64.ofNat 7)).toNat)\n    (.cons ((IntN.rem (I64.ofNeg 1000000000000) (I64.ofNat 7)).toNat)\n    (.cons ((IntN.mul (I64.ofNeg 5) (I64.ofNat (Nat.pow 2 62))).toNat)\n    (.cons ((IntN.shiftRight (I64.ofNeg 123456789) 10).toNat)\n    (.cons (b2n (IntN.lt (I64.ofNeg 1) (I64.ofNat 0)))\n    (.cons (b2n (IntN.lt (I64.ofNat 0) (I64.ofNeg 1)))\n    (.cons (b2n (IntN.le (I8.ofNeg 128) (I8.ofNeg 128)))\n    (.cons (b2n (IntN.lt (I8.ofNat 127) (I8.ofNeg 128)))\n    (.cons (IntN.natAbs (IntN.min 64))\n    (.cons ((IntN.div (IntN.ofNeg 70 (Nat.pow 2 69)) (IntN.ofNeg 70 1)).toNat)\n    (.cons ((IntN.shiftRight (IntN.ofNeg 70 5) 100).toNat)\n    (.cons ((IntN.rem (IntN.ofNeg 70 7) (IntN.ofNeg 70 2)).toNat)\n    (.cons ((UIntN.neg (U8.ofNat 1)).toNat)\n    (.cons ((IntN.sub (I32.ofNat 0) (I32.ofNat 1)).toNat)\n    .nil))))))))))))))))))))))))))))))))))\n"

def wordTableValue : String := ".cons 44 (.cons 254 (.cons 1 (.cons 0 (.cons 18446744073709551613 (.cons 0 (.cons 5242880 (.cons 18446744073709539270 (.cons 1 (.cons 813220142716762761079858673625 (.cons 142 (.cons 6 (.cons 0 (.cons 1000 (.cons 253 (.cons 255 (.cons 128 (.cons 243 (.cons 65535 (.cons 9223372036854775808 (.cons 18446743930852408759 (.cons 18446744073709551615 (.cons 13835058055282163712 (.cons 18446744073709431052 (.cons 1 (.cons 0 (.cons 1 (.cons 0 (.cons 9223372036854775808 (.cons 590295810358705651712 (.cons 1180591620717411303423 (.cons 1180591620717411303423 (.cons 255 (.cons 4294967295 .nil)))))))))))))))))))))))))))))))))"

/-- 64-bit edge cases and the operations natively implemented in stage 22d (words as
their bits: scalars below 2^63, raw boxes below 2^64), plus a 64-bit FNV-1a, generic
width, and `match` on a word. -/
def wordTable64 : String := "import Word\ndef b2n : Bool → Nat\n  | .true => 1\n  | .false => 0\ndef m64 : Nat := 18446744073709551615\ndef p63 : Nat := 9223372036854775808\ndef fnv64 : List Nat → U64 → U64\n  | .nil, h => h\n  | .cons b bs, h => fnv64 bs (UIntN.mul (UIntN.xor h (U64.ofNat b)) (U64.ofNat 1099511628211))\ndef twice {ω w : Nat} (a : UIntN w) : UIntN w := UIntN.add a a\ndef bits (a : U64) : Nat := a.toNat\ndef bump (a : I64) : I64 := IntN.ofNat 64 (Nat.add a.toNat 1)\ndef main : List Nat :=\n  (.cons ((U64.ofNat p63).toNat)\n    (.cons ((UIntN.add (U64.ofNat p63) (U64.ofNat p63)).toNat)\n    (.cons ((UIntN.sub (U64.ofNat 0) (U64.ofNat 1)).toNat)\n    (.cons (b2n (UIntN.beq (U64.ofNat p63) (UIntN.add (U64.ofNat 4611686018427387904) (U64.ofNat 4611686018427387904))))\n    (.cons (b2n (UIntN.lt (U64.ofNat (p63 - 1)) (U64.ofNat p63)))\n    (.cons (b2n (UIntN.le (U64.ofNat m64) (U64.ofNat 5)))\n    (.cons ((UIntN.land (U64.ofNat m64) (U64.ofNat (p63 + 5))).toNat)\n    (.cons ((UIntN.xor (U64.ofNat m64) (U64.ofNat 1)).toNat)\n    (.cons ((UIntN.lor (U64.ofNat p63) (U64.ofNat 1)).toNat)\n    (.cons ((UIntN.shiftRight (U64.ofNat m64) 63).toNat)\n    (.cons ((UIntN.shiftRight (U64.ofNat m64) 64).toNat)\n    (.cons ((UIntN.shiftLeft (U64.ofNat 1) 63).toNat)\n    (.cons ((UIntN.shiftLeft (U64.ofNat 1) 64).toNat)\n    (.cons ((UIntN.shiftLeft (U64.ofNat 1) 1000).toNat)\n    (.cons (b2n (UIntN.testBit (U64.ofNat p63) 63))\n    (.cons (b2n (UIntN.testBit (U64.ofNat m64) 64))\n    (.cons (b2n (UIntN.msb (U64.ofNat p63)))\n    (.cons ((UIntN.resize 8 (U64.ofNat m64)).toNat)\n    (.cons ((UIntN.resize 100 (U64.ofNat m64)).toNat)\n    (.cons ((IntN.resize 100 (I64.ofNeg 1)).toNat)\n    (.cons ((IntN.resize 64 (IntN.ofNeg 100 3)).toNat)\n    (.cons ((I64.ofNeg 1).toNat)\n    (.cons ((IntN.shiftRight (I64.ofNeg 1) 200).toNat)\n    (.cons ((IntN.shiftRight (I64.ofNeg p63) 63).toNat)\n    (.cons (b2n (IntN.lt (I64.ofNeg p63) (I64.ofNat (p63 - 1))))\n    (.cons ((IntN.rem (I64.ofNeg p63) (I64.ofNeg 1)).toNat)\n    (.cons ((IntN.mul (I64.ofNeg 1) (I64.ofNeg 1)).toNat)\n    (.cons (IntN.natAbs (UIntN.toIntN (U64.ofNat m64)))\n    (.cons (b2n (IntN.isNeg (I64.ofNat p63)))\n    (.cons ((U64.ofNat (Nat.add m64 8)).toNat)\n    (.cons ((I64.ofNeg (Nat.add m64 2)).toNat)\n    (.cons ((UIntN.mul (UIntN.ofNat 65 (Nat.add m64 1)) (UIntN.ofNat 65 2)).toNat)\n    (.cons ((UIntN.ofNat 65 (Nat.add m64 1)).toNat)\n    (.cons ((UIntN.div (U64.ofNat m64) (U64.ofNat p63)).toNat)\n    (.cons ((UIntN.mod (U64.ofNat m64) (U64.ofNat p63)).toNat)\n    (.cons ((UIntN.not (U64.ofNat 0)).toNat)\n    (.cons (b2n (IntN.beq (I64.ofNeg 1) (IntN.not (I64.ofNat 0))))\n    (.cons ((fnv64 (.cons 104 (.cons 105 .nil)) (U64.ofNat 14695981039346656037)).toNat)\n    (.cons ((twice (U64.ofNat p63)).toNat)\n    (.cons ((twice (UIntN.ofNat 70 p63)).toNat)\n    (.cons (bits (U64.ofNat m64))\n    (.cons ((bump (I64.ofNeg 1)).toNat)\n    (.cons ((IntN.toUIntN (I64.ofNeg 2)).toNat)\n    .nil)))))))))))))))))))))))))))))))))))))))))))\n"

def wordTable64Value : String := ".cons 9223372036854775808 (.cons 0 (.cons 18446744073709551615 (.cons 1 (.cons 1 (.cons 0 (.cons 9223372036854775813 (.cons 18446744073709551614 (.cons 9223372036854775809 (.cons 1 (.cons 0 (.cons 9223372036854775808 (.cons 0 (.cons 0 (.cons 1 (.cons 0 (.cons 1 (.cons 255 (.cons 18446744073709551615 (.cons 1267650600228229401496703205375 (.cons 18446744073709551613 (.cons 18446744073709551615 (.cons 18446744073709551615 (.cons 18446744073709551615 (.cons 1 (.cons 0 (.cons 1 (.cons 1 (.cons 1 (.cons 7 (.cons 18446744073709551615 (.cons 0 (.cons 18446744073709551616 (.cons 1 (.cons 9223372036854775807 (.cons 18446744073709551615 (.cons 1 (.cons 628919584683901914 (.cons 0 (.cons 18446744073709551616 (.cons 18446744073709551615 (.cons 0 (.cons 18446744073709551614 .nil))))))))))))))))))))))))))))))))))))))))))"

def wordGroup : Group where
  name := "word"
  exercise := "Stage 22c"
  cases := [
    { name := "the definitions compute in the kernel", run := fun _ =>
        okLib (wordTable ++ s!"def t : main = ({wordTableValue} : List Nat) := refl main") },
    { name := "#eval runs the definitions", run := fun _ =>
        okLib (wordTable ++ "#eval main") [wordTableValue] },
    { name := "#run runs the definitions", run := fun _ =>
        okLib (wordTable ++ "#run main") [wordTableValue] },
    { name := "compiled code runs the natives (C)", run := fun _ => cRun wordTable wordTableValue },
    { name := "compiled code runs the natives (LLVM)", run := fun _ => cRun (llvm := true) wordTable wordTableValue },
    { name := "compiled code calls the native", run := fun _ => do
        let loader ← preludeLoader
        let src := "import Word\ndef f (a b : U32) : U32 := UIntN.add a b\n#ir f"
        let s := runFrontend (R := ZeroOneMany) src { loader, trustedModule := Tests.libModule }
        let out := String.intercalate "\n" (s.messages.toList.map (·.text))
        check ((out.splitOn "wiz_word_add").length > 1) s!"no native call in:\n{out}" },
    { name := "the width is part of the type, and is inferred", run := fun _ => do
        okLib "import Word\ndef w {ω n : Nat} (a : UIntN n) : Nat := n\n#check w (U8.ofNat 3)\n#eval w (U8.ofNat 3)"
          ["w 8 (U8.ofNat 3) : Nat", "8"]
        let loader ← preludeLoader
        let s := runFrontend (R := ZeroOneMany) "import Word\ndef bad (x : U8) : U16 := x" { loader, trustedModule := Tests.libModule }
        check (s.messages.any (·.severity == .error)) "U8 was accepted as U16" },
    { name := "field notation through the fixed widths", run := fun _ =>
        okLib "import Word\ndef f (a b : I16) : Bool := a.lt b\n#eval f (I16.ofNeg 2) (I16.ofNat 1)" [".true"] },
    { name := "64-bit edges: the kernel", run := fun _ =>
        okLib (wordTable64 ++ s!"def t : main = ({wordTable64Value} : List Nat) := refl main") },
    { name := "64-bit edges: #eval", run := fun _ => okLib (wordTable64 ++ "#eval main") [wordTable64Value] },
    { name := "64-bit edges: #run", run := fun _ => okLib (wordTable64 ++ "#run main") [wordTable64Value] },
    { name := "64-bit edges: C", run := fun _ => cRun wordTable64 wordTable64Value },
    { name := "64-bit edges: LLVM", run := fun _ => cRun (llvm := true) wordTable64 wordTable64Value },
    { name := "a word is not an object: no constructor in the IR", run := fun _ => do
        let loader ← preludeLoader
        let src := "import Word\ndef f (a b : U64) : U64 := UIntN.add (UIntN.xor a b) (U64.ofNat 3)\n" ++
          "def g (a : U64) : Nat := a.toNat\n#ir f\n#ir g"
        let s := runFrontend (R := ZeroOneMany) src { loader, trustedModule := Tests.libModule }
        let out := String.intercalate "\n" (s.messages.toList.map (·.text))
        check ((out.splitOn "ctor").length == 1 && (out.splitOn "proj").length == 1) s!"a word object in:\n{out}"
        check ((out.splitOn "wiz_word_to_bits").length > 1) s!"toNat doesn't read the bits natively:\n{out}" },
    { name := "a U64 result is read back from a raw box", run := fun _ =>
        cRun "import Word\ndef main : U64 := UIntN.mul (U64.ofNat 18446744073709551615) (U64.ofNat 3)"
          ".mk 18446744073709551613 ()" },
    -- (7e) numeric classes at the words
    { name := "numerals and operators at word types wrap around", run := fun _ =>
        okLib ("import Word\ndef s : U8 := 250 + 10\n#eval s.toNat\ndef t : s = 4 := rfl\n#eval (300 : U8).toNat\n" ++
          "def mac {ω w : Nat} (a b c : UIntN w) : UIntN w := a * b + c\n#eval (mac (16 : U8) 16 3).toNat\n#eval (1 - 2 : U16).toNat")
          ["4", "44", "3", "65535"] },
    { name := "a numeral that does not fit a word type wraps, with a warning", run := fun _ => do
        let loader ← preludeLoader
        let src := "import Word\ndef a : U8 := 255\ndef b : U8 := 300\ndef c : I8 := -128\ndef d : I8 := 200\n#eval b.toNat"
        let s := runFrontend (R := ZeroOneMany) src { loader, trustedModule := Tests.libModule }
        let ws := (s.messages.filter (·.severity == .warning)).map (·.text)
        checkEq (repr #["the numeral 300 does not fit in UIntN 8 (at most 255): it wraps around to 44",
          "the numeral 200 does not fit in IntN 8 (at most 128): it wraps around to -56"]).pretty (repr ws).pretty
        check (s.messages.any (·.text == "44")) "300 : U8 is not 44" },
    { name := "signed and unsigned division are told apart (one shape, two sealed types)", run := fun _ =>
        okLib "import Word\n#eval (-7 / 2 : I32).toNat\n#eval (-7 % 2 : I32).toNat\n#eval ((4294967289 : U32) / 2).toNat"
          ["4294967293", "4294967295", "2147483644"] },
    { name := "compiled: a + b at a word type calls the native", run := fun _ => do
        let loader ← preludeLoader
        let s := runFrontend (R := ZeroOneMany) "import Word\ndef f (a b : U32) : U32 := a + b * 3\n#ir f" { loader, trustedModule := Tests.libModule }
        let out := String.intercalate "\n" (s.messages.toList.map (·.text))
        check ((out.splitOn "wiz_word_add").length > 1 && (out.splitOn "wiz_word_mul").length > 1 &&
          (out.splitOn "proj").length == 1) s!"no native call (or a dictionary) in:\n{out}" },
    { name := "compiled: operators at words run natively (C)", run := fun _ =>
        cRun "import Word\ndef main : Nat := ((250 : U8) + 10 * 2).toNat + (-1 / 2 : I8).toNat" "14" },
    { name := "22l: a word carries its range: no unchecked builder, and the constructor needs the proof", run := fun _ => do
        -- the probe (wiz-notes/soundness-probes/a3-word-ofbitstrusted.wiz)
        for (src, frag) in [("def bad : UIntN 1 := UIntN.ofBitsTrusted 5", "ofBitsTrusted"),
            ("def bad : UIntN 1 := UIntN.mk 5 rfl", "private"), ("def bad : IntN 1 := IntN.mk 5 rfl", "private")] do
          let ms ← msgsLib ("import Word\n" ++ src ++ "\n")
          check (ms.any fun m => m.startsWith "error" && (m.splitOn frag).length > 1) s!"{src}: {ms}" }
  ]

builtin_initialize registerGroup wordGroup

end Tests.Elab
