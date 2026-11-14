import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

def procPrelude : String := "import Prelude
syntax (name := twice) \"twice!\" term : term
def twiceMacro : Macro := fun stx => do
  e ← MacroM.pure (Syntax.getArg stx 1);
  MacroM.pure `(term| let y := $e; Nat.add y y)
attribute [macro term.twice] twiceMacro
"

def builtinGroup : Group where
  name := "builtins"
  exercise := "Stage 6b"
  cases := [
    { name := "import the prelude", run := fun _ =>
        okLib "import Prelude\n#check List.append" ["List.append : {A : Type} → List A → List A → List A"] },
    { name := "a stuck number times a big numeral, in a type (nat-pow-blowup)", run := fun _ =>
        okLib ("import Word\naxiom Q : Nat → Type\naxiom y : (n : Nat) → Q (Nat.mod n 18446744073709551616)\n" ++
          "def bump (a : I64) : I64 := IntN.ofNat 64 (Nat.mod (Nat.add a.toNat 1) (Nat.pow 2 64))") },
    { name := "Nat.beq and Nat.lt compute natively on numerals", run := fun _ =>
        okLib ("import Word\ndef t : Nat.beq 9223372036854775808 9223372036854775808 = Bool.true := rfl\n" ++
          "def u : Nat.lt 9223372036854775807 9223372036854775808 = Bool.true := rfl\n" ++
          "def v : Nat.lt 9223372036854775808 9223372036854775807 = Bool.false := rfl\n" ++
          "def w : UIntN.beq (U64.ofNat 9223372036854775808) (U64.ofNat 9223372036854775809) = .false := rfl\n" ++
          "#reduce Nat.beq 3 4\n#reduce Nat.lt 3 4") [".false", ".true"] },
    { name := "numerals and native arithmetic", run := fun _ =>
        okLib "import Prelude\n#eval 100 * 100 * 100 - 1" ["999999"] },
    { name := "recursion over native numbers", run := fun _ =>
        okLib "import Prelude\ndef fact : Nat → Nat\n  | .zero => 1\n  | .succ n => (.succ n) * fact n\n#eval fact 20"
          ["2432902008176640000"] },
    { name := "numerals reduce in the kernel", run := fun _ =>
        okLib "import Prelude\ndef t : 2 + 2 = 4 := refl 4" },
    { name := "native equality", run := fun _ =>
        okLib "import Prelude\n#eval Nat.beq 3 3" [".true"] },
    { name := "division, powers and bits compute natively (#eval)", run := fun _ =>
        okLib ("import Prelude\n#eval Nat.div 100 7\n#eval Nat.mod 100 7\n#eval 100 / 0\n#eval Nat.mod 5 0\n" ++
          "#eval Nat.pow 2 100\n#eval Nat.land 12 10\n#eval Nat.lor 12 10\n#eval Nat.xor 12 10\n" ++
          "#eval Nat.shiftLeft 3 70\n#eval Nat.shiftRight (Nat.pow 2 100) 98\n#eval Nat.log2 1025\n#eval Nat.log2 0\n#eval Nat.testBit 5 2")
          ["14", "2", "0", "5", "1267650600228229401496703205376", "8", "14", "6", "3541774862152233910272", "4", "10", "0", ".true"] },
    { name := "division, powers and bits in the IR interpreter (#run)", run := fun _ =>
        okLib ("import Prelude\n#run Nat.mod (Nat.pow 3 50) 1000007\n#run Nat.land (Nat.pow 2 70) (Nat.pow 2 70 + 5)\n" ++
          "#run Nat.log2 (Nat.pow 2 70)\n#run Nat.shiftRight 1000 3\n#run Nat.xor 5 3")
          ["961749", "1180591620717411303424", "70", "125", "6"] },
    { name := "division, powers and bits compute natively in the kernel", run := fun _ =>
        okLib ("import Prelude\ndef t1 : Nat.mod 300 256 = 44 := refl 44\n" ++
          "def t2 : Nat.xor (Nat.pow 2 64) 1 = 18446744073709551617 := refl 18446744073709551617\n" ++
          "def t3 : Nat.shiftRight (Nat.shiftLeft 5 200) 199 = 10 := refl 10\n" ++
          "def t4 : Nat.log2 (Nat.pow 2 300) = 300 := refl 300\n" ++
          "def t5 : Nat.land (Nat.pow 2 70) (Nat.pow 2 70 + 5) = Nat.pow 2 70 := refl (Nat.pow 2 70)") },
    { name := "the definitions behind the natives compute too (unfolded)", run := fun _ =>
        -- the fuel-driven helpers, applied directly, are not registered: the kernel unfolds them
        okLib ("import Prelude\ndef t1 : Nat.divGo 17 17 5 = 3 := refl 3\n" ++
          "def t2 : Nat.bitwise Bool.xor 30 12 10 = 6 := refl 6\ndef t3 : Nat.bitwise Bool.and 30 12 10 = 8 := refl 8\n" ++
          "def t4 : Nat.log2Go 9 9 = 3 := refl 3\ndef t5 : Nat.powFrom 10 2 = 1024 := refl 1024") },
    { name := "a Nat operation's erased argument is not compared (nat zero step)", run := fun _ =>
        -- `Nat.add (Nat.mul 0 2) X` is `X`: conversion must not descend into a stuck `X`
        -- (here `f y`, or a `Nat.div`-heavy tree) before finding that out; a re-entry there
        -- made this comparison not terminate (wiz-notes/rv-shift-lemmas.md §7).
        okLib ("import Prelude\n" ++
          "def t (f : Nat → Nat) (y : Nat) : f y = Nat.add (Nat.mul 0 (Nat.pow 2 1)) (f y) := rfl\n" ++
          "def tree : Nat → Nat → Nat\n  | .zero, z => z\n  | .succ k, z => Nat.add (tree k z) (tree k z)\n" ++
          "def u (z : Nat) : Nat.mul 0 (tree 8 z) = Nat.mul 0 (tree 8 (Nat.add (Nat.mul 0 (Nat.pow 2 1)) z)) := rfl\n" ++
          "def v (z : Nat) : Nat.div (Nat.add (Nat.mul 0 (Nat.pow 2 1)) z) 2 = Nat.div z 2 := rfl\n" ++
          -- the product is 0 whatever `slow` is: forcing it here made the check cost `slow`'s
          -- whole `Nat.divGo` recursion (200000 was 46 s before the fix)
          "def slow : Nat := Nat.divGo 20000 20000 1\n" ++
          "def w : Nat.mul 0 slow = Nat.mul 0 (Nat.add (Nat.mul 0 (Nat.pow 2 1)) slow) := rfl") },
    { name := "implemented_by: compiled code runs the implementation, the kernel the model", run := fun _ => do
        -- the implementation is trusted: here it deliberately differs, to show which runs
        let src := "import Prelude\ndef model (n : Nat) : Nat := n\ndef impl (n : Nat) : Nat := n + 1\n" ++
          "attribute [implemented_by impl] model\ndef t : model 5 = 5 := refl 5\n"
        okLib (src ++ "#eval model 5\n#run model 5") ["6", "6"]
        cRun (src ++ "def main : Nat := model 5") "6" },
    { name := "implemented_by: a fast implementation of a recursive definition", run := fun _ =>
        okLib ("import Prelude\ndef sumTo : Nat → Nat\n  | .zero => 0\n  | .succ n => .succ n + sumTo n\n" ++
          "def sumToFast (n : Nat) : Nat := n * (n + 1) / 2\nattribute [implemented_by sumToFast] sumTo\n" ++
          "def t : sumTo 4 = 10 := refl 10\n#erase sumTo\n#eval sumTo 1000000") ["sumTo := sumToFast", "500000500000"] },
    { name := "implemented_by: the types must agree", run := fun _ =>
        failsLib "import Prelude\ndef f (n : Nat) : Nat := n\ndef g (b : Bool) : Nat := 0\nattribute [implemented_by g] f"
          "g can't implement f: its type Bool → Nat is not f's type Nat → Nat" },
    { name := "implemented_by: not on a builtin", run := fun _ =>
        failsLib "import Prelude\ndef g (m n : Nat) : Nat := m\nattribute [implemented_by g] Nat.add" "already has an implementation" },
    { name := "the natives agree with the definitions (n / 0 = 0)", run := fun _ => do
        let prelude ← IO.FS.readFile "lib/Prelude.wiz"
        let s := runFrontend (R := ZeroOneMany) "import Prelude\ndef t : Nat.div 7 0 = 7 := refl 7" { trustedModule := Tests.libModule, loader := fun _ => some prelude }
        check (s.messages.any (·.severity == .error)) "expected an error" },
    { name := "kernel arithmetic on literals is native", run := fun _ =>
        okLib "import Prelude\ndef t : 100000 * 100000 = 10000000000 := refl 10000000000" },
    { name := "literals unfold under eliminators", run := fun _ =>
        okLib ("import Prelude\ndef isZero : Nat → Bool\n  | .zero => .true\n  | .succ _ => .false\n" ++
          "def t : isZero 3 = Bool.false := refl Bool.false\ndef u : Nat.succ 4 = 5 := refl 5") },
    { name := "different literals are not equal", run := fun _ => do
        let prelude ← IO.FS.readFile "lib/Prelude.wiz"
        let s := runFrontend (R := ZeroOneMany) "import Prelude\ndef t : 2 + 2 = 5 := refl 4" { trustedModule := Tests.libModule, loader := fun _ => some prelude }
        check (s.messages.any (·.severity == .error)) "expected an error" },
    { name := "non-ASCII strings are cheap", run := fun _ =>
        okLib "import Prelude\n#eval \"λ✝\"" ["\"λ✝\""] },
    { name := "do notation (a macro)", run := fun _ =>
        okLib ("import Prelude\n#eval (do x ← TacticM.pure 2; y ← TacticM.pure 3; TacticM.pure (x + y) : TacticM Nat)\n" ++
          "  (fun n => Tac.setGoals (.cons n .nil) Tac.done)") [".setGoals (.cons 5 .nil) .done"] },
    { name := "quotations build Syntax (Exercise 6.2)", run := fun _ =>
        okLib "import Prelude\n#eval `(term| f .x)"
          [".node \"term.app\" (.cons (.node \"term.ident\" (.cons (.ident \"f✝\") .nil)) " ++
           "(.cons (.node \"null\" (.cons (.node \"term.dotIdent\" (.cons (.atom \".\") (.cons (.ident \"x\") .nil))) .nil)) .nil))"] },
    { name := "a procedural macro (Exercise 6.3)", run := fun _ =>
        okLib (procPrelude ++ "#eval twice! 21") ["42"] },
    { name := "procedural macros are hygienic", run := fun _ =>
        okLib (procPrelude ++ "def y : Nat := 5\n#eval twice! y") ["10"] },
    { name := "a procedural macro can fail", run := fun _ => do
        let prelude ← IO.FS.readFile "lib/Prelude.wiz"
        let src := procPrelude ++ "syntax (name := boom) \"boom!\" : term\n" ++
          "def boomMacro : Macro := fun _ => MacroM.throw \"kaboom\"\nattribute [macro term.boom] boomMacro\n#eval (boom! : Nat)"
        let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := fun _ => some prelude }
        check (s.messages.any (·.text == "kaboom")) s!"expected kaboom, got {s.messages.map (·.text)}" },
    { name := "only a Macro can be a macro", run := fun _ => do
        let prelude ← IO.FS.readFile "lib/Prelude.wiz"
        let s := runFrontend (R := ZeroOneMany) "import Prelude\nattribute [macro term.app] Nat.add" { trustedModule := Tests.libModule, loader := fun _ => some prelude }
        check (s.messages.any (·.severity == .error)) "expected an error" },
    { name := "infinitary inductive: recursor", run := fun _ =>
        okLib (treePrelude ++ "#check Tree.rec")
          ["Tree.rec : (0 motive : Tree → Sort ?u0) → motive .leaf → ((k : Nat → Tree) → ((x : Nat) → motive (k x)) → " ++
           "motive (.node k)) → (x : Tree) → motive x"] },
    { name := "infinitary inductive: structural recursion through k n", run := fun _ =>
        okLib (treePrelude ++ "#eval Tree.depthAt (.node (fun i => .node (fun j => .leaf))) 3") ["3"] },
    { name := "infinitary inductive: indexed, dependent branching", run := fun _ =>
        okLib ("import Prelude\ninductive W (A : Type) : Nat → Type where\n  | sup (n : Nat) (k : (i : Nat) → W A i) : W A (.succ n)\n" ++
          "#check W.sup") ["W.sup : {A : Type} → (n : Nat) → ((i : Nat) → W A i) → W A (.succ n)"] },
    { name := "infinitary inductive: the domain may not mention the type", run := fun _ => do
        let prelude ← IO.FS.readFile "lib/Prelude.wiz"
        let s := runFrontend (R := ZeroOneMany) "import Prelude\ninductive Bad where\n  | mk (k : Bad → Bad)" { trustedModule := Tests.libModule, loader := fun _ => some prelude }
        check (s.messages.any (·.severity == .error)) "expected an error" },
    { name := "a match does not shadow the user's variables", run := fun _ =>
        okLib "import Prelude\ndef e (x : Bool) (n : Nat) : Bool := match n with\n  | .zero => x\n  | .succ _ => x" },
    { name := "nested match alternatives line up (colGe)", run := fun _ =>
        okLib ("import Prelude\ndef nth : List Bool → Nat → Bool\n  | .cons x t, n => match n with\n" ++
          "    | .zero => x\n    | .succ m => nth t m\n  | _, _ => .false\n#eval nth (.cons .false (.cons .true .nil)) 1") [".true"] },
    { name := "string literals", run := fun _ =>
        okLib "import Prelude\n#eval String.append \"ab\" \"cd\"" ["\"abcd\""] },
    { name := "a numeral is not a string", run := fun _ => do
        let prelude ← IO.FS.readFile "lib/Prelude.wiz"
        let s := runFrontend (R := ZeroOneMany) "import Prelude\ndef s : String := 3" { trustedModule := Tests.libModule, loader := fun _ => some prelude }
        check (s.messages.any (·.severity == .error)) "expected an error" },
    -- S1 (`wiz-notes/soundness-audit.md`): `Term.mapChildrenM` had no case for `natOp`, so
    -- the variable captured by `Nat.add x` was invisible to `Val.lvlBound`, `sameVal` quoted
    -- below it, and `μ D_x () = μ D_y ()` computed to `() = ()`. With `T (Nat.add 0)`
    -- inhabited and `T (Nat.add 1)` empty, `cast (e 0 1)` then gave a closed proof of False.
    { name := "S1: a variable captured by a native operation counts in syntactic equality (it proved False)", run := fun _ => do
        let t := "import Prelude\ndef T (f : Nat → Nat) : Type := match f 0 with\n  | .zero => Unit\n  | .succ _ => Empty\n"
        failsLib (t ++ "def Box (x : Nat) : Type := μ (Desc.arg 1 (T (Nat.add x)) (fun _ => Desc.ret ()) : Desc Unit) ()\n" ++
          "def e (x y : Nat) : Box x = Box y := ()\n") "mismatch"
        failsLib (t ++ "inductive Box (f : Nat → Nat) where\n  | mk (t : T f)\n" ++
          "def e (x y : Nat) : Box (Nat.add x) = Box (Nat.add y) := ()\n") "mismatch"
        failsLib (t ++ "inductive Box (f : Nat → Nat) where\n  | mk (t : T f)\n" ++
          "def e (x y : Nat) : Box (Nat.mul x) = Box (Nat.sub y) := ()\n") "mismatch" },
    { name := "S1: the same family at the same partial application is still one family", run := fun _ =>
        okLib ("import Prelude\ndef T (f : Nat → Nat) : Type := match f 0 with\n  | .zero => Unit\n  | .succ _ => Empty\n" ++
          "inductive Box (f : Nat → Nat) where\n  | mk (t : T f)\n" ++
          "def e (x : Nat) : Box (Nat.add x) = Box (Nat.add x) := rfl\n") }
  ]

builtin_initialize registerGroup builtinGroup

end Tests.Elab
