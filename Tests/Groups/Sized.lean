import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

def sizedPrelude : String := "inductive Nat where\n  | zero\n  | succ (n : Nat)\ndef add : Nat → Nat → Nat\n  | .zero, n => n\n  | .succ m, n => .succ (add m n)\ndef fib {i : Size} : Nat^i → Nat\n  | .zero => .succ .zero\n  | .succ .zero => .succ .zero\n  | .succ (.succ n) => add (fib n) (fib (.succ n))\n\n"

def sizedGroup : Group where
  name := "sized types"
  exercise := "Exercises 4.22–4.23"
  cases := [
    { name := "subtyping: smaller sizes fit bigger ones", run := fun _ =>
        ok (sizedPrelude ++ "#check fun (i : Size) (j : Size< i) (x : Nat^j) => (x : Nat^i)")
          ["fun i j x => (x : Nat^i) : (i : Size) → (j : Size< i) → Nat^j → Nat^i"] },
    { name := "but not the other way round", run := fun _ =>
        fails (sizedPrelude ++ "#check fun (i : Size) (j : Size< i) (x : Nat^i) => (x : Nat^j)") "mismatch" },
    { name := "sized case analysis keeps field sizes", run := fun _ =>
        ok (sizedPrelude ++ "#check @Nat.scasesOn")
          ["Nat.scasesOn : {s : Size} → (0 motive : Nat → Sort ?u0) → ((0 j : Size< s) → motive .zero) → ((0 j : Size< s) → (n : Nat^j) → motive (.succ n)) → (x : Nat^s) → motive x"] },
    { name := "course-of-values recursion (fib)", run := fun _ =>
        ok (sizedPrelude ++ "#reduce fib (.succ (.succ (.succ (.succ .zero))))")
          [".succ (.succ (.succ (.succ (.succ .zero))))"] },
    { name := "a call at the same size is rejected", run := fun _ =>
        fails (sizedPrelude ++ "def bad {i : Size} : Nat^i → Nat\n  | n => bad n") "mismatch" },
    { name := "a call on a rebuilt value is rejected", run := fun _ =>
        fails (sizedPrelude ++ "def bad {i : Size} : Nat^i → Nat\n  | .zero => .zero\n  | .succ n => bad (.succ n)") "not below" },
    { name := "∞ is not a size below ∞", run := fun _ =>
        fails (sizedPrelude ++ "def bad : Size< ∞ := ∞") "mismatch" }
  ]

builtin_initialize registerGroup sizedGroup

end Tests.Elab
