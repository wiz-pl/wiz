import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

def matchGroup : Group where
  name := "match"
  exercise := "stage 4e"
  cases := [
    { name := "pred, add, head, map", run := fun _ => ok matchPrelude },
    { name := "match expression", run := fun _ =>
        ok (matchPrelude ++ "#reduce pred (.succ (.succ .zero))") [".succ .zero"] },
    { name := "structural recursion with a varying argument", run := fun _ =>
        ok (matchPrelude ++ "#reduce add (.succ .zero) (.succ (.succ .zero))") [".succ (.succ (.succ .zero))"] },
    { name := "impossible cases may be omitted (head)", run := fun _ =>
        ok (matchPrelude ++ "#reduce head (Vec.cons Nat.zero Vec.nil)") [".zero"] },
    { name := "recursion over an indexed family (map)", run := fun _ =>
        ok (matchPrelude ++ "#reduce map (fun _ => Nat.zero) (Vec.cons (Nat.succ Nat.zero) Vec.nil)")
          [".cons .zero .zero .nil"] },
    { name := "nested patterns and wildcards", run := fun _ =>
        ok (matchPrelude ++ "def isTwo : Nat → Nat\n  | .succ (.succ .zero) => .succ .zero\n  | _ => .zero\n" ++
            "#reduce isTwo (.succ (.succ .zero))\n#reduce isTwo (.succ .zero)") [".succ .zero", ".zero"] },
    { name := "recursion through two columns", run := fun _ =>
        ok (matchPrelude ++ "def eqb : Nat → Nat → Nat\n  | .zero, .zero => .succ .zero\n" ++
            "  | .succ m, .succ n => eqb m n\n  | _, _ => .zero\n#reduce eqb (.succ .zero) (.succ .zero)") [".succ .zero"] },
    { name := "index unification by substitution (tail)", run := fun _ =>
        ok (matchPrelude ++ "def tail {A : Type} {n : Nat} : Vec A (.succ n) → Vec A n\n  | .cons _ xs => xs\n" ++
            "#reduce tail (Vec.cons Nat.zero (Vec.cons (Nat.succ Nat.zero) Vec.nil))") [".cons .zero (.succ .zero) .nil"] },
    { name := "zip: impossible pairs omitted, lengths unified", run := fun _ =>
        ok (matchPrelude ++ "def zip {A B : Type} {n : Nat} : Vec A n → Vec B n → Vec (A × B) n\n" ++
            "  | .nil, .nil => .nil\n  | .cons a as, .cons b bs => .cons (a, b) (zip as bs)\n" ++
            "#reduce zip (Vec.cons Nat.zero Vec.nil) (Vec.cons (Nat.succ Nat.zero) Vec.nil)")
          [".cons .zero (.zero, .succ .zero) .nil"] },
    { name := "tuples of variables infer their type", run := fun _ =>
        ok (matchPrelude ++ "def t1 (A B : Type) (n : Nat) (a : A) (b : B) (r : Vec (A × B) n) : Vec (A × B) (.succ n) := Vec.cons (a, b) r") },
    { name := "missing cases are reported", run := fun _ =>
        fails (matchPrelude ++ "def missing : Nat → Nat\n  | .zero => .zero") "missing case" },
    { name := "non-structural recursion is rejected", run := fun _ =>
        fails (matchPrelude ++ "def bad : Nat → Nat\n  | .zero => .zero\n  | .succ m => bad (.succ m)") "recursive call" }
  ]

builtin_initialize registerGroup matchGroup

end Tests.Elab
