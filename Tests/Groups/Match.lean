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
    { name := "#267 a parameter before the colon that a recursive call changes", run := fun _ =>
        -- the varying parameter moves after the colon, as Lean does (it used to be
        -- "recursive call of run must pass the parameter s unchanged")
        okLib ("import Prelude\ndef run (s : Nat) : List Nat → Nat\n  | .nil => s\n" ++
          "  | .cons x xs => run (Nat.add s x) xs\n#eval run 1 (.cons 2 (.cons 3 .nil))") ["6"] },
    { name := "#267 a varying parameter before the colon, with another parameter after it", run := fun _ =>
        okLib ("import Prelude\ndef run (s k : Nat) : List Nat → Nat\n  | .nil => Nat.add s k\n" ++
          "  | .cons x xs => run (Nat.add s x) k xs\n#eval run 1 10 (.cons 2 (.cons 3 .nil))") ["16"] },
    { name := "#267 a varying parameter after an implicit binder", run := fun _ =>
        okLib ("import Prelude\ndef run {A : Type} (s : Nat) : List A → Nat\n  | .nil => s\n" ++
          "  | .cons x xs => run (Nat.add s 1) xs\n#eval run 1 (.cons 2 (.cons 3 .nil))") ["3"] },
    { name := "#267 moving a parameter does not accept recursion on a non-field", run := fun _ =>
        failsLib ("import Prelude\ndef bad (s : Nat) : List Nat → Nat\n  | .nil => s\n" ++
          "  | .cons x xs => bad (Nat.add s x) (List.cons 0 xs)") "not a recursive field" },
    { name := "#259 a hypothesis before the colon is refined by the match", run := fun _ =>
        -- `h : b = .true` depends on the scrutinee, so it is generalised into the match
        -- (otherwise the `.false` branch sees `h : b = .true`, and `h.1` has no `False`)
        okLib ("import Logic\ndef f (b : Bool) (h : b = .true) : Nat := match b with\n" ++
          "  | .true => 0\n  | .false => absurd h.1\n#eval f .true rfl") ["0"] },
    { name := "#259 a hypothesis about a scrutinee expression is refined", run := fun _ =>
        okLib ("import Logic\ndef f (n : Nat) (h : Nat.pred n = 0) : Nat := match Nat.pred n with\n" ++
          "  | .zero => 0\n  | .succ m => absurd h.1") },
    { name := "#259 two hypotheses about the scrutinee are both refined", run := fun _ =>
        okLib ("import Logic\ndef f (b : Bool) (h : b = .true) (k : b = .false) : Nat := match b with\n" ++
          "  | .true => absurd k.1\n  | .false => absurd h.1") },
    { name := "missing cases are reported", run := fun _ =>
        fails (matchPrelude ++ "def missing : Nat → Nat\n  | .zero => .zero") "missing case" },
    { name := "non-structural recursion is rejected", run := fun _ =>
        fails (matchPrelude ++ "def bad : Nat → Nat\n  | .zero => .zero\n  | .succ m => bad (.succ m)") "recursive call" }
  ]

builtin_initialize registerGroup matchGroup

end Tests.Elab
