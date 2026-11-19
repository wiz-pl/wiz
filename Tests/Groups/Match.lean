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
    -- (#397) The bare form a user writes over `Vec`'s `{0 n}` cons field. Under rule (b)
    -- (the decision of 2026-11-16) `map`'s `{n : Nat}` is data, ω, and the recursive call
    -- passes the erased field: the expected failure is a quantity error at the binder,
    -- with the migration hint — not "a bug in Wiz". `matchPrelude` writes `{0 n}` for the
    -- tests that need `map` to compile; this case keeps that workaround honest.
    { name := "rule (b): a bare {n : Nat} map over the {0 n} cons field is a quantity error, not a compiler bug", run := fun _ => do
        let bare := matchPrelude.replace "def map {A B : Type} (f : A → B) {0 n : Nat}" "def map {A B : Type} (f : A → B) {n : Nat}"
        unless bare != matchPrelude do throw (IO.userError "matchPrelude's map binder changed: update this test")
        let errs := errors bare
        unless errs.size == 1 do throw (IO.userError s!"expected one error, got {errs.size}:\n{errs}")
        let e := errs[0]!
        let expected := "error: the implementation of map (the term compiled code runs) does not check: variable n declared with quantity 0 but used ω\n" ++
          "  (n is erased: only types, proofs and other erased arguments may use it, not the computation)\n" ++
          "  in a recursive call of map: its implicit parameter n has the default quantity ω of a data implicit, but the call passes it a value the match binds at quantity 0 (an erased constructor field such as `{0 n : Nat}`); write `{0 n : …}` if n is only needed in types"
        unless e.endsWith expected do throw (IO.userError s!"error text changed:\n{e}")
        if (e.splitOn "bug in Wiz").length > 1 then throw (IO.userError s!"blames Wiz:\n{e}")
        unless e.startsWith "20:" do throw (IO.userError s!"not reported at map's binder (line 20):\n{e}") },
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
        -- (`n` is only needed in types, and the recursive call passes the erased field of
        -- `cons`: rule (b) makes a bare `{n : Nat}` data, ω, so it is written 0)
        ok (matchPrelude ++ "def zip {A B : Type} {0 n : Nat} : Vec A n → Vec B n → Vec (A × B) n\n" ++
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
