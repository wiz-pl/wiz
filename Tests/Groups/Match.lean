import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- Stage 4e: `match h : e with`, a split on a computed value with its equation. -/
def eqnPrelude : String := matchPrelude ++ "
inductive Bool where
  | false
  | true

def isZero (n : Nat) : Bool := match n with
  | .zero => .true
  | .succ _ => .false

def f (b : Bool) : Bool := match b with
  | .true => .true
  | .false => .false

def g (n : Nat) : Bool := f (isZero n)

/-- `e : a = b` under a function -/
def cong {A B : Type} (h : A → B) {a b : A} (e : a = b) : h a = h b :=
  transp (fun t _ => h a = h t) (refl (h a)) e

/-- `a = b` then `b = c` -/
def trans {A : Type} {a b c : A} (e : a = b) (f : b = c) : a = c :=
  transp (fun t _ => a = t) e f

/-- `isZero` inspected a second time -/
def f2 (n : Nat) : Bool := isZero (Nat.succ n)
"

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
    -- (#254 + #259) the equation is an extra column after the reverted hypotheses: both
    -- are in scope, and the branch is refined by both, so the columns must line up
    { name := "#254+#259 a named equation and a reverted hypothesis are both refined", run := fun _ =>
        okLib ("import Logic\ndef f (b : Bool) (h : b = .false) : b = .false :=\n" ++
          "  match k : b with\n  | .true => absurd h.1\n  | .false => k\n") },
    { name := "missing cases are reported", run := fun _ =>
        fails (matchPrelude ++ "def missing : Nat → Nat\n  | .zero => .zero") "missing case" },
    { name := "non-structural recursion is rejected", run := fun _ =>
        fails (matchPrelude ++ "def bad : Nat → Nat\n  | .zero => .zero\n  | .succ m => bad (.succ m)") "recursive call" },
    -- `match h : e with`: the branch gets `h : e = <pattern>`
    { name := "a split on a computed value keeps its equation", run := fun _ =>
        ok (eqnPrelude ++
          "def gEq (n : Nat) : g n = isZero n :=\n" ++
          "  match h : isZero n with\n" ++
          "  | .true => cong f h\n" ++
          "  | .false => cong f h\n") },
    { name := "two scrutinees name both equations", run := fun _ =>
        ok (eqnPrelude ++
          "def g2 (b c : Bool) : Bool := match b, c with\n" ++
          "  | .true, .true => .true\n" ++
          "  | .true, .false => .true\n" ++
          "  | .false, .true => .false\n" ++
          "  | .false, .false => .false\n" ++
          "def G2 (n m : Nat) : Bool := g2 (isZero n) (isZero m)\n" ++
          "def G2Eq (n m : Nat) : G2 n m = isZero n :=\n" ++
          "  match h : isZero n, k : isZero m with\n" ++
          "  | .true, .true => trans (cong (fun b => g2 b (isZero m)) h) (cong (fun c => g2 .true c) k)\n" ++
          "  | .true, .false => trans (cong (fun b => g2 b (isZero m)) h) (cong (fun c => g2 .true c) k)\n" ++
          "  | .false, .true => trans (cong (fun b => g2 b (isZero m)) h) (cong (fun c => g2 .false c) k)\n" ++
          "  | .false, .false => trans (cong (fun b => g2 b (isZero m)) h) (cong (fun c => g2 .false c) k)\n") },
    -- the equation's type lives after *all* the scrutinee binders and only the
    -- equations bound before it: an unnamed earlier column must not shift it
    { name := "a named scrutinee after an unnamed one keeps its equation", run := fun _ =>
        ok (eqnPrelude ++
          "def useEq (n : Nat) (b : Bool) (e : isZero n = b) : Nat :=\n" ++
          "  match b with\n" ++
          "  | .true => .succ .zero\n" ++
          "  | .false => .zero\n" ++
          "def mixed (n : Nat) (b : Bool) : Nat :=\n" ++
          "  match b, h : isZero n with\n" ++
          "  | .true, .true => useEq n .true h\n" ++
          "  | .true, .false => useEq n .false h\n" ++
          "  | .false, .true => useEq n .true h\n" ++
          "  | .false, .false => useEq n .false h\n") },
    { name := "a non-dependent match still has its equation", run := fun _ =>
        ok (eqnPrelude ++
          "def useEq (n : Nat) (b : Bool) (e : isZero n = b) : Nat :=\n" ++
          "  match b with\n" ++
          "  | .true => .succ .zero\n" ++
          "  | .false => .zero\n" ++
          "def nonDep (n : Nat) : Nat :=\n" ++
          "  match h : isZero n with\n" ++
          "  | .true => useEq n .true h\n" ++
          "  | .false => useEq n .false h\n") },
    -- (the inner scrutinee is another variable: both of its branches are possible, and
    -- the body uses the outer equation `h` and the inner one `k` in every branch)
    { name := "nested matches both keep their equations", run := fun _ =>
        ok (eqnPrelude ++
          "def useEq (n : Nat) (b : Bool) (e : isZero n = b) : Bool := b\n" ++
          "def nestedEq (n m : Nat) : Bool × Bool :=\n" ++
          "  match h : isZero n with\n" ++
          "  | .true =>\n" ++
          "    match k : isZero m with\n" ++
          "    | .true => (useEq n .true h, useEq m .true k)\n" ++
          "    | .false => (useEq n .true h, useEq m .false k)\n" ++
          "  | .false =>\n" ++
          "    match k : isZero m with\n" ++
          "    | .true => (useEq n .false h, useEq m .true k)\n" ++
          "    | .false => (useEq n .false h, useEq m .false k)\n") },
    { name := "a plain match on a variable named h still parses", run := fun _ =>
        ok (matchPrelude ++
          "def pick (h : Nat) : Nat := match h with\n" ++
          "  | .zero => .zero\n" ++
          "  | _ => h\n") },
    -- the equation of a split on an indexed value would need the index refined in the
    -- context, which this match compiler does not do: reported rather than ill typed
    { name := "an indexed scrutinee's equation is reported, not ill typed", run := fun _ =>
        fails (matchPrelude ++
          "def headEq (v : Vec Nat (.succ .zero)) : Nat :=\n" ++
          "  match h : v with\n" ++
          "  | .cons x _ => x\n") "indexed type" }
  ]

builtin_initialize registerGroup matchGroup

end Tests.Elab
