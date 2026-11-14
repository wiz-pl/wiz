import Wiz
import Tests.Harness

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

open Wiz Raw

namespace Tests.Eval

abbrev T := Term Unit

def nf' (t : Raw Unit) (g : Globals Unit := {}) : String := (nf g t.toTerm).pretty

/-- A few untyped-but-terminating terms; `eval`/`quote` don't need types. -/
def idR : Raw Unit := lams ["x"] "x"
def constR : Raw Unit := lams ["x", "y"] "x"
def church (n : Nat) : Raw Unit :=
  lams ["s", "z"] ((List.range n).foldl (fun acc _ => .app "s" acc) "z")
def addR : Raw Unit := lams ["m", "n", "s", "z"] (apps "m" ["s", apps "n" ["s", "z"]])

def axiomsG : Globals Unit :=
  ({} : Globals Unit) |>.insert (Raw.axiom "f" ty) |>.insert (Raw.axiom "a" ty)

def evalGroup : Group where
  name := "eval/quote"
  parallel := true
  exercise := "Exercises 1.1–1.3"
  cases := [
    { name := "Type normalises to itself", run := fun _ => checkEq "Type" (nf' (.sort 0)) },
    { name := "λx. x is already normal", run := fun _ => checkEq "fun x => x" (nf' idR) },
    { name := "β: (λx. x) (λy. y) ⇝ λy. y",
      run := fun _ => checkEq "fun y => y" (nf' (.app idR (lams ["y"] "y"))) },
    { name := "closures capture: (λx y. x) (λz. z) ⇝ λy z. z",
      run := fun _ => checkEq "fun y z => z" (nf' (.app constR (lams ["z"] "z"))) },
    { name := "de Bruijn levels → indices: λx y. x y",
      run := fun _ => checkEq (Term.lam (R := Unit) "x" (.lam "y" (.app (.var 1) (.var 0))))
        (nf {} (lams ["x", "y"] (.app "x" "y") : Raw Unit).toTerm) },
    { name := "normalise under binders: λx. (λy. y) x ⇝ λx. x",
      run := fun _ => checkEq "fun x => x" (nf' (lams ["x"] (.app idR "x"))) },
    { name := "church 2 + 2 = 4",
      run := fun _ => checkEq (nf' (church 4)) (nf' (apps addR [church 2, church 2])) },
    { name := "let: let y := (λx. x); y ⇝ λx. x",
      run := fun _ => checkEq "fun x => x" (nf' (.letE "y" () ty idR "y")) },
    { name := "axioms stay stuck: f ((λx. x) a) ⇝ f a",
      run := fun _ => checkEq "f a" (nf' (.app "f" (.app idR "a")) axiomsG) },
    { name := "definitions unfold",
      run := fun _ => checkEq "fun x => x"
        (nf' "myid" (({} : Globals Unit).insert (Raw.defn "myid" ty idR))) },
    { name := "Π types: codomain normalised under binder",
      run := fun _ => checkEq "(A : Type) → A"
        (nf' (pi' "A" () ty (.app idR "A"))) }
  ]

/-- Axioms for conversion tests: `A : Type`, `f : A → A`, `a b : A`, `u : Unit`,
`p : A × A`. -/
def convG : Globals Unit :=
  [Raw.axiom "A" ty, Raw.axiom "f" (arr () "A" "A"), Raw.axiom "a" "A", Raw.axiom "b" "A"].foldl
    Globals.insert {}
  |>.insert { name := "u", type := .unit 1, value := none }
  |>.insert { name := "p", type := .sigma "x" (.qlit ()) (.const "A" []) (.const "A" []) ⟨1, 1⟩, value := none }

/-- Are `x` and `y` convertible at type `t`? -/
def isConv (t x y : Raw Unit) : Bool :=
  let ev (r : Raw Unit) := eval convG [] r.toTerm
  conv convG #[] (ev t) (ev x) (ev y)

def isConvTy (x y : Raw Unit) : Bool :=
  let ev (r : Raw Unit) := eval convG [] r.toTerm
  convTy convG #[] (ev x) (ev y)

def aa : Raw Unit := arr () "A" "A"

def convGroup : Group where
  name := "conv"
  parallel := true
  exercise := "Exercise 1.4"
  cases := [
    { name := "Type ≡ Type", run := fun _ => check (isConvTy ty ty) "" },
    { name := "Type ≢ Type 1", run := fun _ => check (!isConvTy ty (.sort 1)) "" },
    { name := "α-equivalence: λx. x ≡ λy. y",
      run := fun _ => check (isConv aa idR (lams ["y"] "y")) "" },
    { name := "β: (λx. x) a ≡ a", run := fun _ => check (isConv "A" (.app idR "a") "a") "" },
    { name := "η: λx. f x ≡ f", run := fun _ => check (isConv aa (lams ["x"] (.app "f" "x")) "f") "" },
    { name := "η (other side): f ≡ λx. f x",
      run := fun _ => check (isConv aa "f" (lams ["x"] (.app "f" "x"))) "" },
    { name := "different axioms: a ≢ b", run := fun _ => check (!isConv "A" "a" "b") "" },
    { name := "f a ≢ f b", run := fun _ => check (!isConv "A" (.app "f" "a") (.app "f" "b")) "" },
    { name := "λx y. x ≢ λx y. y",
      run := fun _ => check (!isConv (arr () "A" aa) constR (lams ["x", "y"] "y")) "" },
    { name := "Π: (A : Type) → A ≢ (A : Type) → Type",
      run := fun _ => check (!isConvTy (pi' "A" () ty "A") (pi' "A" () ty ty)) "" }
  ]

def structGroup : Group where
  name := "conv: structural types"
  parallel := true
  exercise := "Exercises 4.3–4.6"
  cases := [
    { name := "β for pairs: (a, b).1 ≡ a", run := fun _ =>
        check (isConv "A" (.fst (.pair "a" "b")) "a") "" },
    { name := "η for pairs: p ≡ (p.1, p.2)", run := fun _ =>
        check (isConv (.sigma "x" () "A" "A") "p" (.pair (.fst "p") (.snd "p"))) "" },
    { name := "η for unit: u ≡ ()", run := fun _ =>
        check (isConv (.unit 1) "u" .tt) "" },
    { name := "p.1 ≢ p.2", run := fun _ =>
        check (!isConv "A" (.fst "p") (.snd "p")) "" },
    { name := "split computes on pairs", run := fun _ =>
        check (isConv "A" (.split () (.pair "a" "b") "z" "A" "x" "y" "y") "b") "" },
    { name := "nf: (fun q => q.2) (a, b) ⇝ b", run := fun _ =>
        checkEq "b" (nf' (.app (lams ["q"] (.snd "q")) (.pair "a" "b")) convG) },
    { name := "nf of a stuck split", run := fun _ =>
        checkEq "let (x, y) := p; f y"
          (nf' (.split () "p" "z" "A" "x" "y" (.app "f" "y")) convG) },
    { name := "Σ types compare structurally", run := fun _ => do
        check (isConvTy (.sigma "x" () "A" "A") (.sigma "y" () "A" "A")) "names don't matter"
        check (!isConvTy (.sigma "x" () "A" "A") (.sigma "x" () "A" (.unit 1))) "" }
  ]

/-- This module's test groups, which `Tests/Main.lean` runs: one per line, in sorted
order, so that branches adding groups rarely touch the same lines. A new group also
needs a shard in `.github/test-shards.json` (CI checks). -/
def groups : List Group :=
  convGroup ::
  evalGroup ::
  structGroup ::
  []

end Tests.Eval
