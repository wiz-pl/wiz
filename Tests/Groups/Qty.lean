import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

def appDef : String :=
  "def app {A B : Type} {q : Qty} (f : (%q x : A) → B) (%q a : A) : B := f a\n"

def qtyGroup : Group where
  name := "quantity polymorphism"
  exercise := "Exercise 4.15"
  cases := [
    { name := "application at any quantity", run := fun _ => ok appDef },
    { name := "#check shows the quantity variable", run := fun _ =>
        ok (appDef ++ "#check app") ["app : {A : Type} → {B : Type} → {q : Qty} → ((%q x : A) → B) → (%q a : A) → B"] },
    { name := "the quantity is inferred from a linear function", run := fun _ =>
        ok (appDef ++ "def lid (1 x : Unit) : Unit := x\ndef t (1 u : Unit) : Unit := app lid u") },
    { name := "... and checked: passing an ω variable linearly is fine, using it twice is not", run := fun _ =>
        fails (appDef ++ "def lid (1 x : Unit) : Unit := x\ndef t (1 u : Unit) : Unit × Unit := (app lid u, u)") "quantity" },
    { name := "duplicating a %q variable fails (q could be 1)", run := fun _ =>
        fails "def dup {A : Type} {q : Qty} (%q x : A) : A × A := (x, x)" "quantity" },
    { name := "dropping a %q variable fails (q could be 1)", run := fun _ =>
        fails "def drop {A : Type} {q : Qty} (%q x : A) : Unit := ()" "quantity" },
    { name := "even the identity fails: q could be 0", run := fun _ =>
        fails "def keep {A : Type} {q : Qty} (%q x : A) : A := x" "quantity" },
    { name := "products of quantity variables", run := fun _ =>
        ok ("def twice {A B : Type} {q r : Qty} (f : (%q x : A) → B) (g : (%r y : B) → B) (%(r) a : B) : B := g a\n") },
    { name := "quantity literals as terms", run := fun _ =>
        ok "def one : Qty := 1\ndef many : Qty := ω\ndef f {A : Type} (%one x : A) : A := x" },
    -- F6: `(%q x : A) → B = (1 x : A) → B` computed to `False` (the quantities differ as
    -- polynomials), and `q := 1` made it provable: a closed proof of `False`
    { name := "F6: types whose quantities differ only by a variable are not unequal (it proved False)", run := fun _ => do
        fails ("inductive N where\n  | z\n  | s (n : N)\n" ++
          -- (then `def boom : False := flip (q := 1) rfl` was a closed proof of False)
          "def flip {q : Qty} (e : ((%q x : N) → N) = ((1 x : N) → N)) : False := e\n") "mismatch"
        -- (then `bad 1 (refl …)`)
        fails "def bad (q : Qty) (e : ((%q x : Unit) → Unit) = ((1 x : Unit) → Unit)) : False := e\n" "mismatch"
        fails "def bad (q : Qty) (e : ((%q x : Unit) × Unit) = ((1 x : Unit) × Unit)) : False := e\n" "mismatch" },
    { name := "F6: types with two different literal quantities are unequal", run := fun _ =>
        ok ("def apart (e : ((0 x : Unit) → Unit) = ((1 x : Unit) → Unit)) : False := e\n" ++
          "def apart2 (e : ((ω x : Unit) × Unit) = ((1 x : Unit) × Unit)) : False := e\n") }
  ]

builtin_initialize registerGroup qtyGroup

end Tests.Elab
