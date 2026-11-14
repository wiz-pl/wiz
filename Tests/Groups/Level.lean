import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

def levelGroup : Group where
  name := "universes"
  exercise := "Exercises 4.1–4.2 (and 1.7 for imax)"
  cases := [
    { name := "level normal forms (given)", run := fun _ => do
        let u : Level := .param "u"
        check (Level.equiv (.max u (.succ u)) (.succ u)) "max u (u+1) = u+1"
        check (Level.equiv (.max 1 (.succ u)) (.succ u)) "max 1 (u+1) = u+1"
        check (!Level.equiv (.max 1 u) u) "max 1 u ≠ u"
        check (Level.equiv (.imax u 0) 0) "imax u 0 = 0"
        check (Level.equiv (.imax u (.succ u)) (.succ u)) "imax u (u+1) = u+1"
        check (Level.equiv (.max u (.param "v")) (.max (.param "v") u)) "max is commutative" },
    { name := "universe polymorphic identity", run := fun _ =>
        ok "def id.{u} {A : Sort u} (x : A) : A := x\n#check id Type\n#check id.{3} Type"
          ["id (Type 1) Type : Type 1", "id (Type 1) Type : Type 1"] },
    { name := "explicit level too small", run := fun _ =>
        fails "def id.{u} {A : Sort u} (x : A) : A := x\n#check id.{2} Type" "2:8: error: universe level mismatch" },
    { name := "Prop is impredicative", run := fun _ =>
        ok "def True : Prop := (P : Prop) → P → P\ndef trivial : True := fun P p => p\n#check True"
          ["True : Prop"] },
    { name := "Π into Type is not impredicative", run := fun _ =>
        fails "def T : Type := (A : Type) → A" "type mismatch" },
    { name := "levels in types", run := fun _ =>
        ok "def Pred.{u} (A : Type u) : Type (u+1) := A → Type u\n#check Pred.{1}"
          ["Pred : Type 1 → Type 2"] },
    { name := "level metavariables solved by unification", run := fun _ =>
        ok "def id.{u} {A : Sort u} (x : A) : A := x\ndef t (A : Type 3) (a : A) : A := id a" },
    { name := "unknown level parameter", run := fun _ =>
        fails "def f (A : Type u) : Type u := A" "unknown universe level 'u'" },
    { name := "wrong number of explicit levels", run := fun _ =>
        fails "def id.{u} {A : Sort u} (x : A) : A := x\ndef t := id.{0, 1}" "universe parameters" },
    { name := "level mismatch", run := fun _ =>
        fails "def bad.{u} (A : Type u) : Type := A" "mismatch" },
    { name := "unsolved universe level", run := fun _ =>
        fails "def id.{u} {A : Sort u} (x : A) : A := x\ndef t := @id" "universe level" }
  ]

builtin_initialize registerGroup levelGroup

end Tests.Elab
