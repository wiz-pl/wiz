import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

def group : Group where
  name := "elab"
  exercise := "Exercises 3.1–3.9"
  cases := [
    { name := "implicit arguments are inserted", run := fun _ =>
        ok (prelude ++ "def t (A : Type) (a : A) : A := id a") },
    { name := "#check shows implicit binders", run := fun _ =>
        ok (prelude ++ "#check id") ["id : {A : Type} → A → A"] },
    { name := "@ makes implicits explicit", run := fun _ =>
        ok (prelude ++ "def t (A : Type) (a : A) : A := @id A a") },
    { name := "implicit lambda insertion", run := fun _ =>
        ok "def id2 : {A : Type} → A → A := fun x => x" },
    { name := "explicit implicit lambda", run := fun _ =>
        ok "def id3 : {A : Type} → A → A := fun {A} x => x" },
    { name := "return type inferred", run := fun _ =>
        ok "def ap (A B : Type) (f : A → B) (a : A) := f a\n#check ap"
          ["ap : (A : Type) → (B : Type) → (A → B) → A → B"] },
    { name := "fun binder types inferred from use", run := fun _ =>
        ok (prelude ++ "def k (A : Type) := comp (fun (x : A) => x) (fun y => y)\n#check k")
          ["k : (A : Type) → A → A"] },
    { name := "holes solved by unification", run := fun _ =>
        ok (prelude ++ "def t (A : Type) (a : A) : A := @id _ a") },
    { name := "unsolvable hole is reported", run := fun _ =>
        fails "def x : Type := _" "could not infer" },
    { name := "Church numerals and #reduce", run := fun _ =>
        ok (church ++ "#reduce add two two") ["fun A s z => s (s (s (s z)))"] },
    { name := "2 + 2 = 4 by refl, with implicit A", run := fun _ =>
        ok (church ++ "def p : Leibniz (add two two) four := lrefl four") },
    { name := "2 + 2 = 2 is a type mismatch", run := fun _ =>
        fails (church ++ "def p : Leibniz (add two two) two := lrefl two") "type mismatch" },
    { name := "type mismatch message", run := fun _ =>
        fails "def bad (A : Type) (a : A) : Type := a" "type mismatch" },
    { name := "unknown identifier", run := fun _ =>
        fails "def bad : Type := Nope" "unknown identifier 'Nope'" },
    { name := "no recursion yet", run := fun _ =>
        fails "def loop (A : Type) : A := loop A" "recursive call to loop in a definition without equations" },
    { name := "linearity is checked by the kernel", run := fun _ =>
        fails "def dup {A : Type} (f : A → A → A) (1 x : A) : A := f x x" "quantity" },
    { name := "erased implicit used at runtime", run := fun _ =>
        fails "def leak {A : Type} (x : A) : Type := A" "quantity" },
    { name := "binder quantity must match the expected type", run := fun _ =>
        fails "def f : (1 x : Type) → Type := fun (ω x) => x" "quantity" },
    { name := "linear identity checks", run := fun _ =>
        ok "def lid {A : Type} (1 x : A) : A := x" },
    { name := "#260 an unannotated motive for an implicit-typed argument", run := fun _ =>
        -- `P` is a placeholder for `fun x => …`, applied to both the context's `u` and
        -- the argument `u` (a repeated variable in the spine): the solution is still a
        -- pattern (it uses the applied occurrence)
        okLib ("import Logic\ndef t1 (u : Nat) (h : Nat.beq u 0 = .false) (e : u = 0) : Nat.beq 0 0 = .false :=\n" ++
          "  Eq.substProp (fun x => Nat.beq x 0 = .false) e h") },
    { name := "self-application escapes the hole's scope", run := fun _ => do
        -- (with pruning, the escaping variable is pruned away and the occurs check fires
        -- instead: either is right)
        let errs := errors "def w (A : Type) := fun f => f f"
        unless errs.size == 1 do throw (IO.userError s!"expected one error, got {errs.size}: {errs}")
        unless (errs[0]!.splitOn "scope").length > 1 || (errs[0]!.splitOn "occurs check").length > 1 do
          throw (IO.userError s!"error mentions neither the scope nor the occurs check:\n{errs[0]!}") },
    { name := "occurs check", run := fun _ =>
        fails "def o (A : Type) (g : _ → A) := g g" "occurs" },
    { name := "not a function", run := fun _ =>
        fails "def bad (A : Type) (a : A) : A := a a" "function expected" },
    { name := "let", run := fun _ =>
        ok (prelude ++ "def t (A : Type) (a : A) : A :=\n  let b := id a\n  id b") },
    { name := "a parse error doesn't stop later commands", run := fun _ => do
        let msgs := run "def a : Type := (\ndef b : Type 1 := Type\n#check b"
        checkEq 2 msgs.size
        check ((msgs[1]!.splitOn "b : Type 1").length > 1) s!"{msgs}" },
    { name := "user syntax without an elaborator is reported", run := fun _ =>
        fails "syntax \"magic\" : term\ndef x : Type := magic" "the syntax term.magic has no meaning" },
    { name := "duplicate definition", run := fun _ =>
        fails "def a : Type 1 := Type\ndef a : Type 1 := Type" "already been declared" },
    -- 13i: structure update
    { name := "structure update { s with f := v }: fields, nested values, a polymorphic structure", run := fun _ =>
        okLibs ("import Prelude\nstructure Stats where\n  hits : Nat\n  misses : Nat\n" ++
          "def bump (s : Stats) : Stats := { s with hits := Nat.succ s.hits }\n" ++
          "#eval (bump (Stats.mk 3 4)).hits\n#eval (bump (Stats.mk 3 4)).misses\n" ++
          "def both (s : Stats) : Stats := { s with hits := 0, misses := 10 }\n" ++
          "#eval (both (Stats.mk 3 4)).hits\n#eval (both (Stats.mk 3 4)).misses\n" ++
          "structure Inner where\n  x : Nat\nstructure Outer where\n  inner : Inner\n  n : Nat\n" ++
          "def nest (o : Outer) : Outer := { o with inner := { o.inner with x := 1 }, n := 2 }\n" ++
          "#eval (nest (Outer.mk (Inner.mk 7) 9)).inner.x\n#eval (nest (Outer.mk (Inner.mk 7) 9)).n\n" ++
          "structure Box (A : Type) where\n  val : A\n  tag : Nat\n" ++
          "def retag {A : Type} (b : Box A) (n : Nat) : Box A := { b with tag := n }\n" ++
          "#eval (retag (Box.mk Bool.true 1) 9).tag\n" ++
          "def keeps (s : Stats) : (bump s).misses = s.misses := rfl")
          ["4", "4", "0", "10", "1", "2", "9"] },
    { name := "structure update: an unknown field, a repeated field, and a non-structure are errors", run := fun _ => do
        failsLibs ("import Prelude\nstructure Stats where\n  hits : Nat\n  misses : Nat\n" ++
          "def f (s : Stats) : Stats := { s with hit := 1 }")
          "Stats has no field 'hit' (its fields are hits, misses)"
        failsLibs ("import Prelude\nstructure Stats where\n  hits : Nat\n  misses : Nat\n" ++
          "def f (s : Stats) : Stats := { s with hits := 1, hits := 2 }")
          "field 'hits' is updated twice"
        failsLibs "import Prelude\ndef f (n : Nat) : Nat := { n with hits := 1 }"
          "structure update needs a value of a structure type" },
    { name := "deriving DecidableEq: an enumeration and a single-constructor record", run := fun _ =>
        okLibs ("import Deriving\ninductive Status where\n  | pending\n  | completed\n  deriving DecidableEq\n" ++
          "#eval DecidableEq.decide Status.pending Status.pending\n" ++
          "#eval DecidableEq.decide Status.pending Status.completed\n" ++
          "structure Pt where\n  x : Nat\n  y : Bool\n  deriving DecidableEq\n" ++
          "#eval DecidableEq.decide (Pt.mk 1 Bool.true) (Pt.mk 1 Bool.true)\n" ++
          "#eval DecidableEq.decide (Pt.mk 1 Bool.true) (Pt.mk 2 Bool.true)\n" ++
          "#eval DecidableEq.decide (Pt.mk 1 Bool.true) (Pt.mk 1 Bool.false)\n" ++
          "inductive Box (A : Type) where\n  | mk (v : A)\n  deriving DecidableEq\n" ++
          "#eval DecidableEq.decide (Box.mk 7) (Box.mk 7)\n" ++
          "#eval DecidableEq.decide (Option.some 2) (Option.some 2)\n" ++
          "#eval DecidableEq.decide (List.cons 1 List.nil) (List.cons 2 List.nil)\n" ++
          "def cmp (a b : Status) : Bool := DecidableEq.decide a b")
          [".true", ".false", ".true", ".false", ".false", ".true", ".true", ".false"] }
    -- `match h : e with`: the equation in an inferred match, and in a tactic's goal
    { name := "the equation of a match is a tactic hypothesis", run := fun _ =>
        okLib "import Prelude
def isZero (n : Nat) : Bool := match n with
  | 0 => .true
  | _ => .false
def f (b : Bool) : Bool := match b with
  | .true => .true
  | .false => .false
def g (n : Nat) : Bool := f (isZero n)
def gEq (n : Nat) : g n = isZero n :=
  match h : isZero n with
  | .true => by unfold g; rw h; rfl
  | .false => by unfold g; rw h; rfl
" },
    { name := "a named match can be inferred", run := fun _ =>
        okLib "import Prelude
def inferred (n : Nat) :=
  match h : n with
  | 0 => Nat.zero
  | _ => Nat.succ Nat.zero
def usesInferred (n : Nat) : Nat := inferred n
" },
    { name := "a match cannot name its equation twice (the second name is reported)", run := fun _ =>
        fails "inductive Nat where\n  | zero\n  | succ (n : Nat)\n\ndef d (n m : Nat) : Nat :=\n  match h : n, h : m with\n  | _, _ => .zero\n"
          "6:16: the equation hypothesis 'h' is named twice" },
    { name := "the equation's name belongs before the scrutinee, not in a pattern", run := fun _ =>
        fails "inductive Nat where\n  | zero\n  | succ (n : Nat)\n\ndef d (n : Nat) : Nat :=\n  match h : n with\n  | h : .zero => .zero\n  | _ => .zero\n"
          "7:5: a pattern is expected here" }
  ]

builtin_initialize registerGroup group

end Tests.Elab
