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
    { name := "rule (b): a data implicit is ω by default: a named implicit is usable as data", run := fun _ =>
        okLib "import Prelude\ndef width {n : Nat} : Nat := n\ndef t : {n : Nat} → Nat := fun {n} => n\ndef twice {n : Nat} : Nat := Nat.add n n" },
    { name := "an explicit quantity is authoritative: {0 n} stays erased", run := fun _ => do
        okLib "import Prelude\ndef f {0 n : Nat} (x : Nat) : Nat := x"
        failsLib "import Prelude\ndef bad {0 n : Nat} : Nat := n" "quantity" },
    { name := "an explicit quantity is authoritative: {1 n} must be used once", run := fun _ => do
        okLib "import Prelude\ndef good {1 n : Nat} : Nat := n"
        failsLib "import Prelude\ndef bad {1 n : Nat} : Nat := Nat.add n n" "quantity" },
    -- rule (b), the language decision of 2026-11-16: a bare implicit whose type is a sort or
    -- a proposition is 0 (erased anyway, and printed bare), any other implicit ω; the type
    -- is the one known at the binder, so `{A}` with no type is data (ω)
    { name := "rule (b): a bare implicit whose type is a sort or a proposition is 0", run := fun _ => do
        fails "def leak {A : Type} (x : A) : Type := A" "quantity"
        fails "def leakP {P : Prop} (x : P) : Prop := P" "quantity"
        ok "def leakW {ω A : Type} (x : A) : Type := A"
        okLib ("import Prelude\ndef p {P : Prop} {A : Type} {u : Type 1} {h : True} {n : Nat} {F : Type → Type} (x : Nat) : Nat := x\n" ++
          "def q {0 n : Nat} {ω A : Type} (x : Nat) : Nat := x\n#check @p\n#check @q")
          ["p : {P : Prop} → {A : Type} → {u : Type 1} → {h : True} → {n : Nat} → {F : Type → Type} → Nat → Nat",
           "q : {0 n : Nat} → {ω A : Type} → Nat → Nat"] },
    { name := "rule (b): an implicit with no written type is data (ω), decided at the binder", run := fun _ =>
        okLib "import Prelude\ndef g {A} (x : A) (y : List A) : A := x\n#check @g" ["g : {ω A : Type} → A → List A → A"] },
    { name := "rule (b): the default follows a definition that unfolds to a sort", run := fun _ =>
        fails "def Ty : Type 1 := Type\ndef leak {A : Ty} (x : A) : Type := A" "quantity" },
    -- a recursive definition over an erased index: the definition checks (through the
    -- eliminator), the implementation passes the 0-bound field to the ω parameter `n` (a
    -- data implicit's default): an ordinary quantity error at the binder, not "a bug in Wiz"
    { name := "rule (b): a recursive call passing an erased field to a data implicit is a quantity error at the binder", run := fun _ => do
        let src := "inductive Nat where\n  | zero\n  | succ (n : Nat)\n" ++
          "inductive Vec (A : Type) : Nat → Type where\n  | nil : Vec A .zero\n  | cons {0 n : Nat} (x : A) (xs : Vec A n) : Vec A (.succ n)\n" ++
          "def map {A B : Type} (f : A → B) {n : Nat} : Vec A n → Vec B n\n  | .nil => .nil\n  | .cons x xs => .cons (f x) (map f xs)"
        fails src "in a recursive call of map: its implicit parameter n has the default quantity ω"
        let e := (errors src)[0]!
        if (e.splitOn "bug in Wiz").length > 1 then throw (IO.userError s!"still blames Wiz:\n{e}")
        unless e.startsWith "7:" do throw (IO.userError s!"not reported at the binder (line 7):\n{e}")
        ok (src.replace "{n : Nat}" "{0 n : Nat}") },
    { name := "class instance binders are ω by default: the dictionary can be used twice", run := fun _ =>
        okLib ("import Prelude\nclass Twice (A : Type) where\n  val : A\ninstance : Twice Nat where\n  val := 7\n" ++
          "def addIt {A : Type} [c : Twice A] : A := c.val\ndef twice [c : Twice Nat] : Nat := Nat.add c.val c.val") },
    -- Erasure is type-directed, so a type or a proof is `◾` at any quantity (a bare
    -- `{A : Type}` is 0 anyway, rule (b)); a data implicit used only in types is erased
    -- only when written `{0 n}`: a bare `{n}` (ω) is passed and computed at runtime (here
    -- `Nat.add k 5`).
    { name := "erasure of implicits: a type is ◾, a data index is ◾ only when written {0 n}", run := fun _ =>
        okLib ("import Prelude\ninductive V (A : Type) : Nat → Type where\n  | nil : V A .zero\n" ++
          "def onlyType {n : Nat} (v : V Nat n) (x : Nat) : Nat := x\n" ++
          "def onlyType0 {0 n : Nat} (v : V Nat n) (x : Nat) : Nat := x\n" ++
          "def tyArg {A : Type} (x : A) : A := x\n" ++
          "def caller (k : Nat) (v : V Nat (Nat.add k 5)) : Nat := Nat.add (onlyType v 1) (onlyType0 v 1)\n" ++
          "def caller2 : Nat := tyArg (A := Nat) 3\n#erase caller\n#erase caller2")
          ["caller := (λk. (λv. ((Nat.add (((onlyType ((Nat.add #1) 5)) #0) 1)) (((onlyType0 ◾) #0) 1))))",
           "caller2 := ((tyArg ◾) 3)"] },
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
    { name := "erased implicit used at runtime", run := fun _ => do
        fails "def leak {A : Type} (x : A) : Type := A" "quantity"
        fails "def leak0 {0 A : Type} (x : A) : Type := A" "quantity" },
    { name := "binder quantity must match the expected type", run := fun _ =>
        fails "def f : (1 x : Type) → Type := fun (ω x) => x" "quantity" },
    { name := "linear identity checks", run := fun _ =>
        ok "def lid {A : Type} (1 x : A) : A := x" },
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
          [".true", ".false", ".true", ".false", ".false", ".true", ".true", ".false"] },
    -- (a tuple literal in inference position) The kernel cannot infer the type of a pair,
    -- only check one against a `Σ`, and the projection (`(a, b).2`) infers its scrutinee:
    -- `inferTuple` now writes the `ann` the self-hosted frontend already wrote, so the
    -- term is one the kernel can check at all. The sorts pass then fills the sorts inside
    -- it: the elaborator wraps a lambda it *infers* in `ann … (Π … ⟨hole, hole⟩)`
    -- (`term.fun`), and the pass never descended into the pair, so that hole reached the
    -- kernel ("a Π/Σ/ULift in … without its sorts") before the pair's own missing
    -- annotation could be reported. The helper spelling is the control: checked against a
    -- declared `Σ`, the pair is built without either `ann`, which is why the same law was
    -- accepted through a `toStore` helper (`lib/Optic.wiz`'s GetPut, spelled inline).
    { name := "a projected tuple literal: checked at all, and with the sorts inside it (the inline store law)", run := fun _ =>
        okLibs ("import Prelude\n" ++
          "def projPair (n : Nat) : Nat := (n, n).2\n" ++
          "def proj (n : Nat) : Nat := (n, fun x => x).2 n\n" ++
          "def Store (A S : Type) : Type := A × (A → S)\n" ++
          "def toStore (n : Nat) : Store Nat Nat := (n, fun x => x)\n" ++
          "def projViaHelper (n : Nat) : Nat := (toStore n).2 n\n" ++
          "def P : Prop := (n : Nat) → (n, fun x => x).2 n = n\n" ++
          "def p : P := fun n => rfl") },
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
          "the equation hypothesis 'h' is named twice" },
    { name := "the equation's name belongs before the scrutinee, not in a pattern", run := fun _ =>
        fails "inductive Nat where\n  | zero\n  | succ (n : Nat)\n\ndef d (n : Nat) : Nat :=\n  match h : n with\n  | h : .zero => .zero\n  | _ => .zero\n"
          "a pattern is expected here" }
  ]

builtin_initialize registerGroup group

end Tests.Elab
