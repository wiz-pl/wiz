import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

def indPrelude : String := "\ninductive Nat where\n  | zero\n  | succ (n : Nat)\n\ninductive Vec (A : Type) : Nat → Type where\n  | nil : Vec A .zero\n  | cons {0 n : Nat} (x : A) (xs : Vec A n) : Vec A (.succ n)\n\n\ndef two : Vec Nat (.succ (.succ .zero)) := .cons .zero (.cons (.succ .zero) .nil)\n\nstructure Point where\n  x : Nat\n  y : Nat\n\ndef p : Point := Point.mk .zero (.succ .zero)\n\n"

/-- A constructor field at a quantity *parameter* (`%q a : A`): the field must be
strengthened past the local `T` in the constructor's type, and the generated recursor
must take the payload apart with `split`s (a projection needs `1 ≤ q`, not known). -/
def qtyIndPrelude : String := "\ninductive Nat where\n  | zero\n  | succ (n : Nat)\n\ninductive BoxQ (q : Qty) (A : Type) where\n  | mk (%q a : A)\n\ninductive PairQ (q : Qty) (A : Type) where\n  | mk (%q a : A) (b : Nat)\n\ndef box {q : Qty} {A : Type} (%q a : A) : BoxQ q A := .mk a\n\ndef unbox {q : Qty} {A : Type} (f : (%q a : A) → A) (b : BoxQ q A) : A :=\n  match b with\n  | .mk a => f a\n\ndef unbox0 {A : Type} (f : (0 a : A) → A) (b : BoxQ 0 A) : A :=\n  match b with\n  | .mk a => f a\n\ndef mapBox {q : Qty} {A B : Type} (f : (%q a : A) → B) (b : BoxQ q A) : BoxQ q B :=\n  BoxQ.rec (fun _ => BoxQ q B) (fun a => .mk (f a)) b\n\ndef pairQ {q : Qty} {A : Type} (%q a : A) (b : Nat) : PairQ q A := .mk a b\n\ndef firstPair {q : Qty} {A : Type} (f : (%q a : A) → A) (p : PairQ q A) : A :=\n  match p with\n  | .mk a _ => f a\n\ndef bW : BoxQ ω Nat := .mk (.succ .zero)\ndef b1 : BoxQ 1 Nat := .mk (.succ .zero)\ndef b0 : BoxQ 0 Nat := .mk (.succ .zero)\ndef pW : PairQ ω Nat := pairQ (.succ .zero) (.succ .zero)\n\n"

/-- Inductive propositions (#252): an indexed relation in `Prop`, a proof by induction,
and singleton elimination (a one-constructor proposition with proof fields, eliminating
into `Type`). -/
def propIndPrelude : String := "\ninductive Nat where\n  | zero\n  | succ (n : Nat)\n\ninductive Le : Nat → Nat → Prop where\n  | refl (n : Nat) : Le n n\n  | step {n m : Nat} (h : Le n m) : Le n (.succ m)\n\ndef leSucc (n : Nat) : Le n (.succ n) := .step (.refl n)\n\ndef leWiden {a b : Nat} (h : Le a b) : Le a (.succ b) :=\n  Le.rec (fun x y _ => Le x (.succ y)) (fun n => .step (.refl n)) (fun _ ih => .step ih) h\n\ninductive EqP {A : Type} (a : A) : A → Prop where\n  | refl : EqP a a\n\ndef eqPTest : Nat :=\n  EqP.rec (fun (b : Nat) (_ : EqP Nat.zero b) => Nat) (Nat.succ Nat.zero) (EqP.refl)\n\ninductive AndP (A B : Prop) : Prop where\n  | intro (a : A) (b : B)\n\ndef andPComm {A B : Prop} (h : AndP A B) : AndP B A :=\n  AndP.rec (fun _ => AndP B A) (fun a b => .intro b a) h\n\n"

def propIndGroup : Group where
  name := "inductive-props"
  exercise := "issue #252"
  cases := [
    { name := "Le: an indexed proposition, with a proof by induction", run := fun _ =>
        ok propIndPrelude [] },
    { name := "a non-singleton proposition eliminates only into Prop", run := fun _ =>
        ok (propIndPrelude ++
          "def leRefl (k : Nat) : Le k k := Le.casesOn (fun _ _ _ => Le k k) (fun _ => .refl k) (fun _ => .refl k) (.refl k)") [] },
    { name := "singleton elimination computes into Type (EqP.rec)", run := fun _ =>
        ok (propIndPrelude ++ "#reduce eqPTest") [".succ .zero"] },
    { name := "large elimination of a non-singleton proposition is rejected", run := fun _ =>
        fails (propIndPrelude ++
          "def bad (h : Le .zero .zero) : Nat := match h with\n  | .refl _ => .zero\n  | .step _ => .zero")
          "large elimination" },
    { name := "a non-positive occurrence in a proposition is rejected", run := fun _ =>
        fails (propIndPrelude ++ "inductive BadP : Prop where\n  | mk (f : BadP → Nat)") "may only occur" },
    { name := "BEq and Repr are not derived for a proposition", run := fun _ =>
        fails "inductive RP : Prop where\n  | mk\n  deriving BEq" "cannot derive BEq" },
    { name := "AndP: a one-constructor proposition with proof fields", run := fun _ =>
        ok propIndPrelude [] },
    { name := "mutual inductive propositions", run := fun _ =>
        ok "mutual\ninductive A : Prop where\n  | mk\ninductive B : Prop where\n  | mk\nend" [] }
  ]

builtin_initialize registerGroup propIndGroup

def inductiveGroup : Group where
  name := "inductive"
  exercise := "Exercise 4.21"
  cases := [
    { name := "Nat, Vec, Point", run := fun _ => ok indPrelude },
    { name := "constructor types print nominally", run := fun _ =>
        ok (indPrelude ++ "#check Vec.cons")
          ["Vec.cons : {A : Type} → {n : Nat} → A → Vec A n → Vec A (.succ n)"] },
    { name := "values print with constructor names", run := fun _ =>
        ok (indPrelude ++ "#reduce two") [".cons (.succ .zero) .zero (.cons .zero (.succ .zero) .nil)"] },
    { name := "structure fields by name", run := fun _ =>
        ok (indPrelude ++ "#reduce p.y") [".succ .zero"] },
    { name := "wrong index is a type mismatch", run := fun _ =>
        fails (indPrelude ++ "def bad : Vec Nat (.succ .zero) := .nil") "type mismatch" },
    { name := "non-uniform parameters are rejected", run := fun _ =>
        fails "inductive T (A : Type) where\n  | mk (x : T Unit)" "parameters" },
    { name := "guarded recursive descriptions: List and a binary tree", run := fun _ =>
        ok (indPrelude ++ "inductive MyList (A : Type) where\n  | nil\n  | cons (x : A) (xs : MyList A)\n\ninductive Tree where\n  | leaf\n  | node (l : Tree) (r : Tree)\n") },
    { name := "negative occurrences are rejected", run := fun _ =>
        fails "inductive Bad where\n  | mk (f : Bad → Unit)" "may only occur" },
    { name := "a positive, not strictly positive occurrence is rejected", run := fun _ =>
        fails "inductive Bad where\n  | mk (f : (Bad → Unit) → Unit)" "may only occur" },
    { name := "an unguarded recursive description (μ X. X) is rejected", run := fun _ =>
        fails "def Bad : Type := μ (Desc.rec 1 () (Desc.ret ()) : Desc Unit) ()" "unguarded recursive description" },
    { name := "… also when the description is a definition (the check looks through it)", run := fun _ =>
        fails "def D : Desc Unit := Desc.rec 1 () (Desc.ret ())\ndef Bad : Type := μ D ()" "unguarded recursive description" },
    { name := "a size variable that escapes its binder is rejected", run := fun _ =>
        fails (indPrelude ++ "def bad : Type := (Nat)^i") "unknown identifier" },
    { name := "a size must be a Size (a data variable is rejected)", run := fun _ =>
        fails (indPrelude ++ "def bad (n : Nat) : Type := (Nat)^n") "type mismatch" },
    { name := "a guarded coinductive description (ν) is accepted", run := fun _ =>
        ok "def S : Type := ν (Desc.arg 1 Unit (fun _ => Desc.rec 1 () (Desc.ret ())) : Desc Unit) ()" },
    { name := "ν X. X, an observation of itself, is a valid coinductive type", run := fun _ =>
        ok "def S : Type := ν (Desc.rec 1 () (Desc.ret ()) : Desc Unit) ()" },
    { name := "fields may not depend on recursive fields", run := fun _ =>
        fails "inductive T : Type where\n  | mk (x : T) (y : (x, x).1 = x)" "may not depend" },
    { name := "Nat.rec computes", run := fun _ =>
        ok (indPrelude ++ "def add (m n : Nat) : Nat := Nat.rec (fun _ => Nat) n (fun _ ih => .succ ih) m\n" ++
            "#reduce add (.succ .zero) (.succ (.succ .zero))") [".succ (.succ (.succ .zero))"] },
    { name := "Vec.rec has Lean's shape", run := fun _ =>
        ok (indPrelude ++ "#check Vec.rec")
          ["Vec.rec : {A : Type} → (0 motive : (x : Nat) → Vec A x → Sort ?u0) → motive .zero .nil → ({n : Nat} → (x : A) → (xs : Vec A n) → motive n xs → motive (.succ n) (.cons n x xs)) → {x : Nat} → (x' : Vec A x) → motive x x'"] },
    { name := "Vec.rec computes through indices", run := fun _ =>
        ok (indPrelude ++ "def len {A : Type} {n : Nat} (v : Vec A n) : Nat := Vec.rec (fun _ _ => Nat) .zero (fun _ _ ih => .succ ih) v\n" ++
            "#reduce len two") [".succ (.succ .zero)"] },
    { name := "casesOn: predecessor", run := fun _ =>
        ok (indPrelude ++ "def pred (n : Nat) : Nat := Nat.casesOn (fun _ => Nat) .zero (fun m => m) n\n#reduce pred (.succ (.succ .zero))") [".succ .zero"] },
    { name := "a field at a quantity parameter: BoxQ checks and computes", run := fun _ =>
        ok (qtyIndPrelude ++
          "#reduce unbox (fun (n : Nat) => .succ n) bW\n" ++
          "#reduce unbox (fun (n : Nat) => n) b1\n" ++
          "#reduce unbox0 (fun (_ : Nat) => .succ (.succ .zero)) b0\n" ++
          "#reduce mapBox (fun (n : Nat) => (.succ n : Nat)) bW\n" ++
          "#reduce firstPair (fun (n : Nat) => n) pW")
          [".succ (.succ .zero)", ".succ .zero", ".succ (.succ .zero)",
           ".mk (.succ (.succ .zero))", ".succ .zero"] },
    { name := "a field at a quantity parameter is used only at its quantity", run := fun _ =>
        fails (qtyIndPrelude ++
          "def bad {q : Qty} {A : Type} (b : BoxQ q A) : A := match b with\n  | .mk a => a")
          "quantity" },
    { name := "deriving DecidableEq for an enumeration and a single-constructor record", run := fun _ =>
        okLibs ("import Deriving\ninductive Status where\n  | pending\n  | completed\n  deriving DecidableEq\n" ++
          "structure Pt where\n  x : Nat\n  y : Bool\n  deriving DecidableEq\n" ++
          "#eval DecidableEq.decide Status.completed Status.completed\n" ++
          "#eval DecidableEq.decide Status.pending Status.completed\n" ++
          "#eval DecidableEq.decide (Pt.mk 2 Bool.true) (Pt.mk 2 Bool.true)\n" ++
          "#eval DecidableEq.decide (Pt.mk 2 Bool.true) (Pt.mk 2 Bool.false)\n" ++
          "#check @instDecidableEqStatus")
          [".true", ".false", ".true", ".false",
           "instDecidableEqStatus : DecidableEq Status"] },
    { name := "deriving DecidableEq is rejected for a recursive field or more than one constructor", run := fun _ => do
        failsLibs ("import Deriving\ninductive Chain where\n  | mk (next : Chain)\n  deriving DecidableEq")
          "DecidableEq is derived for an enumeration or a single-constructor record only"
        failsLibs ("import Deriving\ninductive Tree where\n  | leaf\n  | node (l : Tree) (n : Nat) (r : Tree)\n  deriving DecidableEq")
          "DecidableEq is derived for an enumeration or a single-constructor record only" },
    { name := "unknown constructor via dot", run := fun _ =>
        fails (indPrelude ++ "def bad : Nat := .three") "no constructor three" }
  ]

builtin_initialize registerGroup inductiveGroup

end Tests.Elab
