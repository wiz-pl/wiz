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
    { name := "negative occurrences are rejected", run := fun _ =>
        fails "inductive Bad where\n  | mk (f : Bad → Unit)" "may only occur" },
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
    { name := "unknown constructor via dot", run := fun _ =>
        fails (indPrelude ++ "def bad : Nat := .three") "no constructor three" }
  ]

builtin_initialize registerGroup inductiveGroup

end Tests.Elab
