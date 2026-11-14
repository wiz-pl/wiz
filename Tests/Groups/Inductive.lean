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

/-- A *recursive* type with a field at a quantity parameter: the recursor's method for
`node` must split the `%q x` field at 1 (a projection needs `1 ≤ q`) and still hand the
recursive fields' hypotheses (about their projections) to the method with the right type.
`sizeW`/`size0` use the hypotheses (at `ω`/`0`), `useF` uses the field at any `q`, and
`rec1`/`recW` call `TreeQ.rec` directly at `q = 1`/`ω`. -/
def qtreePrelude : String := "\ninductive Nat where\n  | zero\n  | succ (n : Nat)\n\ndef plus (m n : Nat) : Nat := Nat.rec (fun _ => Nat) n (fun _ ih => .succ ih) m\n\ninductive TreeQ (q : Qty) (A : Type) where\n  | leaf\n  | node (%q x : A) (l r : TreeQ q A)\n\ndef tW : TreeQ ω Nat := .node (.succ .zero) .leaf (.node .zero .leaf .leaf)\ndef t1 : TreeQ 1 Nat := .node (.succ .zero) .leaf .leaf\ndef t0 : TreeQ 0 Nat := .node .zero .leaf .leaf\n\ndef sizeW (t : TreeQ ω Nat) : Nat :=\n  match t with\n  | .leaf => .zero\n  | .node _ l r => .succ (plus (sizeW l) (sizeW r))\n\ndef size0 (t : TreeQ 0 Nat) : Nat :=\n  match t with\n  | .leaf => .zero\n  | .node _ l r => .succ (plus (size0 l) (size0 r))\n\ndef useF {q : Qty} {A : Type} (f : (%q x : A) → Nat) (t : TreeQ q A) : Nat :=\n  match t with\n  | .leaf => .zero\n  | .node x _ _ => f x\n\ndef rec1 {A : Type} (f : (1 x : A) → Nat) (h : (1 n : Nat) → Nat) (t : TreeQ 1 A) : Nat :=\n  TreeQ.rec (fun _ => Nat) .zero (fun x l r ihl ihr => h (f x)) t\n\ndef recW (t : TreeQ ω Nat) : Nat :=\n  TreeQ.rec (fun _ => Nat) .zero\n    (fun x l r ihl ihr => .succ (plus x (plus ihl ihr))) t\n\ndef use1 {A : Type} (f : (1 x : A) → Nat) (1 t : TreeQ 1 A) : Nat :=\n  match t with\n  | .leaf => .zero\n  | .node x _ _ => f x\n\n"

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
    { name := "a recursive type with a %q field: elimination at q = ω and q = 0", run := fun _ =>
        ok (qtreePrelude ++ "#reduce sizeW tW\n#reduce size0 t0")
          [".succ (.succ .zero)", ".succ .zero"] },
    { name := "the recursor of a recursive %q type: the IH binder has the right type", run := fun _ =>
        ok (qtreePrelude ++ "#check TreeQ.rec")
          ["TreeQ.rec : {q : Qty} → {A : Type} → (0 motive : TreeQ q A → Sort ?u0) → " ++
           "motive .leaf → ((%q x : A) → (l : TreeQ q A) → (r : TreeQ q A) → " ++
           "motive l → motive r → motive (.node x l r)) → (x : TreeQ q A) → motive x"] },
    { name := "the %q field is eliminated at q = ω, 1 and 0", run := fun _ =>
        ok (qtreePrelude ++
          "#reduce useF (fun (n : Nat) => n) tW\n" ++
          "#reduce useF (fun (n : Nat) => n) t1\n" ++
          "#reduce useF (fun (_ : Nat) => .zero) t0")
          [".succ .zero", ".succ .zero", ".zero"] },
    { name := "a direct TreeQ.rec at q = 1, with the field consumed linearly", run := fun _ =>
        ok (qtreePrelude ++
          "#reduce rec1 (fun (n : Nat) => n) (fun (n : Nat) => .succ n) t1")
          [".succ (.succ .zero)"] },
    { name := "a direct TreeQ.rec at q = ω uses the field and its hypotheses", run := fun _ =>
        ok (qtreePrelude ++ "#reduce recW tW")
          [".succ (.succ (.succ .zero))"] },
    { name := "mutual recursion over a recursive %q type", run := fun _ =>
        ok (qtreePrelude ++
          "mutual\n" ++
          "def leavesW (t : TreeQ ω Nat) : Nat :=\n" ++
          "  match t with\n  | .leaf => .succ .zero\n  | .node _ l r => plus (leavesW l) (leavesW r)\n" ++
          "def nodesW (t : TreeQ ω Nat) : Nat :=\n" ++
          "  match t with\n  | .leaf => .zero\n  | .node _ l r => .succ (plus (nodesW l) (nodesW r))\n" ++
          "end\n" ++
          "#eval leavesW tW\n#eval nodesW tW")
          [".succ (.succ (.succ .zero))", ".succ (.succ .zero)"] },
    { name := "a linear-mode eliminator (casesOn1) on a recursive %q type", run := fun _ =>
        ok (qtreePrelude ++
          "#reduce use1 (fun (n : Nat) => n) t1")
          [".succ .zero"] },
    { name := "a linear field of a recursive %q type cannot be duplicated", run := fun _ =>
        fails (qtreePrelude ++
          "def dup {A : Type} (f : (1 x : A) → Nat) (1 t : TreeQ 1 A) : Nat × Nat :=\n" ++
          "  match t with\n  | .leaf => (.zero, .zero)\n  | .node x l r => (f x, f x)")
          "quantity" },
    { name := "an erased field of a recursive %q type cannot be used", run := fun _ =>
        fails (qtreePrelude ++
          "def use0 (t : TreeQ 0 Nat) : Nat := match t with\n  | .leaf => .zero\n  | .node x _ _ => x")
          "quantity" },
    { name := "a recursive field at a quantity variable is rejected with the reason", run := fun _ =>
        fails "inductive BadQ (q : Qty) (A : Type) where\n  | node (%q t : BadQ q A)"
          "cannot be split" },
    { name := "unknown constructor via dot", run := fun _ =>
        fails (indPrelude ++ "def bad : Nat := .three") "no constructor three" }
  ]

builtin_initialize registerGroup inductiveGroup

end Tests.Elab
