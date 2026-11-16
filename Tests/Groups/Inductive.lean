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
    -- (termination) the structural recursion the elaborator accepts, and the shapes it
    -- rejects with a reason (there is no lexicographic or nested measure: `partial def`)
    { name := "termination: structural recursion on a field, a parameter, another column, an infinitary field", run := fun _ =>
        ok (indPrelude ++
          "def add : Nat → Nat → Nat\n  | .zero, m => m\n  | .succ n, m => .succ (add n m)\n" ++
          "def len {A : Type} {n : Nat} : Vec A n → Nat\n  | .nil => .zero\n  | .cons _ xs => .succ (len xs)\n" ++
          "def mapV {A B : Type} (f : A → B) {n : Nat} : Vec A n → Vec B n\n" ++
          "  | .nil => .nil\n  | .cons x xs => .cons (f x) (mapV f xs)\n" ++
          "inductive W where\n  | z\n  | sup (k : Nat → W)\n" ++
          "def depth : W → Nat\n  | .z => .zero\n  | .sup k => .succ (depth (k .zero))\n" ++
          "#reduce add (.succ .zero) (.succ (.succ .zero))\n#reduce len two\n" ++
          "#reduce depth (.sup (fun _ => .sup (fun _ => .z)))")
          [".succ (.succ (.succ .zero))", ".succ (.succ .zero)", ".succ (.succ .zero)"] },
    { name := "termination: a call on a computed argument is nested recursion", run := fun _ =>
        fails (indPrelude ++ "def grow : Nat → Nat\n  | .zero => .zero\n  | .succ n => grow (.succ n)")
          "must be on a variable, not" },
    { name := "termination: a call on the scrutinee itself does not decrease", run := fun _ =>
        fails (indPrelude ++ "def selfCall (n : Nat) : Nat := match n with\n  | .zero => .zero\n  | .succ m => selfCall n")
          "the scrutinee itself, which is not smaller" },
    { name := "termination: a call that changes a parameter is lexicographic, which is not checked", run := fun _ => do
        fails (indPrelude ++ "def lexParam (m : Nat) : Nat → Nat\n  | .zero => m\n  | .succ n => lexParam n m")
          "must pass the parameter m unchanged"
        fails (indPrelude ++ "def lexParam (m : Nat) : Nat → Nat\n  | .zero => m\n  | .succ n => lexParam n m")
          "lexicographic measure Wiz does not check" },
    { name := "termination: a field of a nested pattern has no hypothesis of its own", run := fun _ => do
        fails (indPrelude ++ "inductive Tr where\n  | leaf\n  | node (l : Tr) (r : Tr)\n" ++
          "def nested : Tr → Nat\n  | .leaf => .zero\n  | .node (.node a _) _ => nested a\n  | .node _ _ => .zero")
          "not structurally smaller"
        fails (indPrelude ++ "inductive Tr where\n  | leaf\n  | node (l : Tr) (r : Tr)\n" ++
          "def nested : Tr → Nat\n  | .leaf => .zero\n  | .node (.node a _) _ => nested a\n  | .node _ _ => .zero")
          "lexicographic or nested measure" },
    { name := "termination: the kernel rejects a hand-made implementation that loops, and says why (M1)", run := fun _ => do
        let src := indPrelude ++ "def f : Nat → Nat\n  | .zero => .zero\n  | .succ n => f n\n"
        let s := runFrontend (R := ZeroOneMany) src {}
        let some d := s.globals.find? "f" | throw (IO.userError "f is missing")
        let g0 : Globals ZeroOneMany := { s.globals with decls := s.globals.decls.erase "f" }
        -- (the derived implementation is accepted, as before)
        check ((addDecl g0 d) matches .ok _) "f's derived implementation was rejected"
        let message (impl : Term ZeroOneMany) : IO String :=
          match addDecl g0 { d with impl := some impl } with
          | .ok _ => pure "accepted"
          | .error e => pure (toString e)
        -- a direct self-call: not under a match, so not on a field (the old message said
        -- only that it is not an induction on an argument)
        let m1 ← message (.lam "n" (.app (.const "f" []) (.var 0)))
        check ((m1.splitOn "not under a match").length > 1) s!"expected a termination error, got: {m1}"
        check ((m1.splitOn "compiled code would loop").length > 1) s!"expected the loop hint, got: {m1}"
        -- a call on a rebuilt scrutinee
        let m2 ← message (.lam "n" (.app (.const "f" []) (.app (.const "Nat.succ" []) (.var 0))))
        check ((m2.splitOn "not under a match").length > 1) s!"expected a termination error, got: {m2}" },
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
