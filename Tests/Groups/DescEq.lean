import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-! ## Equality of descriptions (4g) -/

/-- Small data types without the Prelude. -/
def descEqTypes : String :=
  "inductive N where\n  | z\n  | s (n : N)\n" ++
  "inductive B where\n  | f\n  | t\n" ++
  "inductive L (A : Type) where\n  | nil\n  | cons (x : A) (xs : L A)\n" ++
  "def len {A : Type} : L A → N\n  | .nil => .z\n  | .cons _ xs => .s (len xs)\n"

/-- The Abel–Coquand program with the box cast between two *different* descriptions
(`BoxD` and `BoxD'`, whose tags differ in name), along a proof of the computed equation
built by hand from `tautext`. -/
def abelCoquandTwoBoxes : String :=
  ((abelCoquand).replace
    "def omega : Top := fun A a => unbox (cast (apTy Prop Box T2 A (tautext T2 A id2 a)) (mk delta))\n"
    ("def BoxD' (P : Prop) : Desc Unit := Desc.arg 1 ((_ : Enum [v]) × P) (fun _ => Desc.ret ())\n" ++
     "def Box' (P : Prop) : Type := μ (BoxD' P) ()\n" ++
     "def unbox' {P : Prop} (b : Box' P) : P := ind (fun _ _ => P) (fun i xs ih => xs.1.2) b\n" ++
     "def boxEq : Box T2 = Box' T2 := ((), (((), fun _ => (fun _ => id2, fun _ => id2)), fun _ => ()), ())\n" ++
     "def omega : Top := fun A a => unbox' (cast (apTy Prop Box' T2 A (tautext T2 A id2 a)) (cast boxEq (mk delta) : Box' T2))\n"))

def descEqGroup : Group where
  name := "desceq"
  exercise := "Equality of descriptions (4g)"
  cases := [
    { name := "List Nat = List Bool computes through the codes, and gives Nat = Bool", run := fun _ =>
        ok (descEqTypes ++ "#reduce L N = L B\n")
          ["(0 e : True) × (0 e' : (0 e' : True) × ((0 x : Enum [nil, cons]) → cast (transp (fun y _ => (0 e'' : Unit = y) × ((0 x' : Desc Unit) → Unit = y)) (refl (Desc Unit × Unit)) e).1 (ecase x [Desc.ret (), Desc.arg ω N (fun x' => Desc.rec ω () (Desc.ret ()))]) = ecase x [Desc.ret (), Desc.arg ω B (fun x' => Desc.rec ω () (Desc.ret ()))])) × True"] },
    { name := "List Nat = List Bool is refutable (at the tag cons, Nat = Bool; at succ, rec against ret)", run := fun _ =>
        ok (descEqTypes ++ "def refute (e : L N = L B) : Empty := absurd (((e.2.1.2 'cons).1).2.1.2 's)\n") },
    { name := "List A = List C contains A = C (the cons field's equation)", run := fun _ =>
        ok (descEqTypes ++ "def ac (A C : Type) (e : L A = L C) (P : Type → Type) (p : P A) (q : (0 _ : A = C) → P A → P C) : P C :=\n" ++
          "  q (e.2.1.2 'cons).1 p\n") },
    { name := "UIntN 8 = UIntN 16 is refutable (the phantom is in the index type)", run := fun _ =>
        okLib ("import Prelude\ninductive UIntN (w : Nat) where\n  | mk (toNat : Nat)\n" ++
          "def ne (e : UIntN 8 = UIntN 16) : Empty := absurd ((e.1.1.2 16).1 (refl 16))\n") },
    { name := "casts between List A and List C compute, element by element", run := fun _ =>
        ok (descEqTypes ++
          "def lenCast (A C : Type) (h : L A = L C) (x y : A) : len (cast h (L.cons x (L.cons y L.nil)) : L C) = N.s (N.s N.z) := rfl\n" ++
          "def nilCast (A C : Type) (h : L A = L C) : (cast h (L.nil : L A) : L C) = L.nil := rfl\n" ++
          "def numCast (h : L N = L N) : (cast h (L.cons N.z L.nil) : L N) = L.cons N.z L.nil := rfl\n") },
    { name := "a cast at a variable element type stays a cast (no regularity)", run := fun _ =>
        fails (descEqTypes ++
          "def reg (A C : Type) (h : L A = L C) (x : A) (y : C) : (cast h (L.cons x L.nil) : L C) = L.cons y L.nil := rfl\n") "rfl: the two sides are not definitionally equal" },
    { name := "reflexivity: refl T proves T = T for a data type; i = i' alone does not", run := fun _ => do
        ok (descEqTypes ++ "def r (A : Type) : L A = L A := refl (L A)\n")
        fails (descEqTypes ++
          "inductive V (A : Type) : N → Type where\n  | nil : V A .z\n  | cons {0 n : N} (x : A) (xs : V A n) : V A (.s n)\n" ++
          "def bad (A : Type) (n m : N) (h : n = m) : V A n = V A m := h\n") "type mismatch" },
    -- (soundness-audit) `rfl : T = T` at a data type: the equation of the codes has a part
    -- `(t : Enum ls) → …` that is stuck under the binder; `rfl` proves it tag by tag
    { name := "rfl proves T = T for data types: N, an indexed family, a coinductive type", run := fun _ =>
        ok (descEqTypes ++
          "inductive V (A : Type) : N → Type where\n  | nil : V A .z\n  | cons {0 n : N} (x : A) (xs : V A n) : V A (.s n)\n" ++
          "coinductive S (A : Type) where\n  head : A\n  tail : S A\n" ++
          "def r1 : N = N := rfl\n" ++
          "def r2 (A : Type) : L A = L A := rfl\n" ++
          "def r3 (A : Type) (n : N) : V A n = V A n := rfl\n" ++
          "def r4 (A : Type) : S A = S A := rfl\n" ++
          "def c1 (n : N) : (cast (rfl : N = N) n : N) = n := rfl\n" ++
          "def c2 (A : Type) (l : L A) : L A := cast (rfl : L A = L A) l\n") },
    { name := "rfl proves T = T with the Prelude: Bool, Nat, List A, Option A, a structure", run := fun _ =>
        okLib ("import Prelude\nstructure Pt where\n  x : Nat\n  y : Bool\n" ++
          "def r1 : Bool = Bool := rfl\ndef r2 : Nat = Nat := rfl\n" ++
          "def r3 (A : Type) : List A = List A := rfl\ndef r4 (A : Type) : Option A = Option A := rfl\n" ++
          "def r5 : Pt = Pt := rfl\n") },
    { name := "an un-ascribed cast between two data types asks for an ascription (the equation computed)", run := fun _ => do
        fails (descEqTypes ++ "#check fun (A C : Type) (h : L A = L C) (l : L A) => cast h l\n") "has computed"
        ok (descEqTypes ++ "def f (A C : Type) (h : L A = L C) (l : L A) : N := len (cast h l : L C)\n") },
    { name := "rfl still can't prove an equation between different data types", run := fun _ =>
        fails (descEqTypes ++ "def bad : L N = L B := rfl\n") "rfl" },
    { name := "different description constructors are unequal; quantities count", run := fun _ =>
        ok ("#reduce (Desc.ret () : Desc Unit) = Desc.rec 1 () (Desc.ret ())\n" ++
          "#reduce (Desc.rec 1 () (Desc.ret ()) : Desc Unit) = Desc.rec 0 () (Desc.ret ())\n" ++
          "#reduce (Desc.rec 1 () (Desc.ret ()) : Desc Unit) = Desc.rec 1 () (Desc.ret ())\n")
          ["False", "False", "(0 _ : True) × True"] },
    { name := "a quantity variable against a literal at an arg field is stuck too", run := fun _ =>
        ok ("#reduce fun (q : Qty) => (Desc.arg q Unit (fun _ => Desc.ret ()) : Desc Unit) = Desc.arg 1 Unit (fun _ => Desc.ret ())\n")
          ["fun q => Desc.arg q Unit (fun _ => Desc.ret ()) = Desc.arg 1 Unit (fun _ => Desc.ret ())"] },
    { name := "sizes compare as conversion does: μ^{↑∞} ≡ μ^∞ computes like μ^∞ ≡ μ^∞", run := fun _ => do
        let g : Globals ZeroOneMany := {}
        let mu (s : Val ZeroOneMany) : Val ZeroOneMany := .mu 0 (.unit 1) (.dret .tt) .tt s none
        let q (v : Val ZeroOneMany) : Term ZeroOneMany := quote g 0 v
        let inf := q (vEqType g (mu .szInf) (mu .szInf))
        check (match inf with | .eqTy .. => false | _ => true) "μ^∞ ≡ μ^∞ should compute"
        check (inf == q (vEqType g (mu (.szSuc .szInf)) (mu .szInf))) "μ^{↑∞} ≡ μ^∞ should compute like μ^∞ ≡ μ^∞" },
    { name := "a quantity variable against a literal is not unequal (stuck: substituting can make them equal)", run := fun _ =>
        ok ("#reduce fun (q : Qty) => (Desc.rec q () (Desc.ret ()) : Desc Unit) = Desc.rec 1 () (Desc.ret ())\n")
          ["fun q => Desc.rec q () (Desc.ret ()) = Desc.rec 1 () (Desc.ret ())"] },
    -- the Desc analogue of wiz-notes/qty-false-probe.wiz (F6): if the equation computed to
    -- `False`, `bad 1 (refl _)` would be a closed proof of `False`
    { name := "a quantity variable against a literal does not prove False (rec and arg)", run := fun _ => do
        fails "def bad (q : Qty) (e : (Desc.rec q () (Desc.ret ()) : Desc Unit) = Desc.rec 1 () (Desc.ret ())) : False := e\n" "type mismatch"
        fails "def bad (q : Qty) (e : (Desc.arg q Unit (fun _ => Desc.ret ()) : Desc Unit) = Desc.arg 1 Unit (fun _ => Desc.ret ())) : False := e\n" "type mismatch" },
    { name := "lifted proof fields compare by equivalence, not by shape", run := fun _ =>
        okLib ("import Prelude\ninductive PB (P : Prop) where\n  | mk (p : P)\n" ++
          "def pbne (e : PB True = PB False) : Empty := absurd ((e.2.1.2 'mk).1.1 ())\n") },
    -- Hur-style: injectivity of μ in its description must not inject `Type → Prop` into `Type`
    { name := "Hur-style: a description over Type at level 0 is rejected (fields are exactly in Sort (l+1))", run := fun _ =>
        fails ("def HT (F : Type → Prop) : Desc Unit := Desc.arg 1 Type (fun X => Desc.ret ())\n") "universe level mismatch" },
    { name := "Hur-style: over Prop at level 0 it is allowed; injectivity gives the lifted propositions' equation", run := fun _ =>
        okLib ("import Prelude\ninductive H (F : Prop → Prop) where\n  | mk (P : Prop) (p : F P)\n" ++
          "#reduce fun (F G : Prop → Prop) (e : H F = H G) (P : Prop) => ((e.2.1.2 'mk).2 P).1\n")
          ["fun F G e P => ((e.2.1.2 'mk).2 P).1"] },
    { name := "D1 (Abel–Coquand) with two different box descriptions: checks", run := fun _ => do
        unless (abelCoquandTwoBoxes.splitOn "boxEq").length > 2 do throw (IO.userError "variant not built")
        ok abelCoquandTwoBoxes },
    -- with regularity on, the cast between the two descriptions is still structural (it is
    -- on a constructor), so no loop
    { name := "D1 (Abel–Coquand) with two different box descriptions: checks with regularity too", run := fun _ =>
        okWith .full abelCoquandTwoBoxes }
  ]

builtin_initialize registerGroup descEqGroup

end Tests.Elab
