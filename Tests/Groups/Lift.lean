import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- Q4: description fields live exactly in `Sort (l+1)`; the elaborator lifts smaller
ones with `ULift`, invisibly (`Elab/Inductive.lean`, CoreSpec §4.1, §9.1). -/
def liftPrelude : String := "import Prelude
inductive Pos where
  | mk (n : Nat) (h : n = n)
def Pos.val (p : Pos) : Nat := match p with
  | .mk n _ => n
inductive Prod2.{u, v} (A : Type u) (B : Type v) : Type (max u v) where
  | mk (a : A) (b : B)
def Prod2.snd.{u, v} {A : Type u} {B : Type v} (p : Prod2 A B) : B := match p with
  | .mk _ b => b
inductive T3 : Type 1 where
  | leaf
  | node (f : Nat → T3)
def depth : T3 → Nat
  | .leaf => 0
  | .node f => Nat.succ (depth (f 0))
"

def liftGroup : Group where
  name := "lift"
  exercise := "Q4 (lifted description fields)"
  cases := [
    { name := "a proof field is lifted invisibly: constructor, pattern, printing", run := fun _ =>
        okLib (liftPrelude ++ "#eval Pos.val (Pos.mk 3 rfl)\n#check Pos.mk\n#reduce Pos.mk 3 rfl\n#reduce Pos.val (Pos.mk 3 rfl)")
          ["3", "Pos.mk : (n : Nat) → n = n → Pos", ".mk 3 ()", "3"] },
    { name := "the fields of Prod.{u,v} and the tag of a polymorphic type are lifted invisibly", run := fun _ =>
        okLib (liftPrelude ++ "#check Prod2.mk\n#eval Prod2.snd (Prod2.mk 1 Bool.true)\n#reduce Prod2.mk 1 Bool.false\n" ++
            "#check Prod2.casesOn\n#reduce Prod2.desc Nat Bool")
          ["Prod2.mk : {A : Type ?u0} → {B : Type ?u1} → A → B → Prod2 A B", ".true", ".mk 1 .false",
           "Prod2.casesOn : {A : Type ?u0} → {B : Type ?u1} → (0 motive : Prod2 A B → Sort ?u2) → ((a : A) → (b : B) → motive (.mk a b)) → (x : Prod2 A B) → motive x",
           "Desc.arg ω (ULift Enum [mk]) (fun t => ecase t [Desc.arg ω (ULift Nat) (fun a => Desc.arg ω (ULift Bool) (fun b => Desc.ret ()))])"] },
    { name := "an infinitary field over a smaller domain, in a type in Type 1 (structural recursion through it)", run := fun _ =>
        okLib (liftPrelude ++ "#eval depth (T3.node (fun _ => T3.node (fun _ => T3.leaf)))\n" ++
            "inductive Tr : Type 1 where\n  | leaf\n  | node (T : Type) (f : T → Tr)\n" ++
            "def Tr.size (t : Tr) : Nat := match t with\n  | .leaf => 0\n  | .node _ _ => 1\n#eval Tr.size (Tr.node Nat (fun _ => Tr.leaf))")
          ["2", "1"] },
    { name := "a lifted proof field in a coinductive type", run := fun _ =>
        okLib ("import Prelude\ncoinductive S where\n  hd : Nat\n  ok : True\n  tl : S\n" ++
            "def zs : S\n  | .hd => 0\n  | .ok => ()\n  | .tl => zs\n#eval S.hd (S.tl zs)\n#check S.ok") ["0", "S.ok : S → True"] },
    { name := "lifting is erased: the #ir of a lifted type is the unlifted one's", run := fun _ => do
        let src := "import Prelude\ninductive Box.{u} (A : Type u) : Type u where\n  | box (a : A)\n" ++
          "def unbox.{u} {A : Type u} (b : Box A) : A := match b with\n  | .box a => a\n" ++
          "inductive Box0 (A : Type) : Type where\n  | box (a : A)\n" ++
          "def unbox0 {A : Type} (b : Box0 A) : A := match b with\n  | .box a => a\n#ir unbox\n#ir unbox0\n" ++
          "inductive Pos where\n  | mk (n : Nat) (h : n = n)\ninductive Pos0 where\n  | mk (n : Nat)\n" ++
          "def Pos.val (p : Pos) : Nat := match p with\n  | .mk n _ => n\ndef Pos0.val (p : Pos0) : Nat := match p with\n  | .mk n => n\n" ++
          "#ir Pos.val\n#ir Pos0.val\n"
        let s := runFrontend (R := ZeroOneMany) src { loader := ← preludeLoader, trustedModule := Tests.libModule }
        match s.messages.toList.map (·.text) with
        | [a, b, c, d] =>
          checkEq (b.replace "unbox0" "unbox") a
          checkEq (d.replace "Pos0" "Pos") c
        | ms => throw (IO.userError s!"unexpected messages {ms}") },
    { name := "the surface Desc.arg takes a field only in exactly its universe", run := fun _ =>
        failsLib "import Prelude\ndef D : Desc Unit := Desc.arg 1 True (fun _ => Desc.ret ())" "type mismatch" }
  ]

builtin_initialize registerGroup liftGroup

end Tests.Elab
