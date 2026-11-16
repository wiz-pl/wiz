import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-! ## Verification building blocks: lib/SepAlg.wiz (24g, plan S-a), lib/MVarInv.wiz (25h, plan S-c) -/

/-- An MVar whose contents stay at least 3: `modify`, `take`/`put` and `borrow`/`fill`
pass ghost proofs; a trace of the erased model satisfies the invariant theorem. -/
def verifMVarInv : String := "import IO\nimport MVarInv\n-- a counter that never drops below 3: `put` and `modify` must prove it\ndef AtLeast3 (n : Nat) : Prop := Nat.Le 3 n\ndef grow (m : MVar.Inv AtLeast3) : IO Nat :=\n  MVar.Inv.modify m Nat.succ (fun n h => Nat.le_trans 3 n (Nat.succ n) h (Nat.le_succ n))\n-- a ghost proof flows from take to put\ndef addTwo (m : MVar.Inv AtLeast3) : IO Unit := IO.bind (MVar.Inv.take m) (fun r =>\n  MVar.Inv.put m (r.1 + 2) (Nat.le_trans 3 r.1 (r.1 + 2) r.2.1 (Nat.le_add_right r.1 2)))\ndef borrowed (m : MVar.Inv AtLeast3) : IO Nat := MVar.Inv.borrow m (fun a ok h =>\n  MVar.Inv.fill m h (a + a) (Nat.le_trans 3 a (a + a) ok (Nat.le_add_right a a)) (IO.pure a))\ndef main : IO Unit := IO.bind (MVar.Inv.newFull (I := AtLeast3) 4 rfl) (fun m =>\n  IO.bind (grow m) (fun old => IO.bind (addTwo m) (fun _ => IO.bind (borrowed m) (fun b =>\n  IO.bind (MVar.Inv.take m) (fun r =>\n    IO.println (Nat.toString (old + b + r.1)))))))\n#eval Op.run (.cons (Op.put 2) (.cons Op.take (.cons Op.read .nil))) (Option.none (A := Nat))\ndef traceOk : AllHold AtLeast3 (Op.run (.cons (Op.put 5) (.cons Op.take (.cons (Op.put 7) (.cons Op.read .nil)))) .none) :=\n  Op.run_holds AtLeast3 _ .none (rfl, (rfl, ())) ()\n"

/-- Separation algebras: tickets add up, an exclusive value updates under a frame, two
heap cells compose. -/
def verifSepAlg : String := "import SepAlg\n-- two holders of 2 and 3 tickets together hold 5\ndef tickets : RProp.Entails (RProp.star natAdd (RProp.own natAdd 2) (RProp.own natAdd 3))\n    (RProp.own natAdd 5) :=\n  RProp.own_join natAdd 2 3\ndef swapEx (a b : Nat) : PCM.Update (exclPCM Nat) (Excl.ex a) (Excl.ex b) := Excl.update a b\n-- a pair of a counter and an exclusive cell\ndef pairM : PCM (Nat × Excl Nat) := prodPCM natAdd (exclPCM Nat)\ndef pairUpd : PCM.Update pairM (pairM.op (0, Excl.ex 1) (4, Excl.none)) (pairM.op (0, Excl.ex 9) (4, Excl.none)) :=\n  PCM.update_frame pairM (fun c v => (v.1, Excl.update 1 9 c.2 v.2)) (4, Excl.none)\n-- the heap {1 ↦ 5} and {2 ↦ 7} are disjoint, so their composite is valid\ndef h1 : Heap Nat := Heap.single 1 5\ndef h2 : Heap Nat := Heap.single 2 7\ndef comp : Nat → Excl Nat := (heapPCM Nat).op (Heap.toExcl h1) (Heap.toExcl h2)\n#eval comp 1\n#eval comp 2\n#eval comp 3\n#eval Excl.op (Excl.ex 1) (Excl.none (A := Nat))\n#eval Excl.ok (Excl.op (Excl.ex 1) (Excl.ex (A := Nat) 2))\n"

def verifGroup : Group where
  name := "verif"
  exercise := "lib/SepAlg.wiz, lib/MVarInv.wiz (stages 24g, 25h)"
  cases := [
    { name := "SepAlg: the library checks with no axiom; instances compute", run := fun _ =>
        okLibs verifSepAlg [".ex 5", ".ex 7", ".none", ".ex 1", ".false"] },
    { name := "SepAlg: a frame-preserving update must be proved; two exclusive owners clash", run := fun _ => do
        failsLibs "import SepAlg\n-- replacing an exclusive value is an update, but not by reflexivity\ndef bad : PCM.Update (exclPCM Nat) (Excl.ex 1) (Excl.ex 2) := PCM.update_refl (exclPCM Nat) (Excl.ex 1)" "mismatch"
        failsLibs "import SepAlg\n-- two owners of one exclusive cell: the composite is not valid\ndef bad : Excl.Valid (Excl.op (Excl.ex 1) (Excl.ex (A := Nat) 2)) := rfl" "rfl" },
    { name := "MVarInv: ghost proofs flow through take/put, borrow/fill and modify", run := fun _ => do
        okLibs verifMVarInv [".cons .none (.cons (.some 2) (.cons .none .nil))"]
        cRunLibs (verifMVarInv.replace "#eval Op.run (.cons (Op.put 2) (.cons Op.take (.cons Op.read .nil))) (Option.none (A := Nat))\n" "") "25\n" },
    { name := "MVarInv: a put without a proof, an update that breaks the invariant, a dropped hole", run := fun _ => do
        failsLibs "import IO\nimport MVarInv\ndef AtLeast3 (n : Nat) : Prop := Nat.Le 3 n\n-- no proof that 1 is at least 3\ndef bad (m : MVar.Inv AtLeast3) : IO Unit := MVar.Inv.put m 1 rfl" "rfl"
        failsLibs "import IO\nimport MVarInv\ndef AtLeast3 (n : Nat) : Prop := Nat.Le 3 n\n-- `pred` does not keep the invariant\ndef shrink (m : MVar.Inv AtLeast3) : IO Nat := MVar.Inv.modify m Nat.pred (fun n h => h)" "mismatch"
        failsLibs "import IO\nimport MVarInv\ndef AtLeast3 (n : Nat) : Prop := Nat.Le 3 n\n-- the hole is never refilled\ndef bad (m : MVar.Inv AtLeast3) : IO Nat := MVar.Inv.borrow m (fun a ok h => IO.pure a)" "quantity 1" }
  ]

builtin_initialize registerGroup verifGroup

end Tests.Elab
