import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

def failsOptic (input : String) (fragment : String) : IO Unit := do
  let loader ← libLoader
  let s := runFrontend (R := ZeroOneMany) input { loader, trustedModule := Tests.libModule }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render input
  unless errs.size == 1 do throw (IO.userError s!"expected one error, got {errs.size}: {errs}")
  unless (errs[0]!.splitOn fragment).length > 1 do
    throw (IO.userError s!"error does not mention '{fragment}':\n{errs[0]!}")

def opticGroup : Group where
  name := "optic"
  exercise := "lib/Optic.wiz (Feral, RD11)"
  parallel := true
  cases := [
    { name := "the optics library checks, with its lens laws", run := fun _ =>
        okOptic "import Optic\n#check List.atL_lawful\n#check Lens.comp_lawful\n#check Lens"
          ["List.atL_lawful : {A : Type} → (i : Nat) → PLens.Lawful (List A) A (List.atL A i)",
           "Lens.comp_lawful : {S : Type} → {A : Type} → {B : Type} → (l : Lens S A) → (m : Lens A B) → Lens.Lawful S A l → Lens.Lawful A B m → Lens.Lawful S B (Lens.comp S A B l m)",
           -- the store lens is small: the borrow lowering stores and returns it
           "Lens : Type → Type → Type"] },
    { name := "lenses get, put and compose", run := fun _ =>
        okOptic ("import Optic\n#eval Lens.set Pair2.fstL (Pair2.mk 1 2) 5\n" ++
          "#eval Lens.over (Lens.comp Pair2.sndL Pair2.fstL) Nat.succ (Pair2.mk 1 (Pair2.mk 10 20))\n" ++
          "#eval Result.map (fun (st : Store Nat (List Nat)) => st.2 42) (List.atL 1 (List.cons 1 (List.cons 2 (List.cons 3 List.nil))))\n" ++
          "#eval Result.map Store.extract (List.atL 5 (List.cons 1 List.nil))")
          ["(5, 2, ())", "(1, (11, 20, ()), ())", ".ok (.cons 1 (.cons 42 (.cons 3 .nil)))", ".err .outOfBounds"] },
    { name := "zoom, affine borrows and traversals", run := fun _ =>
        okOptic ("import Optic\n#eval zoom Pair2.fstL (fun (n : Nat) => Result.ok (n, n + 1)) (Pair2.mk 7 8)\n" ++
          "#eval Affine.over Nat.succ (Affine.comp (Affine.some (Pair2.mk 1 2) (fun p => p)) (fun p => Affine.some p.fst (fun a => Pair2.mk a p.snd)))\n" ++
          "#eval TraverseMut.traverseM (fun (x : Nat) (acc : Nat) => Result.ok (x * 2, acc + x)) (List.cons 1 (List.cons 2 List.nil)) 0")
          [".ok (7, 8, 8, ())", "(2, 2, ())", ".ok (.cons 2 (.cons 4 .nil), 3)"] },
    { name := "an unlawful lens has no GetPut proof", run := fun _ =>
        failsOptic ("import Optic\ndef bad : Lens (List Nat) Nat := fun s => match s with\n" ++
          "  | .nil => (0, fun a => List.cons a List.nil)\n  | .cons x xs => (x, fun a => List.cons a (List.cons a xs))\n" ++
          "def badGP : Lens.GetPut bad := fun s => refl s") "type mismatch" },
    { name := "an optic that quantifies over a type constructor is Type 1 (predicative Pi rule)", run := fun _ =>
        -- The minimal profunctor shape: no classes, just the `p : Type → Type → Type` binder.
        -- This must fail by the Pi sort rule, not by non-cumulativity, so it stays a
        -- `Type : Type` tripwire: cumulativity would only raise universes, never lower this.
        failsOptic ("import Prelude\ndef Lens (S T A B : Type) : Type :=\n" ++
          "  {p : Type → Type → Type} → (p A B → p S T)") "inferred: Type 1" },
    { name := "the frame rule for values: a zoom keeps every independent place", run := fun _ => do
        okOptic ("import Optic\n" ++
          "def t (m : Nat → Result (Unit × Nat)) (s : Pair2 Nat Nat) :\n" ++
          "    Result.All (fun (p : Unit × Pair2 Nat Nat) => (Pair2.sndL p.2).1 = (Pair2.sndL s).1) (zoom Pair2.fstL m s) :=\n" ++
          "  zoom.frame Pair2.fstL Pair2.sndL Pair2.indep m s")
        -- the zoomed place itself is not kept
        failsOptic ("import Optic\n" ++
          "def bad (m : Nat → Result (Unit × Nat)) (s : Pair2 Nat Nat) :\n" ++
          "    Result.All (fun (p : Unit × Pair2 Nat Nat) => (Pair2.fstL p.2).1 = (Pair2.fstL s).1) (zoom Pair2.fstL m s) :=\n" ++
          "  zoom.frame Pair2.fstL Pair2.sndL Pair2.indep m s") "type mismatch" },
    { name := "profunctor optics: one optic, five interpretations, and the class laws", run := fun _ =>
        okOptic ("import Optic\n" ++
          "#eval view fstL ((7 : Nat), Bool.true)\n" ++
          "#eval over fstL Nat.succ ((1 : Nat), Bool.true)\n" ++
          "#eval toListOf (listT (A := Nat)) (List.cons 1 (List.cons 2 List.nil))\n" ++
          "#eval List.length (overT (listT (A := Nat)) Nat.succ (List.cons 1 (List.cons 2 List.nil)))\n" ++
          "#eval preview headP (List.cons 5 List.nil)\n" ++
          "#eval List.length (overWrite (listT (A := Nat)) (fun n => (n + 1, List.cons n List.nil)) (List.cons 1 (List.cons 2 List.nil))).2\n" ++
          "def lawUse : LensP.Lawful (S := Nat × Bool) (A := Nat) fstL := fstL_lawful\n" ++
          "def classUse : Profunctor.Lawful Hom := Hom.profunctorLawful\n" ++
          "def classUse2 {R : Type} : Profunctor.Lawful (ForgetList R) := ForgetList.profunctorLawful\n")
          ["7", "(2, .true)", ".cons 1 (.cons 2 .nil)", "2", ".some 5", "2"] },
    { name := "a traversal over an index bucket, and the store lens lift", run := fun _ =>
        -- The bucket is the engine's shape: entries carry their key, and only the entries
        -- whose key is the queried one are foci (`listWhereT`).
        okOptic ("import Optic\n" ++
          "def bucket : TraversalP (List (Nat × Nat)) (List (Nat × Nat)) (Nat × Nat) (Nat × Nat) :=\n" ++
          "  listWhereT (fun p => Nat.beq p.1 1)\n" ++
          "#eval toListOf bucket [(1, 7), (2, 8), (1, 9)]\n" ++
          "#eval overT bucket (fun p => (p.1, p.2 + 10)) [(1, 7), (2, 8), (1, 9)]\n" ++
          "#eval List.length (overWrite bucket (fun p => ((p.1, p.2 + 1), List.cons p.1 List.nil)) [(1, 7), (2, 8), (1, 9)]).2\n" ++
          -- the store lens lifts, and over/view agree with the store forms
          "def pairP : LensP (Pair2 Nat Nat) (Pair2 Nat Nat) Nat Nat := LensP.ofLens Pair2.fstL\n" ++
          "#eval Nat.beq (view pairP (Pair2.mk 1 2)) 1\n" ++
          "#eval Nat.beq (Lens.get Pair2.fstL (over pairP Nat.succ (Pair2.mk 1 2))) (Lens.get Pair2.fstL (Lens.over Pair2.fstL Nat.succ (Pair2.mk 1 2)))\n")
          [".cons (1, 7) (.cons (1, 9) .nil)",
           ".cons (1, 17) (.cons (2, 8) (.cons (1, 19) .nil))",
           "2", ".true", ".true"] }
  ]

builtin_initialize registerGroup opticGroup

end Tests.Elab
