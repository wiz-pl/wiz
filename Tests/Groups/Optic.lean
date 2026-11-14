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
  cases := [
    { name := "the optics library checks, with its lens laws", run := fun _ =>
        okOptic "import Optic\n#check List.atL_lawful\n#check Lens.comp_lawful"
          ["List.atL_lawful : {A : Type} → (i : Nat) → PLens.Lawful (List A) A (List.atL A i)",
           "Lens.comp_lawful : {S : Type} → {A : Type} → {B : Type} → (l : Lens S A) → (m : Lens A B) → Lens.Lawful S A l → Lens.Lawful A B m → Lens.Lawful S B (Lens.comp S A B l m)"] },
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
    -- dependent optics (lib/OpticDep.wiz): the focus type is a family over the source
    { name := "dependent optics: a focus whose type depends on the source", run := fun _ =>
        okOptic ("import OpticDep\n" ++
          "def p : (n : Nat) × Vec Nat n := (3, Vec.fromList [10, 20, 30])\n" ++
          "#check DepLens.get\n" ++
          "#eval DepLens.get tabL p (Fin.of 3 1 rfl)\n" ++
          "#eval Vec.toList (DepLens.set tabL p (fun i => Nat.add (DepLens.get tabL p i) 1)).2\n" ++
          "#eval Vec.toList (DepLens.set tabL p (DepLens.get tabL p)).2")
          ["DepLens.get : {S : Type} → {A : S → Type} → DepLens S A → (s : S) → A s",
           "20", ".cons 11 (.cons 21 (.cons 31 .nil))", ".cons 10 (.cons 20 (.cons 30 .nil))"] },
    { name := "a dependent lens has no generic PutGet: the law needs a transport", run := fun _ => do
        okOptic ("import OpticDep\n" ++
          "def p : (n : Nat) × Vec Nat n := (3, Vec.fromList [10, 20, 30])\n" ++
          "#eval Vec.get (DepLens.get sigL (DepLens.set sigL p (Vec.fromList [4, 5, 6]))) (Fin.of 3 0 rfl)")
          ["4"]
        failsOptic ("import OpticDep\n" ++
          "def badPG {S : Type} {A : S → Type} (l : DepLens S A) :\n" ++
          "    (s : S) → (a : A s) → DepLens.get l (DepLens.set l s a) = a := fun s a => rfl")
          "type mismatch" },
    { name := "optics as coends: a residual representation and the normal form", run := fun _ =>
        okOptic ("import OpticDep\n" ++
          "#eval Lens.get (PreCoend.toLens (PreCoend.ofLens Pair2.sndL)) (Pair2.mk 1 2)\n" ++
          "#eval Lens.get (PreCoend.toLens (PreCoend.ofLens Pair2.fstL)) (Pair2.mk 3 4)\n" ++
          "#eval Lens.set (PreCoend.toLens (PreCoend.ofLens Pair2.sndL)) (Pair2.mk 1 2) 9\n" ++
          "#eval (PreCoend.toLens (PreCoend.ofLens Pair2.fstL) (Pair2.mk 5 6)).1")
          ["2", "3", "(1, 9, ())", "5"] },
    { name := "a linear optic moves a linear focus; a linear set is rejected", run := fun _ => do
        okOptic ("import OpticDep\n" ++
          "inductive Tok where | mk (n : Nat)\n" ++
          "def Tok.use (1 t : Tok) : Nat := match t with | .mk n => n\n" ++
          "def bump (1 t : Tok) : Tok := match t with | .mk n => Tok.mk (Nat.add n 1)\n" ++
          "#eval Tok.use (Lens1.over Lens1.id bump (Tok.mk 41))")
          ["42"]
        failsOptic ("import OpticDep\n" ++
          "def badSet {A S : Type} (1 st : Store1 A S) (1 b : A) : S :=\n" ++
          "  let 1 (a, k) := st;\n  k b") "quantity 1 but used 0" },
    { name := "a dependent traversal resizes a vector", run := fun _ =>
        okOptic ("import OpticDep\n" ++
          "#eval Vec.toList (DepTraverse.put vecResize (3, Vec.fromList [1,2,3]) [9, 8]).2\n" ++
          "#eval DepTraverse.get vecResize (2, Vec.fromList [7, 8])\n" ++
          "#eval DepTraverse.get vecResize (DepTraverse.put vecResize (3, Vec.fromList [1,2,3]) [9, 8])")
          [".cons 9 (.cons 8 .nil)", ".cons 7 (.cons 8 .nil)", ".cons 9 (.cons 8 .nil)"] }
  ]

builtin_initialize registerGroup opticGroup

end Tests.Elab
