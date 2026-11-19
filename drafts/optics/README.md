# Profunctor optics in Wiz — result

**The language has what the profunctor encoding needs.** `drafts/optics/Profunctor.wiz`
defines `Profunctor`, `Strong`, `Choice`, `Wandering`, the four optic types, the
`Hom`/`Forget`/`ForgetList`/`ForgetOpt`/`Writer Δ` interpretations, `over`/`view`/
`toListOf`/`preview`, composition, and law predicates with proofs for `Hom` and
`ForgetList R`. `wiz check` accepts it, and `wiz run` compiles and executes a program
that uses it (`Smoke.wiz`).

Checked with both the shipped binary (`wiz 0.1.0-dev (aeaa34ef…)`) and the worktree
train7 build (`/workspace/wt/train7/.lake/build/bin/wiz`, which enforces quantities
strictly). The storage half needs `-I drafts/optics` because the shipped toolchain's
library shadows a worktree `lib/`; no toolchain rebuild was done, see "Moving into
`lib/Optic.wiz`". `drafts/optics/check.sh [WIZ]` runs every check.

## Module map

| file | contents |
|---|---|
| `Traversal.wiz` | **The first useful piece.** `PLens.over` and the pure store-encoding `Traversal { view; overAll }`, plus `Traversal.ofLens`. It uses only features in the shipped library. `drafts/storage-engine/Storage.wiz` now imports it instead of defining its own copies. |
| `Profunctor.wiz` | The profunctor classes, `Coprod`, `Delta`, `Iso`/`LensP`/`PrismP`/`TraversalP`, `iso`/`lens`/`prism`/`traversalOf`, the `Hom`/`Forget`/`ForgetList`/`ForgetOpt`/`Writer` interpretations, `view`/`over`/`set`/`toListOf`/`preview`/`overWrite`, composition, the class laws and their proofs. Names ending in `P` avoid the store `Lens`/`PLens`/`Traversal` (Wiz has no namespaces). |
| `EngineIndex.wiz` | The storage engine's index bucket as a `TraversalP`: `indexViewP` reads it (`ForgetList`), `bumpKindP` updates it and returns the `WriteSet` in the same pass (`Writer Δ`), and the checks compare both with the store `Traversal`. |
| `Tests.wiz` | `#eval` cases: iso, lens and its three laws on values, composition, traversal, prism, and the `Writer` deltas. |
| `Laws.wiz` | `fstL`'s GetPut/PutGet/PutPut proved (`GetPut` with `Optic.pairEq`). |
| `Smoke.wiz` | `wiz run` smoke test (compiled output `3`, `2`, `1`). |

```text
drafts/optics/check.sh                      # or: drafts/optics/check.sh /path/to/wiz
wiz check -I drafts/optics drafts/optics/Profunctor.wiz
wiz check -I drafts/optics drafts/optics/Traversal.wiz
wiz check -I drafts/optics drafts/optics/Tests.wiz
wiz check -I drafts/optics drafts/optics/Laws.wiz
wiz check -I drafts/storage-engine -I drafts/optics drafts/optics/EngineIndex.wiz
wiz check -I drafts/storage-engine -I drafts/optics drafts/storage-engine/Storage.wiz
wiz run   -I drafts/optics drafts/optics/Smoke.wiz
```

## What the tests establish

* **Higher-kinded class parameters** — `class Profunctor (P : Type → Type → Type)`, and
  instances at every `P` used: `Hom`, `Forget R`, `ForgetList R`, `ForgetOpt R`,
  `Writer M`. `#check Strong` prints
  `(p : Type → Type → Type) → [super : Profunctor p] → Type 1`.
* **Type constructors in instance heads** — `instance {R} : Profunctor (Forget R)`,
  `instance {M} [Delta M] : Wandering (Writer M)`.
* **No rank-2 `∀` needed** — an optic is a `Π` over `P`:
  `{P : Type → Type → Type} → [Profunctor P] → [Strong P] → P A B → P S T`.
  The caller picks `P`; the instance problem is solved at a concrete `P` (`Hom`,
  `Forget A`, …). The nested `{F : Type → Type}` in `Wandering.wander` is a `Π` in an
  argument type and works.
* **The interpretations coexist** — the same `listT`/`fstL` is run at `Hom` (update),
  `Forget` (read one), `ForgetList` (read all), `ForgetOpt` (preview) and
  `Writer Δ` (update + delta).
* **Laws** — `Profunctor.Lawful`, `Strong.Lawful`, `Choice.Lawful`,
  `Wandering.Lawful` are stated as `Prop`s and proved for `Hom` (all four) and
  `ForgetList R` (all four). `Choice` needs `funext` + cases on `Coprod`; the others are
  `rfl`. The lens laws `LensP.GetPut`/`PutGet`/`PutPut` are stated, checked on `fstL`
  values and **proved** in `Laws.wiz` (GetPut with `Optic.pairEq` from
  `lib/Optic.wiz`, since pair eta is not definitional).
* **The engine** — `indexTraversalP` sees the same 2/0 nodes as the store traversal and
  records 2 patches; the patched counts are 1, 1, 0 for nodes 1, 3, 2, matching
  `Traversal.overAll`.
* **Codegen** — `wiz run` on `Smoke.wiz` prints the expected three lines, so the class
  dictionaries and the higher-kinded `P` erase/compile.

## Frictions and genuine gaps (none block the encoding)

These are not reasons the encoding fails; they are the costs we paid.

0. **Type parameters used to type a runtime value need `ω`.** On the train7 build, an
   instance/definition type parameter defaults to quantity 0, so

   ```wiz
   instance {R : Type} : Wandering (ForgetList R) where
     wander := fun … => trav (F := ConstList R) …
   -- error: variable R declared with quantity 0 but used ω
   ```

   is fixed by `instance {ω R : Type}`. The shipped binary inferred `ω` and accepted the
   unannotated form, so a module can pass `wiz check` with the shipped toolchain and
   fail on the source build. Annotate `ω` on `R`/`M`/`A` where the parameter types a
   returned runtime value (we did in `view`, `toListOf`, `preview`, `overWrite*`, and
   the two `Wandering` instances). This is a required annotation, not a missing
   feature.

1. **A lambda with implicit binders cannot be an explicit argument.** This is the one
   real language limitation we hit:

   ```wiz
   def ho (g : {F : Type → Type} → [i : Applicative F] → (Nat → F Nat) → Nat → F Nat) : Nat :=
     g (F := Id) (fun x => x) 1
   #eval ho (fun {F : Type → Type} [i : Applicative F] (f : Nat → F Nat) (x : Nat) => f x)
   -- error: unexpected implicit binder: the expected type takes an explicit argument
   ```

   Workaround (used for `listTrav`, `idTrav`, `indexTrav`): hoist the traversal to a
   named definition and pass the name. Smallest language change: when checking a
   lambda against a `Π` with implicit/instance binders, bind them the same way a `def`
   signature does. This is ergonomic, not semantic; the optics work today.

2. **Instance fields do not bind the method's implicit arguments.** In an `instance`,
   write only the explicit arguments:

   ```wiz
   class C (A : Type) where f : {n : Nat} → Nat
   instance : C Nat where f := fun {n : Nat} => n   -- error: expected Nat, inferred {n} → Nat
   instance : C Nat where f := fun n => n           -- accepted; `n` is abstracted for you
   ```

3. **There is no `extends`; a superclass is an instance-implicit parameter**
   (docs/stages/30-selfhost-typeclasses.md §30f). Every signature that forms
   `Strong P`/`Choice P`/`Wandering P` must also carry `[Profunctor P]`. This is why
   `LensP`/`TraversalP` have two instance binders. Accepted cost, not a blocker.

4. **Class binder names in a type alias shadow the definition's parameters.** In

   ```wiz
   def TraversalP ... := {P} → [d : Profunctor P] → [w : Wandering P] → ...
   def indexTraversalP (d : IndexDef) ... := ... d ...   -- `d` is the Profunctor instance!
   ```

   we renamed the alias binders to `pf`/`st`/`ch`/`wd`. A distinction between type-alias
   binders and term binders, or warning on capture, would remove the trap.

5. **No namespaces in this line.** The profunctor types are `LensP`/`PrismP`/
   `TraversalP`/`IsoP` because `lib/Optic.wiz` already owns `Lens`/`PLens`/`ALens` and
   `drafts/optics/Traversal.wiz` owns `Traversal`.

## Moving into `lib/Optic.wiz`

The engine-facing piece (`PLens.over`, `Traversal`) needs **no language change**; it
can be appended to `lib/Optic.wiz` as is. The profunctor module also can, with:

1. **Names.** Keep the store `Lens`/`PLens`/`ALens`/`Traversal`; add the profunctor
   classes and `LensP`/`PrismP`/`TraversalP`/`IsoP` (or wait for namespaces, then
   `Optics.Lens` etc.).
2. **Imports.** `lib/Optic.wiz` already imports `Result`/`Logic`; add `Functor` for
   `Applicative`. `Logic.funext` is needed by the `Choice` law. `Coprod`, `Delta`,
   `Writer`, `Hom`, `Forget*`, `ConstList` are new top-level names (no collisions in
   `lib/`); `Delta` avoids `lib/FingerTree.wiz`'s `Monoid` (do not import both and
   define a second `Monoid`).
3. **Rebuild.** A `lib/Optic.wiz` edit is shadowed by the installed toolchain library,
   so testing it needs a toolchain rebuild (`heavy lake build`, one job at a time,
   `heavy --queue`). We did **not** rebuild; all checks above use `drafts/optics` with
   `-I`.
4. **Laws.** Move `fstL`'s GetPut/PutGet/PutPut proofs with `Optic.pairEq` (already in
   `lib/Optic.wiz`) or state them pointwise; add `Traversal`-from-`Lens` law lemmas.
5. **Engine.** Once rebuilt, `Storage.wiz` can import `Optic` alone (drop the local
   `-I drafts/optics` and the `drafts/optics/Traversal.wiz` import); the test scripts
   revert their extra `-I`.

## What was not tested

* No `lib/Optic.wiz` edit and no toolchain rebuild (see 3 above). Both the shipped
  `wiz` (`aeaa34ef`) and the train7 build check the drafts; only the latter is
  authoritative for quantities (friction 0).
* `drafts/storage-engine/Tests.wiz` has pre-existing duplicate definitions
  (`kindIndex`, `uniqueLabel`, `setLabel`, `delNode`) also defined in `Storage.wiz`;
  the shipped and train7 binaries print those diagnostics (and still print the
  expected `#eval` values). We left that file alone; `Storage.wiz`, `EngineIndex.wiz`
  and the optics `Tests.wiz` check cleanly.
* The IO halves of the storage engine (`Durable.wiz`, `Compact.wiz`) need the worktree
  build (`Fd.sync`/`Fd.dataSync` are not in the shipped library); the pure half
  (`Storage.wiz`, `Tests.wiz`) checks and runs, and `Registry`/`Mmap` check. The IO
  failures are unrelated to the optics change (they predate it and are library
  shadowing).
* `Writer`'s `Wandering.Lawful` is not proved (it needs pair eta + `Delta.empty`); the
  law is stated. `TraversalP`/`PrismP`/`IsoP` laws are tested on values, not proved as
  general theorems.
