# Profunctor optics in Wiz — result

**The language has what the profunctor encoding needs**, and the layer now lives in
`lib/Optic.wiz` under `import Optic` (branch `optics-lib`). What remains under
`drafts/optics/` is the storage-engine side (`EngineIndex.wiz`), a value-level test
file (`Tests.wiz`) and a compiled smoke test (`Smoke.wiz`); the store `Traversal` that
used to be here is `lib/Optic.wiz`'s (next to `PLens.over`).

`lib/Optic.wiz` defines `Profunctor`, `Strong`, `Choice`, `Wandering`, the four optic
types (`Iso`/`LensP`/`PrismP`/`TraversalP`), the `Hom`/`Forget`/`ForgetList`/
`ForgetOpt`/`Writer Δ` interpretations, `over`/`view`/`set`/`toListOf`/`preview`/
`overWrite`, composition, `LensP.ofLens` (store lens → profunctor lens), the class laws
with proofs for `Hom` and `ForgetList R`, and `fstL`'s lens laws. `wiz check` accepts
it, and `wiz run` compiles and executes a program that uses it (`Smoke.wiz`).

**Every command here needs a rebuilt toolchain** (`heavy lake build`, or the branch's
`.lake/build/bin/wiz`): a `lib/` edit is shadowed by the installed library. The old
shipped-binary `-I drafts/optics` path is gone because the definitions moved.

## Module map

| file | contents |
|---|---|
| `EngineIndex.wiz` | The storage engine's index bucket: `Storage.indexTraversalP` is the canonical `TraversalP`; the module reads it at `ForgetList`, updates it and returns the `WriteSet` in the same pass (`Writer Δ`), and compares both with the store `Traversal` shim. |
| `Tests.wiz` | `#eval` cases: iso, lens and its three laws on values, composition, traversal, prism, and the `Writer` deltas. |
| `Limits.wiz` | Where the profunctor layer stops: an indexed place as a `TraversalP` (a 0-or-1 focus that cannot fail), beside `List.atL`'s `.err .outOfBounds`. |
| `limits/*.wiz` | Expected-to-fail programs for the four things that cannot move: `Lens.pair`, a `Getter`/`Fold`, `TraverseMut`, and `ALens`'s `Result`. Their errors are quoted in the report and in `limits/README.md`. |
| `Smoke.wiz` | `wiz run` smoke test (compiled output `3`, `2`, `1`). |

```text
drafts/optics/check.sh /path/to/worktree/.lake/build/bin/wiz
wiz check -I drafts/optics drafts/optics/Tests.wiz
wiz check -I drafts/storage-engine -I drafts/optics drafts/storage-engine/Storage.wiz
wiz check -I drafts/storage-engine -I drafts/optics drafts/optics/EngineIndex.wiz
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
  `Forget` (read one), `ForgetList` (read all), `ForgetOpt` (preview) and `Writer Δ`
  (update + delta).
* **Laws** — `Profunctor.Lawful`, `Strong.Lawful`, `Choice.Lawful`,
  `Wandering.Lawful` are stated as `Prop`s and proved for `Hom` (all four) and
  `ForgetList R` (all four). `Choice` needs `funext` + cases on `Coprod`; the others are
  `rfl`. The lens laws `LensP.GetPut`/`PutGet`/`PutPut` are stated, checked on `fstL`
  values and proved for `fstL` in `lib/Optic.wiz` (GetPut with `Optic.pairEq`, since
  pair eta is not definitional).
* **Store lenses lift** — `LensP.ofLens` turns a store `Lens` into a `LensP`, and
  `LensP.ofLens_view`/`_over` prove the two readings agree by `rfl`, so derived field
  lenses (`deriving Lens`) work with the profunctor API.
* **The engine** — `indexTraversalP` sees the same 2/0 nodes as the store traversal and
  records 2 patches; the patched counts are 1, 1, 0 for nodes 1, 3, 2, matching
  `Traversal.overAll`. Moving it needs the key in the focus (`U64 × Node`), which the
  store encoding hid in the lens closure.
* **Codegen** — `wiz run` on `Smoke.wiz` prints the expected three lines, so the class
  dictionaries and the higher-kinded `P` erase/compile.

## Frictions and genuine gaps (none block the encoding)

These are not reasons the encoding fails; they are the costs we paid. The first two are
annotated away in `lib/Optic.wiz`.

0. **Type parameters used to type a runtime value need `ω`.** A toolchain build's
   instance/definition type parameter defaults to quantity 0, so

   ```wiz
   instance {R : Type} : Wandering (ForgetList R) where
     wander := fun … => trav (F := ConstList R) …
   -- error: variable R declared with quantity 0 but used ω
   ```

   is fixed by `instance {ω R : Type}`. We annotated `ω` on `R`/`M`/`A` where the
   parameter types a returned runtime value (`view`, `toListOf`, `preview`,
   `overWrite*`, the two `Wandering` instances). A required annotation, not a missing
   feature.

1. **A lambda with implicit binders cannot be an explicit argument.** This is the one
   real language limitation we hit:

   ```wiz
   def ho (g : {F : Type → Type} → [i : Applicative F] → (Nat → F Nat) → Nat → F Nat) : Nat :=
     g (F := Id) (fun x => x) 1
   #eval ho (fun {F : Type → Type} [i : Applicative F] (f : Nat → F Nat) (x : Nat) => f x)
   -- error: unexpected implicit binder: the expected type takes an explicit argument
   ```

   Workaround (used for `listTrav`, `listWhereTrav`, `idTrav`, `indexTrav`): hoist the
   traversal to a named definition and pass the name. The hoist has a second half: an
   *applied* named definition whose result is a Π with implicit binders is still
   normalised first and cannot be an argument either, so `traversalOf (listWhereTrav
   keep)` fails while `@Wandering.wander … (listWhereTrav keep) x` works (we build
   `listWhereT` that way), and `view (LensP.ofLens l)` fails while binding
   `def p := LensP.ofLens l` first works (we state the lift's laws on the fully applied
   `LensP.ofLensAt`). Smallest language change: when checking a lambda or an
   application against a `Π` with implicit/instance binders, bind them the same way a
   `def` signature does. Ergonomic, not semantic; the optics work today.

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
   `LensP`/`TraversalP` have two instance binders. Consequence: `Wandering P` does not
   give `Strong P`, so a `LensP` is not usable where a `TraversalP` is expected even
   though a lens is a traversal; a `TraversalP`-valued conversion would need both
   dictionaries carried through. Accepted cost, not a blocker.

4. **Class binder names in a type alias shadow the definition's parameters.** In

   ```wiz
   def TraversalP ... := {P} → [d : Profunctor P] → [w : Wandering P] → ...
   def indexTraversalP (d : IndexDef) ... := ... d ...   -- `d` is the Profunctor instance!
   ```

   we renamed the alias binders to `pf`/`st`/`ch`/`wd`. A distinction between type-alias
   binders and term binders, or a warning on capture, would remove the trap.

5. **No namespaces in this line.** The profunctor types are `LensP`/`PrismP`/
   `TraversalP`/`IsoP` because `lib/Optic.wiz` already owns `Lens`/`PLens`/`ALens` and
   `drafts/optics/Traversal.wiz` owns the store `Traversal`.

## What was not tested

* The IO halves of the storage engine (`Durable.wiz`, `Compact.wiz`) need the worktree
  build; unrelated to the optics change.
* `drafts/storage-engine/Tests.wiz` has pre-existing duplicate definitions
  (`kindIndex`, `uniqueLabel`, `setLabel`, `delNode`) also defined in `Storage.wiz`.
* `Writer`'s `Wandering.Lawful` is not proved (it needs pair eta + `Delta.empty`); the
  law is stated. `TraversalP`/`PrismP`/`IsoP` laws are tested on values, not proved as
  general theorems beyond the class laws.
