# Scry optics

`Scry.Optics` and `Scry.CstOptics` are the additive, read-only accessor layer for Scry.
They follow `wiz-notes/analysis-optics-decisions.md`:

* **O4**: read-only optics over Wil, analyses and facts; CST traversal is direct and
  read-only. There is no lens per CST node and no second store.
* **O11**: a few stable traversals/accessors (nodes, edges, relations, fields, uses,
  defs) plus composition. Fields are getters, not generated lenses.
* **O12**: additive. No pass or existing CLI query is migrated. The tests exercise the
  API beside the current code; migration waits for laws, tests and measurements.

## Where it lives

| module | imports | contents |
|---|---|---|
| `lib/Scry/Optics.wiz` (`Scry.Optics`) | `Scry.Wil`, `Scry.Analysis`, `Scry.PointsTo` | the four optic records, Wil origins/statements/terms, def-use folds, points-to views, query/rewrite helpers |
| `scry/src/Scry/CstOptics.wiz` (`Scry.CstOptics`) | `Scry.Optics`, `Scry.Schema`, `Scry.Facts`, `Scry.CstStore` | CST node/edge/relation field getters, `Facts`/`CstStore` folds, facts query paths |

The core and the Wil side are in the library root so a `lib/Scry` pass or rule can import
`Scry.Optics` without depending on the CLI/source package. Only the CST-aware half pays
for `Scry.CstStore`.

## The four optics

| optic | reading | local write |
|---|---|---|
| `Getter S A` | exactly one `A` in an `S` | none |
| `Fold S A` | zero or more `A`s in an `S` | none |
| `Lens S A` | exactly one `A`, `get`/`over` | pure rewrite of a value |
| `Traversal S A` | zero or more `A`s, `toList`/`over` | pure rewrite of a value |

There is no store and no in-place update: `over f s` returns a new `s`. Only Wil values
have local rewrites (an origin, a data-dependence variable). A `Facts` or `CstStore`
value has folds only.

Composition and the common query vocabulary:

```
Getter.comp        get (comp g h) s = get h (get g s)        (rfl)
Fold.comp          toList (comp f g) s = flatMap (toList g) (toList f s)  (rfl)
Fold.mapGetter     Fold S A -> Getter A B -> Fold S B
Fold.filter/any/all/find/length/foldl
Lens.comp          get (comp l m) s = get m (get l s)        (rfl)
Traversal.comp     toList (comp t u) s = flatMap (toList u) (toList t s)  (rfl)
```

## Accessors and traversals

The stable set is deliberately small (O11).

* CST fields: `Cst.nodeId`, `nodeKind`, `nodeField`, `nodeSpan`, `nodeParent`;
  `Cst.edgeSrc`, `edgeDst`, `edgeLabel`; `Cst.relationName`, `relationArity`.
* CST/facts traversal: `Facts.nodesF`, `edgesF`, `relationsF`, `filesF`, `nodeF id`,
  `relationF name`, `relationTuplesF name`, `allTuplesF`; `CstStore.nodesF`, `edgesF`,
  `relationsF`; `Cst.relationTuplesF`, `relationColumnF i`.
* Wil: `stmtOriginL`, `termOriginL`, `funcOriginL`; `blockStmtsT`, `funcBlocksT`,
  `funcStmtsT`, `funcTermsT`, `funcStmtOriginsT`; `Traversal.list`.
* Def-use: `stmtUsesF`, `stmtDefsF`, `termUsesF`, `rhsUsesF`, `fnUsesF`, `fnDefsF`,
  `fnDepsF`, `depFrom`, `depTo`, `depVar`, `depVarL`.
* Points-to: `ptStateG`, `ptLocsF`, `ptLocF`, `ptIdF`, `ptVarsF`, `indirectF`.

## Laws

For a `Lens` the read-only form of the usual laws is stated and proved for each concrete
lens:

* `Lens.GetOver`: `get (over f s) = f (get s)`;
* `Lens.OverId`: `over id s = s`;
* `Lens.OverOver`: `over f (over g s) = over (f ∘ g) s`.

For a `Traversal`:

* `Traversal.OverId`: `over id s = s`;
* `Traversal.OverList`: `toList (over f s) = List.map f (toList s)`.

Proved: `Traversal.list` (OverId by induction, OverList definitionally),
`Wil.blockStmtsT` and `Wil.funcBlocksT` (OverList definitionally), and all three laws for
`stmtOriginL`, `termOriginL`, `funcOriginL` and `depVarL` (by cases/record eta, `rfl`).
`Getter.comp_get`, `Fold.comp_toList`, `Lens.comp_get` and `Traversal.comp_toList` are
definitional.

**Limit.** The generic `Lens.comp`/`Traversal.comp` law is not proved: it needs the
same `List.map`/`flatMap` fusion lemmas as `OverList`, and the composition is exercised
on the fixture instead. `blockStmtsT`/`funcBlocksT` state `OverList`; their generic
`OverId` is a componentwise structure equality in Wiz and is tested on a concrete block
rather than proved as one equation.

## Use

### Query, including the CLI

A query is a path, not a scan written out by hand. The additive `scry query
--edge-src` command (the older `--edge` output is unchanged) is:

```wiz
def Scry.renderQueryEdgeSrc (f : Scry.Facts) (label : String) : String :=
  let ids := Scry.CstOptics.edgeSources f label;   -- edges -> filter label -> edgeSrc
  ...
```

and `Scry.CstOptics.edgeSources` is the composition

```wiz
Fold.mapGetter (Fold.filter (fun e => String.eq (Cst.edgeLabel.get e) label) Facts.edgesF)
  Cst.edgeSrc
```

Compare the previous shape: a filter, a map, and one hand-written field projection per
query. The test checks `--edge` (unchanged) and `--edge-src` on the same fixture.

Other query paths:

```wiz
Scry.CstOptics.nodesOfKind f "identifier"       -- nodes -> filter kind
Scry.CstOptics.relationTuples f "cfg"           -- relations -> lookup name -> tuples
Scry.Fold.toList (Scry.Fold.mapGetter
  (Scry.Facts.nodeF (Scry.nodeId 4)) Scry.Cst.nodeKind) f  -- a focused path
```

### A pass or rule (available, not migrated)

`lib/Scry` code can `import Scry.Optics`; no CLI package dependency. The useful shapes
are folds over uses/defs/deps:

```wiz
-- the registers a function reads, in point order
Scry.Fold.toList Scry.Analysis.fnUsesF info

-- every data-dependence edge, for a rule that asks whether a source reaches a sink
Scry.Fold.toList Scry.Analysis.fnDepsF info
```

The current `Scry.Interproc`/`Scry.RuleTaint` code is **not** changed (O12): it already
has direct loops, and a migration would have to preserve their certificates and golden
outputs. The API is in place for the next measured refactor.

### Rewrite

Rewrites are pure and only over Wil. This shifts every statement origin of a function by
`d` bytes, leaving names, blocks and semantics alone:

```wiz
def Scry.Optics.shiftStmtOrigins (d : Nat) (fn : Wil.Func) : Wil.Func :=
  Traversal.over Wil.funcStmtOriginsT
    (fun sp => Wil.Span.mk sp.file (sp.start + d) (sp.stop + d) sp.node) fn
```

and this renames the register on every data-dependence edge:

```wiz
def Scry.Optics.renameDepVars (f : Nat → Nat) (info : Scry.FnInfo) : Scry.FnInfo :=
  { info with deps := List.map (fun d => Lens.over Analysis.depVarL f d) info.deps }
```

On the fixture, `10,30,70` becomes `110,130,170`; no original value is mutated.

## What is an optic and what is an ordinary function

**Optic:** a composable path to part of an existing value, where the same path is used
to read (and, for Wil only, to rewrite locally). Examples: a node's kind, the sources of
edges with a label, every statement of a function, a function's uses, a register's
points-to locations.

**Ordinary function:** anything that builds or transforms a whole representation, or
maintains an invariant. Keep these as they are:

* the tree-sitter parse and `CstStore.ofFacts` (columns and CSR);
* lowering (CST to Wil), validation, the points-to and reaching-definition fixpoints;
* `Facts.load`, `CstStore.render`/`ofText`, SARIF and certificate construction;
* a rewrite that changes the *shape* of a term or block (an expression simplifier)
  rather than a field of an existing value.

Do not add a lens per structure field, and do not make the CST a chain of lenses: the
native store is columns plus CSR, and a per-node object graph would be the second
representation this API avoids.

## Tests and counts

* `scry/tests/optics.wiz` (`grail test optics`) has 21 `#eval` checks: CST/facts folds
  and composition, a focused node path, edge and relation query paths, the additive
  `--edge-src` query, Wil uses/defs/deps, statement-origin traversal and rewrite, all
  three lens laws plus the list-traversal laws and the composed-origin OverList check,
  the native store view (7 nodes/6 edges/2 relations) and the points-to counts (3
  registers with a location, 2 locations), and a data-dependence rename.
* `grail test` runs the whole `scry` test set; `lake test -- '=scry-taint'` runs the
  existing S4 group, which is unchanged.
* The module adds 4 optic records, 14 field getters, 25 folds, 4 lenses, 6 traversals,
  9 query/rewrite helpers and 26 law/lemma definitions (the law statements, the four
  composition equations, the concrete proofs and `listMapId`; no second data type).
* Native store and points-to behavior is unchanged: `Scry.Native`, `Scry.CstStore` and
  `Scry.PointsTo` are not edited. The tests recompute the same counts from the fixture,
  and the existing `scry-taint`/`grail test` goldens still pass.

## Limits

* No mutable/owned optics, no affine/profunctor/indexed optics, no coends (O1/O13).
* No generic law proof for lens/traversal composition; concrete fixtures only.
* `CstStore.nodesF` materializes one `Node` per column row. For a scale query, read
  `kindName`/`spanOf`/`childArcs`/the CSR directly; the fold is the uniform model view,
  not the fast path.
* Uses and defs are folds: a register occurrence is a fact about a statement, not a
  settable value. Renaming is a separate pure rewrite (`renameDepVars`); no
  use-site-rewriting traversal is exposed yet.
* Rewrites cover origins and data-dependence variables, not arbitrary expression
  rebuilding. That belongs in a lowering/simplifier pass, not an accessor.
* No CLI/query/pass migration yet (O12); `--edge-src` is the only new query, and it is
  additive.
