# The structured view: `wiz-info/1` on `wiz-lint/2`

**Status.** Implementation lane `structured-view`, 2026-11-23, base
`integration/train12` `f489cc876`, branch `agent/structured-view`. Host-side code and
tests are written; no build was run in this lane (the queue is for train11). §7 lists
what must be run later. This is Ext Item 3 of `wiz-notes/extensibility.md` §4: the
structured view of a declaration, as a capability-scoped, versioned view, wired through
the lint registry and through one `Tac` request.

**Verdict.** `wiz-lint/2` adds exactly one capability, `info`. It carries a per-declaration
binder projection (name, use, depth, binder kind, binder info, the **head constant and
arity** of the binder's type) and a whitelist of the elaboration `Info` nodes. Every
term the view does not name is an opaque `h<n>` handle. `wiz-lint/1` is untouched: a v1
set builds the same text as before, and `lib/Lint.wiz` ignores the new tags. The core
`W101` is re-expressed as a `wiz-lint/2` fixture rule and compared with the Lean rule on
the same source; the Lean body is **not** deleted in this slice (§6).

---

## 1. Why this shape

`wiz-notes/extensibility.md` §3.1 B5: the v1 view is line-oriented and has no term, so a
rule like `W101` (an unused binder) cannot be a Wiz rule. The two bad extremes are a
text blob of a term (unpinnable) and the kernel's `Term` (leaks the representation and
churns). This view names only the facts an analysis rule needs:

* names, spans, depths, counts, booleans and fixed spellings;
* the head constant of a type and the number of arguments applied to it;
* an opaque handle for the term when head/arity do not name it.

No `Term`, de Bruijn index, universe level, metavariable, local context or goal
hypothesis is in the wire format.

## 2. Versioning and capability

| ABI | capabilities | `info` |
|---|---|---|
| `wiz-lint/1` | `decl`, `spans`, `imports`, `globals`, `messages`, `facts` | refused |
| `wiz-lint/2` | v1's set plus `info` | **offered** |

* A set's `lint-set "name" "wiz-lint/2" [info]` header names the version. The registry
  (`Wiz/Lint.lean` `checkSet`) refuses an unknown ABI; it refuses a capability the ABI
  does not provide (`Wiz/Lint/Basic.lean` `abiCapability`).
* A v1 set that declares `info` is a registration error that names `info` and says the
  structured view is in `wiz-lint/2`.
* `wiz-lint/2` with no `info` declaration emits exactly the v1 sections; only the
  `view` header changes. `tactics`, `kernelTerm` and `sourceText` remain unavailable at
  every version.
* `lib/Lint.wiz` has `Lint.Capability.at ABI c` (the versioned predicate) beside the v1
  `stable`; a test compares both with `Wiz/Lint/Basic.lean`.

## 3. The view document

The header and v1 sections are those of `docs/lint-abi.md`; a v2 document appends two
sections **after** `message`, in this order:

```
binder-info	<decl>	<depth>	<name>	<used>	<kind>	<bi>	<head>	<arity>	<handle>
info	<decl>	<node>	<start>	<stop>	<name>	<flag>	<head>	<arity>	<handle>	<data>
```

### 3.1 `binder-info`

| field | meaning |
|---|---|
| `decl` | the declaration name (the v1 `binder` row cannot say which declaration it belongs to) |
| `depth` | the binder's depth in its declaration's binder stack; the same number `W101` uses in `anchor = decl#depth` |
| `name` | the binder's name |
| `used` | does its scope mention it (a type or proof use counts, as `W101` counts) |
| `kind` | `pi`, `lam`, `let`, `sigma`, `split` or `ecase` |
| `bi` | a `Π`'s `default`, `implicit` or `instImplicit`; `default` for other kinds |
| `head` | the head constant of the binder's type, `""` if it is not a constant application |
| `arity` | the number of arguments applied to that head |
| `handle` | `h<n>` when the binder has a type term; `""` for a `lam`/`split`/`ecase` binder |

The traversal is the one `W101`/`W102` already used, moved to `Wiz/Elab/View.lean`:
`pi`/`lam`/`letE`/`sigma`/`split`/`ecase` binders are handled explicitly, other
constructors' children generically; a declaration parameter is not counted twice (the
`Π` in the type and the `lam` in the value are paired); quantity-0 binders are omitted
(they are erased, and `W101` exempts them); `_`, `_…` and `x✝` names are exempt.

### 3.2 `info`

| node | `name` | `flag` | `head`/`arity` | `data` |
|---|---|---|---|---|
| `ident` | the identifier | `local`/`global` | its type | `""` |
| `decl` | the declaration | `annotated`/`inferred` | the declared type | `""` |
| `term` | the hole's name | `hole`/`term` | the goal's target | hypothesis count |
| `tactic` | `""` | `block`/`single` | `""` | `before->after` goal counts |
| `match` | the inductive type | `catchAll`/`covered` | `arity` = columns | covered constructor count |
| `unknownIdent` | the name | `unknown` | `arity` = locals | `""` |
| `syntaxRef` | the kind/category | `kind`/`cat` | `""` | `""` |
| `expansion` | the syntax kind | `rule`/`fn` | `""` | the handler (module or function) |
| `import` | the module | `""` | `""` | `""` |
| `inst` | `""` | `instance` | the class type | the instance's head, or `opaque` |

Only these variants are exposed. `warning` and `trace` are messages (the `messages`
capability already carries the command's messages), and `fix` is quick-fix data; none is
a rule input. Synthetic nodes (a macro's output) are not in the view. A module-scope
rule gets no `info` rows: the section is the command's declarations.

Attribution: a `decl` node names its own declaration; any other node belongs to the
command's only declaration, else the first declaration whose site contains it. A command
that adds several declarations through one span (a `mutual` block) therefore attributes
everything but its `decl` nodes to its first declaration; the view does not guess further.

### 3.3 Handles

`h<n>` is opaque. A `binder-info` handle is meaningful only among that declaration's
binder rows (`(decl, handle)` identifies the occurrence); an `info` handle only among the
command's info rows. They are not interchangeable, not canonical (two equal types may
carry different handles), and not stable across runs or files. A rule can tell two rows
apart without reading either term. There is no inverse, no API to resolve a handle, and
no handle appears in a v1 row. The builder stores no term: it allocates a fresh number
at the point of projection, so the handle cannot leak the representation even by
accident.

## 4. The `Tac` request

`lib/Prelude.wiz` appends one constructor (tags 0–44 are unchanged):

```
| getBinderFacts (n : String) (k : Option (List String) → Tac)
```

`TacticM.getBinderFacts n` returns `some rows` when `n` is a declaration in the globals
and `none` otherwise. Each row is exactly a `binder-info` line (§3.1), including the
declaration name, so a tactic and a lint rule read one schema. `Wiz/Elab/Term.lean`'s
`runTac` answers it from `View.declFacts`; the selfhost's `runMacroTac` still serves only
its five cases and fails closed for this one, as for every request it does not know.

## 5. Files

| file | change |
|---|---|
| `Wiz/Elab/View.lean` | new: `BinderFact`, the binder walk (`scanTerm`/`telescope`/`declFacts`), `headArity?`, the `Info` projection (`infoNode?`), `BinderRow`/`InfoRow` and their renderers, `viewText`, `hiddenName` |
| `Wiz/Lint.lean` | `CommandView` gains `abi`, `binderFacts`, `infoNodes`; `viewOf` takes the set's ABI and builds the structured sections for a v2 `info` request; `checkSet` accepts `wiz-lint/2` and gates `info`; `RuleInput` gains the command's `infos` (synthetic filtered, span-clipped); the binder walk is imported from `View` |
| `Wiz/Lint/Basic.lean` | `supportedAbi`, `abiCapability`; the capability comments |
| `Wiz/Elab/Tactic.lean` | `TacTag.getBinderFacts := 45` |
| `Wiz/Elab/Term.lean` | imports `Wiz.Elab.View`; answers `TacTag.getBinderFacts` |
| `lib/Prelude.wiz` | the `Tac.getBinderFacts` constructor and `TacticM.getBinderFacts` |
| `lib/Lint.wiz` | `Lint.Capability.at`; the versioned capability comments |
| `docs/lint-abi.md` | the `wiz-lint/2` schema and the capability table |
| `Tests/fixtures/lint-pkg/Structured.wiz` | `W504` (type head/arity) and `W505` (the `W101` re-expression) |
| `Tests/fixtures/lint-pkg/BadInfoV1.wiz` | a v1 set asking for `info` |
| `Tests/Groups/WizLint.lean` | the v2 rule, the `W101`/`W505` comparison, the v1 refusal, the `Lint.Capability.at` probe update |
| `Tests/Groups/Tactic.lean` | `TacticM.getBinderFacts` returns the `binder-info` row |

## 6. Tests written (not run here)

* `=wiz-lint`: `Structured.wiz` loads at `wiz-lint/2`; on
  `def unusedResult (r : Result Nat) : Nat := 0` the `W504` finding is
  `binder 'r' has type head 'Result' (arity 1)` — the v1 `binder` row has no head, so
  the text view cannot express it.
* `=wiz-lint`: `W505` (a `wiz-lint/2` rule) and core `W101` report the same
  `(text, anchor)` pairs on the same source. This is the ratchet: deleting `W101`'s Lean
  body and enabling `W505` is the next slice, not this one.
* `=wiz-lint`: a `wiz-lint/1` set declaring `info` is refused with `info` and
  `wiz-lint/2` in the message.
* `=wiz-lint`: the typed probe prints `v2info` for `Lint.Capability.at "wiz-lint/2" .info`
  and still prints `info=false` for the v1 `stable`.
* `=tactics`: a tactic calls `TacticM.getBinderFacts "unusedResult"` and traces
  `binder-info	unusedResult	0	r	false	pi	default	Nat	0	h0|`.

## 7. What must be run later

1. `lake build` (or the repository's standard build), then `=wiz-lint`, `=tactics` and
   `=selfhost` (the prelude gained a `Tac` constructor; the selfhost must still refuse it
   by name, not mis-tag it).
2. The libdiff gate: `lib/Prelude.wiz` and `lib/Lint.wiz` changed, so their baseline
   rows/verdicts must be inspected (`Tests/libdiff-baseline.tsv`); this lane did not run
   it.
3. The cache/`--region-cache` gate if `Wiz/Elab/View.lean` changes the kernel-input
   digest (it should not: the view is post-elaboration).
4. `wiz lint --json` on the structured fixture, to check the new rows do not appear in
   the JSON output (they are the runner's input, not messages).

## 8. Deliberately not exposed

* The kernel `Term` and every constructor; de Bruijn indices; universe levels;
  metavariables; `Level`/`VTy`/`LocalCtx`; sort constraints.
* Goal contexts (hypotheses, their types and values), `GoalView` itself, and the
  target term beyond head/arity/handle.
* `Info.warning`, `Info.trace`, `Info.fix` (messages/quick-fix data, not rule input),
  and synthetic nodes.
* `Syntax` trees, macro templates and expansion bodies; the `SyntaxHandler` is reduced
  to `rule`/`fn` plus a name.
* The declaration body, its implementation, witness, `typeWritten` flag, levels, and
  doc text; those stay `decl`/`globals`/`docs`.
* The whole file's info tree from a declaration-scope rule; the view is the command's
  declarations, not the module's.
* A way to resolve a handle. If a consumer needs the term, it needs a new capability and
  a new ABI version.

## 9. Follow-ups this opens

* **Typed rows in `lib/Lint.wiz`.** The host schema is fixed; the wrapper now parses only
  v1 tags. `Lint.BinderInfo`/`Lint.Info` and a `Command.binderInfos`/`infoNodes` list
  would move the fixture's hand-splitting into the library.
* **Delete `W101`'s Lean body.** After `W505` is enabled by default and the goldens are
  stable, the core rule can be retired; the comparison test is the ratchet.
* **Selfhost.** The selfhost lint table and the `Tac.getBinderFacts` answer need FeEval
  before a package rule can read the view there; until then both fail closed.
* **Size/cost.** The info section is per command and can be large on dense files; a
  future `--lint-view` budget or a per-rule `info` filter (only `ident`, say) is a
  schema addition, not a rewrite.
