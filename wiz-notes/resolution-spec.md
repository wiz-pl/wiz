# Selfhost resolution and declaration order — normative spec (2026-11-23)

Status: live. The visibility/order model the self-hosted frontend implements (and the
host reference it is measured against), plus the conformance plan that pins it. No
product change in this lane.

- Lane: `research-resolution-spec`. Branch: `agent/research-resolution-spec`.
- Base: local `integration/train12` `f489cc876`; worktree `/workspace/wt/research-resolution-spec`.
- F48 reference: `/workspace/wt/f48-resolution` `8cdf33a24` (`selfhost: plain inductives
  carry Desc.hrec`), stacked on `226487b9b` (`selfhost: resolve the deriver's declarations
  in its own module`, the prelude slice).
- Evidence class: **static only**. No build, no test, no `integration/*` push. Expected
  outputs below are derived from the code and from cases already pinned in
  `Tests/Groups/SelfHost.lean`; the ones marked *capture* need their exact text recorded
  on the first run.
- Line numbers are the train12 base unless marked `[F48]` (the F48 tree is based on an
  earlier integration, so its numbers differ; symbols are stable).

Companions: `codebase-audit-2026-11-22.md` F48; `docs/stages/21-bootstrap.md` §21n
(privacy/resolution) and §21an; `docs/stages/13-language.md` 13b/13t/13v;
`selfhost-parity.md` A14; `import-shadowing.md` (the duplicate rule).

**Tree status.** Neither `226487b9b` nor `8cdf33a24` is an ancestor of
`f489cc876`. This note describes the target state (train12 + the F48 branch); the cases
that need the slice/hrec are marked with that prerequisite. Everything else is the
train12 behavior and is pinned by existing tests.

---

## 0. The result in one page

F48 was not a resolution bug. The self-hosted frontend reports `unknown identifier X`
for every declaration that names a name which is **not in the environment**. A
declaration enters the environment only when its whole command succeeds. F48's chain was
a cascade of *absent* declarations:

1. Before `226487b9b`, the embedded prelude did not declare the reflection slice
   (`BinderKind`, `ParamView`, `FieldView`, `CtorView`, `IndView`, `Tac`, `TacticM`,
   `MacroM`, `Deriver`). The first use, `binderKindV` in `Frontend.wiz`, failed with
   `unknown identifier BinderKind`; every later use failed in turn.
2. After the slice was added, `Tac` failed the plain-`inductive` positivity check, because
   its field `getInductive (n : String) (k : Option IndView → Tac)` is a *higher-order*
   recursive field and `ctorDesc` only recognised a direct `T ps`. `Tac` was therefore
   **not added**; `TacticM` (which names `Tac`), `MacroM` (names `TacticM`), `Deriver`
   (names `MacroM`), then `deriveInhabitedV`, `runMacroTac`, `runDeriver`,
   `deriveInhabitedR`, `deriveClassOn`, `deriveEach`, `deriveForTypes`, `withDeriving`,
   `commandStep` each failed at their own first use, in declaration order — the exact
   "every name is declared in the same file" illusion the audit recorded.
3. `8cdf33a24` teaches `ctorDesc` the `Desc.hrec` shape (`hrecField`), `Tac` checks, and
   the whole chain resolves.

The normative rules this exposes are simple, and the rest of this note elaborates them:

- **R-ENV.** Resolution is against one flat *environment* of successful declarations
  across all loaded modules plus the current module's earlier commands. "Same file" is
  irrelevant. Modules affect only privacy and the per-module namespace/`open` state.
- **R-FAIL.** A failed command adds nothing. There is no "declared but failed" entry, no
  placeholder, and no retry. The first diagnostic is the root cause only when the
  dependency graph is a chain.
- **R-ORDER.** Commands run strictly in source order; imports are a fixed header and are
  loaded before the importing module. There are no forward references. `mutual` is the
  one forward-looking construct, and even there signatures are sequential while *bodies*
  see all signatures.
- **R-SELF.** A command's own declared name is not visible while elaborating that
  command unless it was pre-declared (`partial`/`mutual` signature, mutual-inductive
  family/member, a structure's type before its projections).
- **R-NAME.** Locals shadow globals; a private declaration of the current module beats a
  public one of the same spelling; the enclosing namespace, the bare name, and each
  `open` are a *candidate set* whose distinct members are an ambiguity error, not a
  precedence chain; `__root__.x` is the absolute escape.
- **R-PRIV.** Privacy is a module-scoped kernel name (`_private.M._0.x`), not a scope.
  Public names are visible transitively through imports; private names and `open`s are
  not.

---

## 1. Vocabulary and the model

**Command.** One top-level form the parser produces (`def`, `inductive`, `structure`,
`class`, `instance`, `axiom`, `extern`, `private …`, `partial …`, `mutual … end`,
`namespace`, `open`, `end`, `import`, `deriving …`, `#check`, `#reduce`, a notation or
macro registration, …). The unit of elaboration, of output, and of failure.

**Module.** A source text with a name (`Prelude`, `A`, `A.B`, `Main`/`input`). The loader
elaborates each module once, dependencies first. A module has its own namespace prefix,
`open` list and aliases; it does **not** have its own name table.

**Environment `E`.** The ordered sequence of declarations added by successful commands
of every module already loaded plus the current module's previous commands. Entries are
`Global`s keyed by kernel name. Resolution never queries anything else.

**Point.** The state immediately before a command, or inside one of its sub-elaborations.
The whole spec is "what `E` and the module state look like at each point".

Two consequences worth stating because they cause most confusion:

1. A module boundary is not a visibility boundary for public names. If `Main` imports
   `A` which imports `B`, `B`'s public names are in `E` and `Main` may use them
   unqualified. Only `open`s and private names are stopped by a boundary.
2. A file boundary is not a visibility boundary either. In the self-check, the frontend
   files are concatenated into one module (`Main`/`input`); the prelude slice is a
   different module (`Prelude`). Both resolve through the same `E`. "Declared in the same
   file" is not a rule and never was.

---

## 2. The visibility model

### 2.1 The resolver, exactly

The selfhost resolver is `Scope.lookupV` → `lookupExact` → `resolveNameV` →
`resolvePlain` → `resolvePlainRel` (`selfhost/Frontend.wiz:155,169,1026,1018,993`), plus
`nsCandidates` (`:973`) and `expandAliases` (`:966`). `identHead` (`:5202`) calls
`resolveNameV` for a term identifier; `patOf`/constructor paths use the same functions.

For a written name `n`, in order:

1. **Local binder.** `Scope.localNames` is searched innermost-first; a hit is the de
   Bruijn index. A local always wins, including over a global of the same spelling and
   including over a macro-scoped spelling (`n` exactly).
2. **Macro scope.** If `n` contains `✝`, `lookupExact sc n` is tried first (this is how
   the frontend's own generated helper `f✝s` resolves; `selfhost-parity.md` records the
   bug when it was stripped first). If that misses, the scope-free `stripScope n` is
   resolved by the rules below.
3. **`__root__.` escape.** If `n` starts with `__root__.`, drop the nine characters and
   `lookupExact` the rest. No alias expansion, no namespace fallback, no `open`. This is
   the only absolute form.
4. **Qualified name** (contains a dot, after the escape): apply the longest `open … as`
   alias (`A.x` → `M.x`); `lookupExact` exactly; inside a namespace, if that misses, try
   `ns.x` once (so `B.x` in `namespace A` may be `A.B.x`); otherwise `missing`.
5. **Unqualified name:** build the candidate list
   `[ns.x] (if a namespace is open) ++ [x] ++ [open M.x for each open M]`,
   resolve each with `lookupExact`, deduplicate by declaration index, and:
   - one candidate → it;
   - two or more distinct → `ambiguous` (sorted source names in the message);
   - none → `lookupExact sc x` once more for the private-of-another-module diagnostic,
     else `missing`.

`lookupExact` itself is the private preference: for a written `x` it first tries
`_private.<current module>._0.x`, then the public `x`; a public kernel name that is
itself `_private.M._0.…` is returned as `privTo M` when `M` is not the current module;
finally `privOwner` reports a private *source* name of another module. That is why a
current module's private `x` wins over an imported public `x`, and why an importer gets
`'x' is private to module M` for the bare name in selfhost (the host says `unknown
identifier` there; see §3.11).

The candidate list is a **set**, not a search order. `[ns.x] ++ [x] ++ opens` is the
order candidates are *collected* (and the order names are tried inside the namespace
fallback), but distinct candidates are an ambiguity error. Locals and the current
module's private declaration are the only true precedences.

### 2.2 What a declaration sees at each point

`E` means the environment of §1; "own" is the command's declared name(s).

| Point | Sees | Own name? | Siblings? | Notes |
|---|---|---|---|---|
| `def` type | `E` | no | no | `def f : f = f` reports unknown `f` at the type (host: unknown; selfhost: unknown) |
| `def` body | `E` | no | no | selfhost: `unknown identifier f`; host: `recursive call to f …` (code `recursive-without-equations`); neither can see `f` |
| `def … \| p => …` (equations) | `E` + recursion hypotheses | no, but recursive calls are rewritten | no | the equation compiler, not the resolver, makes recursion work |
| `partial def` signature | `E` | no | n/a | |
| `partial def` body | `E` + **all** group signatures | yes | yes (same group) | signatures are added as axioms with witnesses first |
| `mutual def` member signature | `E` + earlier member signatures | only if declared earlier | earlier only | signatures are **sequential**, not simultaneous |
| `mutual def` member body | `E` + all signatures + earlier bodies | yes | yes | all signatures are present |
| plain `inductive` parameters/signature | `E` | no | n/a | |
| plain `inductive` constructor fields | `E` + parameters + earlier fields | **not as a name**; only the two description shapes are recognised | no | `T ps i` (direct) and `(h : H) → T ps i` (higher-order, F48); anything else that mentions `T` is the positivity error |
| `mutual inductive` member fields | `E` + family + all member aliases + parameters + earlier fields | yes (the family) | yes (member aliases) | family and members are added before any constructor field is checked |
| `structure` fields | as plain `inductive` (synthetic constructor) | not as a name | no | a field's type may not depend on an earlier field (both reject at the projection/observation); a projection may not depend on an earlier projection |
| `structure` projections | `E` + the type | yes (`S`) | n/a | generated as ordinary `def`s after the type |
| `instance` | `E` | no | no | |
| `deriving` generated commands | `E` + the type and its constructors | type yes; helpers yes | n/a | a failed derivation leaves the type declared and reports the derivation error |
| command macro / deriver output | `E` at the expansion point | n/a | n/a | host prefixes generated command names with the current namespace; selfhost's deriver path does not (§3.15) |
| `#check` / `#reduce` / `#eval` | `E` | n/a | n/a | no additions |
| `import` | loader state, not `E` | n/a | n/a | header only; imports after a declaration are an error |

Two rows deserve to be repeated as rules:

- **A plain `def` cannot see itself.** `TCtx.fix` is set for the linear-fixpoint rule
  (`selfhost/Frontend.wiz:7521`), not for name resolution; `Scope` does not contain the
  name. Recursion is available only through the equation compiler (`defEqns`/`match` on
  parameters) or `partial`.
- **A plain `inductive`'s `T` is not a name in its constructor fields.** The host binds
  `T` as a local while elaborating fields (`Wiz/Elab/Inductive.lean:339`) and then the
  description builder rejects non-recursive occurrences. The selfhost does not bind it;
  `ctorDesc` recognises exactly the direct and higher-order recursive shapes and rejects
  any other mention with `positivityError` (`selfhost/Frontend.wiz:1399,1499,1475`). The
  *accepted language is the same* because the host's description builder is also
  syntactic; the difference is implementation and the error path. F48 was exactly a
  shape the selfhost did not recognise but the host did.

### 2.3 Namespaces, `open`, aliases, `__root__`

`namespace N` pushes a prefix; a declaration `def x` inside is elaborated as `N.x` (the
syntax is rewritten once at the command boundary, `prefixDeclName`,
`selfhost/Frontend.wiz:7934`). `namespace` is only a prefix, never a privacy boundary.
Nested namespaces concatenate (`A.B.x`). `end`/`end N` pops; a mismatch is an error at
the `end` but still pops (so the file is not also reported unclosed); an unclosed block
is reported at its `namespace`.

`open N` requires that some visible declaration `N.…` already exists in `E`
(`Globals.hasDeclUnder`, `:896`); it appends `N` to the module's open list. `open N as A`
does **not** open `N`; it records an alias, and `A.x` is a spelling of `N.x` (longest
alias wins). Opens and aliases are block-scoped: `end` restores the enclosing block's
lists. Each module starts with an empty prefix/open list (`Globals.atModuleStart`,
`:758`; `modRunBody`, `:12273`), so an importer never inherits them.

`__root__` is Lean's `_root_`: `namespace __root__` opens the empty prefix;
`namespace __root__.X` opens the root-level `X`; `open __root__.X` strips; a written
`__root__.x` is the root `x`. It is *not* a namespace named `__root__`, and declarations
inside `namespace __root__` are root-level.

**Declarations and `__root__`.** The host also strips `__root__.` from a *declaration*
name (`def __root__.x` declares `x`) and rejects a bare `__root__` or `__root__` in a
non-leading segment (`Wiz/Elab/Command.lean:2025,2055,2135`). The selfhost
`prefixDeclName` has no such case, so `namespace A; def __root__.r` declares
`A.__root__.r` (wrong), and `def __root__` at the root declares a literal `__root__`.
This is an observed gap, not a semantic choice; see Q2.

### 2.4 Privacy

A `private` command sets the "private" flag for the whole command
(`stepCommand` → `Globals.setPrivate`, `:11831`; cleared after the command). Every name
the command declares gets the kernel name `_private.<module>._0.<source>` (`privName`,
`:80`; `Globals.declName`, `:773`; `Globals.add`, `:777`). Consequences:

- Two modules' private `x`s are different constants and never clash.
- The declaring module resolves `x` to its private kernel name first; a public `x` of an
  imported module is shadowed.
- An importer's `x` does not resolve to the private one. For a **root-level** private
  declaration, selfhost reports `'x' is private to module M` for the bare spelling while
  the host says `unknown identifier`; for a qualified spelling both report the private
  error. For a private declaration **under a namespace** (`Secret.hidden`), the bare
  short name is unknown in both and the qualified spelling gives the private error in
  both (§3.11).
- A private name is never re-exported through a module that imports it; the imported
  *term* works (its constants are closed), the *name* does not.
- A source name is declared at most once per module, private or not
  (`Scope.declaredIn`, `:117`; duplicate check `dupFrom`/`newDuplicate`, `:1155,1172`).
  A public declaration of a different module still clashes by kernel name.
- The root file has no importers, so its privacy is only observable through the
  duplicate rules (host makes the root module `""`, selfhost `Main`/`input`).

### 2.5 Duplicates, shadowing, ambiguity

- **Kernel names are unique.** The duplicate check runs after every command and compares
  the *new* globals with `E` and among themselves (`newDuplicate`). The only allowance is
  a partial/mutual signature (an axiom) followed once by its body (a definition) *within
  the same command*; a top-level `axiom f` followed by `def f` is still a duplicate.
- **A failed declaration's name is free.** Nothing was added, so a later declaration of
  the same name succeeds. This is the complement of R-FAIL.
- **Locals shadow globals**, innermost-first.
- **The current module's private name shadows a public name of the same spelling.**
- **The enclosing namespace does not shadow an open.** `ns.x`, bare `x`, and `M.x` are
  all candidates; two distinct ones are an ambiguity error naming both. (Whether the
  enclosing namespace *should* win is Q8; the current behavior in both frontends is
  ambiguous.)
- **Aliases shadow a real namespace of the same prefix** for qualified names (the alias
  is applied first); an alias does not open anything unqualified.
- **`open M` twice** is one candidate, not an ambiguity (dedup by index).

### 2.6 Wrappers and commands

| Command | Visibility effect |
|---|---|
| `private C` | Sets the private mode for `C`; all names `C` declares are mangled; the mode ends with the command. `private inside mutual` is rejected by both (only whole-block `private mutual` is accepted). |
| `local C` | Grammar/registration only. Host restricts which commands may be `local` and drops the module's `local` tables at `endModule`. Selfhost `unwrapLocal` simply drops the wrapper, so the grammar leaks to importers (Q5). |
| `sealed inductive T` | Adds `T.seal✝ : Type` and uses it as the phantom parameter of `T`. Host always marks the seal private to the declaring module; selfhost's seal is public unless the command is `private sealed` (Q6). |
| `partial def f` | Adds the signature `f : T` (with a witness) first, then the body; the body sees `f`. A failed body currently leaves the signature behind (Q1). |
| `mutual` (defs) | Adds all member signatures in source order (each sees earlier ones), then all bodies in source order (each sees all signatures and earlier bodies). A failed signature aborts the whole block; a failed body currently does not (Q1). |
| `mutual` (inductives) | One family `A_B` (namespace-aware), then member aliases `A := A_B …`, then constructors; every member's fields see the family and all member aliases. Selfhost supports parameters here, host currently rejects them (Q10). |
| `deriving` | Runs after the declaration. The generated `def` helper and anonymous instance are ordinary declarations added immediately; later commands see them. Host prefixes generated command names with the current namespace; selfhost's `elabDerivedGo` does not (§3.15). On a derivation error, selfhost's `withDeriving` replaces the type's output line with the error (the type is still declared); the host reports the declaration and the error separately. |
| command macro / tactic output | Elaborated at the expansion point; a generated declaration is visible from the next command on, not to the command that generated it. |

### 2.7 Failure semantics (the F48 rule)

A command's step returns either a line and a new `Globals`, or an error line and the
**old** `Globals` (`errStep gs`, `:1176`). `stepCommand` then continues with the next
command. Therefore:

- A failed command contributes zero declarations.
- Every later command that mentions a name that only the failed command would have
  declared reports its **own** `unknown identifier` at its own first use.
- The cascade's order is the declaration order of the users, not a topological order of
  the failure. With several independent roots, the first line is just the earliest
  command, not necessarily "the" cause.
- A later declaration of the same name is legal and succeeds.
- A failed declaration inside an imported module does not stop the loader: the module is
  still loaded, the failing command's line is nested under the import, and the importer
  sees only the successful names. This is how a Prelude failure cascades into `Main`.

The one observed exception is the partial/mutual body: `addPartials` commits the
signatures before `defsSteps` checks the bodies, so a failed body leaves the signature
(and earlier bodies) in `E`. The host commits the whole block atomically. This is Q1 and
is soundness-relevant: the leftover signature is an axiom with a witness, usable by later
code.

### 2.8 Modules, imports and the generated prelude

The loader is `modLoadOne`/`modRunBody` (`selfhost/Frontend.wiz:12311,12273`):

- Imports are a fixed header: only before the first non-import command. A later import is
  an error (`import-order`); an import inside `mutual`/`partial` is an error.
- Each module is elaborated once, depth-first in source order, dependencies before the
  importer; a cycle and a missing module are diagnosed at the import. The root is last.
- Every module runs with `Globals.setModule` (privacy), `atModuleStart` (namespace/opens),
  and its own output/error block (`tagFirst`, nesting). The *name table* is shared.
- Public names are visible transitively (importing B gives A's public names if B imports
  A); `open`s and private names are not transitive.
- The embedded prelude is `preludeText` (`:10151`), a single-line string. The table seeds
  `ModSrc "Prelude" "prelude" preludeText []` (`moduleRootSourcesAs`, `:12484`);
  `modCanonical` maps `IO`, `Std`, `Sys` to `Prelude` (`:12026`), so one prelude is
  loaded. The loader path loads it only if imported.
- The `--oneshot`/`checkFile` path is different: every `import` runs `preludeText`
  inline (`stepCommand`, `:11803`; `checkFileOpts`, `:11933`). It does not resolve the
  imported module, and two imports run the prelude twice (duplicate errors). This is
  documented for one import; multiple imports are Q7.

### 2.9 The F48 worked example, identifier by identifier

The prelude slice (`[F48] selfhost/Frontend.wiz`, `preludeText`, commit `226487b9b`;
formatted here, the embedded copy is a single-line string):

```
inductive BinderKind where | default | implicit | instImplicit
inductive ParamView where | mk (name : String) (kind : BinderKind) (type : Syntax)
inductive FieldView where | mk (name : String) (kind : BinderKind) (type : Syntax)
                                  (recursive : Bool) (proof : Bool)
inductive CtorView where | mk (name : String) (fields : List FieldView) (indices : List Syntax)
inductive IndView where | mk (name : String) (levelParams : List String) (params : List ParamView)
                               (indices : List ParamView) (ctors : List CtorView) (isStructure : Bool)
inductive Tac where
  | done
  | result (stx : Syntax)
  | fail (msg : String)
  | trace (msg : String) (next : Tac)
  | getInductive (n : String) (k : Option IndView → Tac)
def TacticM (A : Type) : Type := (A → Tac) → Tac
def MacroM (A : Type) : Type := TacticM A
def Deriver : Type := String → MacroM (List Syntax)
```

The dependency chain and its outcome, in declaration order:

| Declared | Names | Before `226487b9b` | After the slice, before `8cdf33a24` | After `8cdf33a24` |
|---|---|---|---|---|
| `BinderKind` | — | absent (unknown at first use) | ok | ok |
| `ParamView` | `BinderKind` | absent | ok | ok |
| `FieldView` | `BinderKind` | absent | ok | ok |
| `CtorView` | `FieldView` | absent | ok | ok |
| `IndView` | `ParamView`, `CtorView` | absent | ok | ok |
| `Tac` | `IndView`, itself (hrec) | absent | **positivity error** | ok |
| `TacticM` | `Tac` | absent | unknown `Tac` | ok |
| `MacroM` | `TacticM` | absent | unknown `TacticM` | ok |
| `Deriver` | `MacroM` | absent | unknown `MacroM` | ok |
| `deriveInhabitedV` (Main) | `Deriver` | unknown `Deriver` (the file's first error is `BinderKind` at `binderKindV`) | unknown `Deriver` | ok |
| `runMacroTac` (Main) | `Tac` | … | unknown `Tac` | ok |
| `runDeriver` (Main) | `Deriver`, `runMacroTac` | … | unknown `Deriver` | ok |
| `deriveInhabitedR` | `runDeriver` | … | unknown `runDeriver` | ok |
| `deriveClassOn` | `runDeriver`/`Globals` | … | unknown `runDeriver` | ok |
| `deriveEach` | `deriveClassOn` | … | unknown `deriveClassOn` | ok |
| `deriveForTypes` | `deriveEach` | … | unknown `deriveEach` | ok |
| `withDeriving` | `deriveEach` | … | unknown `deriveEach` | ok |
| `commandStep` | `withDeriving` | … | unknown `withDeriving` | ok |

The audit's `unknown identifier BinderKind` is the first line of the pre-slice run. The
post-slice run moved the first *failing declaration* to `Tac` (the positivity error) and
the first `unknown identifier` to `TacticM`. The final run has none. The audit's
hypotheses — declaration order, `namespace __root__`, a missed `Scope` entry, a wrapper
command — were each eliminated: `Tac` supplied through a `mutual` block (stage 19e's
`hrecMember` path) made the same input check with zero errors, proving the only missing
entry was `Tac` itself.

---

## 3. Host vs selfhost

The host is the reference implementation; the selfhost is normative for its own frontend.
"Same" means the observable rule agrees; wording may differ.

| # | Rule | Host | Selfhost | Verdict |
|---|---|---|---|---|
| 3.1 | Order; no forward references | source order, one command at a time (`Wiz/Frontend/Frontend.lean:252,355`) | `runCommands`/`stepCommand` (`:11858,11784`) | same |
| 3.2 | Failed declaration absent | `elabCommand` state unchanged on error | `errStep gs` | same |
| 3.3 | Plain `def` self-reference | rejected; body gets a specific `recursive-without-equations` error (`Wiz/Elab/Term.lean:3865`) | rejected as `unknown identifier`; no `defining` guard | same semantics, wording differs |
| 3.4 | Equations / lambda-wrapped `match` | converts `def f := fun ys => match …` to equations (`defMatchAsEqns?`, `Wiz/Elab/Command.lean:999`); F44 accepted | converts only a direct `:= match` on parameters (`selfhost/Frontend.wiz:8645`); F44 rejected | **diverges** (F44; selfhost gap) |
| 3.5 | `partial`/`mutual` signatures | all sigs added to a local `g`, then bodies; committed only if every sig and body succeeds (`Command.lean:2595-2682`) | `addPartials` commits all sigs, then `defsSteps` checks bodies and keeps going; a failed body leaves sigs/earlier bodies | **diverges** (Q1, selfhost bug) |
| 3.6 | `mutual` inductives | one family + tag + alias defs, expanded into commands (`mutualInductive`, `:1730`); no params/indices | one family in one `Step` (`mutualInductiveCmd0`, `:7740`); params supported, no indices | family model same; **selfhost extension** (Q10) |
| 3.7 | Plain inductive self name | binds `T` in the field context (`Inductive.lean:339`); description builder accepts only direct/higher-order recursive shapes | `T` not bound; `recField`/`hrecField` recognise the same shapes syntactically | accepted language same after F48; implementation differs |
| 3.8 | Namespaces | prefix; block-scoped opens/aliases; per-module reset (`Command.lean:2114,2326`) | same (`nsTarget`/`nsCommand`, `:11583,11596`; `atModuleStart`) | same |
| 3.9 | `__root__` use | absolute; errors on bare/misplaced (`Term.lean:872`) | absolute (`resolvePlain`, `:1018`); no bare/misplaced error | use same; **errors missing** (Q2) |
| 3.10 | `__root__` declaration | strips to the root name (`prefixDeclName`, `:2055`) | `prefixDeclName` prefixes it (`:7934`) | **diverges** (Q2, selfhost bug) |
| 3.11 | Private resolution/diagnostics | current module's private wins; a bare **root-level** private name of another module → `unknown identifier`; a qualified/aliased spelling → private error | current module's private wins; a bare root-level private name → private error (`privOwner`); qualified → private error | same rule; **diagnostic differs for a bare root-level name** |
| 3.12 | Private kernel timing | types pre-renamed; defs/axioms/mutual post-renamed in a module (`renamePrivate`, `:445`); root `module == ""` not renamed | every declaration mangled at `Globals.add` | **diverges** (Q3; host module duplicate hole) |
| 3.13 | Duplicate a source name per module | root: yes; library module: private+public allowed, two private defs can replace | yes, always | **diverges** in library modules (Q3) |
| 3.14 | `open` a private-only namespace in its module | allowed (`declares` checks `_private.<module>._0.N.`) | rejected: `hasDeclUnder` only sees public prefixes (`:896`) | **diverges** (Q4, selfhost bug) |
| 3.15 | Generated command names | `elabExpansion` prefixes with the namespace (`:2258`) | `elabDerivedGo` calls `instanceCmd`/`defStep` directly (`:11469`); no prefix | **diverges** (Q9) |
| 3.16 | `local` scope | restricts the command set; drops module-local tables at `endModule` (`:1901,2454`) | `unwrapLocal` drops the wrapper; any command accepted; grammar leaks | **diverges** (Q5) |
| 3.17 | `sealed` seal visibility | always private to the declaring module (`:2448`) | public unless `private sealed` (`sealedCmd`, `:8625`) | **diverges** (Q6, selfhost soundness question) |
| 3.18 | `deriving instance … for T` name resolution | `resolveName` for T and C (`:3903`) | raw names into `Globals.ind`/`Globals.class` (`derivingCmd`, `:11551`) | **diverges** in a namespace (Q9) |
| 3.19 | Command macros/tactics adding declarations | full `TacticM.define` sides and command macros | interpreter over a fixed `STacOp`; only instance/defEqns from derivers | selfhost subset (feature) |
| 3.20 | Modules/prelude | `lib/Prelude.wiz`, loaded once per graph; cache effects replayed | embedded `preludeText`, canonicalised `IO`/`Std`/`Sys`; no replay | same model; different source (Q7) |
| 3.21 | `modulePrefix` default namespace | stage 3, off by default; `legacy` allowlist (`:2114`) | none | host-only, latent (Q10) |
| 3.22 | Macro scopes | local first; otherwise always `stripScope` for globals | local first; exact scoped global first, then stripped | selfhost has one extra rule for its generated helpers |

### 3.1 Where the divergence actually matters for F48

None of 3.1–3.22 caused F48. The chain was entirely 3.2/R-FAIL plus 3.7's missing
higher-order shape. That is why the fix is in `ctorDesc`, not in `Scope` or
`prefixDeclName`, and why a `mutual` block worked around it. Keep this distinction when
debugging the next "unknown identifier" cascade: first ask **which declaration failed**
and why, not how names are resolved.

---

## 4. Conformance test plan

All cases are static to design and can be written now; they need the test binaries to
run. Selfhost cases go in `Tests/Groups/SelfHost.lean` (`selfHostGroup`), using the
existing helpers:

- `selfhostCheckFile file expected` — the checker on one file (embedded prelude);
- `selfhostCheckModules files expected` — the loader on a module graph;
- `selfhostAgrees header decls` — each declaration accepted/rejected by both frontends;
- `selfhostVerdicts header decls` — pinned differences (`leanOk`, `selfOk`);
- `selfhostCheckFails` / `selfhostModuleCompileFails` — compiler-level errors.

Host-side namespace cases go in `Tests/Groups/Namespace.lean`; host declarations in
`Tests/Groups/Elab.lean`.

**Prerequisite for C7/C8/C16:** the F48 branch (`8cdf33a24` + the prelude slice) or its
merge. On `f489cc876` those cases fail for the known F48 reason; add them with the
merge or mark them skipped with a comment naming F48. The other cases run on train12.

### C1 — no forward references (new)

```wiz
import Prelude
def a : Nat := b
def b : Nat := 1
```

Expected (selfhost):

```
error: unknown identifier b
b : Nat
```

Pins: `a` fails at its use; `b` is still declared; the error is at the *use*, not at
`b`. Host analogue: `def a : Nat := b` then `def b` → `unknown identifier 'b'`, `b`
declared. Existing coverage: none for a plain forward reference (the `bad2` case covers
a failed declaration, not a later one).

### C2 — a failed declaration is absent and its name is reusable (new)

```wiz
import Prelude
def a : Nat := missing
def a : Nat := 1
#check a
```

Expected:

```
error: unknown identifier missing
a : Nat
Nat
```

Pins: R-FAIL and the complement ("a failed name is free"). Host: same verdicts; its
message is `unknown identifier 'missing'`. Existing coverage: the `bad`/`#check bad`
case at `Tests/Groups/SelfHost.lean:2610` pins absence; the *redeclaration* half is new.

### C3 — plain self-reference vs equations (new)

```wiz
import Prelude
def f (n : Nat) : Nat := f n
def g : Nat → Nat
  | .zero => .zero
  | .succ n => g n
#check g
```

Expected:

```
error: unknown identifier f
g : (x0 : Nat) → Nat
(x0 : Nat) → Nat
```

Pins: R-SELF; the equation form is accepted and `g` is declared. Host: `f` gets
`recursive call to f …` (a better diagnostic), `g` accepted. Use `selfhostVerdicts` if
only the verdict matters; use `selfhostCheckFile` to pin the selfhost text.

### C4 — mutual signatures are sequential, bodies see all (new)

```wiz
import Prelude
mutual
def f : Nat := g
def g : Nat := 1
end
mutual
def h : Nat := 2
def k : Ty := 3
def Ty : Type := Nat
end
#check f
#check h
```

Expected:

```
f : Nat
g : Nat
error: unknown identifier Ty
Nat
error: unknown identifier h
```

Pins: `f`'s body sees `g` (all signatures); the second block's *signature* `k : Ty`
does not see the later `Ty`, so the whole block is rejected and nothing from it is
declared — not even `h`, whose body would have been fine. Host behaves the same (its
signature loop returns before the commit). Existing coverage: `Tests/Groups/SelfHost.lean:2667`
pins the positive mutual case, not the sequential-signature failure.

### C5 — a failed mutual body: atomicity (expected-red; Q1)

```wiz
import Prelude
mutual
def f : Nat := 1
def g : Nat := Type
end
#check f
#check g
```

Current selfhost (observed rule: signatures committed before bodies):

```
f : Nat
error: type mismatch: expected Nat, got U1
Nat
Nat
```

Host: the block is rejected atomically, so its output is the one `type mismatch` error
followed by `unknown identifier` for both `f` and `g`. Normative proposal: the host
behavior. Add the case with that desired output and mark it `expected-red` until Q1 is
fixed; alternatively use `selfhostVerdicts` once the semantics are decided.

### C6 — a mutual block does not see a later top-level sibling (new)

```wiz
import Prelude
mutual
inductive A where
  | mk (b : B)
end
inductive B where
  | mk
```

Expected:

```
error: unknown identifier B
B : U0
```

Pins: the block's member set is closed at `end`; a later top-level `B` cannot satisfy a
field reference. (In a `mutual`, `B` would be a member and the field would be
recognised as a member field.) Host: same verdict (`unknown identifier 'B'`), then `B`
declared.

### C7 — F48 regression: higher-order recursive field in a plain inductive

Prerequisite: the F48 branch.

```wiz
import Prelude
inductive MyTac where
  | done
  | more (k : Option IndView → MyTac)
```

Expected (F48 tree):

```
MyTac : U0
```

Before `8cdf33a24`:

```
error: the type being defined may only occur as the type of a recursive field or the result
```

Also pin the mutual workaround (both frontends accept):

```wiz
mutual
inductive MyTac where
  | more (k : Option MyView → MyTac)
inductive MyView where
  | mk
end
```

Use `selfhostAgrees ""` for the mutual form (no parameters) and `selfhostCheckFile` for
the direct form. This is the *minimal* F48 regression, independent of the 12k-line
frontend.

### C8 — the prelude slice resolves (prerequisite: `226487b9b`)

```wiz
import Prelude
def k : BinderKind := BinderKind.default
def t : Tac := Tac.done
def d : Deriver := fun T k => MacroM.throw "x" k
#check k
#check t
#check d
```

Expected:

```
k : BinderKind
t : Tac
d : Deriver
BinderKind
Tac
Deriver
```

This pins three of the nine slice type names (`BinderKind`, `Tac`, `Deriver`) and their
use, without compiling the frontend; the projections and the other six are exercised by
the self-check. The same source on the pre-slice tree fails at `BinderKind` (the first
line the audit saw).

### C9 — namespace root: use vs declaration (declaration half expected-red; Q2)

Use form (should pass now; only `__root__` block cases exist):

```wiz
import Prelude
namespace A
def x : Nat := 1
end A
def y : Nat := __root__.A.x
#check y
```

Declaration form (desired; currently wrong):

```wiz
import Prelude
namespace A
def __root__.r : Nat := 1
end A
#check r
#check __root__.r
```

Desired:

```
r : Nat
Nat
Nat
```

Current selfhost declares `A.__root__.r` and both `#check`s are unknown. Also pin the
error cases: `def __root__`, and `def A.__root__.x` inside `namespace A` (host:
`root-name` errors; selfhost currently declares them).

### C10 — shadowing and ambiguity (new host+selfhost case)

```wiz
import Prelude
def x : Nat := 1
def f (x : Nat) : Nat := x
#reduce Nat.beq (f 5) 5
def g : Nat := x
#check g
namespace A
def y : Nat := 10
end A
namespace B
open A
def y : Nat := 20
def z : Nat := y
end B
```

Expected:

```
x : Nat
f : (x0 : Nat) → Nat
con((#1, (tt, tt)))
g : Nat
Nat
A.y : Nat
error: 'y' is ambiguous: it refers to 'A.y', 'B.y'; qualify it with a namespace
```

Pins: local shadowing; the enclosing namespace `B.y` does *not* shadow the opened
`A.y` — they are ambiguous (Q8). Use `selfhostAgrees` for the local-shadowing half; the
ambiguity is already partly covered by `Tests/Groups/SelfHost.lean:3863` (two opens), not
by namespace-vs-open.

### C11 — privacy: same module, importer, bare vs qualified (new module case)

The root-level case is already pinned by `Tests/Groups/SelfHost.lean:3451`:
`A.wiz` declares `private def secret`, an importer that uses `secret` gets
`'secret' is private to module A`. The host reports `unknown identifier 'secret'` for the
same bare spelling, so cross-frontend tests must not share one expected string here.

The namespaced case is parity and is worth pinning explicitly:

```wiz
A.wiz:   import Prelude
         namespace Secret
         private def hidden : Nat := 1
         def shown : Nat := 2
         end Secret
input:   import Prelude
         import A
         open Secret
         def bad1 : Nat := hidden          -- short name: unknown in both
         def bad2 : Nat := Secret.hidden   -- qualified: private in both
         def ok : Nat := Secret.shown
```

Selfhost: `bad1` → `unknown identifier hidden`; `bad2` → `'Secret.hidden' is private to
module A`; `ok : Nat`. Host: the same three verdicts, with its own wording. This pins
that the private diagnostic names the module only when the written spelling identifies
the mangled name (or the source name is root-level and `privOwner` matches it).

### C12 — `open` a namespace with only this module's private names (expected-red; Q4)

```wiz
import Prelude
namespace P
private def x : Nat := 1
end P
open P
def z : Nat := x
```

Desired:

```
P.x : Nat
z : Nat
```

Current selfhost:

```
P.x : Nat
error: unknown namespace 'P': there is no declaration `P.…`
error: unknown identifier x
```

Host: allows the open and resolves `x` (private to the module). This is a small,
high-value fix in `hasDeclUnder`.

### C13 — command-body visibility (new)

```wiz
import Prelude
def x : Nat := 1
def f (x : Nat) : Nat := x
#check f
partial def p (n : Nat) : Nat := p n
#check p
private def q : Nat := 2
def r : Nat := q
#check r
```

Expected:

```
x : Nat
f : (x0 : Nat) → Nat
(x0 : Nat) → Nat
p : (x0 : Nat) → Nat
(x0 : Nat) → Nat
q : Nat
r : Nat
Nat
```

Pins: a local binder shadows the global in a def body; a `partial` body sees its own
signature; a later command sees a private declaration of the same module. (The failing
`def f := f`/`partial` contrast is C3; this is the positive half.)

### C14 — `local` grammar stays in its module (expected-red; Q5)

```wiz
A.wiz:   import Prelude
         local infixl:65 " +++ " => Nat.add
         def a : Nat := 1 +++ 2
input:   import Prelude
         import A
         def b : Nat := 1 +++ 2
```

Desired: A's `a : Nat`; input's `b` is a **parse error** (`+++` is not a token there).
Current selfhost: input accepts `+++` (the tables are shared; no module-local
restoration on train12). Host: rejects input. The `agent/sh-a14` branch already has
`modExportAt`/`modReplay`; the test should be added with that fix.

### C15 — one-shot with two imports (expected-red; Q7)

`input.wiz`, run with `--oneshot`:

```wiz
import Prelude
import IO
#check Nat
```

Desired: `Nat` once. Current: the second `import` runs `preludeText` again, so every
prelude declaration is a duplicate and the output is a cascade of
`'Nat' has already been declared` etc. Decide: dedupe the embedded prelude in
`checkFileOpts` (a `Bool`/`Globals` flag), or reject a second import in one-shot mode
with one clear error. Add the case with the chosen expectation.

### C16 — generated prelude gates (prerequisites: F48)

- Static: `python3 scripts/check-prelude-drift.py` (on the F48 tree it prints
  `ok: the embedded prelude's surface is in sync`; 213 names).
- Light: C8 above.
- Heavy, later: `=selfhost` cases 212 ("text to checked term, all in Wiz") and 226
  ("Backend.wiz erases the value of a let at 0, and keeps it at 1 and ω"); these are the
  cases F48 broke. After the fix, both should pass with the F48 branch. Also run the
  pipeline meta-case `selfhost-host#3` (it proves the group is not vacuous).
- A negative pin for the slice: removing `Tac` from the prelude must reproduce the
  cascade, one `unknown identifier` per dependent declaration (this is what the F48
  commit's bisect did; encode it as a Wiz unit test over `preludeText`? The prelude is a
  string constant, so a test can check that the slice's names occur; a *semantic*
  negative is the `=selfhost#212` run with the slice removed, not a regular case).

### C17 — transitive public names vs non-transitive opens (existing, add a `#check`)

`Tests/Groups/SelfHost.lean:3256` already pins `three` being usable in `input` through
`B` (transitive public). Add the contrast explicitly:

```wiz
C.wiz:   import Prelude
         namespace N
         def deep : Nat := 3
         end N
B.wiz:   import Prelude
         import C
         open N
input:   import Prelude
         import B
         #check N.deep       -- public name: visible (module names are not prefixes)
         def bad : Nat := deep -- open: not transitive
```

Expected: `Nat` for the qualified check; `unknown identifier deep` for `bad`. This
documents that "imports are flat for names, per-module for opens".

### C18 — duplicate probes (extend the existing `dupNames` case)

`Tests/Groups/SelfHost.lean:2604` already pins: duplicate `def`, duplicate inductive,
duplicate constructor, duplicate projection, `axiom` then `def`, `partial` twice,
`mutual` twice, and `fine` still declared. Extend with the module-sensitive cases:

```wiz
M.wiz:  import Prelude
        private def p : Nat := 1
        def p : Nat := 2
```

and

```wiz
M.wiz:  import Prelude
        private def q : Nat := 1
        private def q : Nat := 2
```

Selfhost: both are `'p'/'q' has already been declared` and neither `p`/`q` is
(re)declared. Host library module: currently *accepts* both (post-rename; Q3) — pin the
difference with `selfhostVerdicts` or, better, fix the host and make it `selfhostAgrees`.

### C19 — property test: failure closure (new, strongest single test)

Generate a random DAG of declarations `d₁ … dₙ`, each body/type using only earlier
names (a small alphabet: `Nat`, `Bool`, `List`, `def`, `partial`, `mutual` groups,
`inductive`, structures). Then:

1. Run the program in both frontends; both must accept, and the set of printed names
   must agree.
2. Pick one declaration `dᵢ`, replace one of its referenced names with a fresh unknown,
   and run again. Compute the transitive closure of users of `dᵢ`. Assert: every user
   fails with its own `unknown identifier`; every non-user is declared; the first error
   is at the earliest user in source order.
3. Permute the declaration order (a random topological shuffle is still valid; a
   non-topological shuffle must fail at the first declaration whose dependency moved
   later). Assert the set of successful declarations is exactly the prefix closed under
   dependencies.

This pins R-FAIL, R-ORDER and the cascade shape without hard-coding messages. It is a
natural addition next to the existing `selfhostAgrees`/`selfhostVerdicts` helpers; run it
in the `selfhost` group (it compiles the checker once, then many small files).

---

## 5. Code sites

### 5.1 Selfhost (`selfhost/Frontend.wiz`, train12 line numbers)

| Role | Site |
|---|---|
| Scope, binders, module, private markers | `Scope` `:101`, `Scope.bind` `:105`, `Scope.setModule` `:108`, `Scope.declaredIn` `:117`, `Scope.addGlobal` `:122`, `Scope.find` `:131`, `privOwner` `:136` |
| Macro scope | `stripScope` `:144` |
| Exact lookup / private preference | `lookupExact` `:155`, `lookupV` `:169`, `lookup` `:177` |
| Globals, flat name map | `Globals` `:684`, `atModuleStart` `:758`, `pushNs`/`popNs` `:760`, `setModule` `:768`, `setPrivate` `:770`, `declName` `:773`, `add` `:777`, `addInd`/`ind` `:784` |
| Namespace candidate set / resolver | `nsCandidates` `:973`, `resolvePlainRel` `:993`, `resolvePlain` `:1018`, `resolveNameV` `:1026` |
| Closing a scope-checked term | `closeG` `:1042` |
| Duplicate check | `newDuplicate`/`dupFrom` `:1172,1155`; `Step` `:1127` |
| Inductive fields / positivity / hrec | `recField` `:1399`, `ctorDesc` `:1499`, `inductiveCmdL` `:1985`; `[F48]` `hrecField` (`8cdf33a24`) |
| Mutual inductives | `mutualInductiveCmd0` `:7740`, `addMembers` `:7687`, `addMCtors` `:7703` |
| Mutual/partial defs | `addPartials` `:8895`, `addAxioms` `:8863`, `defsSteps` `:9401`, `partialCmd` `:9415` |
| One declaration | `defStep` `:8637`, `command` (def) `:7505`, `identHead` `:5202` |
| Namespaces/prefixing | `prefixDeclName` `:7934`, `mutualTypeShorts`/`rewriteShort` `:7904,7922`, `nsTarget` `:11583`, `stripRootS` `:11593`, `nsCommand` `:11596` |
| Wrappers | `unwrapPrivate` `:10828`, `unwrapLocal` `:10791`, `sealedCmd` `:8625` |
| Structures/classes/instances | `structCmd`/`projections` `:9467,9452`, `instanceCmd` `:9663` |
| Derivers | `elabDerivedGo` `:11469`, `withDeriving` `:11540`, `derivingCmd` `:11551` |
| Command loop | `commandStep` `:11700`, `stepCommand` `:11784`, `runCommands` `:11858` |
| One-shot / loader | `checkFileOpts` `:11933`, `modCanonical` `:12026`, `modRunBody` `:12273`, `moduleRootSourcesAs` `:12484` |
| Embedded prelude | `preludeText` `:10151` |

### 5.2 Host (Lean)

| Role | Site |
|---|---|
| Globals fields (prefix/opens/aliases/module/privacy) | `Wiz/Core/Term.lean:679-687` |
| `Globals.insert` / `resolve` / `privateName` / `privateBase` / `privateTo?` | `:777,839,826,830,845` |
| `expandAliases` / `resolveName` | `:852,872` |
| Term identifier resolution | `Wiz/Elab/Term.lean:3808` (`infer`), `:3820` local, `:3828` resolveName, `:3834` find, `:3838` private, `:3865` defining guard, `:3876` fields |
| Declared-name / duplicate messages | `Wiz/Elab/Command.lean:346` |
| Private post-rename | `:445` |
| Prefixing / module start | `:2055,2114` |
| Command dispatch | `:2132`; namespace `:2326`; open `:2357`; private `:2380`; sealed `:2430`; local `:2454`; def `:2488`; partial/mutual `:2595`; inductive/structure `:2895`; deriving `:3903` |
| Mutual inductive expansion | `:1730` |
| Module end / local table drop | `:1901` |
| Expansions (prefix generated names) | `:2249` |
| Inductive elaboration / T binding / hrec | `Wiz/Elab/Inductive.lean:280,339,211,221`; structure `:529` |
| Frontend loop / imports / step | `Wiz/Frontend/Frontend.lean:252,~275-350,355` |

### 5.3 Tests and docs

- `Tests/Groups/SelfHost.lean`: `dupNames` `:2604`, failed `def` `:2610`, partial/mutual
  `:2667`, mutual inductives `:2676`, private `:2903`, modules `:3254`, private modules
  `:3451`, source-name-once `:3473`, deriving `:3837`, namespaces `:3856`, root `:3889`.
- `Tests/Groups/Namespace.lean`: the `namespace` group `:194-278` (including the
  `def __root__.x` case `:273`).
- `Tests/Groups/Elab.lean`: unknown identifier `:94`, duplicate `:126`.
- `Tests/Elab.lean`: `selfhostCheckFile` `:2019`, `selfhostModuleOutput` `:2090`,
  `selfhostCheckModules` `:2131`.
- Docs: `docs/stages/21-bootstrap.md` §21n `:308-380` (the current privacy/resolution
  prose), §21an `:1447`; `docs/stages/13-language.md` 13b/13t/13v.
- Notes: `codebase-audit-2026-11-22.md` F48; `import-shadowing.md` (the duplicate rule;
  `Cache.Effect.apply` replay path is host-only); `selfhost-parity.md` A14.

---

## 6. Open questions

Each is a decision or a fix, with the site and the smallest test that pins it.

**Q1 — Should a failed partial/mutual body roll the block back? (soundness)**
Host: yes (one local `g`, committed at the end). Selfhost: no — `addPartials` commits
all signatures, `defsSteps` keeps earlier bodies; a failed body leaves an axiom
signature usable by later commands. Proposal: make `partialCmd` collect the body results
and return the pre-block `Globals` if any body failed (or make `finishStep` compare and
roll back), so the block is atomic. Evidence: C5; code `:8895,9401,9415`. This is the
highest-priority item: the residue is an unproven assumption.

**Q2 — `__root__` in a declaration name, and bare/misplaced `__root__`.**
Selfhost `prefixDeclName` prefixes it; host strips it and rejects bare/misplaced. Decide
for the host rule (13v), add the strip in `prefixDeclName`, and add the `root-name`
errors in `stepCommand`. Evidence: C9; code `:7934`; host `:2025,2055,2135`.

**Q3 — Private kernel name timing and duplicate detection.**
Selfhost mangles at `Globals.add`, so a private and a public declaration of one source
name in one module clash, and two private ones clash. Host types are pre-renamed but
defs/axioms/mutual defs are post-renamed in a module (`renamePrivate`), so a
private+public pair is accepted and the second private definition can replace the first.
Decide which is normative (selfhost's "one source name per module" is the documented
rule, 21n), and either pre-rename defs in the host or add a source-name duplicate check
there. Evidence: C18; host `:445,2380`; selfhost `:1172,1155`.

**Q4 — `open` a namespace with only private declarations.**
Host allows it for the declaring module; selfhost `hasDeclUnder` only scans public
prefixes. Fix `hasDeclUnder` to also accept `_private.<current module>._0.<n>.` when the
namespace is being opened from its own module. Evidence: C12; code `:896`.

**Q5 — `local` scope.**
Selfhost accepts `local` on any command and leaks grammar/registrations to importers;
host restricts the command set and drops module-local tables at `endModule`. Port
`agent/sh-a14`'s `modExportAt`/`modReplay` (or an equivalent) and reject `local def`
with the host's message. Evidence: C14; code `:10791,10796`; host `:1901,2454`.

**Q6 — The seal of a `sealed` type.**
Host always marks `T.seal✝` private to the module; selfhost's seal is public unless
`private sealed`. A public seal lets an importer write `T seal` (the phantom parameter)
and forge the type's identity. Decide: always private (host), and check the `sealed`
tests in `Tests/Groups/Repr.lean`. Evidence: `sealedCmd` `:8625`; host `:2448`.

**Q7 — One-shot imports.**
`checkFile` treats every `import` as the embedded Prelude and re-runs it per import.
Decide: dedupe in `checkFileOpts` (a `Bool` "prelude loaded" threaded through
`runCommands`), or reject non-`Prelude` imports in one-shot mode with one clear error.
Evidence: C15; code `:11803,11933`.

**Q8 — Namespace vs `open` precedence.**
Both frontends currently report an ambiguity when the enclosing namespace and an opened
namespace provide the same name. Lean-style resolution often lets the current namespace
win. Decide: ambiguity (current) or prefix precedence; the candidate list
`nsCandidates` and host `resolveName` must change together. Evidence: C10.

**Q9 — `deriving` name resolution and generated names in a namespace.**
Selfhost `deriving instance C for T` passes the written names to `Globals.ind`/
`Globals.class`/`Globals.deriver` (raw), so a namespaced type/class is not found; host
resolves T and C in `command.deriving` (but not in an inductive's `deriving` clause).
`elabDerivedGo` also does not prefix generated command names, unlike host
`elabExpansion`. Decide: resolve all three names through `resolveNameV` at the command
boundary, and prefix emitted commands. Evidence: C8/C13 and a namespace+deriving case;
code `:11469,11551`; host `:2258,3903`.

**Q10 — Mutual-inductive parameters and the host's `modulePrefix`.**
Selfhost supports parameters in `mutual inductive` (existing tests rely on it); host
rejects them. Selfhost has no `modulePrefix` default namespace; host's is off by default.
Decide whether to keep the extension (pin it with `selfhostVerdicts`) or drop it for
parity; do not turn `modulePrefix` on without a selfhost counterpart. Evidence:
`Tests/Groups/SelfHost.lean:2679`; host `:1734,2114`.

**Q11 — F44: the recursion recogniser.**
Host accepts `def f := fun ys => match … f …` by converting it to equations; selfhost
only converts a direct `:= match` on parameters and reports `unknown identifier f`
inside the lambda. Decide: peel lambdas in `defStep`/`withDefault` to match
`defMatchAsEqns?`, or pin the gap (the fuzzer classification is frozen). Evidence: C3;
selfhost `:8645`; host `:999`; audit F44.

**Q12 — Diagnostics for a bare root-level private name.**
For a private declaration at the root of another module, selfhost names the module
(`'x' is private to module M`); host says `unknown identifier` unless the name is
qualified or aliased. For a private declaration under a namespace, both say unknown for
the short name and the private error for the qualified one. Both reject, so this is
wording; decide whether to align (selfhost's message is more useful for the root case)
and keep cross-frontend tests on verdicts, not text. Evidence: C11; host
`Tests/Groups/Namespace.lean:212`.

**Q13 — Public-name transitivity.**
Public names are visible through an importer even though the importer does not `open`
anything; `open`s are not transitive. This is the host behavior and is already pinned by
the transitive test (`:3256`), but the 21n prose ("a module's exported set is every
public name it declares") reads as if only direct imports are visible. Clarify the doc:
the environment is flat; a module's public names are in `E` for every later module in
the graph. Evidence: C17.

**Q14 — The macro-scope exact-name rule.**
Selfhost tries an exact global `f✝s` before the stripped `f` (needed for its generated
helpers); host always strips for globals. This is safe for now (the host generates no
such names), but if the host ever emits a scoped global the two will differ. Document the
rule and add a regression if the host gains one. Evidence: `resolveNameV` `:1026`; host
`Wiz/Elab/Term.lean:3828`.

---

## 7. References

- `codebase-audit-2026-11-22.md` F48 (the failure chain and the audit's incorrect
  "same-file resolution" hypothesis).
- `/workspace/wt/f48-resolution`: `226487b9b` (the prelude slice) and `8cdf33a24`
  (`hrecField`/`ctorDesc`; the fix). Commit messages quote the verified self-check runs.
- `docs/stages/21-bootstrap.md` §21n (`private` and resolution), §21an (`closeG`/`sigma`);
  `docs/stages/13-language.md` 13b (privacy), 13t (namespaces), 13v (`__root__`).
- `import-shadowing.md` — the duplicate/import rule and the soundness bug it fixed.
- `selfhost-parity.md` A14 — the namespace pass, including the `resolveNameV` fixes.
- `Tests/Groups/Namespace.lean` — the host namespace matrix; `Tests/Groups/SelfHost.lean`
  — the selfhost pins, notably `dupNames`, failed declarations, partial/mutual,
  modules and `__root__`.
- `scripts/check-prelude-drift.py` — the embedded prelude surface gate.

---

## 8. Handover

- No product code changed. The branch carries this note only.
- Next action for a fix lane: Q1 (atomic mutual/partial), then Q4 + Q2 (small,
  self-contained), then Q6 (soundness review), then Q3/Q5/Q7.
- The conformance cases can be added now; C5/C9/C12/C14/C15 are expected-red on
  train12 and become green with their fixes. C7/C8/C16 need the F48 branch.
