# Module namespaces: rules, migration, and what it costs

**Status:** design, 2026-11-19. No code in this branch. Counts are from the branch point
`c2efe881` (local `master`), scanned as described in §9; they are declaration counts, not
guesses.

**This file supersedes `namespace-plan.md` (2026-11-17/18), the module-reorganisation
plan.** The old plan is archived as
`archive/namespace-plan-module-reorg-2026-11-18.md`. Its move list
(`Scry.Tool.*`, `Scry.Examples.*`, `Data.*`, `Proof.*`, `Run.*`, `Hdl.Trace`) is **not**
a prerequisite for namespaces and is not re-decided here. Its settled decisions of
2026-11-18 (`lib/Scry` leaves the standard library; a `Data.*` group is wanted) remain in
force and are recorded in the archive. This plan is about the *language* rule and the
migration that makes today's tree check under it.

The short version:

1. A module's default namespace is its module path: `scry/src/Scry/CstStore.wiz` is
   `Scry.CstStore`; `f` there is `Scry.CstStore.f`.
2. `__root__.f` is the only way to declare or name a true global (Lean's `_root_.f`).
3. `namespace X … end X` and `open X` exist, are relative to the current namespace, and
   `open X as A` is a qualified alias only.
4. Today's tree is made safe by a **generated compatibility allowlist**, not by a
   flag-day rename: every existing declaration keeps its current name until its module is
   migrated. The allowlist has 8,757 rows over 157 files for the five library/tool
   trees (11,153 over 169 with `selfhost/`, §3.3).
5. The five interaction verdicts are in §5: `private` composes (24 declarations),
   `import` brings the namespace but not an open (502 import edges), instances stay
   global (191 commands), the trust ledger's `module` column already *is* the namespace
   (730 rows, 576 to re-key over the whole programme), and the self-hosted frontend's
   flat table must be re-keyed (2,396 declarations, 12 files).

---

## 0. The model in one screen

```wiz
-- scry/src/Scry/CstStore.wiz, module Scry.CstStore
def lineIndexGo (n : Nat) : Nat := n          -- Scry.CstStore.lineIndexGo
def __root__.cstVersion : Nat := 1            -- cstVersion (a true global)

namespace Internal                            -- Scry.CstStore.Internal
def scratch : Nat := 0                        -- Scry.CstStore.Internal.scratch
end Internal

-- another file, with `import Scry.CstStore`
def use : Nat := CstStore.lineIndexGo 0       -- the direct import's leaf alias
def use2 : Nat := Scry.CstStore.lineIndexGo 0 -- the full path always works
def use3 : Nat := cstVersion                  -- the root name
```

The main structural difference from Lean is the first line: Lean has no implicit
per-file namespace. The smaller differences (`open` scope, no `section`, `scoped`
notation, the import leaf alias) are listed in §1.9; everything else is Lean's behaviour.

---

## 1. Rules

### 1.1 The default namespace is the module path

A module's name is derived from its path under the package root that owns it
(`Wiz/Module.lean`, `Module.nameOf`; the self-hosted loader derives the same name,
`selfhost/Frontend.wiz`, `modRelPath`). The module's **default namespace** is that name:

| file | module | a declaration `def f` is |
|---|---|---|
| `scry/src/Scry/CstStore.wiz` | `Scry.CstStore` | `Scry.CstStore.f` |
| `scry/src/Scry/TaintCmd.wiz` | `Scry.TaintCmd` | `Scry.TaintCmd.f` |
| `lib/Nat.wiz` | `Nat` | `Nat.f` |
| `lib/Prelude.wiz` | `Prelude` | `Prelude.f` — except that this file is root (§3.4) |
| `selfhost/Frontend.wiz` | `Frontend` | `Frontend.f` — except that this tree is frozen (§5.5) |

Inside the module, `f` and `CstStore.lineIndexGo` both name the declaration: the resolver
tries the current namespace first (§1.5). Outside, `Scry.CstStore.f` always works; the
*leaf* `CstStore.f` works for a direct `import Scry.CstStore` (§1.7).

The prefix applies to the **declared name**; constructors, fields, recursors, `T.desc`,
`T.seal✝`, and generated instance names follow the type, exactly as `Globals.privateName`
already derives a private name from its declaration. There is no second rule for them.

### 1.2 `__root__` (Lean's `_root_`)

`__root__` is a leading name segment, not a variable and not a namespace you can
declare. It resets the prefix to the empty one:

```wiz
def f : Nat := 0                    -- Scry.CstStore.f
def __root__.f : Nat := 0           -- f
namespace __root__.Shared           -- Shared
def g : Nat := 0                    -- Shared.g
end
def h : Nat := __root__.f           -- the root f, even if Scry.CstStore.f exists
```

* It is allowed in a declaration name, in `namespace`, in `open`, and in a term or
  pattern. It is only meaningful as the **first** segment: `A.__root__.b` is an error
  (`root-name`), as is a declaration named exactly `__root__` or `namespace __root__.`
  with nothing after the dot.
* `namespace __root__` with no dot opens the root for a block (`end` or `end __root__`
  closes it). That is the bulk exemption for a file whose declarations must stay global
  (`Prelude`, the frozen self-hosted sources): one line at the top and one `end` at the
  bottom, instead of 260 or 2,259 `__root__.` markers.
* `__root__` is an ordinary identifier lexically (`Wiz/Parser/Token.lean` already accepts
  `_` and `.` in an identifier), so the grammar does not change; the resolver and
  `prefixDeclName` interpret it. It is *reserved in name position* by a check, not by the
  token table, so `__root__` remains usable as a local variable name (nobody should, but
  nothing breaks).
* A true global name is the only place the old flat collision rules still apply: two
  modules that both declare `__root__.x` collide exactly as they do today. A shared
  namespace (`namespace __root__.List`) is also global, and collisions *inside* it remain;
  that is the price of an open-world family such as `List` or `Bits` (§3.2).

### 1.3 `namespace X … end X`

`namespace` opens a namespace **relative to the current one**, as in Lean:

```wiz
namespace A            -- Scry.CstStore.A
namespace B            -- Scry.CstStore.A.B
def x : Nat := 0       -- Scry.CstStore.A.B.x
end B                  -- or `end`
def y : Nat := B.x     -- Scry.CstStore.A.B.x
end A
```

* Nested `namespace A.B` is one command with a dotted name, or two commands; both are
  the same prefix.
* `end` closes the innermost namespace; `end X` must name its last segment (or its full
  name). A missing `end` is reported at its own `namespace` line; a stray or mismatching
  `end` at the `end` (`unclosed-namespace`, `stray-end`). This is the 13t behaviour and
  its tests.
* `namespace` does **not** fall back to the root: inside module `M`, `namespace List`
  means `M.List`, never the global `List`. To reopen a global namespace, write
  `namespace __root__.List` (§1.2). This is the single most important rule for the
  migration of the extension families (`ListLemmas` extends `List`, `IntRing` extends
  `Int`, `BitVecAdd`/`BitVecShift`/`BitBlast` extend `Bits`).
* `namespace M` at the top of module `M` is **not** a no-op: it would open `M.M`. The
  elaborator reports it as a warning (`namespace-repeats-module`) and ignores it; the
  module's default already is `M`. Do not write it.
* A namespace is a prefix, not a privacy boundary: `private` is still per module (§5.1).

### 1.4 `open X` and `open X as A`

`open X` makes the names under `X` visible unqualified from that line to the end of the
file:

```wiz
namespace A
def x : Nat := 0
end A
open A
def y : Nat := x       -- A.x
```

* **File-scoped from the line on.** `end A` does not undo the `open`, and an `open`
  inside a module does not reach a file that imports it (`CommandState.endModule` drops
  it). This is the 13t rule and it is a deliberate divergence from Lean, which scopes an
  `open` to the enclosing `section`/`namespace`; Wiz has no `section`, and the file is
  the module. The 13t test "an `open` is file-scoped: it outlives its namespace's `end`"
  is the contract.
* **`open` resolves like a reference**, not like a declaration prefix: it tries
  `currentNs ++ "." ++ X`, then the root `X`, then an import alias (§1.7). An unknown
  name is an error (`unknown-namespace`). Thus `open List` inside `ListLemmas` opens the
  root `List` if `ListLemmas.List` does not exist — unlike `namespace List`, which would
  *create* `ListLemmas.List`.
* **An unqualified name that two opens provide, or an open and a declaration, is an
  error** naming both candidates (`ambiguous-name`), never a silent last-wins. The same
  declaration found twice (this namespace and an open of it) is one candidate. The
  candidate order is: enclosing namespaces (innermost first), root, then each open; only
  distinct full names conflict.
* **`open X as A` is a prefix alias, not an open.** `A.x` is `X.x`; `x` is not. An alias
  is for a long or clashing prefix. The longest matching alias wins for a qualified name.
* `open` does not change declaration names: with `open A`, `def y` is still `M.y`, not
  `A.y`.
* **No `open … in` in v1.** It is a small command wrapper and can be added later without
  changing the resolution rules; nothing in the tree needs it.

### 1.5 Resolution, precisely

`Ns` is the current namespace: the module path, then each `namespace` on the stack.
`root` is the empty namespace.

**Unqualified `x`** (in a term, pattern, `#check`, `builtin`, `extern`, …):

1. a local binder (unchanged; locals shadow globals);
2. `Ns.x`, then the enclosing namespaces outward;
3. `root.x`;
4. `N.x` for each `open N` (in source order);
5. `root.x` as a builtin (`Unit`, `True`, …) if nothing was found.

Distinct full names in the candidate set are an ambiguity error. A private declaration
of another module is not a candidate; this module's private declaration is (under its
kernel name, §5.1).

**Qualified `A.x`:**

1. `Ns.A.x` (relative), then the enclosing namespaces outward;
2. `A.x` (root);
3. an `open … as` alias or an import leaf alias, longest prefix first.

Again, distinct full names are an error. There is **no general suffix search**: `CstStore.x`
works because `import Scry.CstStore` registers the leaf alias, not because the resolver
scans for a declaration ending in `.CstStore.x`.

**`__root__.x`:** exactly `root.x`; no relative or alias fallback.

The resolver lives in `Globals.resolveName` (`Wiz/Core/Term.lean`), called from
`infer`'s `term.ident` case, `patView`, `fieldByTypeName?`, `implicitFix`, `binopHead`,
`numOperands`, and the command paths (`#check`, `#print axioms`, `builtin`, `extern`,
`app_unexpander`, `derive`, instance heads). Most already call `resolve`; stage 2 routes
the rest through `resolveName` (the 13t branch already changes `infer` and `patView`). The
private lookup must be composed: for each candidate full name `c`, also try
`Globals.privateName module c` (§5.1).

### 1.6 `private`, `local`, and notation

* **`private` is per module, not per namespace** (§5.1). A private name is invisible
  through `open` and through an alias; a qualified name still needs the privacy check.
* **`local` stays module-scoped** (`docs/stages/13-language.md`, 13m): it does not follow
  a namespace or an `open`. `local instance` is module-scoped too (the existing
  `localInsts` mechanism).
* **`scoped` notation is deferred.** Lean's `scoped` notation is active where a namespace
  is open; Wiz has no notation-scope machinery, and the self-hosted parser has no
  `syntax` command at all. `local` covers the module case, which is the only one the
  library uses today. Adding `scoped` later means teaching the parser tables to
  activate/deactivate rules on `open`/`end` (the `localRules` machinery is the starting
  point); estimate one to two days plus a self-hosted table change, and nothing in the
  tree depends on it. Do not couple it to this plan.

### 1.7 `import`

`import M` brings M's declarations, at their full names, and (for a direct import) one
**leaf alias**. It does not open anything:

| after `import Scry.CstStore` | works? |
|---|---|
| `Scry.CstStore.lineIndexGo` | yes |
| `CstStore.lineIndexGo` | yes, the direct import's leaf alias |
| `lineIndexGo` | no — write `open Scry.CstStore` or qualify |
| a name from a module that `Scry.CstStore` imports | yes, at its full name (imports re-export declarations, as today); its leaf alias is **not** registered |

* The alias is registered only if the leaf is unambiguous: not another direct import's
  leaf, and not already a root namespace or declaration (so `Text.x` keeps meaning the
  root `Text`; an `import Hdl.Text` uses `Hdl.Text.x`, with a warning at the import).
  When two direct imports share a leaf (`Main` in `selfhost/Main.wiz` and
  `tower/Main.wiz`), only the full path is available; a use of `Main.x` is an ambiguity
  error naming both modules.
* The alias is a **prefix** alias: `CstStore.Internal.x` is
  `Scry.CstStore.Internal.x`.
* The alias is per direct import and per file; it is not re-exported. An `open M` in an
  imported module does not reach the importer (13t's rule); neither does its leaf alias.
* `import` does not change the module's own default namespace: a file that imports
  `Scry.CstStore` and declares `def f` still declares `M.f`.

This is the answer to "does `import` bring the prefix?": it brings the module's full
namespace (the names are `M.*`) and a leaf alias for qualified use; it does not bring an
implicit open.

### 1.8 Instances

Instance search is by class head over the flat `CommandState.instances` array
(`Wiz/Elab/Class.lean`), not by name and not by namespace. Under the model:

* an instance declared in namespace `N` of module `M` is named `M.N.inst…` (anonymous
  instances get `M.N.inst<Class>…`), which removes instance-name collisions;
* the search still sees every instance in the file's imported state, regardless of the
  namespace it was declared in — the Lean behaviour;
* `local instance` remains module-scoped (and is not namespace-scoped).

There is nothing to change in the search algorithm; the only change is the name of the
declaration, in `prefixDeclName` and in the anonymous-instance base name (§5.3).

### 1.9 Divergences from Lean (deliberate)

| Lean | Wiz | why |
|---|---|---|
| no implicit file namespace | module path is the default namespace | the proposal; this is what removes `Msg`/`Settings`/`main` collisions |
| `_root_` | `__root__` | the spelling requested and used by the plan |
| `open` scoped to the enclosing section/namespace | file-scoped from the line on | Wiz has no `section`; the file is the module; 13t already ships and tests this |
| `section`, `variable` | not proposed | Wiz has no section variables; `namespace` is enough |
| `scoped` notation | deferred; `local` is module-scoped | parser-table work, not needed by the library |
| `import` brings names at full names | same, plus a direct import's leaf alias | the `CstStore.lineIndexGo` spelling in the brief; a leaf alias is cheaper and safer than suffix search |

Everything else — relative `namespace`, `__root__`, aliases, ambiguity as an error,
`private` per module, global instance search — is Lean's behaviour.

---

## 2. What the tree does today (the evidence)

### 2.1 The flat table

The host keeps every declaration in one `Std.HashMap Name (Decl R)` (`Globals.decls`,
`Wiz/Core/Term.lean`); there is no namespace field, and `find?` is an exact lookup. The
self-hosted frontend does the same with `Scope.globals : StrMap Nat` keyed by the kernel
name (`selfhost/Frontend.wiz`). `docs/stages/23-grail.md` (23b) says it in one line:
"Wiz has no namespaces (`Nat.repr` is one global)".

The consequences are in the history, not in theory:

* **`Msg`.** `lib/Session.wiz:104` declares `inductive Msg`; `lib/Web/Loom.wiz:50`
  declares another; `web/framework/gen.wiz:12` a third. `lib/Web/Playground.wiz` had to
  rename its type to `PlaygroundMsg` (`861a8cc7`): "a top-level name is global across
  lib/, so `Msg` collided with `lib/Session.wiz`'s `Msg` and the trust-ledger job (which
  elaborates the whole library) failed with `'Msg' is declared by both module Session and
  module Web.Playground` — while this component's own fixture, which imports only what it
  needs, passed." Three `Msg` declarations in three modules.
* **`Scry.lineIndexGo` / `Scry.lineColFrom`.** `scry/src/Scry/TaintCmd.wiz:256` and
  `:266` carried copies of these (declared in `Scry.CstStore`); the driver refused to
  load: "Wiz has no per-module namespacing, so a second definition makes the driver
  unloadable" (`0950f32f`), and "the second definition of `Scry.lineColFrom` made the
  driver refuse to start (`declared by both module Scry.CstStore and module
  Scry.TaintCmd`)" (`73398c4c`). The fix was deleting one copy. Under the model they
  would be `Scry.TaintCmd.lineIndexGo` and `Scry.CstStore.lineIndexGo`: distinct names.
  (The *duplication* is still a maintenance bug; namespaces only stop it being a name
  clash.)
* **`Scry.boolD` / `Scry.dedup`.** Declared in `Scry.Codegen` (`boolD` at `:73`, `dedup`
  at `:113`) and `Scry.Facts` (`boolD` at `:62`), and `Scry.Lower` (`dedup` at `:2343`).
  Legal today only because no module imports both halves; a new importer would fail the
  same way as `Msg`.
* **`Settings`, `Model`, `view`, `app`, `main`.** `Settings` is in `lib/Grail.wiz` and
  `tower/Tower/Basic.wiz`; `Model`/`view`/`app` in `lib/Web/Loom.wiz` and
  `web/framework/gen.wiz`; `main` in `Hdl.Core`, `IO`, `Main`, `Serial`, `Sys`,
  `framework.gen`. A scan of the five library/tool trees finds **23 exact top-level names
  declared in more than one module, across 32 modules**. That is the latent collision
  surface; the subset that has been hit is the four stories above.

### 2.2 The tree in numbers

The five library/tool trees (`lib/`, `scry/src/`, `scry/gen/`, `tower/`, `web/`) have
159 `.wiz` files and **8,757 top-level declarations in 157 files**; the two declaration-free
files are `lib/Scry/Ai.wiz` (an aggregator) and `tower/tests/pure.wiz`. Adding
`selfhost/` (12 files, 2,396 declarations) gives **11,153 declarations in 169 files**;
`examples/` adds 2,482 in 106 files and `drafts/` 407 in 56. The six trees are 92,131
lines of Wiz.

| class of written name | declarations | files | what the default prefix makes it | migration |
|---|---:|---:|---|---|
| `bare` (`def f`) | 540 | 70 | `M.f` (68 Prelude names stay root) | rename or `open` |
| `exact-module` (`def M`) | 16 | 16 | `M.M` | `__root__` the type |
| `exact-leaf` (`structure Pipe` in `Hdl.Pipe`) | 1 | 1 | `Hdl.Pipe.Pipe` | `__root__` or keep nested |
| `module-prefixed` (`def M.f`) | 1,026 | 40 | strip `M.` → `M.f` (**same name**) | mechanical, no rename |
| `first-prefixed` (`def Hdl.f` in `Hdl.Core`) | 2,752 | 62 | `Hdl.Core.f` | rename |
| `leaf-prefixed` (`def Apb.f` in `Hdl.Apb`) | 801 | 21 | `Hdl.Apb.f` | rename |
| `other-dotted` (`def Fe.f` in `Feral`) | 3,621 | 74 | `Feral.Fe.f` or a root extension | split (§3.2) |
| **total** | **8,757** | **157** | | |

**8,217 of the 8,757 (94 %) are already dotted, in 152 files** — the five trees. The
self-hosted tree adds 136 dotted declarations (`8,353` in the six trees). That is the
migration. The other trees: `selfhost/` 2,396 declarations in 12 files; `examples/` 2,482
in 106; `drafts/` 407 in 56; 67 fixture files under `Tests/`, `editors/` and `examples/`
that are registry-test evidence and must not be renamed.

Module graph: 170 distinct module names in 171 files; one duplicate name (`Main` in
`selfhost/Main.wiz` and `tower/Main.wiz` — different packages, never loaded together); two
prefix overlaps (`Web` vs `Web.Loom`, `Web` vs `Web.Widget` — a module name and a
namespace may coexist, so these are legal, but the case-only `Web`/`Web.*` is the same
latent case-insensitive-filesystem issue the old plan noted); 502 `import` lines to 115
distinct targets; 56 modules never imported.

---

## 3. Migration: what happens to already-dotted names

### 3.1 The problem

Under the rule, a `def Scry.lineIndexGo` in module `Scry.CstStore` is
`Scry.CstStore.Scry.lineIndexGo`, and the same declaration in `Scry.TaintCmd` is
`Scry.TaintCmd.Scry.lineIndexGo`. Both are wrong: the author wrote `Scry.` as the
*intended* global prefix, not as a nested namespace. (The historical copy was in
`Scry.CstStore`; today's is in `Scry.TaintCmd`.) The same applies to `Hdl.f` in
`Hdl.Core`, `Apb.f` in `Hdl.Apb`, `Fe.f` in `Feral`, `Bits.f` in `BitBlast`, and the
`List`/`Int`/`Bytes` extension families. A mechanical strip is not enough either: a
declaration whose written prefix is a *different* concept (`Bits` in `BitBlast`) must not
become `BitBlast.odd` unless the owner means to rename the family.

### 3.2 The three options, and the recommendation

**Option A — one-off rewrite of every dotted declaration.** Strip the module's own path;
rename the rest into the module namespace or a root family. Touches **8,217 declaration
lines in 152 files** (five trees), plus every reference and **576 trust-ledger rows** (the
60 module-prefixed, 68 cross-module-extension, 24 Prelude and 2 principal-type rows are
name-preserving; see §3.3). It is the clean end state, but as a flag day it is
unreviewable: one mistake in a family (`Bits`, `Bytes`, `File`) breaks a whole analysis
or the HDL library, and the ledger diff is 576 rows with one shared reason.

**Option B — a temporary compatibility rule.** The brief's wording is "a name starting
with the module's own prefix is absolute". A *text* rule of that shape does not work:
`Scry.lineIndexGo` does not start with the module path `Scry.CstStore`, and `Bits.odd` in
`BitBlast` does not start with `BitBlast`; making it "starts with the module's first
segment" would also capture unrelated names in a module such as `Scry.CstStore`, and
"any dotted name" would capture every new declaration that wants a nested namespace. A
prefix heuristic is either too narrow or too broad.

The safe form of B is a **generated allowlist**, not a text rule:
`legacy-names.tsv` with one row per `(module, full name)`, generated from the current
elaborator before the default prefix flips. A declaration whose written name is in the
row set for its module is declared at that absolute name and emits a `legacy-name`
warning; everything else gets the default prefix. A new legacy name is an error; an
unused row is an error (the batch forgot to delete it); `--strict-names` makes the
warnings errors. The allowlist is read by the elaborator, so its digest must be mixed
into the module cache key (`Frontend.isoKey`, `Cache.moduleKeys`) or a stale artifact
will disagree with a fresh run; alternatively, apply it as a source rewrite in
`runFrontend.step` before elaboration, and the cache key is just the rewritten text.

*Size:* **8,757 rows / 157 files** for the five library/tool trees (11,153 / 169 with
`selfhost`; every declaration, not only the dotted ones, so bare names are safe too);
2,482 more for `examples/` if that root is checked under the same rule. **Day-one
renames: zero. Day-one ledger changes: zero.**

**Option C — `__root__` every legacy declaration.** Prefix the 8,217 dotted declarations
with `__root__` (one token each, 152 files). Zero reference and ledger changes, but it
cements the flat table: every collision rule stays in force everywhere, and the
`Msg`/`Settings`/`main` class is not fixed. It is the right tool for a *file* that must
stay global (`Prelude`, the frozen self-hosted tree, a generated schema), not for the
library.

**Recommendation: B, then A in batches.** Start with the allowlist (zero behaviour
change, all gates green), then migrate one module or one family per commit, deleting its
allowlist rows. The end state is A's clean rule with a reviewable diff per batch. B is
least surprising because the observable names do not move until a commit says they do;
A as a flag day is least surprising only *after* the migration, and C never gets there.
The allowlist is the only compatibility rule; when it is empty it is deleted, and
`legacy-name` becomes an error.

### 3.3 The batch rewrite rules and their counts

Within a module batch, a declaration's written name is rewritten by the first applicable
rule:

| written name | rewrite | target | name preserved? | declarations | files |
|---|---|---|---|---:|---:|
| `M.f` (module path is a prefix) | strip `M.` | `M.f` | **yes** | 1,026 | 40 |
| extends another module's type/namespace (`File.f` in `Handle`, `List.f` in `ListLemmas`) | `namespace __root__.P` + strip `P.`, **or** follow the owner's move (`namespace Sys.File`) | `P.f` or `Owner.P.f` | yes if root, no if the owner moved | 528 | 41 |
| own type family (`Fe.f` in `Feral`, `File.f` in `Sys`, `U8Array.f` in `WordArray`) | `namespace P` + strip `P.` | `M.P.f` | no (rename) | 3,093 | 65 |
| module's first/leaf segment (`Hdl.f` in `Hdl.Core`, `Apb.f` in `Hdl.Apb`, `Scry.f` in `Scry.TaintCmd`) | strip the segment | `M.f` | no (rename) | 3,553 | 83 |
| principal type (`inductive Int` in `Int`, `structure Pipe` in `Hdl.Pipe`) | `__root__` the type | `Int`, `Pipe` | **yes** | 17 | 17 |
| bare (`def f`) | none; it becomes `M.f` | `M.f` | no (rename), except Prelude | 472 | 60 |
| Prelude (all 260) | `namespace __root__` around the file | root | **yes** | 260 | 1 |
| selfhost (all 2,396) | `namespace __root__` per file, or a root flag until stage 4 | root | **yes** | 2,396 | 12 |

The classes overlap in files (a module can have several), so summing files is not
meaningful. The declaration sums are disjoint except that Prelude's 192 dotted core
names (`Nat.*`, `List.*`, …) sit in the 528 extension row and its 68 bare names in the
bare row; count them once, in the Prelude batch. The dotted subset of the five trees is
**8,217 in 152 files** (1,026 + 528 + 3,553 + 3,093 + 17). Of those, **1,026 + 528 + 17 =
1,571 are name-preserving** (including Prelude's 192) and **3,553 + 3,093 = 6,646 are
renames**. The 472 bare names (Prelude's 68 excluded) are renames; the 2,396 selfhost
declarations stay root.

For `def Scry.lineIndexGo` in `Scry/TaintCmd.wiz` the batch is the fourth row: rewrite to
`def lineIndexGo` (target `Scry.TaintCmd.lineIndexGo`), replace `Scry.lineIndexGo` by
`lineIndexGo` inside the module and by `TaintCmd.lineIndexGo` outside. That is a rename.
If the owner wants the old spelling, the explicit alternative is
`namespace __root__` around the file or `def __root__.Scry.lineIndexGo`; the allowlist
keeps it until then.

### 3.4 The files that must stay root

* `lib/Prelude.wiz` (260 declarations) declares the language's vocabulary (`Nat`, `Bool`,
  `List`, `Option`, `String`, `Char`, the numeric classes). It is root by definition;
  wrap it in `namespace __root__`. This is not a compatibility hack: the self-hosted
  prelude's names are root, and `modCanonical` maps `IO`/`Std`/`Sys` to the embedded
  prelude by a string match (`selfhost/Frontend.wiz`), so a `Prelude.Nat` would not be
  the `Nat` every program and every test uses.
* `selfhost/*.wiz` (12 files, 2,396 declarations) are concatenated into one file with
  their imports dropped (`Wiz/Selfhost.lean`, "their imports dropped: they are
  concatenated"). The same text is elaborated as 12 modules and as one concatenated
  module; a per-module prefix would give the same declaration two names. The tree is
  frozen (the old plan's hard rule) and stays root. Stage 4 may add
  `namespace __root__` to each file so the intent is in the source; until the selfhost
  frontend parses it, a root flag in the driver is the bridge.
* `lib/IO.wiz`, `lib/Std.wiz`, `lib/Sys.wiz` do **not** need root: their declarations are
  `IO.*`, `Std.*`, `Sys.*` and a single-segment module's own prefix is exactly the module
  name, so they are in the name-preserving 1,026. (The self-hosted frontend canonicalises
  those module names to its embedded prelude, a separate world; see §5.5.)
* `scry/gen/C/Schema.wiz` (33 declarations) is generated by the `schema` command; change
  the generator, not the checked-in file. It should emit the module-namespace form or
  `namespace __root__`; the `schema-check` target is the gate.
* `web/framework/gen.wiz` and `web/widget/gen.wiz` (79 declarations) are generated by the
  web build; change the generator and regenerate, or they will drift.

---

## 4. The migration in batches (the plan of record)

Each row is one PR, independently landable and revertable. The allowlist shrinks by the
batch's rows; a batch that leaves a stale row fails the name check.

| batch | what | declarations | files | ledger rows re-keyed |
|---|---|---:|---:|---:|
| 0 | allowlist + `scripts/check-names.py`; no behaviour change | 11,153 rows | 169 | 0 |
| 1 | `namespace __root__` around `Prelude` and the 12 selfhost files | 2,656 | 13 | 0 |
| 2 | name-preserving strip: `def M.f` → `def f` | 1,026 | 40 | 0 (60 rows already match) |
| 3 | principal types: `inductive __root__.Int`, `def add` | 17 | 17 | 2 rows unchanged |
| 4 | shared extensions: `namespace __root__.P`, strip `P.` | 528 | 41 | 0 (68 rows unchanged) |
| 5 | own-type families: `namespace P`, strip `P.` | 3,093 | 65 | 493 |
| 6 | first/leaf prefix renames: `Hdl.f` → `Hdl.Core.f`, `Scry.f` → `Scry.TaintCmd.f` | 3,553 | 83 | 66 |
| 7 | bare names: qualify; add `open M` to importers | 472 | 60 | 17 |
| 8 | examples, docs, tests, Lean strings, loaders | 2,482 + 309 refs | 106 + 67 sites | 0 |
| 9 | delete the empty allowlist and the compatibility code | 0 | 0 | 0 |

The programme touches the same 11,153 declarations (six trees) and 730 ledger rows, but
no single PR is a flag day. The batch rows are a work breakdown, not a partition:
Prelude's 260 declarations are counted in batch 1 and are also a subset of the class
table's bare/other-dotted rows, so do not add the rows to a total. Batches 2–7 are
independent once 1 lands; do 2 and 4 first (they are name-preserving and prove the
machinery), then 3, then 6, 5, 7, 8. Batch 5's 493 ledger rows are the review bottleneck
(Sys 108, WordArray 93, Word 78, Feral 70, IO 32, WordMap 25, …; Prelude's 20 are root
and unchanged); split it by module if review bandwidth is tight.

---

## 5. The five interaction verdicts

### 5.1 `private` — composes; one change to the key

`private` is per **module** (`Globals.module`, `Globals.privates`, `privateName`; the
self-hosted `Scope.cur`/`privName`). A namespace is not a privacy boundary, as in Lean.
The only change is the kernel name: it must be derived from the **full** name, not the
written one:

```text
private def secret in module M            -> _private.M._0.M.secret
private def secret in M, namespace N      -> _private.M._0.M.N.secret
private def __root__.secret in M          -> _private.M._0.secret
```

The resolver must therefore try the private kernel name for each candidate full name
(`Globals.resolve` lifted over `resolveName`'s candidates), not only for the written name.
This matters for every private declaration once modules have a default prefix: today
there are **24 private lines in 7 files** (`Handle`, `IO`, `MVar`, `Ref`, `Region`,
`Session`, `Word`, in `lib/` and `scry/src/`) plus the private `mk`/extern forms.
Semantics: unchanged; messages may print the full private name (Lean does), so strip the
current module's prefix for display if the tests are noisy.

### 5.2 `import` — brings the namespace, not an open

Verdict: **`import M` makes `M.x` available (transitively, as today) and registers the
leaf alias for a direct import; it does not make `x` unqualified.** `open M` is the
separate, explicit operation. This is Lean's split, with one convenience: the leaf alias.

What changes for today's code: a declaration that was bare and used unqualified from
another module is now `M.name`, so the importer needs `open M` (or a qualification). The
migration adds `open M` where a file used M's bare names; the upper bound is the number
of import edges, **502**, and the declaration count is **472 bare names in 60 files**
(Prelude's 68 excluded). Names that are already dotted at the owner (`M.f`, `Scry.f`,
`Bits.f`) are not affected by `import` at all; they are the rename batches.

Two edge cases to decide in review:

* **Duplicate leaves.** `Main` is the only one today (2 files). Only the full path is
  available; a `Main.x` use is an ambiguity error. Do not auto-pick.
* **Transitive aliases.** A direct import gets the leaf alias; a module visible only
  through another import does not. If a file needs `CstStore.x` for a module it does not
  import directly, it adds `import Scry.CstStore` or `open Scry.CstStore as CstStore`.
  This keeps the alias table small and predictable.

### 5.3 Instances — global, unchanged

Verdict: **instance search is unaffected.** `Wiz/Elab/Class.lean` filters
`CommandState.instances` by `cls` (the class head), then by local instances; it never
looks at the instance's name or a namespace. `local instance` is module-scoped through
`localInsts`. The model only changes the *name* an instance is declared under: a named
instance in `M.N` is `M.N.name`; an anonymous one gets `M.N.inst<Class>…`
(`Elab/Command.lean`, the `base` computation). That removes the last class of instance
name collisions. Today: **191 `instance` commands, 0 `local instance`**. No breaking
change to resolution; names change only where a module is migrated.

### 5.4 Trust ledger — the `module` column already is the namespace

Verdict: **no schema change; the `module` column is exactly the module path, which is now
the default namespace.** The `declaration` column should become the fully qualified
name (`Feral.Fe.appE`, `Scry.TaintCmd.lineIndexGo`), so a row identifies a constant even
if a later move changes the module. The key remains `(module, declaration, item)`; a
rename is a re-key and needs `scripts/trust-ledger.sh --update --reason ...`, as the
ledger rules require ("a rename is a new trust claim").

Numbers: **730 rows in 41 modules**. 60 rows are module-prefixed (name-preserving), 68
are cross-module extensions kept at root (name-preserving), 24 are Prelude's (root,
unchanged) and 2 are principal types kept at root (unchanged); **576 rows are re-keyed
over the whole programme** (51 first-prefixed, 15 leaf-prefixed, 493 own-family, 17
bare). Batches 2–4 re-key nothing; batch 5 re-keys 493; batch 6 re-keys 66; batch 7
re-keys 17. The ledger also drives the `native` test group; the `--update` run belongs in
the same PR as the batch, with the reason naming the batch.

### 5.5 Self-hosted frontend — the flat table must be re-keyed

Verdict: **a real code change in `selfhost/Frontend.wiz`, and the 12 self-hosted source
files stay root.** The table is flat (`Scope.globals : StrMap Nat`, keyed by kernel name;
`Scope.names` keyed `module:M:x`). Under the model:

* `Globals.declName`/`Globals.add` prefix a non-private declaration with the current
  namespace (`Scope.cur` + any `namespace` prefix); `Globals.ind`/`addInd` do the same for
  types; `Globals.setModule` (`modRunBody`) sets the default prefix.
* `Scope.lookupExact` tries the prefixed name first, then the root, then opens; `privName`
  uses the full name (`_private.M._0.M.N.x`) to match the host; `privSplit`/`privBase`
  must accept a dotted base (the `Kernel.wiz` `show` and the "private to module" message).
* `Scope.declaredIn` can stay keyed by `(module, source name)`; duplicate detection is
  unchanged.
* `modCanonical` (IO/Std/Sys → Prelude) and the embedded `preludeText` stay root; the
  selfhost never reads `lib/IO.wiz`, so the host's `IO.*` rename is invisible to it.
* The self-hosted **sources** are 2,396 declarations in 12 files and are frozen; stage 4
  implements the rule for user modules, stage 5 wraps the 12 files in `namespace __root__`
  (or keeps the driver's root flag). Applying the default prefix to them blind would give
  the same declaration two names, because `Wiz/Selfhost.lean` concatenates the files with
  their imports dropped.

---

## 6. Syntax proposed

### 6.1 Grammar

```text
command.namespace := "namespace" ident                      (namespace / open / as are non-reserved)
command.open      := "open" ident ["as" ident]
command.end       := "end" [ident]                          (precedence 0, below a mutual body)
```

`__root__` needs no grammar rule: it is an identifier (`[A-Za-z_][A-Za-z0-9_'.]*`,
`Wiz/Parser/Token.lean`), and the resolver/`prefixDeclName` interpret a leading segment.
`namespace` and `open` stay usable as identifiers (13t); `end` was already reserved by
`mutual`. `end`'s precedence 0 keeps `mutual … end` closing at its own `end` (13t).

### 6.2 Examples

```wiz
-- module Scry.CstStore
def lineIndexGo (n : Nat) : Nat := n           -- Scry.CstStore.lineIndexGo
def __root__.version : Nat := 1                -- version
namespace Internal                             -- Scry.CstStore.Internal
def scratch : Nat := lineIndexGo 0             -- Scry.CstStore.Internal.scratch
end Internal
namespace __root__.List                        -- the shared List family
def map2 (f : Nat → Nat) (xs : List Nat) : List Nat := xs
end List
```

```wiz
-- another file
import Scry.CstStore
def use : Nat := CstStore.lineIndexGo 0        -- leaf alias of the direct import
open CstStore                                  -- lineIndexGo unqualified from here
def use2 : Nat := lineIndexGo 0
open __root__.List as L                        -- L.map2, nothing unqualified
```

### 6.3 Errors

| code | when |
|---|---|
| `ambiguous-name` | an unqualified name has two distinct candidates (two opens, or an open and a declaration); an aliased qualified name has two distinct targets |
| `unclosed-namespace` | a `namespace` with no `end`, reported at the `namespace` |
| `stray-end` | `end` with no open namespace, or `end X` that does not name the innermost |
| `unknown-namespace` | `open X` where no `X` exists (new) |
| `root-name` | `__root__` not as the first segment; a declaration named exactly `__root__` (new) |
| `namespace-repeats-module` | `namespace M` inside module `M`; a warning, ignored (new) |
| `legacy-name` | a declaration uses an allowlist row; a warning during migration, an error under `--strict-names` |

---

## 7. Staged implementation order

The parser → elaborator → import/reference → selfhost → migration order the brief asks
for. The 13t namespace implementation (not on master) already contains the parser
commands, `Globals.namespacePrefix`, `resolveName`, `prefixDeclName`, `nsStack`,
`atModuleStart`, `checkUnclosedNamespaces`, and the host tests; stages 1–2 are mostly a
delta on it (the initial prefix, `__root__`, relative `namespace`/`open`), not a rewrite.
If 13t has not merged, stages 1–2 must land it first.

### Stage 0 — baseline and allowlist (no behaviour change)

Generate `legacy-names.tsv` from the current elaborator (one row per declaration: module,
full name, source path/line), check it in, add `scripts/check-names.py` (no new legacy
name, no unused row, no duplicate row), and mix its digest into `Frontend.isoKey` and
`Cache.moduleKeys`. **Gate:** every group unchanged; the check is a no-op; the file has
11,153 rows for the six trees (8,757 for the five library/tool trees; add `examples/` if
that root is enabled).

### Stage 1 — parser (`Wiz/Parser/Builtin.lean`, `Wiz/Core/ErrorCode.lean`)

`command.namespace`, `command.open`, `command.end` (precedence 0); `nsStack` in
`CommandState`; unclosed/stray/mismatch errors; `namespace`/`open`/`as` non-reserved;
`__root__` accepted by `ident` with no change. **Gate:** `=parser`/`=language`,
`Tests/Groups/Namespace.lean` (host), `docs/error-codes.md` rows.

### Stage 2 — elaborator (`Wiz/Core/Term.lean`, `Wiz/Elab/Command.lean`, `Wiz/Elab/Term.lean`)

Add `Globals.namespacePrefix`, `opens`, `aliases`; `resolveName` with `__root__`,
relative `namespace`, relative-then-root-then-alias `open`, ambiguity; `prefixDeclName`
with `__root__` and the `namespace-repeats-module` warning; private kernel names from the
full name; `mutual`, type self-references, anonymous instance names; route `#check`,
`#print axioms`, `builtin`, `extern`, `app_unexpander`, `derive` through `resolveName`;
`endModule` resets user opens and the prefix. Leave the initial prefix `""` in this
stage, so every existing test still passes. **Gate:** `=namespace`, `=language`,
`=private`, `=elab`, `=modules`.

### Stage 3 — import and reference resolution (`Wiz/Frontend/Frontend.lean`, `Wiz/Module.lean`, `Wiz/Cache.lean`, `Wiz/Query.lean`, `Wiz/LSP.lean`, `Wiz/Format.lean`)

Set `namespacePrefix := m` at module start (`atModuleStart`); register direct-import leaf
aliases (preserve them across `endModule`; reset user `open`s); root flags for `Prelude`
and the self-hosted tree; the allowlist lookup; the cache digest; completion/hover show
full names and offer the leaf alias; `Module.nameOf`/`roots` unchanged. **Gate:**
`=modules`, `=cache`, the scry groups, `=native` (the ledger), the language server's
`=lsp`/`=grail` groups.

### Stage 4 — self-hosted frontend (`selfhost/Frontend.wiz`, `selfhost/Tables.wiz`)

`Scope`/`Globals` prefix, `declName`/`add`/`ind`, `lookupExact`, `privName`/`privSplit`,
`modRunBody`/`setModule`; `namespace`/`open`/`end` commands and the same resolution
order; regenerate the tables; the 13t selfhost cases. **Gate:** `=selfhost`,
`=grail-selfhost`, the bootstrap fixpoint (this is the memory-heavy one; run it through
the shared queue with its measured peak, not in the foreground).

### Stage 5 — migration (batches 1–9 of §4)

`namespace __root__` around Prelude and the selfhost; the name-preserving strips; the
principal types; the shared families; the own-family nests; the first/leaf renames; the
bare names with `open` insertion; examples/docs/tests/Lean strings/loaders; delete the
allowlist. **Gate per batch:** the groups of the tree it touches, `=selfhost-libdiff`
(compare the aggregate verdict, `regressed: 0`, not per-file `same`), the trust ledger
with `--update --reason`, `scripts/check-names.py`, docs-style. Batch 8 also needs the
docs-example re-elaboration (one cold run) and the `Tests/Groups` string updates.

### Stage 6 — remove the compatibility code

Delete `legacy-names.tsv`, the allowlist branch in the resolver, and the `legacy-name`
code; make an unknown name in a namespace position an error; update the stage doc
(13t or a new 13u "module namespaces") and the old plan's archive note.

---

## 8. Breaking changes, flagged

| change | breaking? | affected declarations | files | ledger rows |
|---|---|---:|---:|---:|
| default prefix on bare names (cross-module use) | **yes**, unless the importer adds `open` | 472 | 60 | 17 |
| first/leaf prefix renames (`Hdl.f` → `Hdl.Core.f`, `Scry.f` → `Scry.TaintCmd.f`) | **yes** | 3,553 | 83 | 66 |
| own-type families (`Fe.f` → `Feral.Fe.f`) | **yes** | 3,093 | 65 | 493 |
| principal types (`Int`, `Pipe`) via `__root__` | no (name preserved) | 17 | 17 | 2 unchanged |
| module-prefixed strip (`M.f` → `def f`) | no (name preserved) | 1,026 | 40 | 0 |
| cross-module extensions kept at root (`namespace __root__.List`) | no if kept root | 528 | 41 | 0 |
| Prelude (root) | no if `namespace __root__` | 260 | 1 | 24 unchanged |
| selfhost (root/frozen) | no if exempt | 2,396 | 12 | not in the ledger |
| examples/docs/tests (strings, snippets, loaders) | **yes** (they are gates) | 2,482 + 309 `Scry.` strings | 106 + 67 loader sites | 0 |
| `Main` duplicate (two packages) | potential module-name clash | 2 | 2 | 0 |
| `C.Schema` generated | **yes** (change the generator) | 33 | 1 | 0 |
| `web/*/gen.wiz` generated | **yes** (change the generator) | 79 | 2 | 0 |
| `#check`/`#print` expected strings | **yes** (test output) | 309 `Scry.` mentions in `Tests/Groups` | — | 0 |

**Nothing in the shipped library can adopt the default prefix without a rename** except
the 1,026 module-prefixed declarations, the 528 extensions left at root, and the 17
principal types kept root. That is the honest answer: 7,118 declarations (3,553 + 3,093 +
472) change name somewhere in the programme, 576 ledger rows are re-keyed, and the
allowlist is what makes the change landable one module at a time. The name-preserving
part is 1,571 dotted declarations, Prelude's 68 bare names and the 2,396 selfhost
declarations — 4,035 in all — which can move with no reference edits.

If the scope is cut to **namespaces for new code only** (leave the whole current tree on
the allowlist forever), the cost is zero renames and zero ledger changes, but the
`Msg`/`Settings`/`main` class remains for every old module; that is the status quo with
new syntax, not the fix the brief asks for.

---

## 9. Method

Counts were produced by scanning the branch point `c2efe881` with a one-pass script:

* a declaration is a line at column 0 whose first keyword is `def`, `inductive`,
  `structure`, `class`, `coinductive`, `axiom`, `extern`, `foreign_type`, `glue`,
  `c_struct`, `builtin`, `instance` or `deriving`, after the `private`/`sealed`/`local`/
  `partial`/`mutual` wrappers; comments and indented lines are skipped; a `mutual` block's
  members are at column 0 and are counted;
* a module name is the path under its package root with `/` → `.` (`lib/`, `scry/src/`,
  `scry/gen/`, `selfhost/`, `tower/`, `web/`), the same rule as `Module.nameOf`;
* the class of a name is by its written segments versus the module path: exact module,
  module-prefixed, first-prefixed, leaf-prefixed, other-dotted, bare;
* the ledger counts are read from `.github/trust-baseline.tsv` (730 rows, 41 modules) and
  classified by the same rule; a "cross-module extension" is a dotted name whose prefix
  is a type/class/axiom declared in a different module, or a builtin core name
  (`Nat`, `List`, `Int`, `Bytes`, `File`, …), and is kept at root when the owner does not
  move it.

The file/line counts include only the eight source trees; `Tests/`, `editors/` and
`examples/grail-index` fixtures (67 files) are registry-test evidence and are out of
scope for renaming. `drafts/` is out of scope; a draft that is promoted is migrated with
its target.

---

## 10. Decisions wanted

1. **File-scoped `open`** (13t, shipped) versus Lean's block-scoped `open`. This plan
   keeps file-scoped; changing it now costs one 13t test and the `nsStack` entry.
2. **The leaf alias** for a direct import. This plan takes it; the alternative is Lean's
   "no alias unless `open … as`", which would make `CstStore.lineIndexGo` in the brief
   invalid.
3. **The allowlist** as the migration mechanism, versus a flag-day rewrite. This plan
   takes the allowlist; the cost is a temporary table and a cache-key input.
4. **The shared families** (`List`, `Int`, `Bits`, `Bytes`, `File`): keep them at root
   with `namespace __root__.P`, or move the family under its owner (`Sys.File`,
   `WordArray.U8Array`) and rewrite the extensions. The former is name-preserving; the
   latter is cleaner but re-keys the extension rows and every cross-module reference.
   Decide per family, not globally.
5. **`Scry.Tool.*` / `Data.*` moves** from the old plan: parked. They are compatible with
   either choice above and are not a namespace prerequisite.
6. **`scoped` notation**: defer (this plan) or schedule after stage 4. No current notation
   depends on it.
