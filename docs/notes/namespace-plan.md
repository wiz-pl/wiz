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
force and are recorded in the archive.

This revision folds in four decisions:

1. **`open` is block-scoped** (Lean), not file-scoped.
2. **No leaf aliases.** A direct import brings `M.*` and no short `CstStore.x` spelling.
3. **Shared families move under their owner.** `List`, `Int`, `Bits`, `Bytes`, `File`
   (the families the note lists as shared); `List`/`Int` are root-owned exceptions,
   `Bits`/`Bytes`/`File` move.
4. **`open import M`** is the shorthand: import M and open it at that point.

And one external constraint, enforced by another change in flight:

* **Imports are a fixed header:** top level, before every other declaration, and not
  producible by any syntax extension. Consequently `open import M` is header-only and
  **file-scoped**; block-scoped `open` is for namespace bodies only. The dependency graph
  is a syntactic fact per file, so the migration graph and the collision checker's
  `--reachable` can be read without elaborating.

The short version:

1. A module's default namespace is its module path: `scry/src/Scry/CstStore.wiz` is
   `Scry.CstStore`; `f` there is `Scry.CstStore.f`.
2. `__root__.f` is the only way to declare or name a true global (Lean's `_root_.f`).
3. `namespace X … end X` is relative to the current namespace; shared families live under
   their owner (`Sys.File`, `IO.Bytes`, `BitBlast.Bits`), with `List`/`Int` root-owned.
4. `open X` is block-scoped to the enclosing `namespace` body; `open import M` is
   header-only and file-scoped.
5. **No leaf aliases.** Outside the module, write `Scry.CstStore.f`, or `open import
   Scry.CstStore` in the header, or `open Scry.CstStore` in a body.
6. Today's tree is made safe by a **generated compatibility allowlist**, then migrated in
   batches: **6,740 declarations rename, 4,413 are name-preserving, 608 of 730 ledger rows
   re-key**. The bare-name work is **472 declarations (floor), 193 importer-module edges
   in 120 files, 3,567 use sites**; `open import` would be used by **155 files / 423
   edges** (any imported name), **120 files / 193 edges** for bare names.

---

## 0. The model in one screen

```wiz
-- scry/src/Scry/CstStore.wiz, module Scry.CstStore
import Prelude                                  -- the fixed header: imports first
import Nat

def lineIndexGo (n : Nat) : Nat := n            -- Scry.CstStore.lineIndexGo
def __root__.cstVersion : Nat := 1              -- cstVersion (a true global)

namespace Internal                              -- Scry.CstStore.Internal
def scratch : Nat := 0                          -- Scry.CstStore.Internal.scratch
end Internal
```

```wiz
-- another file
import Scry.CstStore
open import Scry.CstStore                       -- header, file-scoped: import + open
def use : Nat := lineIndexGo 0                  -- Scry.CstStore.lineIndexGo
def use2 : Nat := Scry.CstStore.lineIndexGo 0   -- the full path, always
-- CstStore.lineIndexGo                         -- no leaf alias: this is unknown

namespace Inner
open Scry.CstStore                              -- body-scoped: ends at `end Inner`
def use3 : Nat := lineIndexGo 0
end Inner
-- def use4 : Nat := lineIndexGo 0              -- after the end: qualify or reopen
```

The main structural difference from Lean is the first line: Lean has no implicit
per-file namespace. The smaller differences (`open` placement, no `section`, `scoped`
notation, `open import`) are listed in §1.9.

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

Inside the module, `f` names `M.f`; outside, `Scry.CstStore.f` always works. There is no
leaf alias: `CstStore.f` is unknown unless `CstStore` is itself a namespace (§1.7).

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
  token table.
* A true global name is the only place the old flat collision rules still apply: two
  modules that both declare `__root__.x` collide exactly as they do today. A shared
  namespace reopened at root (`namespace __root__.Bus`) is also global, and collisions
  *inside* it remain; that is the price of a family the plan chooses to keep at root.

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
  `end` at the `end` (`unclosed-namespace`, `stray-end`).
* `namespace` does **not** fall back to the root: inside module `M`, `namespace List`
  means `M.List`, never the global `List`.
* **Shared families live under their owner.** The owner is the module that declares the
  type/class/axiom/foreign_type `P`, or, for a family with no type (`Bits`), the module
  that declares most of its members. An extension module reopens the owner's namespace
  with `namespace __root__.Owner.P`:

  ```wiz
  -- lib/Handle.wiz, extending Sys.File
  namespace __root__.Sys.File
  def withOwned (f : File) : File := f
  end File
  ```

  The five named families resolve as follows:

  | family | owner | target | extension declarations |
  |---|---|---|---:|
  | `List` | `Prelude` (root) | `List.*` | 85 stay root |
  | `Int` | `Int` (root-level namespace) | `Int.*` | 104 stay |
  | `Bits` | `BitBlast` (167 of 208) | `BitBlast.Bits.*` | 41 rename |
  | `Bytes` | `IO` | `IO.Bytes.*` | 8 rename |
  | `File` | `Sys` | `Sys.File.*` | 7 rename |

  `List` and `Int` are exceptions because their owners are root (`Prelude`) or the family
  name itself (`Int`); moving them would make `Prelude.List`/`Int.Int` and break every
  program. The other shared families (`Bus`, `Circuit`, `Prog`, `Spi`, `Axi4`, …) stay at
  root by this plan (§3.3), unless their owner asks for the same move later.
* `namespace M` at the top of module `M` is **not** a no-op: it would open `M.M`. The
  elaborator reports it as a warning (`namespace-repeats-module`) and ignores it.
* A namespace is a prefix, not a privacy boundary: `private` is still per module (§5.1).

### 1.4 `open X` and `open X as A`

`open X` makes the names under `X` visible unqualified in the **enclosing block**:

```wiz
namespace A
def x : Nat := 0
end A
namespace B
open A
def y : Nat := x       -- A.x
end B
-- def z : Nat := x    -- after `end B`: unknown; open A again or qualify
```

* **Block-scoped.** `open X` is active from its line to the `end` of the enclosing
  `namespace` block; at file top it has no enclosing block and reaches EOF. This is Lean's
  behaviour. The 13t implementation is file-scoped and its test "an `open` is file-scoped:
  it outlives its namespace's `end`" must be reversed.
* **`open` resolves like a reference**, not like a declaration prefix: it tries
  `currentNs ++ "." ++ X`, then the root `X`, then an `open … as` alias. An unknown name is
  an error (`unknown-namespace`). Thus `open List` inside `ListLemmas` opens the root `List`
  if `ListLemmas.List` does not exist — unlike `namespace List`, which would *create*
  `ListLemmas.List`.
* **An unqualified name that two opens provide, or an open and a declaration, is an
  error** naming both candidates (`ambiguous-name`), never a silent last-wins. The same
  declaration found twice (this namespace and an open of it) is one candidate. The
  candidate order is: enclosing namespaces (innermost first), root, then each open; only
  distinct full names conflict.
* **`open X as A` is a prefix alias, not an open.** `A.x` is `X.x`; `x` is not. An alias
  is for a long or clashing prefix. The longest matching alias wins for a qualified name.
  This is the *only* alias; there is no import leaf alias (§1.7).
* `open` does not change declaration names: with `open A`, `def y` is still `M.y`, not
  `A.y`.
* **No `open … in` in v1.** It is a small command wrapper and can be added later without
  changing the resolution rules; nothing in the tree needs it. `open import` is a separate
  header command, not an `open … in` form (§1.7.1).

### 1.5 Resolution, precisely

`Ns` is the current namespace: the module path, then each `namespace` on the stack.
`root` is the empty namespace. `Opens` is the open set of the current block (the enclosing
`namespace`, or the file-scope set from `open import` and file-top `open`).

**Unqualified `x`** (in a term, pattern, `#check`, `builtin`, `extern`, …):

1. a local binder (unchanged; locals shadow globals);
2. `Ns.x`, then the enclosing namespaces outward;
3. `root.x`;
4. `N.x` for each `open N` in `Opens` (in source order);
5. `root.x` as a builtin (`Unit`, `True`, …) if nothing was found.

Distinct full names in the candidate set are an ambiguity error. A private declaration
of another module is not a candidate; this module's private declaration is (under its
kernel name, §5.1).

**Qualified `A.x`:**

1. `Ns.A.x` (relative), then the enclosing namespaces outward;
2. `A.x` (root);
3. an `open … as` alias, longest prefix first.

Again, distinct full names are an error. There is **no import leaf alias and no suffix
search**: `CstStore.x` is unknown; write `Scry.CstStore.x`, or put `open import
Scry.CstStore` in the header or `open Scry.CstStore` in the enclosing body.

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
  through `open` and through an alias; `open import M` does not expose M's private names.
* **`local` stays module-scoped** (`docs/stages/13-language.md`, 13m): it does not follow
  a namespace or an `open`. `local instance` is module-scoped too (the existing
  `localInsts` mechanism).
* **`scoped` notation is deferred.** Lean's `scoped` notation is active where a namespace
  is open; Wiz has no notation-scope machinery, and the self-hosted parser has no
  `syntax` command at all. `local` covers the module case, which is the only one the
  library uses today. Adding `scoped` later means teaching the parser tables to
  activate/deactivate rules on `open`/`end` (the `localRules` machinery is the starting
  point); estimate one to two days plus a self-hosted table change. Do not couple it to
  this plan.

### 1.7 `import` is a fixed header, and brings no short name

**Imports are a fixed header:** top level, before every other declaration, and not
producible by a syntax extension. This is an external constraint, not a Wiz design choice.
Consequences:

* `Module.importsOf`'s line scan is now **exact**, not a superset; the dependency graph of
  a file is a syntactic fact. The migration graph and the collision checker's
  `--reachable` can be computed from headers without elaborating (§7, stage 3).
* An `import` cannot appear inside a namespace, a body or a macro expansion. `open import`
  is therefore header-only (§1.7.1); its open is file-scoped.

`import M` brings M's declarations at their full names, and **no short name and no alias**:

| after `import Scry.CstStore` | works? |
|---|---|
| `Scry.CstStore.lineIndexGo` | yes |
| `CstStore.lineIndexGo` | **no** — no leaf alias |
| `lineIndexGo` | no — use `open import Scry.CstStore` in the header, or `open Scry.CstStore` in the body |
| a name from a module that `Scry.CstStore` imports | yes, at its full name (imports re-export declarations, as today) |

* The import is transitive in visibility, not in aliases: a module visible only through
  another import is still usable at its full name; it gets no short spelling.
* Duplicate leaves (`Main` in `selfhost/Main.wiz` and `tower/Main.wiz`) are now only a
  module-name issue for the package graph, not an alias ambiguity: there is no alias to be
  ambiguous. `import` resolves a module by its dotted path.
* `import` does not change the module's own default namespace: a file that imports
  `Scry.CstStore` and declares `def f` still declares `M.f`.
* **`open import M`** is the shorthand for `import M` plus a file-scope `open M`; it is the
  only ergonomic way to get M's names unqualified when you do not want to write the full
  path. See §1.7.1.

### 1.7.1 `open import M`

```wiz
import Prelude
open import Scry.CstStore      -- header: import M, and open M for the whole file
open import Scry.Rules
```

* **Syntax.** `command.openImport` := `"open" "import" ident`. `open` is non-reserved;
  `import` is the import keyword; the rule is a leading parser before `command.open`
  (the `ident` of `open ident` cannot match the reserved `import`). It is header-only:
  it must appear among the imports, before every other declaration; an `import` or
  `open import` after the header is an error (`import-not-in-header`).
* **Semantics.** `open import M` = `import M` (once, as today; a second occurrence is just
  the open) + `open M` at that point. Because it is in the header, the open has no
  enclosing block: it is **file-scoped**. Its names are in the file-scope open set of
  §1.5, visible to every namespace body in the file. The import part is file-wide, like any
  import; the module is loaded once.
* **Can it be combined with `in`?** No. `open import M in <command>` is rejected
  (`open-import-in`): `import` is a header command and cannot be scoped to a command. If a
  future `open … in` lands, the form is `import M` in the header plus `open M in <command>`
  in the body; `open import` never takes `in`. To confine an open to a namespace body, use
  a plain `open M` there (block-scoped, §1.4).
* **`private`.** `open import M` does not expose M's private names; the privacy check is
  unchanged (§5.1).
* **Ambiguity.** Two `open import`s (or an `open import` and a file-top `open`) that
  provide the same name are ambiguous at the use (`ambiguous-name`), naming both. The
  import itself does not report ambiguity; only the use does.
* **Why it earns its syntax.** With leaf aliases gone, a file has three choices: fully
  qualify (`Scry.CstStore.x`), `open import M` in the header (short names, file scope), or
  `open M` in a body (short names, block scope). For a file that uses M's names at all,
  `open import` is the only header-level way to avoid both full paths and a separate
  `open` line. **155 files / 423 importer-module edges** use at least one imported name;
  **120 files / 193 edges** use a *bare* name (the ones that cannot be fully qualified
  without a rewrite). Those 155 files would want the shorthand; the 120 are the ones for
  which it is close to mandatory. A conservative token scan (names of four or more
  characters, common words removed) gives 107 files / 138 edges, so the honest range is
  **107–155 files**.

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
| `_root_` | `__root__` | the requested spelling |
| `open` scoped to the enclosing section/namespace | block-scoped to the enclosing `namespace`; file-scoped at top | Wiz has no `section`; the file is the module. Now matches Lean's block scope. |
| `section`, `variable` | not proposed | Wiz has no section variables; `namespace` is enough |
| `scoped` notation | deferred; `local` is module-scoped | parser-table work, not needed by the library |
| `import` brings names at full names | same, with **no** leaf alias | the decided rule; `open import` is the shorthand |
| `open … in` | not in v1; `open import` is a separate header command | imports are header-only, so an import cannot be command-scoped |

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
| `bare` (`def f`) | 540 | 70 | `M.f` (68 Prelude names stay root) | rename or `open import` |
| `exact-module` (`def M`) | 16 | 16 | `M.M` | `__root__` the type |
| `exact-leaf` (`structure Pipe` in `Hdl.Pipe`) | 1 | 1 | `Hdl.Pipe.Pipe` | `__root__` or keep nested |
| `module-prefixed` (`def M.f`) | 1,026 | 40 | strip `M.` → `M.f` (**same name**) | mechanical, no rename |
| `first-prefixed` (`def Hdl.f` in `Hdl.Core`) | 2,752 | 62 | `Hdl.Core.f` | rename |
| `leaf-prefixed` (`def Apb.f` in `Hdl.Apb`) | 801 | 21 | `Hdl.Apb.f` | rename |
| `other-dotted` (`def Fe.f` in `Feral`) | 3,621 | 74 | owner-local or shared family | §3.3 |
| **total** | **8,757** | **157** | | |

**8,217 of the 8,757 (94 %) are already dotted, in 152 files** — the five trees. The
self-hosted tree adds 136 dotted declarations (`8,353` in the six trees). The other trees:
`selfhost/` 2,396 declarations in 12 files; `examples/` 2,482 in 106; `drafts/` 407 in 56;
67 fixture files under `Tests/`, `editors/` and `examples/` that are registry-test evidence
and must not be renamed.

Module graph: 170 distinct module names in 171 files; one duplicate name (`Main` in
`selfhost/Main.wiz` and `tower/Main.wiz` — different packages, never loaded together); two
prefix overlaps (`Web` vs `Web.Loom`, `Web` vs `Web.Widget` — a module name and a
namespace may coexist, so these are legal, but the case-only `Web`/`Web.*` is the same
latent case-insensitive-filesystem issue the old plan noted); 502 `import` lines to 115
distinct targets; 56 modules never imported. Under the fixed-header constraint the 502
`import` lines are the complete graph (no macro can add an edge).

---

## 3. Migration: what happens to already-dotted names

### 3.1 The problem

Under the rule, a `def Scry.lineIndexGo` in module `Scry.CstStore` is
`Scry.CstStore.Scry.lineIndexGo`, and the same declaration in `Scry.TaintCmd` is
`Scry.TaintCmd.Scry.lineIndexGo`. Both are wrong: the author wrote `Scry.` as the
*intended* global prefix, not as a nested namespace. (The historical copy was in
`Scry.CstStore`; today's is in `Scry.TaintCmd`.) The same applies to `Hdl.f` in
`Hdl.Core`, `Apb.f` in `Hdl.Apb`, `Fe.f` in `Feral`, `Bits.f` in `BitBlast`, and the
shared families. A mechanical strip is not enough either: a declaration whose written
prefix is a *different* concept (`Bits` in `BitBlast`) must not become `BitBlast.odd`
unless the owner means to rename the family.

### 3.2 The three options, and the recommendation

**Option A — one-off rewrite of every dotted declaration.** Strip the module's own path;
rename the rest into the module namespace or the owner's family. Touches **8,217
declaration lines in 152 files** (five trees), plus every reference and **608 trust-ledger
rows**. It is the clean end state, but as a flag day it is unreviewable: one mistake in a
family (`Bits`, `Bytes`, `File`) breaks a whole analysis or the HDL library, and the
ledger diff is 608 rows with one shared reason.

**Option B — a temporary compatibility rule.** A text rule "a name starting with the
module's own prefix is absolute" does not work: `Scry.lineIndexGo` does not start with the
module path `Scry.CstStore`, and `Bits.odd` in `BitBlast` does not start with `BitBlast`.
The safe form is a **generated allowlist**:
`legacy-names.tsv` with one row per `(module, full name)`, generated from the current
elaborator before the default prefix flips. A declaration whose written name is in the
row set for its module is declared at that absolute name and emits a `legacy-name`
warning; everything else gets the default prefix. A new legacy name is an error; an
unused row is an error; `--strict-names` makes the warnings errors. The allowlist is read
by the elaborator, so its digest must be mixed into the module cache key
(`Frontend.isoKey`, `Cache.moduleKeys`), or apply it as a source rewrite in
`runFrontend.step` before elaboration.

*Size:* **8,757 rows / 157 files** for the five library/tool trees (11,153 / 169 with
`selfhost`; every declaration, not only the dotted ones); 2,482 more for `examples/` if
that root is checked under the same rule. **Day-one renames: zero. Day-one ledger changes:
zero.**

**Option C — `__root__` every legacy declaration.** Prefix the 8,217 dotted declarations
with `__root__` (one token each, 152 files). Zero reference and ledger changes, but it
cements the flat table: every collision rule stays in force everywhere, and the
`Msg`/`Settings`/`main` class is not fixed. It is the right tool for a *file* that must
stay global (`Prelude`, the frozen self-hosted tree, a generated schema), not for the
library.

**Recommendation: B, then A in batches.** Start with the allowlist (zero behaviour
change, all gates green), then migrate one module or one family per commit, deleting its
allowlist rows. The end state is A's clean rule with a reviewable diff per batch. B is
least surprising because the observable names do not move until a commit says they do.

### 3.3 The batch rewrite rules and the final counts

Within a module batch, a declaration's written name is rewritten by the first applicable
rule:

| written name | rewrite | target | name preserved? | declarations | files |
|---|---|---|---|---:|---:|
| `M.f` (module path is a prefix) | strip `M.` | `M.f` | **yes** | 1,026 | 40 |
| owner-local family (`Fe.f` in `Feral`, `U8Array.f` in `WordArray`) | `namespace P` + strip `P.` | `M.P.f` | no | 2,659 | 56 |
| prelude owner-local (`List.f` in `Prelude`) | `namespace __root__` | root | **yes** | 189 | 1 |
| five-family extension preserved (`List.f` in `ListLemmas`, `Int.f` in `IntRing`) | `namespace __root__.P` | `P.f` | **yes** | 189 | 9 |
| five-family extension moved (`Bits.f` in `BitVecAdd`/`BitVecShift`, `Bytes.f` in `Std`/`WordBytes`, `File.f` in `Handle`) | `namespace __root__.Owner.P` + strip | `Owner.P.f` | no | 56 | 5 |
| other shared family kept root (`Bus.f`, `Circuit.f`, `Prog.f`, `Spi.f`, …) | `namespace __root__.P` | `P.f` | **yes** | 528 | 39 |
| module's first/leaf segment (`Hdl.f` in `Hdl.Core`, `Apb.f` in `Hdl.Apb`, `Scry.f` in `Scry.TaintCmd`) | strip the segment | `M.f` | no | 3,553 | 83 |
| principal type (`inductive Int` in `Int`, `structure Pipe` in `Hdl.Pipe`) | `__root__` the type | `Int`, `Pipe` | **yes** | 17 | 17 |
| bare (`def f`) | none; it becomes `M.f` | `M.f` | no, except Prelude | 472 | 60 |
| Prelude (all 260) | `namespace __root__` around the file | root | **yes** | 260 | 1 |
| selfhost (all 2,396) | `namespace __root__` per file, or a root flag | root | **yes** | 2,396 | 12 |

The classes overlap in files (a module can have several). The disjoint partition is:

| class | declarations | files | renames? |
|---|---:|---:|---|
| module-prefixed (`M.f`) | 1,026 | 40 | no |
| principal (`M` / `L`) | 17 | 17 | no |
| first/leaf (`F.f`, `L.f`) | 3,553 | 83 | **yes** |
| bare, non-Prelude | 472 | 60 | **yes** |
| bare, Prelude | 68 | 1 | no |
| owner-local family (`Fe.f` in `Feral`) | 2,659 | 56 | **yes** |
| owner-local, Prelude (`List.f` in `Prelude`) | 189 | 1 | no |
| five-family extension preserved (`List`/`Int`) | 189 | 9 | no |
| five-family extension moved (`Bits`/`Bytes`/`File`) | 56 | 5 | **yes** |
| other shared family kept root (`Bus`, `Circuit`, …) | 528 | 39 | no |
| selfhost (all, frozen) | 2,396 | 12 | no |
| **six trees** | **11,153** | **169** | **6,740** |

The five-tree total is 8,757 (all except selfhost); the dotted subset of the five trees is
**8,217 in 152 files** (everything except the 540 bare). Name-preserving dotted:
1,026 + 17 + 189 + 189 + 528 = **1,949**; renaming dotted: 2,659 + 56 + 3,553 = **6,268**;
bare: 472 rename + 68 Prelude. Five trees: **6,740 renames**, 2,017 name-preserving; six
trees: **6,740 / 4,413**. The Prelude row (260) is the 68 bare + 189 owner-local + 3
core-extension declarations, so count it once in batch 1.

**Final numbers (before → after the four decisions).** The previous draft's 7,118 / 4,035
double-counted the 245 `List`/`Int`/`Bits`/`Bytes`/`File` extensions as local renames while
also keeping them at root; the clean owner split is below. The "before" column is that
clean base, with decision 3 applied in the "after" column.

| metric | before (clean base) | after decisions | delta |
|---|---:|---:|---:|
| declaration renames (six trees) | 6,684 | **6,740** | **+56** |
| name-preserving | 4,469 | **4,413** | −56 |
| dotted name-preserving | 2,005 | **1,949** | −56 |
| shared extensions at root | 773 | **717** | −56 |
| `Bits`/`Bytes`/`File` extensions moved | 0 | **56** | +56 |
| ledger rows re-keyed | 608 | **608** | 0 |
| bare declarations needing an open | 472 (floor) | **472 (floor)** | 0 |
| importer edges needing an open | 502 (all imports) | **423 any-name / 193 bare** | — |
| importer files needing an open | — | **155 any / 120 bare** | — |
| `open import` users | — | **155 files / 423 edges** | — |

The five-family move is 56 declarations (Bits 41, Bytes 8, File 7), **0 additional
ledger rows**: the extension declarations have no trust rows, and the 18 `IO.Bytes` + 20
`Sys.File` owner rows are already in the 608 (they are owner-local renames). The 32
`MVar`/`Ref`/`Session`/`Handle`/`IO`/`Std` private/native ledger rows keep their names
and are not re-keyed by this move.

The old draft's **528 "extensions kept at root"** were the *other* shared families
(`Bus`, `Circuit`, `Prog`, `Spi`, `Axi4`, …), not the five named families; the five
families' 245 extensions were in the 3,093 owner-local bucket. Decision 3 moves 56 of
those 245 (`Bits`/`Bytes`/`File`); the 189 `List`/`Int` extensions stay root, and the 528
other families stay root. The 528 therefore does **not** become zero; the rename count
rises by 56 from the five-family bucket.

For `def Scry.lineIndexGo` in `Scry/TaintCmd.wiz` the batch is the first/leaf row: rewrite
to `def lineIndexGo` (target `Scry.TaintCmd.lineIndexGo`), replace `Scry.lineIndexGo` by
`lineIndexGo` inside the module and by `Scry.TaintCmd.lineIndexGo` outside (or `open
import Scry.TaintCmd` in the importer's header). That is a rename. If the owner wants the
old spelling, the explicit alternative is `namespace __root__` around the file or
`def __root__.Scry.lineIndexGo`; the allowlist keeps it until then.

### 3.4 The files that must stay root

* `lib/Prelude.wiz` (260 declarations) declares the language's vocabulary (`Nat`, `Bool`,
  `List`, `Option`, `String`, `Char`, the numeric classes). It is root by definition;
  wrap it in `namespace __root__`. The self-hosted prelude's names are root, and
  `modCanonical` maps `IO`/`Std`/`Sys` to the embedded prelude by a string match
  (`selfhost/Frontend.wiz`), so a `Prelude.Nat` would not be the `Nat` every program uses.
* `selfhost/*.wiz` (12 files, 2,396 declarations) are concatenated into one file with
  their imports dropped (`Wiz/Selfhost.lean`, "their imports dropped: they are
  concatenated"). The same text is elaborated as 12 modules and as one concatenated
  module; a per-module prefix would give the same declaration two names. The tree is
  frozen and stays root; stage 4 may add `namespace __root__` to each file, until then a
  root flag in the driver is the bridge.
* `lib/IO.wiz`, `lib/Std.wiz`, `lib/Sys.wiz` do **not** need root: their declarations are
  `IO.*`, `Std.*`, `Sys.*` and a single-segment module's own prefix is exactly the module
  name, so they are in the name-preserving 1,026. The self-hosted frontend canonicalises
  those module names to its embedded prelude, a separate world (§5.5).
* `List` and `Int` are the two named families that do **not** move: `List`'s owner is
  `Prelude` (root), and `Int`'s owner is the module `Int`, whose namespace is the
  root-level `Int`. Moving them would mean `Prelude.List`/`Int.Int`; that is 189 extra
  renames and breaks the core. Not adopted.
* `scry/gen/C/Schema.wiz` (33 declarations) is generated by the `schema` command; change
  the generator, not the checked-in file.
* `web/framework/gen.wiz` and `web/widget/gen.wiz` (79 declarations) are generated by the
  web build; change the generator and regenerate.

---

## 4. The migration in batches (the plan of record)

Each row is one PR, independently landable and revertable. The allowlist shrinks by the
batch's rows; a batch that leaves a stale row fails the name check. **The order changed**
after decision 3: the owner families (batch 4) must exist before the shared extensions
that target them (batch 5).

| batch | what | declarations | files | ledger rows re-keyed |
|---|---|---:|---:|---:|
| 0 | allowlist + `scripts/check-names.py`; no behaviour change | 11,153 rows | 169 | 0 |
| 1 | `namespace __root__` around `Prelude` and the 12 selfhost files | 2,656 | 13 | 0 |
| 2 | name-preserving strip: `def M.f` → `def f` | 1,026 | 40 | 0 (60 rows already match) |
| 3 | principal types: `inductive __root__.Int`, `def add` | 17 | 17 | 2 rows unchanged |
| 4 | **owner-local families**: `namespace P`, strip `P.` | 2,659 | 56 | 525 |
| 5 | **five-family extensions under owner**: `namespace __root__.Owner.P` | 56 | 5 | 0 |
| 6 | shared families kept root: `List`/`Int` (189) + other (525; three Prelude rows are in batch 1) | 714 | 46 | 0 (32 private/native rows unchanged) |
| 7 | first/leaf prefix renames: `Hdl.f` → `Hdl.Core.f`, `Scry.f` → `Scry.TaintCmd.f` | 3,553 | 83 | 66 |
| 8 | bare names + `open import` in importer headers | 472 | 60 | 17 |
| 9 | examples, docs, tests, Lean strings, loaders | 2,482 + 309 refs | 106 + 67 sites | 0 |
| 10 | delete the empty allowlist and the compatibility code | 0 | 0 | 0 |

Batch 4 creates the owner namespaces (`Feral.Fe`, `WordArray.U8Array`, `IO.Bytes`,
`Sys.File`, `BitBlast.Bits`); batch 5's extensions target them; batch 6 keeps the other
shared families at root; batch 7 is the flat `Hdl.*`/`Scry.*` renames; batch 8 uses
`open import` and full qualification for the bare names. Batches 2, 3, 4, 6 and 7 are
independent once 1 lands; 5 depends on 4; 8 depends on the parser (stage 1/2) and on the
owner names from 4/5; 9 is the tree-wide cleanup.

The batch rows partition the 11,153 declarations (Prelude's 260 are in batch 1; the class
table above also lists them in its Prelude row). Batch 4's 525 rows are the review
bottleneck (Sys 128, WordArray 93, Word 78, Feral 70, IO 48, Std 34, WordMap 25,
Intern 16, …); split it by module if review bandwidth is tight.

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
`open import M` does not expose M's private names; `private` is still module-private.
Semantics: unchanged; messages may print the full private name (Lean does), so strip the
current module's prefix for display if the tests are noisy.

### 5.2 `import` — the header, full names, no alias

Verdict: **`import M` is a header command that makes `M.x` available (transitively, as
today); it brings no short name and no leaf alias. `open import M` is the header
shorthand for import + file-scope open; `open M` is the body-scoped form.**

What changes for today's code: a declaration that was bare and used unqualified from
another module is now `M.name`; the importer either writes `M.name`, adds `open import
M` to its header, or adds a body `open M`. The counts:

* **155 files / 423 importer-module edges** use at least one imported name (the set that
  may want `open import`); **120 files / 193 edges** use a bare name (the set for which a
  qualification is a rewrite, not just a spelling change).
* **3,567 bare-name use sites** (1,923 excluding Prelude's root names) are the actual
  occurrences; a conservative token scan gives 107 files / 138 edges.
* **No leaf aliases**: the 801 leaf-prefixed declarations (already in the 3,553 rename
  column) have no alternative short spelling. Every external use is `M.L.f`, an `open
  import M` in the header, or a body `open M`; they add no declaration renames, but their
  importers are in the 423-edge / 155-file open set.
* Block-scoped `open` does **not** multiply the import count: `open import` is header-only
  and file-scoped, so it covers every namespace body in the file. A body `open X` is a
  separate namespace-scoped open; it ends at the enclosing `end`, and a sibling body
  needs its own. The migration's bodies are 56 owner-family files + 5 shared-owner files +
  13 root files (overlapping), so at most one body `open` per block that opens a namespace;
  that is independent of the 155 import files.
* Duplicate leaves (`Main`) are no longer an alias ambiguity; they are a module-name
  concern for the two packages, which never load together.
* Transitive imports: a module visible only through another import is usable at its full
  name; it gets no short spelling unless the file imports it directly and adds `open
  import`.

### 5.3 Instances — global, unchanged

Verdict: **instance search is unaffected.** `Wiz/Elab/Class.lean` filters
`CommandState.instances` by `cls` (the class head), then by local instances; it never
looks at the instance's name or a namespace. `local instance` is module-scoped through
`localInsts`. The model only changes the *name* an instance is declared under: a named
instance in `M.N` is `M.N.name`; an anonymous one gets `M.N.inst<Class>…`
(`Elab/Command.lean`, the `base` computation). Today: **191 `instance` commands, 0 `local
instance`**. No breaking change to resolution; names change only where a module is
migrated.

### 5.4 Trust ledger — the `module` column already is the namespace

Verdict: **no schema change; the `module` column is exactly the module path, which is now
the default namespace.** The `declaration` column becomes the fully qualified name
(`Feral.Fe.appE`, `Scry.TaintCmd.lineIndexGo`), so a row identifies a constant. The key
remains `(module, declaration, item)`; a rename is a re-key and needs
`scripts/trust-ledger.sh --update --reason ...` ("a rename is a new trust claim").

Numbers: **730 rows in 41 modules**. **608 rows re-key** (51 first-prefixed, 15
leaf-prefixed, 525 owner-local, 17 non-Prelude bare); **122 stay**: 60 module-prefixed, 2
principal, 24 Prelude, 4 root core extensions, 32 private/native rows that keep their
names. The five-family move adds **0** rows: the 56 extension declarations have no trust
rows, and the 18 `IO.Bytes` + 20 `Sys.File` owner rows are already in the 525. Batch 4
re-keys 525; batch 7 re-keys 66; batch 8 re-keys 17; batches 2, 3, 5, 6 re-key nothing
(batch 3's 2 rows and batch 6's 32 rows are unchanged). The exact set is produced by
`--update`; the `native` test group is the gate.

### 5.5 Self-hosted frontend — the flat table must be re-keyed

Verdict: **a real code change in `selfhost/Frontend.wiz`, and the 12 self-hosted source
files stay root.** The table is flat (`Scope.globals : StrMap Nat`, keyed by kernel name;
`Scope.names` keyed `module:M:x`). Under the model:

* `Globals.declName`/`Globals.add` prefix a non-private declaration with the current
  namespace (`Scope.cur` + any `namespace` prefix); `Globals.ind`/`addInd` do the same for
  types; `Globals.setModule` (`modRunBody`) sets the default prefix.
* `Scope.lookupExact` tries the prefixed name first, then the root, then the current
  block's opens; `privName` uses the full name (`_private.M._0.M.N.x`) to match the host;
  `privSplit`/`privBase` must accept a dotted base.
* `Scope.declaredIn` can stay keyed by `(module, source name)`; duplicate detection is
  unchanged.
* `modCanonical` (IO/Std/Sys → Prelude) and the embedded `preludeText` stay root; the
  selfhost never reads `lib/IO.wiz`, so the host's `IO.*` rename is invisible to it.
* The self-hosted **sources** are 2,396 declarations in 12 files and are frozen; stage 4
  implements the rule for user modules, stage 5 wraps the 12 files in `namespace __root__`
  (or keeps the driver's root flag). Applying the default prefix to them blind would give
  the same declaration two names, because `Wiz/Selfhost.lean` concatenates the files with
  their imports dropped.
* Block-scoped `open` is a `nsStack` change in the selfhost too: an entry saves the open
  list as well as the prefix, and `end` restores it. `open import` is header-only; the
  selfhost's `modImportsAt` already scans the header, so it can read the imports (and
  `open import` is a header entry) without elaboration.

---

## 6. Syntax proposed

### 6.1 Grammar

```text
command.import     := "import" ident                              (header only)
command.openImport := "open" "import" ident                       (header only)
command.namespace  := "namespace" ident                           (namespace / open / as are non-reserved)
command.open       := "open" ident ["as" ident]                   (body only)
command.end        := "end" [ident]                               (precedence 0, below a mutual body)
```

`__root__` needs no grammar rule: it is an identifier (`[A-Za-z_][A-Za-z0-9_'.]*`,
`Wiz/Parser/Token.lean`), and the resolver/`prefixDeclName` interpret a leading segment.
`namespace` and `open` stay usable as identifiers; `end` was already reserved by `mutual`.
`end`'s precedence 0 keeps `mutual … end` closing at its own `end`.

The header is a grammar phase: zero or more `import`/`open import` commands, then the
body. A later `import` or `open import` is `import-not-in-header`; a syntax extension
cannot produce either command (the external constraint).

### 6.2 Examples

```wiz
-- module Scry.CstStore
import Prelude
import Nat
def lineIndexGo (n : Nat) : Nat := n           -- Scry.CstStore.lineIndexGo
def __root__.version : Nat := 1                -- version
namespace Internal                             -- Scry.CstStore.Internal
def scratch : Nat := lineIndexGo 0             -- Scry.CstStore.Internal.scratch
end Internal
```

```wiz
-- another file
import Scry.CstStore
open import Scry.CstStore                      -- header, file-scoped
def use : Nat := lineIndexGo 0                 -- Scry.CstStore.lineIndexGo
def use2 : Nat := Scry.CstStore.lineIndexGo 0  -- full path, always
-- CstStore.lineIndexGo                        -- no leaf alias
namespace Inner
open Scry.CstStore                             -- body-scoped: ends at `end Inner`
def use3 : Nat := lineIndexGo 0
end Inner
-- def use4 : Nat := lineIndexGo 0             -- qualify or reopen
```

```wiz
-- lib/Handle.wiz, extending Sys.File
import Sys
namespace __root__.Sys.File
def withOwned (f : File) : File := f
end File
```

### 6.3 Errors

| code | when |
|---|---|
| `ambiguous-name` | an unqualified name has two distinct candidates (two opens, an open and a declaration, two `open import`s); an aliased qualified name has two distinct targets |
| `unclosed-namespace` | a `namespace` with no `end`, reported at the `namespace` |
| `stray-end` | `end` with no open namespace, or `end X` that does not name the innermost |
| `unknown-namespace` | `open X` where no `X` exists |
| `root-name` | `__root__` not as the first segment; a declaration named exactly `__root__` |
| `namespace-repeats-module` | `namespace M` inside module `M`; a warning, ignored |
| `import-not-in-header` | an `import` or `open import` after the header (new) |
| `open-import-in` | `open import M in …` (new; no such form) |
| `legacy-name` | a declaration uses an allowlist row; a warning, or an error under `--strict-names` |

---

## 7. Staged implementation order

The parser → elaborator → import/reference → selfhost → migration order. The 13t
namespace implementation (not on master) already contains the parser commands,
`Globals.namespacePrefix`, `resolveName`, `prefixDeclName`, `nsStack`, `atModuleStart`,
`checkUnclosedNamespaces`, and the host tests; stages 1–2 are mostly a delta on it (the
initial prefix, `__root__`, relative `namespace`/`open`, block scope, no aliases, `open
import`), not a rewrite. If 13t has not merged, stages 1–2 must land it first.

### Stage 0 — baseline and allowlist (no behaviour change)

Generate `legacy-names.tsv` from the current elaborator (one row per declaration: module,
full name, source path/line), check it in, add `scripts/check-names.py` (no new legacy
name, no unused row, no duplicate row), and mix its digest into `Frontend.isoKey` and
`Cache.moduleKeys`. **Gate:** every group unchanged; the check is a no-op; the file has
11,153 rows for the six trees (8,757 for the five library/tool trees; add `examples/` if
that root is enabled).

### Stage 1 — parser (`Wiz/Parser/Builtin.lean`, `Wiz/Core/ErrorCode.lean`)

`command.namespace`, `command.open`, `command.end` (precedence 0), `command.openImport`;
the header phase (`import`/`open import` first; `import-not-in-header`, `open-import-in`);
`nsStack` in `CommandState`; unclosed/stray/mismatch errors; `namespace`/`open`/`as`
non-reserved; `__root__` accepted by `ident` with no change. **Gate:** `=parser`,
`=language`, `Tests/Groups/Namespace.lean` (host), `docs/error-codes.md` rows.

### Stage 2 — elaborator (`Wiz/Core/Term.lean`, `Wiz/Elab/Command.lean`, `Wiz/Elab/Term.lean`)

Add `Globals.namespacePrefix`, `opens` (block-scoped, saved/restored in `nsStack`),
`open import` (header, file-scoped); `resolveName` with `__root__`, relative `namespace`,
relative-then-root `open`, ambiguity; `prefixDeclName` with `__root__` and the
`namespace-repeats-module` warning; private kernel names from the full name; `mutual`, type
self-references, anonymous instance names; route `#check`, `#print axioms`, `builtin`,
`extern`, `app_unexpander`, `derive` through `resolveName`; `endModule` resets user opens
and the prefix. Leave the initial prefix `""` in this stage, so every existing test still
passes. **Gate:** `=namespace`, `=language`, `=private`, `=elab`, `=modules`.

### Stage 3 — import and reference resolution (`Wiz/Frontend/Frontend.lean`, `Wiz/Module.lean`, `Wiz/Cache.lean`, `Wiz/Query.lean`, `Wiz/LSP.lean`, `Wiz/Format.lean`)

Set `namespacePrefix := m` at module start (`atModuleStart`); **no leaf aliases**;
`open import` headers become the file-scope open set; root flags for `Prelude` and the
self-hosted tree; the allowlist lookup; the cache digest. **The header rule makes this
stage cheaper:** `Module.importsOf` is exact, so the import graph, the migration graph and
`--reachable` in the collision checker are read from headers without elaborating; no
import-alias state is carried through elaboration. Completion/hover show full names and
offer `open import`; `Module.nameOf`/`roots` unchanged. **Gate:** `=modules`, `=cache`,
the scry groups, `=native` (the ledger), `=lsp`/`=grail`.

### Stage 4 — self-hosted frontend (`selfhost/Frontend.wiz`, `selfhost/Tables.wiz`)

`Scope`/`Globals` prefix, `declName`/`add`/`ind`, `lookupExact`, `privName`/`privSplit`,
`modRunBody`/`setModule`; `namespace`/`open`/`end` commands with block scope, `open
import` in the header, and the same resolution order; regenerate the tables; the 13t
selfhost cases. **Gate:** `=selfhost`, `=grail-selfhost`, the bootstrap fixpoint (the
memory-heavy one; run it through the shared queue with its measured peak).

### Stage 5 — migration (batches 1–10 of §4)

`namespace __root__` around Prelude and the selfhost; the name-preserving strips; the
principal types; **owner-local families first** (batch 4, which creates `IO.Bytes`,
`Sys.File`, `BitBlast.Bits`); **then the five-family extensions** (batch 5); the other
shared families at root (batch 6); the first/leaf renames (batch 7); the bare names with
`open import` (batch 8); examples/docs/tests (batch 9); delete the allowlist. **Gate per
batch:** the groups of the tree it touches, `=selfhost-libdiff` (aggregate verdict,
`regressed: 0`), the trust ledger with `--update --reason`, `scripts/check-names.py`,
docs-style. Batch 9 also needs the docs-example re-elaboration and the `Tests/Groups`
string updates.

### Stage 6 — remove the compatibility code

Delete `legacy-names.tsv`, the allowlist branch in the resolver, and the `legacy-name`
code; make an unknown name in a namespace position an error; update the stage doc (13t or
a new 13u "module namespaces") and the old plan's archive note.

---

## 8. Breaking changes, flagged

| change | breaking? | affected declarations | files | ledger rows |
|---|---|---:|---:|---:|
| default prefix on bare names (cross-module use) | **yes**, unless the importer adds `open import`/`open` | 472 | 60 | 17 |
| first/leaf prefix renames (`Hdl.f` → `Hdl.Core.f`, `Scry.f` → `Scry.TaintCmd.f`) | **yes** | 3,553 | 83 | 66 |
| owner-local families (`Fe.f` → `Feral.Fe.f`, `Bits.f` in `BitBlast`) | **yes** | 2,659 | 56 | 525 |
| five-family extensions moved (`Bits.f` → `BitBlast.Bits.f`, `Bytes.f` → `IO.Bytes.f`, `File.f` → `Sys.File.f`) | **yes** | 56 | 5 | 0 |
| principal types (`Int`, `Pipe`) via `__root__` | no | 17 | 17 | 2 unchanged |
| module-prefixed strip (`M.f` → `def f`) | no | 1,026 | 40 | 0 |
| `List`/`Int` extensions kept root | no | 189 | 9 | 0 |
| other shared families kept root (`Bus`, `Circuit`, `Prog`, …) | no if kept root | 528 | 39 | 0 (32 private/native rows unchanged) |
| Prelude (root) | no if `namespace __root__` | 260 | 1 | 24 unchanged |
| selfhost (root/frozen) | no if exempt | 2,396 | 12 | not in the ledger |
| no leaf aliases: importer headers gain `open import`/qualification | **yes** (source churn) | 155 files / 423 edges | 155 | 0 |
| block-scoped `open` after an `end` | **yes** (body opens) | 193 edges / 120 files; 3,567 sites | 120 | 0 |
| examples/docs/tests (strings, snippets, loaders) | **yes** (gates) | 2,482 + 309 `Scry.` strings | 106 + 67 loader sites | 0 |
| `Main` duplicate (two packages) | potential module-name clash | 2 | 2 | 0 |
| `C.Schema` generated | **yes** (change the generator) | 33 | 1 | 0 |
| `web/*/gen.wiz` generated | **yes** (change the generator) | 79 | 2 | 0 |

Final totals: **6,740 declarations rename**, **4,413 are name-preserving**, **608 of 730
ledger rows re-key**; the five-family move adds 56 renames and 0 ledger rows; `open
import` is wanted by **155 files / 423 edges** (bare: 120 / 193). If the scope is cut to
"namespaces for new code only" (the allowlist forever), the cost is zero renames and zero
ledger changes, but the `Msg`/`Settings`/`main` class remains for every old module; that is
the status quo with new syntax, not the fix the brief asks for.

---

## 9. Method

Counts were produced by scanning the branch point `c2efe881`:

* a declaration is a line at column 0 whose first keyword is `def`, `inductive`,
  `structure`, `class`, `coinductive`, `axiom`, `extern`, `foreign_type`, `glue`,
  `c_struct`, `builtin`, `instance` or `deriving`, after the `private`/`sealed`/`local`/
  `partial`/`mutual` wrappers; comments and indented lines are skipped; a `mutual` block's
  members are at column 0 and are counted;
* a module name is the path under its package root with `/` → `.` (`lib/`, `scry/src/`,
  `scry/gen/`, `selfhost/`, `tower/`, `web/`), the same rule as `Module.nameOf`;
* a family `P`'s owner is the module declaring the type/class/axiom/foreign_type `P`, or,
  for a family with no type (`Bits`), the module declaring most `P.*` members (`BitBlast`,
  167 of 208);
* an "extension" is a `P.*` declaration in a module other than the owner; a five-family
  extension is moved if the owner is not root (`Bits`, `Bytes`, `File`) and kept if the
  owner is root (`List` in `Prelude`, `Int` in the module `Int`);
* the import/open counts use the header `import` list and a token scan of the importer:
  an edge is an `(importer, imported module)` pair with at least one occurrence of a
  declared name of the module; the bare-name count restricts that to declarations with no
  dot. The unfiltered counts (423 edges / 155 files; 193 / 120) are the plan's upper
  bound; a conservative scan (names of four or more characters, common words removed)
  gives 138 / 107. The 3,567 sites are token occurrences; 1,923 exclude Prelude's root
  names;
* the ledger counts are read from `.github/trust-baseline.tsv` (730 rows, 41 modules) and
  classified by declaration-name prefix; private/native kernel names are counted
  separately (32 rows keep their names). The 608 re-key figure is the pre-`--update`
  estimate; the exact set is produced by the ledger driver.

The file/line counts include only the eight source trees; `Tests/`, `editors/` and
`examples/grail-index` fixtures (67 files) are registry-test evidence and are out of
scope for renaming. `drafts/` is out of scope; a draft that is promoted is migrated with
its target.

---

## 10. Decisions taken, and what remains

Taken 2026-11-19 (this revision):

1. **`open` is block-scoped** to the enclosing `namespace`; at file top it reaches EOF.
   The 13t "open outlives end" test is reversed.
2. **No leaf aliases.** `import M` brings `M.*`; `open import M` is the header shorthand.
3. **Shared families move under their owner.** `Bits` → `BitBlast.Bits`, `Bytes` →
   `IO.Bytes`, `File` → `Sys.File`; `List`/`Int` stay root because their owners are root.
4. **`open import M`** = `import M` + file-scope `open M`, header-only; no `in` form.
5. **Imports are a fixed header**; the dependency graph and `--reachable` are syntactic.

Remaining:

* Whether the other 528 shared-family extensions (`Bus`, `Circuit`, `Prog`, `Spi`,
  `Axi4`, …) should follow their owners in a later batch. The plan keeps them at root;
  the move would add their 375 non-root declarations to the rename count and 0 new
  ledger rows (their extension rows are not trust sources).
* Whether a future `open … in` command is worth adding for namespace bodies; `open
  import` never takes `in`.
* `scoped` notation: defer; nothing in the tree depends on it.
* `Scry.Tool.*` / `Data.*` moves from the old plan: parked; they are compatible with
  either choice above.
