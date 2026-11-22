# Error codes

Every common error carries a stable **code**: a short name for the kind of mistake. The
language server sends it as the diagnostic's `code` (with the data its quick fixes use,
such as `suggestions`) and keys its code actions on it (`Wiz/Actions.lean`). The wording
of a message may change; its code does not. The codes are defined in
`Wiz/Core/ErrorCode.lean` (`ErrorCode.all`); the `lsp-server` test group checks that this
table lists exactly those. Messages not listed here have no code yet.

| code | the error | example | quick fixes |
|---|---|---|---|
| `root-name` | `__root__` not as the first segment of a name, or a declaration named exactly `__root__` (it is the root escape) | `def A.__root__.x`, `def __root__` | write `__root__.x` for a global, or drop the segment |
| `unknown-identifier` | a name that is neither a local nor a global in scope | `doubel 2` | did you mean (locals and globals, edit distance ≤ 2); add the missing `import` of a module of the package or the library that declares it |
| `ambiguous-name` | an unqualified name that two `open`s, or an `open` and a declaration, both provide | `open A` and `open B` with `A.x` and `B.x`, then `x` | qualify it with a namespace |
| `unclosed-namespace` | a `namespace` with no `end` (the error is at the `namespace`) | `namespace A` … end of file | add `end` |
| `no-such-field` | the type has no field (or name in its namespace) of that name | `p.cuont`, `{ p with cuont := 1 }` | did you mean (a structure's fields; for a data type `T`, the names `T.f` that `t.f` can mean) |
| `unknown-constructor` | the type has no constructor of that name | `(.gren : Color)`, `\| .gren => …` | did you mean (the type's constructors) |
| `unknown-module` | no root has the module of an `import` | `import Prelud` | did you mean (the modules the server knows) |
| `import-cycle` | an `import` leads back to the module itself | | |
| `module-errors` | an imported module has errors (they are listed) | | |
| `failed-declaration` | a reference to a declaration whose own command failed to elaborate; the root error is a related diagnostic (the reference is never also `unknown-identifier`) | `def broken : Nat := Bool.true` then `def uses : Nat := broken` | fix the first declaration |
| `missing-import` | a name (or a `deriving` class) declared in a module the file does not import | `Array` without `import Std`; `deriving Repr` without `import Deriving` | add `import M` (one per module) |
| `no-such-file` | the file a command names cannot be read | `wiz check no.wiz` | |
| `import-order` | an `import` after a declaration, or nested in a command: imports are a fixed header | `def x := 1` then `import Prelude`; `mutual import M end` | |
| `missing-case` | a `match` or equations miss constructors | | add missing cases |
| `missing-copattern` | a copattern definition misses an observation | | |
| `missing-field` | an instance misses a field of its class | | |
| `type-mismatch` | the expected and the inferred type don't unify | `def b : Nat := Bool.true` | |
| `not-defeq` | `rfl` where the two sides are not definitionally equal | | |
| `wrong-argument-count` | too many arguments (`function expected`), or a pattern or constructor with the wrong number of fields | `Nat.succ 1 2`, `myId Nat 1` | when the count is off by the implicit parameters: give them explicitly (`@myId Nat 1`) |
| `unknown-parameter` | a named argument `(x := e)` for a parameter the function doesn't have | | |
| `named-argument` | a named argument given twice, or after the explicit parameter it would follow; a structure field updated twice, or an instance field given twice | | |
| `unsolved-hole` | a hole nothing determines (`_`, an implicit argument, a binder's type) | `(fun (A : Type) => 0) _` | |
| `unsolved-level` | a universe level nothing determines | | |
| `cannot-infer` | an expression whose type can't be inferred without an ascription | | |
| `unsolved-goals` | a tactic block ends with goals left | | |
| `tactic-failed` | a tactic failed (`fail`, `intro`, `rewrite`, `change`, …) | | |
| `type-expected` | a term where a type was expected | `(x : 3)` | |
| `binder-mismatch` | a `fun` binder whose quantity or implicitness differs from the expected type's | | |
| `private` | a private name of another module, or a type whose constructors are private to it taken apart | | |
| `duplicate-declaration` | a name declared twice (an import that would redeclare one is not brought in) | | |
| `duplicate-hypothesis` | a `match` names its equation hypothesis twice | `match h : e, h : f with` | |
| `duplicate-constructor` | a constructor declared twice in one `inductive` | | |
| `shadowed-recursive` | a local variable shadows the recursive definition it is in | | |
| `not-structural` | a recursive call that is not structural | `def f : Nat → Nat \| n => f n` | |
| `unknown-syntax` | syntax that no macro or elaborator gives a meaning | | |
| `unknown-class` | an instance of something that is not a class, or of an unknown class | | |
| `unknown-declaration` | a command (`builtin`, `attribute`, `export`, …) names an unknown declaration | | |
| `simp-lemma-not-equation` | `attribute [simp] f` where `f`'s type is not an equation after its binders | `attribute [simp] Nat.succ` | |
| `simp-lemma-conditional` | `attribute [simp] f` where `f` has a premise before its equation (S3) | `attribute [simp] f` for `f : n = 0 → g n = n` | |
| `quantity` | a variable used against its quantity (erased, linear) | | |
| `kernel-rejected` | any other error of the kernel's | | |
| `parse-error` | the parser's errors | `def := 1` | |

## Lint codes

Lint findings use the same `Msg.code` namespace but a different table: a `W` code is a
judgement about a program the elaborator **accepted**, never an error code
(`Wiz/Core/ErrorCode.lean` does not list them). The registry is `Wiz/Lint.lean`
(`Wiz.Lint.registry`); `wiz lint --json` carries the code, and the language server sends
it as a diagnostic's `code`. `default` is the rule's severity before repository policy;
`scope` says whether the rule runs per command or once per module; `suppressible` says
whether the per-site `-- lint: allow Wxxx (reason)` marker may silence it.

| code | rule | category | default | scope | suppressible | detects |
|---|---|---|---|---|---|---|
| `W101` | unused-binding | correctness | warning | declaration | yes | a `pi`/`lam`/`letE` binder with no occurrence in its scope; `_`, `_…`, `x✝` and quantity-0 binders are exempt |
| `W102` | shadowed-local | correctness | hint | declaration | yes | an inner local binder with the same name as an outer local, where the inner binder is used (never a global) |
| `W103` | discarded-result | correctness | warning | declaration | yes | `let _ := e` where `e : Result`/`ResultQ`/`Option`; `do e` is `Monad.bind` and is not reported |
| `W301` | missing-doc | api | warning | declaration | yes | a top-level public `def`/`abbrev`/`structure`/`class`/`inductive`/`coinductive`/`axiom`/`opaque`/`theorem` under a public root with no doc comment |
| `W302` | unused-import | api | warning | module | yes | a direct import no target declaration uses, and that contributes no instance, syntax, notation, builtin, attribute, export or FFI/link effect |

A rule retired later keeps its row as `default: off` (the code is never reused). Core
owns `W001`–`W499`; a package lint set owns `W500`–`W999` and registers its rules with
`lint-set`/`lint` (`docs/lint-abi.md`). The registry refuses a code outside the package
block, a duplicate in the enabled closure, and a rule whose declared capability the set
does not declare. Core registers only the five rules above.

One more quick fix is not keyed on a code: an error inside `@f a…` where `f` is given
as many arguments as it has explicit parameters offers to let the implicit ones be
inferred (drop the `@`: `@myId 1` ↦ `myId 1`).

The elaborator records what a quick fix needs where it throws the error (`throwFix`, an
`Info.fix` entry of the info tree: the misspelt name and the type it was looked up in, or
the head of an application and its parameter counts); the suggestions themselves are
computed when the client asks, so elaboration pays nothing for them.
