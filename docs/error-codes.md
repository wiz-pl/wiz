# Error codes

Every common error carries a stable **code**: a short name for the kind of mistake. The
language server sends it as the diagnostic's `code` (with the data its quick fixes use,
such as `suggestions`) and keys its code actions on it (`Wiz/Actions.lean`). The wording
of a message may change; its code does not. The codes are defined in
`Wiz/Core/ErrorCode.lean` (`ErrorCode.all`); the `lsp-server` test group checks that this
table lists exactly those. Messages not listed here have no code yet.

| code | the error | example | quick fixes |
|---|---|---|---|
| `unknown-identifier` | a name that is neither a local nor a global in scope | `doubel 2` | did you mean (locals and globals, edit distance ≤ 2); add the missing `import` of a module of the package or the library that declares it |
| `no-such-field` | the type has no field (or name in its namespace) of that name | `p.cuont`, `{ p with cuont := 1 }` | did you mean (a structure's fields; for a data type `T`, the names `T.f` that `t.f` can mean) |
| `unknown-constructor` | the type has no constructor of that name | `(.gren : Color)`, `\| .gren => …` | did you mean (the type's constructors) |
| `unknown-module` | no root has the module of an `import` | `import Prelud` | did you mean (the modules the server knows) |
| `import-cycle` | an `import` leads back to the module itself | | |
| `module-errors` | an imported module has errors (they are listed) | | |
| `missing-case` | a `match` or equations miss constructors | | add missing cases |
| `missing-copattern` | a copattern definition misses an observation | | |
| `missing-field` | an instance misses a field of its class | | |
| `type-mismatch` | the expected and the inferred type don't unify | `def b : Nat := Bool.true` | |
| `not-defeq` | `rfl` where the two sides are not definitionally equal | | |
| `wrong-argument-count` | too many arguments (`function expected`), or a pattern or constructor with the wrong number of fields | `Nat.succ 1 2`, `myId Nat 1` | when the count is off by the implicit parameters: give them explicitly (`@myId Nat 1`) |
| `unknown-parameter` | a named argument `(x := e)` for a parameter the function doesn't have | | |
| `named-argument` | a named argument given twice, or after the explicit parameter it would follow; a field updated twice | | |
| `unsolved-hole` | a hole nothing determines (`_`, an implicit argument, a binder's type) | `(fun (A : Type) => 0) _` | |
| `unsolved-level` | a universe level nothing determines | | |
| `cannot-infer` | an expression whose type can't be inferred without an ascription | | |
| `unsolved-goals` | a tactic block ends with goals left | | |
| `tactic-failed` | a tactic failed (`fail`, `intro`, `rewrite`, `change`, …) | | |
| `type-expected` | a term where a type was expected | `(x : 3)` | |
| `binder-mismatch` | a `fun` binder whose quantity or implicitness differs from the expected type's | | |
| `private` | a private name of another module, or a type whose constructors are private to it taken apart | | |
| `duplicate-declaration` | a name declared twice (an import that would redeclare one is not brought in) | | |
| `duplicate-constructor` | a constructor declared twice in one `inductive` | | |
| `shadowed-recursive` | a local variable shadows the recursive definition it is in | | |
| `not-structural` | a recursive call that is not structural | `def f : Nat → Nat \| n => f n` | |
| `unknown-syntax` | syntax that no macro or elaborator gives a meaning | | |
| `unknown-class` | an instance of something that is not a class, or of an unknown class | | |
| `unknown-declaration` | a command (`builtin`, `attribute`, `export`, …) names an unknown declaration | | |
| `quantity` | a variable used against its quantity (erased, linear) | | |
| `kernel-rejected` | any other error of the kernel's | | |
| `parse-error` | the parser's errors | `def := 1` | |

One more quick fix is not keyed on a code: an error inside `@f a…` where `f` is given
as many arguments as it has explicit parameters offers to let the implicit ones be
inferred (drop the `@`: `@myId 1` ↦ `myId 1`).

The elaborator records what a quick fix needs where it throws the error (`throwFix`, an
`Info.fix` entry of the info tree: the misspelt name and the type it was looked up in, or
the head of an application and its parameter counts); the suggestions themselves are
computed when the client asks, so elaboration pays nothing for them.
