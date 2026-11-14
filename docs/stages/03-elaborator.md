# Stage 3: the elaborator

```
Wiz/
  Elab/Basic.lean        ElabM, metavariables, the local context
  Elab/Unify.lean        force, partial renamings, pattern unification
  Elab/Zonk.lean         replacing solved metavariables before the kernel sees a term
  Elab/Term.lean         bidirectional elaboration of term syntax, implicit arguments
  Elab/Command.lean      def / axiom / #check / #reduce / syntax
  Frontend/Frontend.lean parse a command, elaborate it, repeat
examples/church.wiz      try `lake exe wiz check examples/church.wiz`
```

The elaborator produces *candidate* core terms and the stage 1 kernel re-checks every
declaration. Metavariables are therefore untyped, and quantity errors come from the
kernel. This follows Kovács' elaboration-zoo (`03-holes`, `04-implicit-args`).

Stage 3 changed stage 1 in three small ways (and stage 4 added universe levels): Π types carry a `BinderInfo`
(explicit/implicit), there is a `Term.mvar` / `Head.mvar` the kernel rejects, and the
pretty printer prints surface syntax.

| #   | Where                | What                                                     |
|-----|----------------------|----------------------------------------------------------|
| 3.1 | `Elab/Unify.lean`    | `force`: unfold solved metas                             |
| 3.2 | `Elab/Unify.lean`    | `invert`: spine → partial renaming                       |
| 3.3 | `Elab/Unify.lean`    | `rename`: with scope and occurs checks                   |
| 3.4 | `Elab/Unify.lean`    | `solve`                                                  |
| 3.5 | `Elab/Unify.lean`    | `unify`                                                  |
| 3.6 | `Elab/Zonk.lean`     | `zonk`                                                   |
| 3.7 | `Elab/Term.lean`     | `insertImplicits`                                        |
| 3.8 | `Elab/Term.lean`     | `check`: implicit lambdas, holes, and the mode switch    |
| 3.9 | `Elab/Term.lean`     | `inferApp`: application, `@f`, and functions of unknown type |

## Optional extensions to stage 3

* **3.10** *Pruning*: solve `?m x y =?= ?n x` by pruning `y` from `?n`. See
  elaboration-zoo `05-pruning`.
* **3.11** Typed metavariables and contextual "could not infer `?A : Type`" messages.
* **3.12** Named arguments `f (A := Nat)`.
* **3.13** Postponement: when a check is stuck on an unsolved meta, such as a lambda
  checked against `?m`, postpone it and retry at the end of the declaration.
* **3.14** Universe level metavariables, so `checkType` always knows the level.
* **3.15** User-defined term elaborators: `attribute [elab k] f` hands a term of the
  syntax kind `k` to the Wiz function `f : Syntax → TacticM Unit` with a hole of the
  expected type, and accepts what it assigns if the goal is closed. The dispatch is in
  `check`/`infer`, after macro expansion (`Elab/Term.lean`, `userElab?`) — see
  [6h](06-macros.md).
