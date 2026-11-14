# DSLs in Wiz

Wiz's surface syntax is extensible (stage 6: `syntax`, `notation`, `macro_rules`,
procedural macros; 13j keyword scopes; 13m `local`; 11r printing), and several libraries
use that to embed a language of their own. This page is the overview: which DSLs exist,
how to enter each, the symbols they take, how they print and report errors, and the
conventions a new one follows. Details are in the stage sections cited.

## The DSLs

| DSL | `import` | entered by | notation | details |
|---|---|---|---|---|
| core notation | (Prelude) | always | `+ - * / %`, `-x`, `\|>`, `if … then … else`, `&&`, `\|\|`, `!`, `do`, `[a, b]`, `++` | 6b, 13c, 13k, 13l |
| logic | `Logic` | import | `∧ ∨ ¬ ↔ ∃` (ASCII `/\ \/ <-> exists`) | 13e, 24a |
| functors | `Functor` | import | `<$> <*>` | 13d |
| tactics | (Prelude) | `by` | `intro`, `exact`, `apply`, `rw`, `unfold` … | 6c–6f |
| separation logic | `HProp`, `Hoare` | import | `⊢ ↦ ⋆ −∗`, `⌜P⌝`, `∃ʰ x, H`, `⦃P⦄ c ⦃r, Q⦄` | 24b–c, 24e |
| x-tactics | `HoareTactics` | `by` | `xsimpl xpull xwp xstep xval xseq xapp xchange xunfold xgo` | 24d |
| Feral (Rust-like) | `Feral` | `feral … end`, `#lower feral … end`, `#unchecked feral … end` | its own grammar (keyword scope `feral_kw`) | 22j |
| HDL | `Hdl.Core` | import | none: combinators `Hw.add`, `Hw.mux`, `Circuit.mk` … | libraries.md, H14 |
| optics | `Optic` | import | none (the target of Feral's lowering) | libraries.md |

**Entering a DSL.** There is no `open`: a library's notation is on from its `import` to
the end of the file. A language with a grammar of its own is a block command
(`feral … end`) whose categories share one *keyword scope* (13j), so its words (`fn`,
`mut`, `while` …) are keywords inside the block and ordinary identifiers outside it. The
block's entry word (`feral`) is the one word it reserves everywhere.

## Symbols and precedence

One meaning per symbol across the libraries. The levels (higher binds tighter):

| level | symbols | library |
|---|---|---|
| 10 | `\|>` | Prelude |
| 15 | `⊢` (entailment of heap predicates) | HProp |
| 20 | `↔` `<->` | Logic |
| 30 | `∨` `\/` `\|\|` | Logic, Prelude |
| 35 | `∧` `/\` `&&` | Logic, Prelude |
| 52 | `−∗` | HProp |
| 55 | `⋆` | HProp |
| 60 | `↦` | HProp |
| 65 | `+` `-` | Prelude |
| 67 | `++` | Prelude |
| 70 | `*` `/` `%` | Prelude |
| 75 | `-x` | Prelude |
| 100 | `<$>`; `<*>` is 60 | Functor |
| max | `!` `¬` `[…]`, `⌜P⌝`, `⦃P⦄ c ⦃r, Q⦄` | Prelude, Logic, HProp, Hoare |
| lead (extends right) | `∃ x, P`, `∃ʰ x, H`, `if`, `fun` | Logic, HProp, Prelude |

Words reserved by an import: `exists` (Logic, as in Lean) and `feral` (Feral). Using one
as a name is an error that says which syntax reserved it:
`expected identifier ('exists' is a keyword: the notation `exists …, …` of module Logic)`.

Notation a library uses only in its own implementation is `local` (13m), so importers
neither see it nor print with it (List.cons as `∷` in HoareTactics, Feral's `+++`, `⊕`,
`▸`). A library's public operator stays public: `Hdl.Core`'s `<+>` (`String.append`) is
used by `Hdl.Prim`, `Hdl.Xdc`, `Hdl.Xilinx7`, `Hdl.Sim` and the HDL examples.

## Printing

Terms print in the notation they were written with (11r): `#check`, `#eval`, messages,
hovers, the infoview's goals, and (24e) `trace_state` and tactic messages, so an x-tactic
that gets stuck shows `⊢ (l ↦ 1 ⊢ l ↦ 2)` (a target that shows a `⊢` of its own is put in
parentheses, so it isn't read as the goal's) and a
specification reads `⦃p ↦ a ⋆ q ↦ b⦄ Prog.swap p q ⦃_, p ↦ b ⋆ q ↦ a⦄`. Infix and `notation` rules whose template is a constant
applied to the rule's variables print automatically; binder notation (`∃ x, P`) and
macros declare an `app_unexpander`. When a constant has several notations, the one
declared last prints, so ASCII spellings are declared first. `set_option pp.notation
false` (or `--pp-all`) turns it off.

Feral prints as the Wiz it lowers to: goals about a Feral function are goals about its
lowering (`#lower feral … end` shows it).

## Errors

Errors point at the DSL source: a macro's template splices the user's own syntax, so a
type error inside `if c then a else b` or `[1, "y"]` is at the offending piece, and a
command macro reports at the node it names (`Syntax.errorAt path`, 22j). Messages say
what the DSL expects: `if n then …` at `n : Nat` is
`the value matched has type Nat, which has no constructor .true (…); the condition of
`if`, `&&` and `||` is a Bool`; Feral's front end reports in Feral's terms (`type
mismatch: expected Bool, found U64`, E0499 …); an x-tactic's failure starts with its name
(`xsimpl: …`).

## Writing a DSL: the conventions

1. **A module** `lib/<Dsl>.wiz` whose header comment says how to enter it, lists its
   notation (symbol, meaning, precedence, ASCII spelling) and gives an example.
2. **Entering**: notation by import; a language with its own grammar by one block
   command, with every category in one keyword scope:
   `declare_syntax_cat mydsl_expr (keywords := mydsl_kw)`.
3. **Scoping**: what users write is exported, helpers are `local`. A new symbol must not
   already mean something else in lib/ (the table above) or something well known
   elsewhere. Export one spelling per constant (plus an ASCII one, declared first).
4. **Precedence** from the table above.
5. **Printing**: every exported notation prints as itself; add an `app_unexpander` where
   it isn't automatic, and a test with `#check`.
6. **Errors** at the DSL source and in DSL terms: splice the user's syntax rather than
   rebuild it, use `Syntax.errorAt` in command macros, prefix a DSL's own errors with the
   construct (`xsimpl:`).
7. **Docs**: the module header, a row here, the stage section.
8. **Tests** in the DSL's test group: a use, its printing, an error at a DSL position, and
   (block DSLs) that its words stay identifiers outside.

There is no `dsl` declaration command: each part above is already one command, and the
grammar tools (go to definition, hovers, the printer) read those commands directly.
The audit behind these rules: `wiz-notes/dsl-conventions.md`.
