# drafts/jsx: a markup prototype for `Web.React`

An experiment, not a library. The design write-up (including the self-host
verdict and the recommendation) is `wiz-notes/jsx-prototype.md`.

| file | what |
|------|------|
| `Markup.wiz` | the `ui! <tag …> … </tag>` grammar, and the procedural macro that translates it to `React.el`/`React.on`/`React.keyed` |
| `App.wiz` | a component tree written with markup, `#eval`ing its HTML and diff patches, and a `main` that prints both |
| `Dsl.wiz` | the same tree with the builder DSL (`H.div [H.cls "row"] [...]`), for comparison; prints the same HTML |
| `selfhost-declarative.wiz` | the subset the self-hosted frontend accepts (declarative `syntax` + `macro_rules`), and its silent mismatched-tag bug |
| `selfhost-procmacro.wiz` | the same shape with a procedural macro, which the self-hosted checker rejects |

From the repository root:

```
wiz run -I drafts/jsx drafts/jsx/App.wiz
wiz run drafts/jsx/Dsl.wiz
```

`Markup.wiz` is host-only: the self-hosted frontend parses the grammar and runs
`macro_rules`, but it does not run procedural macros, and its prelude has no
`Macro`/`MacroM`. To reproduce the self-host verdict, copy either selfhost file to a
scratch directory as `input.wiz` and run a self-hosted `checker` there (see the test
harness's `Tests.Elab.selfhostChecker`).
