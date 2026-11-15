import Wiz.Selfhost

/-!
# The checked-in parser tables (stage 23e)

`selfhost/Tables.wiz` is the self-hosted parser's grammar: the tables of the Lean parser
(`Wiz.Parser.Builtin.tables`) rendered as Wiz source (`catN`, `cats`, `tokens`). The
selfhost programs read it like any other module, so the fixpoint's input set is
`selfhost/*.wiz` and nothing generated. It is 39 KB, one line per category, sorted by
category name (no timestamps: regenerating an unchanged grammar gives an identical file).

Regenerate it after a change to `Wiz/Parser/Builtin.lean`:

    lake build genSelfhostTables && .lake/build/bin/genSelfhostTables

and commit the result. The `selfhost` group's "selfhost/Tables.wiz is current" case runs
the same rendering in-process and fails when the file differs, so CI catches a stale
copy (the `selfhost` shard's inputs include `Wiz/Parser/*`, so a grammar edit runs it).
The semantic check — that the file's tables accept the same corpus as the Lean parser —
is the same group's parse differential case.
-/

def main : IO Unit := do
  IO.FS.writeFile "selfhost/Tables.wiz" Wiz.Selfhost.tablesFile
