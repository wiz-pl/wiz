import Lean
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
  -- WIZ_TABLES_OUT lets a check (scripts/fixpoint.sh) render the tables into its own
  -- directory and diff them, without writing the checked-in file a test run may be
  -- reading. The default is the checked-in path, as the regeneration workflow expects.
  let out := (← IO.getEnv "WIZ_TABLES_OUT").getD "selfhost/Tables.wiz"
  IO.FS.writeFile out Wiz.Selfhost.tablesFile

/- `lake lean scripts/GenSelfhostTables.lean` with WIZ_TABLES_OUT set renders the
tables there (the fixpoint's check). Without the variable this is a no-op, so building
the `genSelfhostTables` executable does not touch the source tree. -/
#eval show IO Unit from do
  if let some out ← IO.getEnv "WIZ_TABLES_OUT" then
    IO.FS.writeFile out Wiz.Selfhost.tablesFile
