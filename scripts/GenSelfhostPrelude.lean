import Wiz.Selfhost

/-!
# The embedded prelude's string form (A1)

`selfhost/Prelude.wiz` is the readable source of the prelude the self-hosted frontend
substitutes for `import Prelude`. `selfhost/Frontend.wiz` carries the same text as one
Wiz string literal (`preludeText`) because the self-hosted frontend has no
`include_str`, and the WebAssembly playground has no filesystem to read a file from.

This writer keeps the second a function of the first. It rewrites only the
`def preludeText : String := "…"` line of `selfhost/Frontend.wiz`; every other byte of
that file is left alone (the literal stays where the module loader and the prelude
drift check read it):

    lake build genSelfhostPrelude && .lake/build/bin/genSelfhostPrelude

Edit `selfhost/Prelude.wiz`, run that, and commit both. The `selfhost` group's "the
embedded prelude is current" case renders the line in-process and fails when the file
does not match, so a source edit without a regenerated literal cannot land.
-/

open Wiz.Selfhost

def main : IO Unit := do
  let source ← IO.FS.readFile preludeSourcePath
  let frontend ← IO.FS.readFile preludeFrontendPath
  match replacePreludeBinding frontend source with
  | .error e => throw (IO.userError e)
  | .ok updated =>
    if updated != frontend then
      IO.FS.writeFile preludeFrontendPath updated
    IO.println s!"{preludeFrontendPath}: preludeText regenerated from \
      {preludeSourcePath} ({source.length} characters)"
