import HotReload.Tests

/-!
# The P0 prototype command

This is deliberately not wired into `wiz`. `hotreload` is a non-default executable
and does nothing unless `--allow-reload` is passed; the default path (the `wiz`
build and CLI) never imports this library. The flag is the seam a later,
build-gated change would replace with a real `wiz --allow-reload` and the
`reloadable` command.
-/

open HotReload

def main : IO Unit := do
  let args ← IO.getArgs
  if !args.contains "--allow-reload" then
    IO.println "hot-reload P0 prototype: disabled (pass --allow-reload to run the model's cases)"
  else
    IO.println "hot-reload P0 prototype: model cases (NOT a Wiz build/test)"
    for entry in tests do
      let status := if entry.2 then "PASS" else "FAIL"
      IO.println s!"{status}  {entry.1}"
