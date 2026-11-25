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

def main (args : List String) : IO UInt32 := do
  if !args.contains "--allow-reload" then
    IO.println "hot-reload P0 prototype: disabled (pass --allow-reload to run the model's cases)"
    -- Disabled is not a verdict: nothing ran, so nothing failed. Exit 0 with the reason
    -- printed; a script that wants "the cases were run" must pass the flag.
    return 0
  else
    IO.println "hot-reload P0 prototype: model cases (NOT a Wiz build/test)"
    let mut failed := 0
    for entry in tests do
      let status := if entry.2 then "PASS" else "FAIL"
      if !entry.2 then failed := failed + 1
      IO.println s!"{status}  {entry.1}"
    -- The exit status is the verdict: a FAIL must be visible to a script, not only in the
    -- log, or "run the cases" means "read the output".
    IO.println s!"{tests.length - failed} passed, {failed} failed"
    if failed == 0 then return 0 else return 1
