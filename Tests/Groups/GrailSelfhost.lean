import Tests.Grail

namespace Tests.Grail
open Wiz Tests

def grailSelfhostGroup : Group where
  name := "grail-selfhost"
  exercise := "Stage 23e"
  cases := [
    { name := "grail builds the self-hosted checker, the same program as the tests'", run := fun _ => do
        -- the suite's elaboration cache (`lake test -- --cache DIR`, as CI does), else a fresh one
        let tc ← toolchain
        let tc : Toolchain := { tc with cacheDir := some (← tc.cacheDir.getDM IO.FS.createTempDir) }
        let dir ← IO.FS.realPath "."
        let log ← IO.mkRef ""
        let target := Grail.Target.selfhost "selfhost-checker" "checker"
        let r ← runner dir tc { name := "wiz", targets := [target], settings := [] } 4 log
        if !(← r.build [target] [target]) then
          if ((← log.get).splitOn "gmp.h").length > 1 then skip "no toolchain"; return
          throw (IO.userError (← log.get))
        let mine := dir / ".grail" / "bin" / "selfhost-checker"
        let .ok theirs ← Tests.Elab.selfhostChecker | throw (IO.userError "the tests' checker failed")
        let work ← IO.FS.createTempDir
        IO.FS.writeFile (work / "input.wiz") "import Prelude\ndef two : Nat := 1 + 1\n#check two\n"
        let a ← IO.Process.output { cmd := mine.toString, cwd := work }
        let b ← IO.Process.output { cmd := theirs.toString, cwd := work }
        checkEq b.stdout a.stdout
        check (!a.stdout.isEmpty) "no output"
        -- again: nothing runs
        let r : Grail.Runner := { r with stats := ← IO.mkRef ({} : Grail.Stats), memo := ← IO.mkRef ({} : Grail.Memo) }
        check (← r.build [target] [target]) "the second build failed"
        checkEq 0 (← r.stats.get).ran }
  ]

builtin_initialize registerGroup grailSelfhostGroup

end Tests.Grail
