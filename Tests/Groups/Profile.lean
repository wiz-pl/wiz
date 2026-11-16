import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

def profileWiz : IO String := do pure (← IO.FS.realPath ".lake/build/bin/wiz").toString

def profileRun (args : Array String) : IO IO.Process.Output := do
  -- the toolchain flags the suite was started with (`--cc`, `--cflags`, …), so the
  -- spawned compiler finds GMP where this machine keeps it
  IO.Process.output { cmd := ← profileWiz, args := args ++ (← flagsRef.get).toArray }

def checkExit (what : String) (r : IO.Process.Output) : IO Unit :=
  check (r.exitCode == 0) s!"{what} failed ({r.exitCode}): {r.stderr}"

def readProfileJson (f : System.FilePath) : IO Lean.Json := do
  let text ← IO.FS.readFile f
  match Lean.Json.parse text with
  | .ok j => pure j
  | .error e => throw (IO.userError s!"{f}: not JSON: {e}")

def jsonNat (j : Lean.Json) (key : String) : IO Nat := do
  match j.getObjVal? key with
  | .error e => throw (IO.userError s!"no {key}: {e}")
  | .ok v => match v.getNat? with
    | .error e => throw (IO.userError s!"{key} is not a natural: {e}")
    | .ok n => pure n

def profileGroup : Group where
  name := "profile"
  exercise := "Exercise 8.1"
  cases := [
    { name := "--profile-json: every phase, non-negative, and sums within the total", run := fun _ => do
        let dir ← IO.FS.createTempDir
        let src := dir / "p.wiz"
        IO.FS.writeFile src "import Prelude\ndef double (n : Nat) : Nat := n + n\ndef main : Nat := double 21\n"
        let out := dir / "p"
        let json := dir / "p.json"
        let r ← profileRun #["build", src.toString, "-o", out.toString, "--no-cache",
                             "--profile-json", json.toString]
        checkExit "build" r
        let j ← readProfileJson json
        let total ← jsonNat j "total_ns"
        check (total > 0) "total_ns is zero"
        let elab ← jsonNat j "elaboration_ns"
        check (elab > 0) "elaboration_ns is zero"
        -- declarations: present, each with a name, kind and time, and their sum is
        -- within the total (the spans are disjoint in time)
        let some (.arr decls) := (j.getObjVal? "declarations").toOption
          | throw (IO.userError "no declarations array")
        check (!decls.isEmpty) "no declarations were profiled"
        let mut declNs := 0
        for d in decls do
          let _ ← jsonNat d "ns"
          let some (.str _) := (d.getObjVal? "name").toOption
            | throw (IO.userError "a declaration has no name")
          declNs := declNs + (← jsonNat d "ns")
        check (declNs ≤ total) s!"declaration times ({declNs}) exceed the total ({total})"
        -- modules: the check of each import, and whether it was a cache hit or miss
        let some (.arr mods) := (j.getObjVal? "modules").toOption
          | throw (IO.userError "no modules array")
        check (!mods.isEmpty) "no module was profiled"
        for m in mods do
          let _ ← jsonNat m "ns"
          let some (.str status) := (m.getObjVal? "status").toOption
            | throw (IO.userError "a module has no status")
          check (status == "hit" || status == "miss") s!"bad module status {status}"
        -- every backend phase is present, zero or more, and the phases fit in the total
        let some (.obj backend) := (j.getObjVal? "backend").toOption
          | throw (IO.userError "no backend object")
        let phases := ["ir_ns", "lower_ns", "optimize_ns", "codegen_ns", "object_ns", "link_ns"]
        let mut phaseNs := 0
        for k in phases do
          let n ← jsonNat backend k
          phaseNs := phaseNs + n
        check (phaseNs ≤ total) s!"phase times ({phaseNs}) exceed the total ({total})"
        let some (.obj cache) := (j.getObjVal? "cache").toOption
          | throw (IO.userError "no cache object")
        let hits ← jsonNat cache "hits"
        let misses ← jsonNat cache "misses"
        check (misses > 0) "a --no-cache build reported no misses"
        check (hits + misses > 0) "no commands were counted" },
    { name := "--profile does not change the generated C or the executable", run := fun _ => do
        let dir ← IO.FS.createTempDir
        let src := dir / "q.wiz"
        IO.FS.writeFile src "import Prelude\ndef square (n : Nat) : Nat := n * n\ndef main : Nat := square 7\n"
        let plain := dir / "plain"
        let prof := dir / "prof"
        let r1 ← profileRun #["build", src.toString, "-o", plain.toString, "--no-cache"]
        checkExit "plain build" r1
        let r2 ← profileRun #["build", src.toString, "-o", prof.toString, "--no-cache", "--profile"]
        checkExit "profile build" r2
        check ((r2.stdout.splitOn "wiz build --profile").length > 1) s!"no table: {r2.stdout}"
        check ((r2.stdout.splitOn "backend phase").length > 1) "the table has no backend phases"
        let c1 ← IO.FS.readBinFile (plain.withExtension "c")
        let c2 ← IO.FS.readBinFile (prof.withExtension "c")
        check (c1 == c2) "the generated C differs with --profile"
        let e1 ← IO.FS.readBinFile plain
        let e2 ← IO.FS.readBinFile prof
        check (e1 == e2) "the executable differs with --profile" },
    { name := "a warm cache reports hits and no misses", run := fun _ => do
        let dir ← IO.FS.createTempDir
        let src := dir / "w.wiz"
        IO.FS.writeFile src "import Prelude\ndef three : Nat := 3\ndef main : Nat := three\n"
        let cache := dir / "cache"
        let out := dir / "w"
        let json := dir / "w.json"
        let r1 ← profileRun #["build", src.toString, "-o", out.toString, "--cache", cache.toString,
                              "--profile-json", json.toString]
        checkExit "cold build" r1
        let r2 ← profileRun #["build", src.toString, "-o", out.toString, "--cache", cache.toString,
                              "--profile-json", json.toString]
        checkExit "warm build" r2
        let j ← readProfileJson json
        let some (.obj cacheJ) := (j.getObjVal? "cache").toOption
          | throw (IO.userError "no cache object")
        let hits ← jsonNat cacheJ "hits"
        let misses ← jsonNat cacheJ "misses"
        check (hits > 0) "the warm build got nothing from the cache"
        checkEq 0 misses }
  ]

builtin_initialize registerGroup profileGroup

end Tests.Elab
