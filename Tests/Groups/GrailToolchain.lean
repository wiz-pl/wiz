import Tests.Grail

namespace Tests.Grail
open Wiz Tests

/-- The first `(file, entry)` that a cache's manifests list (for a tamper test). -/
def firstManifestEntry (cache : System.FilePath) : IO (Option (System.FilePath × Cache.ManifestEntry)) := do
  for f in ← manifestFiles cache do
    let text ← IO.FS.readFile f
    if let some m := Cache.parseManifest text then
      if let some e := m.allEntries[0]? then return some (cache / e.file, e)
  pure none

/-- Change the first digit of a manifest's root (its own root no longer matches). -/
def tamperManifestRoot (f : System.FilePath) : IO Unit := do
  let text ← IO.FS.readFile f
  match text.splitOn "(root " with
  | before :: after :: _ =>
    let after := after.drop 1
    let bad := if after.startsWith "0" then "1" else "0"
    IO.FS.writeFile f (before ++ "(root " ++ bad ++ after.drop 1)
  | _ => IO.FS.writeFile f (text ++ " ")

/-- Every file under `dir`, recursively. -/
partial def everyFile (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out := #[]
  for e in ← dir.readDir do
    if ← e.path.isDir then out := out ++ (← everyFile e.path)
    else out := out.push e.path
  pure out

/-- Every `.lean` file under a directory. -/
partial def leanFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out := #[]
  for e in ← dir.readDir do
    if ← e.path.isDir then out := out ++ (← leanFiles e.path)
    else if e.path.extension == some "lean" then out := out.push e.path
  pure out

def toolchainGroup : Group where
  name := "toolchain"
  exercise := "Stage 23a"
  parallel := true
  cases := [
    { name := "wiz, grail and the test driver read no environment variables", run := fun _ => do
        let files := (← leanFiles "Wiz") ++ (← leanFiles "Grail") ++ #[System.FilePath.mk "Main.lean", "Tests/Main.lean"]
        for f in files do
          let text ← IO.FS.readFile f
          check ((text.splitOn "getEnv \"WIZ").length == 1) s!"{f} reads a WIZ_ variable" },
    { name := "wiz: an unknown flag or command is an error (exit 2), the usage alone is not", run := fun _ => do
        let wiz := ".lake/build/bin/wiz"
        let run (args : Array String) := IO.Process.output { cmd := wiz, args }
        let o ← run #["--impl=elab", "check", "x.wiz"]
        checkEq 2 o.exitCode
        check ((o.stderr.splitOn "unknown flag: --impl=elab").length > 1) s!"stderr: {o.stderr}"
        let o ← run #["frobnicate", "x.wiz"]
        checkEq 2 o.exitCode
        check ((o.stderr.splitOn "unknown command").length > 1) s!"stderr: {o.stderr}"
        checkEq 0 (← run #[]).exitCode
        checkEq 0 (← run #["--help"]).exitCode },
    { name := "flags fill the toolchain record", run := fun _ => do
        let (tc, rest) := ({} : Toolchain).parseFlags
          ["check", "--cc", "clang", "--cflags", "-I/a  -I/b", "-I", "src", "x.wiz", "--no-cache", "--llvm"]
        checkEq ["check", "x.wiz", "--llvm"] rest
        checkEq "clang" tc.cc
        checkEq ["-I/a", "-I/b"] tc.cflags
        checkEq ["src"] (tc.searchPath.map toString)
        check tc.cacheDir.isNone "the cache is on"
        -- and back to flags, for another process
        let tc := { tc with ldflags := ["-L/x"], cacheDir := some "/c" }
        let (tc', rest) := ({} : Toolchain).parseFlags tc.toFlags
        checkEq [] rest
        checkEq (repr tc).pretty (repr tc').pretty
        check (tc.id != ({ tc with cflags := [] } : Toolchain).id) "cflags are not in the id"
        checkEq tc.id ({ tc with cacheDir := none } : Toolchain).id },
    { name := "--cache-ro is repeatable and --no-cache clears both caches", run := fun _ => do
        let parse (args : List String) := ({} : Toolchain).parseFlags args
        -- left to right: reads keep their order, --cache sets the write cache
        let (tc, rest) := parse ["--cache-ro", "/a", "--cache", "/w", "--cache-ro", "/b", "check", "x.wiz"]
        checkEq ["/a", "/b"] (tc.readCaches.map toString)
        checkEq (some "/w") (tc.cacheDir.map toString)
        checkEq ["check", "x.wiz"] rest
        -- --no-cache clears both; a later --cache-ro (or --cache) adds again
        let (tc, _) := parse ["--cache-ro", "/a", "--cache", "/w", "--no-cache"]
        check tc.readCaches.isEmpty "a read cache survived --no-cache"
        check tc.cacheDir.isNone "the write cache survived --no-cache"
        let (tc, _) := parse ["--cache-ro", "/a", "--cache", "/w", "--no-cache", "--cache-ro", "/c"]
        checkEq ["/c"] (tc.readCaches.map toString)
        check tc.cacheDir.isNone "the write cache survived --no-cache"
        let (tc, _) := parse ["--no-cache", "--cache", "/w2"]
        checkEq (some "/w2") (tc.cacheDir.map toString)
        -- a grail build file's setting appends
        checkEq (some ["/a"]) ((({} : Toolchain).set "cache-ro" "/a").map fun t => t.readCaches.map toString)
        -- toFlags round-trips, with a write cache and read-only only
        let full : Toolchain := { cacheDir := some "/w", readCaches := ["/a", "/b"] }
        checkEq ["--cache-ro", "/a", "--cache-ro", "/b", "--cache", "/w"]
          ((full.toFlags).dropWhile (· != "--cache-ro") |>.take 6)
        let (back, rest) := parse full.toFlags
        checkEq [] rest
        checkEq (repr full).pretty (repr back).pretty
        let roOnly : Toolchain := { readCaches := ["/a", "/b"] }
        let (back, rest) := parse roOnly.toFlags
        checkEq [] rest
        checkEq (repr roOnly).pretty (repr back).pretty
        -- render: one line per read cache, in order, then the write cache
        check ((full.render.splitOn "cache-ro /a\ncache-ro /b\ncache /w\n").length > 1) full.render
        check ((roOnly.render.splitOn "cache-ro /a\ncache-ro /b\ncache (off)\n").length > 1) roOnly.render },
    { name := "--cache-verify off|warn|strict round-trips and is not in the toolchain id", run := fun _ => do
        let parse (args : List String) := ({} : Toolchain).parseFlags args
        let (tc, rest) := parse ["--cache-verify", "strict", "check", "x.wiz"]
        checkEq "strict" tc.cacheVerify
        checkEq ["check", "x.wiz"] rest
        let (tc2, _) := parse ["--cache-verify=off", "check", "x.wiz"]
        checkEq "off" tc2.cacheVerify
        checkEq "warn" ({} : Toolchain).cacheVerify
        check (tc.id == ({ tc with cacheVerify := "warn" } : Toolchain).id)
          "cache-verify is in the toolchain id"
        let (back, rest) := parse ({ tc with cacheVerify := "strict" }).toFlags
        checkEq [] rest
        checkEq "strict" back.cacheVerify
        check ((tc.render.splitOn "cache-verify strict").length > 1) tc.render },
    { name := "wiz cache verify/manifest, and a --cache-ro layer is strict by default", run := fun _ => do
        let dir ← mkTree [("M.wiz", "import Prelude\ndef x : Nat := 2\n"),
                          ("main.wiz", "import M\n#eval x\n")]
        let cache ← IO.FS.createTempDir
        let wiz := (← IO.FS.realPath ".lake/build/bin/wiz").toString
        let run (args : Array String) := IO.Process.output { cmd := wiz, args, cwd := some dir }
        let base : Array String := #["check", "main.wiz", "-I", dir.toString]
        let cold ← run (base ++ #["--cache", cache.toString])
        checkEq 0 cold.exitCode
        checkEq "main.wiz:2:1: info: 2\n" cold.stdout
        -- (a full scan: the manifests match the bytes)
        let v0 ← run #["cache", "verify", "--cache", cache.toString]
        checkEq 0 v0.exitCode
        -- (each layer prints `DIR: N modules, …, N unmanifested`; match the separators too,
        -- or a read-only layer of 120 modules reads as an empty one)
        check ((v0.stdout.splitOn ": 0 modules").length == 1) s!"no modules verified: {v0.stdout}"
        check ((v0.stdout.splitOn ", 0 unmanifested").length > 1) s!"unmanifested: {v0.stdout}"
        -- (the generation index names its predecessor and an expiry)
        let m ← run #["cache", "manifest", "--cache", cache.toString, "--valid-days", "1"]
        checkEq 0 m.exitCode
        let gen ← IO.FS.readFile (cache / "manifest.sexpr")
        check ((gen.splitOn "(valid-until ").length > 1) gen
        check ((gen.splitOn "(prev ").length > 1) gen
        -- (a tampered entry: the scan fails, a warm run repairs it)
        let some (entryFile, ent) ← firstManifestEntry cache
          | throw (IO.userError "no manifest entry")
        checkEq "wizc" ent.kind
        let _ ← flipByte entryFile
        checkEq 1 (← run #["cache", "verify", "--cache", cache.toString]).exitCode
        let warm ← run (base ++ #["--cache", cache.toString])
        checkEq 0 warm.exitCode
        checkEq cold.stdout warm.stdout
        checkEq 0 (← run #["cache", "verify", "--cache", cache.toString]).exitCode
        -- (a read-only layer: strict by default; nothing there is written or repaired)
        let ro := cache
        let before ← snapshot ro
        let rw ← run (base ++ #["--no-cache", "--cache-ro", ro.toString, "--cache-verify-stats"])
        checkEq 0 rw.exitCode
        checkEq cold.stdout rw.stdout
        check ((rw.stderr.splitOn "cache verify: ").length > 1) s!"no verify stats: {rw.stderr}"
        checkEq before (← snapshot ro)
        -- (a tampered read-only entry: a miss, the text path answers, the layer is unchanged)
        let some (roFile, _) ← firstManifestEntry ro
          | throw (IO.userError "no read-only manifest entry")
        let _ ← flipByte roFile
        let bad ← snapshot ro
        let o ← run (base ++ #["--no-cache", "--cache-ro", ro.toString])
        checkEq 0 o.exitCode
        checkEq cold.stdout o.stdout
        checkEq bad (← snapshot ro)
        -- (delete a manifest: its entries are not used, and the layer says so; still no write)
        let some mf ← manifestFor ro "M"
          | throw (IO.userError "no manifest for M")
        IO.FS.removeFile mf
        let after ← snapshot ro
        let o2 ← run (base ++ #["--no-cache", "--cache-ro", ro.toString])
        checkEq 0 o2.exitCode
        checkEq cold.stdout o2.stdout
        check ((o2.stderr.splitOn "no manifest for a module").length > 1) s!"no warning: {o2.stderr}"
        checkEq after (← snapshot ro) },
    { name := "--region-cache is a toolchain flag and a build-file setting", run := fun _ => do
        let parse (args : List String) := ({} : Toolchain).parseFlags args
        let (tc, rest) := parse ["--region-cache", "check", "x.wiz"]
        checkEq ["check", "x.wiz"] rest
        check tc.regionCache "the flag did not set region-cache"
        check (!({} : Toolchain).regionCache) "region-cache is on by default"
        -- (the build-file setting: `(set "region-cache" "true")`)
        checkEq (some "true") ((({} : Toolchain).set "region-cache" "true").map fun t => toString t.regionCache)
        checkEq (some "false") ((({} : Toolchain).set "region-cache" "false").map fun t => toString t.regionCache)
        -- (`--region-stats` is the same kind of flag: a job gets it from `toFlags`)
        let (ts, _) := parse ["--region-stats", "check", "x.wiz"]
        check ts.regionStats "the flag did not set region-stats"
        check (!({} : Toolchain).regionStats) "region-stats is on by default"
        checkEq (some "true") ((({} : Toolchain).set "region-stats" "true").map fun t => toString t.regionStats)
        checkEq (some "false") ((({} : Toolchain).set "region-stats" "false").map fun t => toString t.regionStats)
        -- (forwarded to every job, beside the layered cache flags)
        let full : Toolchain := { cacheDir := some "/w", readCaches := ["/a"], regionCache := true }
        check (full.toFlags.contains "--region-cache") "toFlags drops region-cache"
        checkEq ["--cache-ro", "/a", "--cache", "/w", "--region-cache"]
          ((full.toFlags).dropWhile (· != "--cache-ro") |>.take 5)
        let (back, rest) := parse full.toFlags
        checkEq [] rest
        checkEq (repr full).pretty (repr back).pretty
        let fullStats : Toolchain := { full with regionStats := true }
        check (fullStats.toFlags.contains "--region-stats") "toFlags drops region-stats"
        let (backStats, rest) := parse fullStats.toFlags
        checkEq [] rest
        checkEq (repr fullStats).pretty (repr backStats).pretty
        -- render, for `grail config`
        check ((full.render.splitOn "cache /w\nregion-cache true\n").length > 1) full.render
        check ((fullStats.render.splitOn "region-cache true\nregion-stats true\n").length > 1) fullStats.render
        check ((({} : Toolchain).render.splitOn "region-cache false\nregion-stats false\n").length > 1) ({} : Toolchain).render },
    { name := "-I DIR adds a module root", run := fun _ => do
        let dir ← mkTree [("Pkg/Three.wiz", "import Prelude\ndef three : Nat := 3\n")]
        let (tc, _) := ({} : Toolchain).parseFlags ["check", "main.wiz", "-I", dir.toString]
        let src := "import Pkg.Three\n#eval three\n"
        let ms ← Module.loadClosure ("lib" :: tc.searchPath) src
        let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := loaderOf ms }
        checkEq "[2:1: info: 3]" (toString (s.messages.toList.map (·.render src))) },
    { name := "#262: `wiz check -I src FILE` and `wiz check FILE -I src` both find the package's modules", run := fun _ => do
        let dir ← mkTree [("src/Crux/B.wiz", "import Prelude\ndef b : Nat := 1\n"),
                          ("src/Crux/A.wiz", "import Crux.B\n#eval b\n")]
        let wiz := (← IO.FS.realPath ".lake/build/bin/wiz").toString
        for args in [["check", "-I", "src", "src/Crux/A.wiz"], ["check", "src/Crux/A.wiz", "-I", "src"],
                     ["-I", "src", "check", "src/Crux/A.wiz"]] do
          let out ← IO.Process.output { cmd := wiz, args := (args ++ ["--no-cache"]).toArray, cwd := some dir }
          checkEq s!"{args}: 0 src/Crux/A.wiz:2:1: info: 1\n" s!"{args}: {out.exitCode} {out.stdout}{out.stderr}"
        -- the usage text names -I for check
        let out ← IO.Process.output { cmd := wiz, args := #["help"] }
        check ((out.stdout.splitOn "wiz check [-I DIR] FILE").length > 1) out.stdout },
    { name := "wiz cache prune: --days/--dry-run, and a --cache-ro layer is never pruned", run := fun _ => do
        let wiz := (← IO.FS.realPath ".lake/build/bin/wiz").toString
        let run (args : Array String) := IO.Process.output { cmd := wiz, args }
        let write ← IO.FS.createTempDir
        let ro ← IO.FS.createTempDir
        let old (dir : System.FilePath) (name : String) : IO System.FilePath := do
          let f := dir / name
          IO.FS.writeFile f "x"
          touchAgo f "40 days ago"
          pure f
        let oldEntry ← old write "old.wizc"
        let oldRegion ← old write "old.wizr"
        let oldSum ← old write "old.wizs"
        let roEntry ← old ro "ro.wizc"
        let before ← snapshot ro
        -- (dry run: a summary, nothing removed; say that read-only caches are out of scope)
        let o ← run #["cache", "prune", "--cache", write.toString, "--cache-ro", ro.toString,
                       "--days", "7", "--dry-run"]
        checkEq 0 o.exitCode
        check ((o.stdout.splitOn "cache prune: would remove 3 files").length > 1) s!"stdout: {o.stdout}"
        check ((o.stderr.splitOn "never pruned").length > 1) s!"stderr: {o.stderr}"
        check (← oldEntry.pathExists) "the dry run removed a file"
        -- (the real thing: the write cache only)
        let o ← run #["cache", "prune", "--cache", write.toString, "--cache-ro", ro.toString, "--days", "7"]
        checkEq 0 o.exitCode
        check ((o.stdout.splitOn "cache prune: removed 3 files").length > 1) s!"stdout: {o.stdout}"
        check (!(← oldEntry.pathExists) && !(← oldRegion.pathExists) && !(← oldSum.pathExists))
          "an old keyed file survived"
        check (← roEntry.pathExists) "a read-only cache was pruned"
        checkEq before (← snapshot ro)
        -- (a zero age or an unknown argument is an error)
        checkEq 2 (← run #["cache", "prune", "--days", "0"]).exitCode
        checkEq 2 (← run #["cache", "prune", "--bogus"]).exitCode },
    { name := "--cache-prune DAYS prunes the write cache before a run (a pruned entry is a miss)", run := fun _ => do
        let dir ← mkTree [("M.wiz", "import Prelude\ndef x : Nat := 2\n"),
                          ("main.wiz", "import M\n#eval x\n")]
        let cache ← IO.FS.createTempDir
        let wiz := (← IO.FS.realPath ".lake/build/bin/wiz").toString
        let base : Array String := #["check", "main.wiz", "-I", dir.toString, "--cache", cache.toString,
                                     "--region-cache"]
        let go (extra : Array String := #[]) : IO IO.Process.Output :=
          IO.Process.output { cmd := wiz, args := base ++ extra, cwd := some dir }
        let o1 ← go
        checkEq 0 o1.exitCode
        checkEq "main.wiz:2:1: info: 2\n" o1.stdout
        check ((← regionFiles cache).size > 0) "no region was written"
        -- (age everything keyed; the run prunes it first, and still answers the same)
        for f in ← everyFile cache do
          let name := f.fileName.getD ""
          if [".wizc", ".wizm", ".wizr", ".wizs"].any (fun e => name.endsWith e) then
            touchAgo f "40 days ago"
        let o2 ← go #["--cache-prune", "7"]
        checkEq 0 o2.exitCode
        checkEq o1.stdout o2.stdout
        check ((o2.stderr.splitOn "cache prune: removed").length > 1) s!"stderr: {o2.stderr}"
        check ((o2.stderr.splitOn "removed 0 files").length == 1) s!"nothing was pruned: {o2.stderr}"
        check ((← regionFiles cache).size > 0) "the pruned regions were not rewritten"
        -- (and the run's own files are fresh: pruning again removes nothing)
        let o3 ← go #["--cache-prune", "7"]
        checkEq 0 o3.exitCode
        check ((o3.stderr.splitOn "cache prune: removed 0 files").length > 1) s!"stderr: {o3.stderr}"
        -- (a bad number of days is an error, not a silent no-op)
        checkEq 1 (← go #["--cache-prune", "0"]).exitCode },
    { name := "--cache-ro with --region-cache serves the read-only layer and never writes it", run := fun _ => do
        let dir ← mkTree [("M.wiz", "import Prelude\ndef x : Nat := 2\n"),
                          ("main.wiz", "import M\n#eval x\n")]
        let ro ← IO.FS.createTempDir
        let wiz := (← IO.FS.realPath ".lake/build/bin/wiz").toString
        let coldArgs : Array String := #["check", "main.wiz", "-I", dir.toString, "--cache", ro.toString,
                                       "--region-cache"]
        let cold ← IO.Process.output { cmd := wiz, args := coldArgs, cwd := some dir }
        checkEq 0 cold.exitCode
        checkEq "main.wiz:2:1: info: 2\n" cold.stdout
        let regions ← regionFiles ro
        check (regions.size > 0) "no region was written"
        let before ← snapshot ro
        -- (read caches only: the regions answer, and nothing in the layer changes)
        let warm (stats : Bool) : IO IO.Process.Output := do
          let extra : Array String := if stats then #["--region-stats"] else #[]
          let args : Array String := #["check", "main.wiz", "-I", dir.toString, "--no-cache",
                                       "--cache-ro", ro.toString, "--region-cache"] ++ extra
          IO.Process.output { cmd := wiz, args, cwd := some dir }
        let o ← warm true
        checkEq 0 o.exitCode
        checkEq cold.stdout o.stdout
        check ((o.stderr.splitOn "0 modules from a region").length == 1) s!"no region answered: {o.stderr}"
        checkEq before (← snapshot ro)
        -- (a bad checksum in the read-only layer: a miss, the text answers, nothing is repaired)
        let _ ← flipByte regions[0]!
        let beforeBad ← snapshot ro
        let o ← warm true
        checkEq 0 o.exitCode
        checkEq cold.stdout o.stdout
        check ((o.stderr.splitOn "0 without").length == 1) s!"the corrupt region was not a miss: {o.stderr}"
        checkEq beforeBad (← snapshot ro) },
    { name := "wiz check --region-cache: a warm run comes from regions, and corrupt ones are misses", run := fun _ => do
        let dir ← mkTree [("M.wiz", "import Prelude\ndef x : Nat := 2\n"), ("main.wiz", "import M\n#eval x\n")]
        let cache ← IO.FS.createTempDir
        let wiz := (← IO.FS.realPath ".lake/build/bin/wiz").toString
        let args := #["check", "main.wiz", "-I", dir.toString, "--cache", cache.toString,
                      "--region-cache", "--region-stats"]
        let run := IO.Process.output { cmd := wiz, args, cwd := some dir }
        let o1 ← run
        checkEq 0 o1.exitCode
        checkEq "main.wiz:2:1: info: 2\n" o1.stdout
        check ((o1.stderr.splitOn "region cache:").length > 1) s!"no stats: {o1.stderr}"
        let regions ← regionFiles cache
        check (regions.size > 0) "no region files were written"
        -- (a warm run: modules come from the regions, the answer is the same)
        let o2 ← run
        checkEq 0 o2.exitCode
        checkEq o1.stdout o2.stdout
        check ((o2.stderr.splitOn "region cache: 0 modules").length == 1)
          s!"nothing came from a region: {o2.stderr}"
        -- (corrupt every region: the next run falls back to the text entries and rewrites them)
        for f in regions do IO.FS.writeFile f ""
        let o3 ← run
        checkEq 0 o3.exitCode
        checkEq o1.stdout o3.stdout
        for f in ← regionFiles cache do
          check ((← f.metadata).byteSize > 0) s!"{f} was not rewritten" },
    { name := "output manifests: warm hits are verified; a tampered entry or manifest is a miss", run := fun _ => do
        let dir ← mkTree libFiles
        let cache ← IO.FS.createTempDir
        let ms ← Module.loadAll ["lib", dir]
        let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, loader := loaderOf ms }
        let src := "import Data.Two\ndef a : Nat := two\n#eval a\n"
        let stats ← IO.mkRef ({} : Cache.VerifyCounts)
        let run : IO (CommandState ZeroOneMany) := do
          pure (← Cache.elaborateCached (some cache) [] src init 0 (verify := .warn)
            (rig := "zero-one-many") (stats := some stats)).1
        let cold ← run
        check (!cold.messages.any (·.severity == .error)) s!"cold: {cold.messages.toList.map (·.text)}"
        check ((← manifestFiles cache).size > 0) "no module manifest was written"
        let c0 ← stats.get
        checkEq 0 c0.mismatches
        -- (a warm run: every entry comes from a manifest and matches its digest)
        stats.set {}
        let warm ← run
        checkEq (cold.messages.toList.map (·.render src)) (warm.messages.toList.map (·.render src))
        let c1 ← stats.get
        check (c1.hits > 0) s!"no entry was served from a manifest: {repr c1}"
        checkEq 0 c1.mismatches
        -- (flip a byte of a manifested `.wizc`: a miss, the text is rebuilt, the file repaired)
        let some (entryFile, ent) ← firstManifestEntry cache
          | throw (IO.userError "no manifest lists an entry")
        checkEq "wizc" ent.kind
        let before ← IO.FS.readFile entryFile
        let _ ← flipByte entryFile
        stats.set {}
        let tampered ← run
        checkEq (cold.messages.toList.map (·.render src)) (tampered.messages.toList.map (·.render src))
        let c2 ← stats.get
        check (c2.mismatches > 0) s!"a tampered entry was not a miss: {repr c2}"
        checkEq before (← IO.FS.readFile entryFile)
        -- (tamper a manifest's root: its entries are misses, and it is rewritten)
        let mfile := (← manifestFiles cache)[0]!
        tamperManifestRoot mfile
        stats.set {}
        let t2 ← run
        checkEq (cold.messages.toList.map (·.render src)) (t2.messages.toList.map (·.render src))
        let c3 ← stats.get
        check (c3.mismatches > 0) s!"a tampered manifest was trusted: {repr c3}"
        check ((← manifestFiles cache).size > 0) "the manifest was not rewritten" }
  ]

builtin_initialize registerGroup toolchainGroup

end Tests.Grail
