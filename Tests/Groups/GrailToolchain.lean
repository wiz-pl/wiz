import Tests.Grail
import Tests.Groups.GrailModules

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

/-- `ssh-keygen` signs and verifies a cache layer's generation index; a machine without
it cannot run the signed-cache cases, so they fail by default (`skipMissing`) and are
reported as skips only under `--allow-missing-deps` (as the registry's signed cases do). -/
def cacheHaveSshKeygen : IO Bool := do
  try
    let _ ← IO.Process.output { cmd := "ssh-keygen", args := #["-h"] }
    pure true
  catch _ => pure false

/-- A throwaway Ed25519 key and its `.pub` in `dir`. -/
def cacheKeypair (dir : System.FilePath) (name : String) :
    IO (System.FilePath × System.FilePath) := do
  let key := dir / name
  let _ ← runIn dir "rm" ["-f", key.toString, key.toString ++ ".pub"]
  let _ ← runIn dir "ssh-keygen"
    ["-q", "-t", "ed25519", "-N", "", "-C", "wiz cache test", "-f", key.toString]
  pure (key, System.FilePath.mk (key.toString ++ ".pub"))

/-- An `allowed_signers` line naming `id` for the public key in `pub`. -/
def cacheAllowSigner (allowed pub : System.FilePath) (id : String) : IO Unit := do
  IO.FS.writeFile allowed s!"{id} {(← IO.FS.readFile pub)}\n"

/-- A signed read-only cache layer: a cold verified run into `dir`, then seal and sign
with a throwaway key whose allowlist lives outside the layer. Returns the allowlist and
the policy that admits it. -/
def cacheSignedLayer (dir : System.FilePath) (src : String)
    (init : CommandState ZeroOneMany) (rig : String) :
    IO (System.FilePath × Cache.SignaturePolicy) := do
  let _ ← Cache.elaborateCached (some dir) [] src init 0 (verify := .warn) (rig := rig)
  let _ ← Cache.sealLayer dir true 0
  let keyDir ← IO.FS.createTempDir
  let (key, pub) ← cacheKeypair keyDir "key"
  let allowDir ← IO.FS.createTempDir
  let allowed := allowDir / "allowed_signers"
  cacheAllowSigner allowed pub "wiz-cache-test"
  match ← Cache.signLayer dir key (some "wiz-cache-test") with
  | .ok _ => pure ()
  | .error e => throw (IO.userError e)
  pure (allowed, { signers := some allowed, keyId := some "wiz-cache-test" })

/-- Copy a cache layer tree (the fixtures are small). -/
def cacheCopyTree (src dst : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dst
  let _ ← runIn dst "cp" ["-a", src.toString ++ "/.", dst.toString]
  pure ()

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
    { name := "wiz cache verify/manifest, and a --cache-ro layer is refused unless opted in", run := fun _ => do
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
        -- (a read-only layer: refused by default, its manifests are self-signed)
        let ro := cache
        let before ← snapshot ro
        let rw ← run (base ++ #["--no-cache", "--cache-ro", ro.toString, "--cache-verify-stats"])
        checkEq 0 rw.exitCode
        checkEq cold.stdout rw.stdout
        check ((rw.stderr.splitOn "refusing an unauthenticated layer").length > 1)
          s!"the read-only layer was not refused: {rw.stderr}"
        check ((rw.stderr.splitOn "--cache-ro-unsigned").length > 1) s!"no opt-in named: {rw.stderr}"
        checkEq before (← snapshot ro)
        -- (the explicit opt-in serves it, through its manifests; nothing is written or repaired)
        let rw2 ← run (base ++ #["--no-cache", "--cache-ro", ro.toString, "--cache-ro-unsigned",
          "--cache-verify-stats"])
        checkEq 0 rw2.exitCode
        checkEq cold.stdout rw2.stdout
        check ((rw2.stderr.splitOn "cache verify: ").length > 1) s!"no verify stats: {rw2.stderr}"
        check ((rw2.stderr.splitOn ", 0 entries").length == 1) s!"no entry was served: {rw2.stderr}"
        checkEq before (← snapshot ro)
        -- (a tampered read-only entry: a miss, the text path answers, the layer is unchanged)
        let some (roFile, _) ← firstManifestEntry ro
          | throw (IO.userError "no read-only manifest entry")
        let _ ← flipByte roFile
        let bad ← snapshot ro
        let o ← run (base ++ #["--no-cache", "--cache-ro", ro.toString, "--cache-ro-unsigned"])
        checkEq 0 o.exitCode
        checkEq cold.stdout o.stdout
        checkEq bad (← snapshot ro)
        -- (delete a manifest: its entries are not used, and the layer says so; still no write)
        let some mf ← manifestFor ro "M"
          | throw (IO.userError "no manifest for M")
        IO.FS.removeFile mf
        let after ← snapshot ro
        let o2 ← run (base ++ #["--no-cache", "--cache-ro", ro.toString, "--cache-ro-unsigned"])
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
        let dir ← mkTree [("src/Neutral/B.wiz", "import Prelude\ndef b : Nat := 1\n"),
                          ("src/Neutral/A.wiz", "import Neutral.B\n#eval b\n")]
        let wiz := (← IO.FS.realPath ".lake/build/bin/wiz").toString
        for args in [["check", "-I", "src", "src/Neutral/A.wiz"], ["check", "src/Neutral/A.wiz", "-I", "src"],
                     ["-I", "src", "check", "src/Neutral/A.wiz"]] do
          let out ← IO.Process.output { cmd := wiz, args := (args ++ ["--no-cache"]).toArray, cwd := some dir }
          checkEq s!"{args}: 0 src/Neutral/A.wiz:2:1: info: 1\n" s!"{args}: {out.exitCode} {out.stdout}{out.stderr}"
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
    { name := "--cache-ro with --region-cache serves the read-only layer (opted in) and never writes it", run := fun _ => do
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
                                       "--cache-ro", ro.toString, "--cache-ro-unsigned",
                                       "--region-cache"] ++ extra
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
    { name := "a forged .wizc + .wizmf in a read-only layer is refused by default (the opt-in serves it)", run := fun _ => do
        -- (the threat: a foreign layer ships a self-consistent manifest+entry whose effect is
        -- a `theorem` of `False` and a `builtin` registration the elaborator would refuse.
        -- Defaults must refuse the layer: a manifest is a self-signed digest.)
        let dir ← mkTree [("M.wiz", "import Prelude\ndef x : Nat := 2\n")]
        let ms ← Module.loadAll ["lib", dir]
        let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, loader := loaderOf ms }
        let rig := RigTag.tag (R := ZeroOneMany)
        let pkg ← IO.FS.createTempDir
        -- (a genuine cold run writes M's manifest and entries)
        let (cold, _) ← Cache.elaborateCached (some pkg) [] "import M\n" init 0 (verify := .warn) (rig := rig)
        check (!cold.messages.any (·.severity == .error)) s!"cold: {cold.messages.toList.map (·.text)}"
        let some mf ← manifestFor pkg "M"
          | throw (IO.userError "no manifest for M")
        let some man := Cache.parseManifest (← IO.FS.readFile mf)
          | throw (IO.userError "M's manifest does not parse")
        let some ent := man.entries[0]?
          | throw (IO.userError "M's manifest lists no entry")
        let key : Cache.Key := { fast := man.key, strong := man.keySha,
                                 toolchain := man.toolchainTag, target := man.targetTag }
        let cmdKey : Cache.Key := { fast := ent.key, strong := ent.keySha,
                                    toolchain := man.toolchainTag, target := man.targetTag }
        let forged : Cache.Effect ZeroOneMany :=
          { decls := #[{ name := "forgedFalse", type := .const "False" [],
                         value := some (.const "Nat.zero" []) }],
            builtins := [("nat.forged", "forgedFalse")] }
        -- (an attacker with write access rewrites the entry and recomputes the manifest)
        IO.FS.writeFile (pkg / ent.file) forged.toSx.render
        let attacker ← Cache.ManifestStore.create (some pkg) [] man.binary man.toolchain man.rig .warn
        attacker.writeManifest key man.module
          #[Cache.ManifestEntry.ofEffect man.binary cmdKey forged] man.region
        let tampered ← snapshot pkg
        let served : IO (CommandState ZeroOneMany) := do
          let (s, _) ← Cache.elaborateCached none [pkg] "import M\n" init 0 (verify := .warn) (rig := rig)
          pure s
        -- (the documented default: the layer is refused, so the module is elaborated)
        let s0 ← served
        check (!s0.globals.contains "forgedFalse") "the forged declaration was served by default"
        check (s0.globals.contains "x") "the genuine module did not answer in its place"
        checkEq (none : Option Name) (s0.globals.builtinOf? "nat.forged")
        checkEq tampered (← snapshot pkg)
        -- (the explicit opt-in really does serve it: this is what the default refuses, not a
        -- fixture that happens to miss)
        let (s1, _) ← Cache.elaborateCached none [pkg] "import M\n" init 0 (verify := .warn)
          (rig := rig) (roUnsigned := true)
        check (s1.globals.contains "forgedFalse") "the opt-in did not serve the forged entry"
        check (match s1.globals.find? "forgedFalse" with
          | some d => (match d.type with | .const "False" _ => true | _ => false)
          | none => false) "the forged declaration is not of type False"
        checkEq (some "forgedFalse") (s1.globals.builtinOf? "nat.forged")
        checkEq tampered (← snapshot pkg) },
    { name := "a region with no manifest entry is never served (not in warn, not in off)", run := fun _ => do
        -- (a region is type-erased at the boundary and its `.wizs` sidecar is written by the
        -- same writer; only a manifest entry binds the image to a module key)
        let dir ← mkTree [("M.wiz", "import Prelude\ndef x : Nat := 2\n")]
        let ms ← Module.loadAll ["lib", dir]
        let rig := RigTag.tag (R := ZeroOneMany)
        let cache ← IO.FS.createTempDir
        let binary ← Cache.binaryId (some cache)
        let k := moduleCacheKey ms 0 "M"
        let forged : Cache.Effect ZeroOneMany :=
          { decls := #[{ name := "forgedFalse", type := .const "False" [],
                         value := some (.const "Nat.zero" []) }] }
        let _ ← Cache.writeModuleRegion (R := ZeroOneMany) cache binary rig k "M" #[forged] #[k.fast]
        let opts : Cache.RegionOptions := { rig }
        for mode in [Cache.VerifyMode.warn, .strict] do
          let store ← Cache.Store.layeredRegion (R := ZeroOneMany) (some cache) [] binary opts mode rig
          check (← store.getRegion k).isNone s!"{repr mode}: an unmanifested region was served"
        -- (`off` has no manifest store: it serves no region either, and writes none)
        let offCache ← IO.FS.createTempDir
        let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, loader := loaderOf ms }
        let _ ← Cache.elaborateCached (some offCache) [] "import M\n" init 0
          (region := some opts) (verify := .off) (rig := rig)
        checkEq 0 (← regionFiles offCache).size
        let storeOff ← Cache.Store.layeredRegion (R := ZeroOneMany) (some offCache) [] binary opts .off rig
        check (← storeOff.getRegion k).isNone "an unmanifested region was served with --cache-verify off" },
    { name := "a fast-only legacy key is a miss in warn (the unmanifested fallback is gone)", run := fun _ => do
        -- (path D of the audit: the public `Key`/`Coe UInt64 Key` API must not turn into an
        -- unverified lookup just because the key has no SHA-256 half)
        let write ← IO.FS.createTempDir
        let binary : UInt64 := 4242
        let k : UInt64 := 7
        let forged : Cache.Effect ZeroOneMany :=
          { decls := #[{ name := "forgedFalse", type := .const "False" [],
                         value := some (.const "Nat.zero" []) }] }
        IO.FS.writeFile (write / s!"{mixHash binary k}.wizc") forged.toSx.render
        let store ← Cache.Store.layered (R := ZeroOneMany) (some write) [] binary (.warn)
        check (← store.getEntry k).isNone "an unmanifested fast-only entry was served in warn"
        -- (`off` is the explicit unverified mode and the old lookup is still there)
        let storeOff ← Cache.Store.layered (R := ZeroOneMany) (some write) [] binary (.off)
        check (← storeOff.getEntry k).isSome "the explicit off mode lost the old lookup" },
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
        check ((← manifestFiles cache).size > 0) "the manifest was not rewritten" },
    { name := "a signed generation index admits only recorded manifests; tampering is refused", run := fun _ => do
        unless ← cacheHaveSshKeygen do
          skipMissing "no ssh-keygen"
          return
        let dir ← mkTree [("M.wiz", "import Prelude\ndef x : Nat := 2\n"),
                          ("N.wiz", "import Prelude\ndef y : Nat := 3\n")]
        let ms ← Module.loadAll ["lib", dir]
        let init : CommandState ZeroOneMany :=
          { trustedModule := Tests.libModule, loader := loaderOf ms }
        let rig := RigTag.tag (R := ZeroOneMany)
        let layer ← IO.FS.createTempDir
        let (_allowed, policy) ← cacheSignedLayer layer "import M\nimport N\n" init rig
        let sig ← Cache.checkLayerSignature layer policy
        check sig.accepted s!"the signed index was refused: {sig.status} {sig.detail}"
        checkEq "valid" sig.status
        check ((sig.domain.render).startsWith "signed:wiz-cache-test") sig.domain.render
        check (sig.index.size > 0) "the signed index records no manifests"
        -- (a pinned minimum generation rejects an older index)
        let rollback ← Cache.checkLayerSignature layer
          { policy with minGeneration := some (sig.generation + 1) }
        check (!rollback.accepted) "a rollback pin was ignored"
        check (rollback.code == Cache.Refusal.indexRollback) s!"unexpected code: {rollback.code.code}"
        let serve (layerDir : System.FilePath) (policy : Cache.SignaturePolicy) :
            IO (CommandState ZeroOneMany × Cache.VerifyCounts) := do
          let stats ← IO.mkRef ({} : Cache.VerifyCounts)
          let (s, _) ← Cache.elaborateCached none [layerDir] "import M\nimport N\n" init 0
            (verify := .warn) (rig := rig) (stats := some stats) (policy := policy)
          pure (s, ← stats.get)
        let (s0, c0) ← serve layer policy
        check (s0.globals.contains "x" && s0.globals.contains "y")
          "the signed layer did not answer"
        check (c0.hits > 0) s!"the signed layer served nothing: {repr c0}"
        -- (no allowlist: fail closed, even though the index carries a signature)
        let (s1, c1) ← serve layer {}
        check (s1.globals.contains "x") "the text path did not answer"
        checkEq 0 c1.hits
        -- (a signature is never downgraded by --cache-ro-unsigned)
        let statsU ← IO.mkRef ({} : Cache.VerifyCounts)
        let (sU, _) ← Cache.elaborateCached none [layer] "import M\nimport N\n" init 0
          (verify := .warn) (rig := rig) (stats := some statsU) (roUnsigned := true)
        check (sU.globals.contains "x") "the text path did not answer"
        checkEq 0 (← statsU.get).hits
        -- (a tampered index: the signature no longer covers the bytes)
        let badIndex ← IO.FS.createTempDir
        cacheCopyTree layer badIndex
        let _ ← flipByte (badIndex / "manifest.sexpr")
        let isig ← Cache.checkLayerSignature badIndex policy
        check (!isig.accepted) "a tampered index was accepted"
        check (isig.code == Cache.Refusal.indexTampered ||
          isig.code == Cache.Refusal.indexInvalid ||
          isig.code == Cache.Refusal.indexOrphan) s!"unexpected code: {isig.code.code}"
        let (s2, c2) ← serve badIndex policy
        check (s2.globals.contains "x") "the text path did not answer after a tampered index"
        checkEq 0 c2.hits
        -- (a tampered manifest under an intact signature: the index record no longer
        -- matches, so the module is refused; N's intact manifest still serves)
        let badManifest ← IO.FS.createTempDir
        cacheCopyTree layer badManifest
        let some mf ← manifestFor badManifest "M" | throw (IO.userError "no manifest for M")
        let _ ← flipByte mf
        let mfsig ← Cache.checkLayerSignature badManifest policy
        check mfsig.accepted "the intact index should still verify"
        let (s3, c3) ← serve badManifest policy
        check (s3.globals.contains "x") "the text path did not answer after a tampered manifest"
        check (c3.hits > 0) "N's intact manifest should still serve"
        check (c3.mismatches > 0) s!"the tampered manifest was not counted: {repr c3}"
        -- (a re-seal chains the generation and the previous root)
        let g1 ← match ← Cache.readGeneration layer with
          | some g => pure g
          | none => throw (IO.userError "the signed layer has no generation index")
        let chain ← IO.FS.createTempDir
        cacheCopyTree layer chain
        IO.FS.removeFile (chain / "manifest.sexpr.sig")
        let _ ← Cache.sealLayer chain true 0
        let g2 ← match ← Cache.readGeneration chain with
          | some g => pure g
          | none => throw (IO.userError "the re-sealed layer has no generation index")
        check (g2.generation == g1.generation + 1)
          s!"the generation did not advance: {g1.generation} → {g2.generation}"
        check (g2.prev == g1.root) "prev does not name the old index's root"
        -- (a signed layer is never pruned or written, even when passed as --cache)
        let before ← snapshot layer
        let pruned ← Cache.pruneCache layer 7
        checkEq 0 pruned.total
        let msWrite ← Cache.ManifestStore.create (some layer) [] (← Cache.binaryId none) "" rig .warn
        msWrite.writeManifest { fast := 1, strong := String.ofList (List.replicate 64 '0') } "" #[] none
        let store ← Cache.Store.layered (R := ZeroOneMany) (some layer) [] (← Cache.binaryId none)
          (.warn) rig
        store.put { fast := 1 } {}
        store.markSeen { fast := 1 } "M"
        checkEq before (← snapshot layer) },
    { name := "a layer from another trust domain is refused and cannot ride an index", run := fun _ => do
        unless ← cacheHaveSshKeygen do
          skipMissing "no ssh-keygen"
          return
        let dir ← mkTree [("M.wiz", "import Prelude\ndef x : Nat := 2\n")]
        let ms ← Module.loadAll ["lib", dir]
        let init : CommandState ZeroOneMany :=
          { trustedModule := Tests.libModule, loader := loaderOf ms }
        let dirB ← mkTree [("M.wiz", "import Prelude\ndef x : Nat := 5\n")]
        let msB ← Module.loadAll ["lib", dirB]
        let initB : CommandState ZeroOneMany :=
          { trustedModule := Tests.libModule, loader := loaderOf msB }
        let rig := RigTag.tag (R := ZeroOneMany)
        let a ← IO.FS.createTempDir
        let (allowedA, policyA) ← cacheSignedLayer a "import M\n" init rig
        let b ← IO.FS.createTempDir
        let (_allowedB, policyB) ← cacheSignedLayer b "import M\n" initB rig
        -- (B verifies under its own key, not under A's: the signer names the domain)
        let bOwn ← Cache.checkLayerSignature b policyB
        check bOwn.accepted s!"B does not verify under its own key: {bOwn.status} {bOwn.detail}"
        let bUnderA ← Cache.checkLayerSignature b policyA
        check (!bUnderA.accepted) "a foreign signer was accepted"
        checkEq "invalid" bUnderA.status
        let statsB ← IO.mkRef ({} : Cache.VerifyCounts)
        let (sB, _) ← Cache.elaborateCached none [b] "import M\n" initB 0
          (verify := .warn) (rig := rig) (stats := some statsB) (policy := policyA)
        check (sB.globals.contains "x") "the text path did not answer"
        checkEq 0 (← statsB.get).hits
        let statsB2 ← IO.mkRef ({} : Cache.VerifyCounts)
        let (_, _) ← Cache.elaborateCached none [b] "import M\n" initB 0
          (verify := .warn) (rig := rig) (stats := some statsB2) (policy := policyB)
        check ((← statsB2.get).hits > 0) "B's own policy did not admit B"
        -- (B's manifest transplanted into A after A was signed: A's index records another
        -- digest, so the bytes are refused, not served)
        let mixed ← IO.FS.createTempDir
        cacheCopyTree a mixed
        let some mfA ← manifestFor mixed "M" | throw (IO.userError "no manifest for M in A")
        let some mfB ← manifestFor b "M" | throw (IO.userError "no manifest for M in B")
        IO.FS.writeBinFile mfA (← IO.FS.readBinFile mfB)
        let msig ← Cache.checkLayerSignature mixed policyA
        check msig.accepted "the index itself should still verify"
        let statsM ← IO.mkRef ({} : Cache.VerifyCounts)
        let (sM, _) ← Cache.elaborateCached none [mixed] "import M\n" init 0
          (verify := .warn) (rig := rig) (stats := some statsM) (policy := policyA)
        check (sM.globals.contains "x") "the text path did not answer"
        checkEq 0 (← statsM.get).hits
        let cm ← statsM.get
        check (cm.mismatches > 0) s!"the transplanted manifest was not refused: {repr cm}"
        -- (a policy file inside the layer is not a trust root)
        let inside ← IO.FS.createTempDir
        cacheCopyTree a inside
        IO.FS.writeFile (inside / "allowed_signers") (← IO.FS.readFile allowedA)
        let insidePolicy := { policyA with signers := some (inside / "allowed_signers") }
        let isig ← Cache.checkLayerSignature inside insidePolicy
        check (!isig.accepted) "a policy inside the layer was accepted"
        check (isig.code == Cache.Refusal.policyInLayer) s!"unexpected code: {isig.code.code}" },
    { name := "--cache-ro-unsigned serves an unsigned layer but never makes it writable", run := fun _ => do
        let dir ← mkTree [("M.wiz", "import Prelude\ndef x : Nat := 2\n")]
        let ms ← Module.loadAll ["lib", dir]
        let init : CommandState ZeroOneMany :=
          { trustedModule := Tests.libModule, loader := loaderOf ms }
        let rig := RigTag.tag (R := ZeroOneMany)
        let ro ← IO.FS.createTempDir
        let opts : Cache.RegionOptions := { rig }
        let _ ← Cache.elaborateCached (some ro) [] "import M\n" init 0
          (region := some opts) (verify := .warn) (rig := rig)
        check ((← regionFiles ro).size > 0) "no region was written"
        let before ← snapshot ro
        let stats ← IO.mkRef ({} : Cache.VerifyCounts)
        let rstats ← IO.mkRef ({} : Cache.RegionCounts)
        let ropts : Cache.RegionOptions := { rig, stats := some rstats }
        let (s, _) ← Cache.elaborateCached none [ro] "import M\n" init 0
          (region := some ropts) (verify := .warn) (rig := rig) (stats := some stats)
          (roUnsigned := true)
        check (s.globals.contains "x") "the opt-in layer did not answer"
        let ctext ← stats.get
        let cregion ← rstats.get
        check (ctext.hits > 0) s!"no text entry was served: {repr ctext}"
        check (cregion.hits > 0) s!"no region was served: {repr cregion}"
        checkEq before (← snapshot ro)
        -- (a miss still writes nothing: there is no write cache)
        let (s2, _) ← Cache.elaborateCached none [ro] "import M\ndef z : Nat := x\n" init 0
          (region := some ropts) (verify := .warn) (rig := rig) (roUnsigned := true)
        check (s2.globals.contains "z") "the miss did not elaborate"
        checkEq before (← snapshot ro)
        -- (the opt-in domain is named by its path; without the opt-in it is refused)
        let binary ← Cache.binaryId none
        let ms1 ← Cache.ManifestStore.create none [ro] binary "" rig .warn (roUnsigned := true)
        let t1 ← ms1.trustOf ro
        check t1.accepted "the opt-in layer was not admitted"
        checkEq s!"unsigned:{ro}" t1.domain.render
        let ms2 ← Cache.ManifestStore.create none [ro] binary "" rig .warn
        let t2 ← ms2.trustOf ro
        check (!t2.accepted) "an unsigned layer was admitted without the opt-in"
        check (t2.refusal == some Cache.Refusal.foreign) s!"unexpected refusal: {repr t2.refusal}" },
    { name := "--cache-signers/--cache-key-id/--cache-min-generation round-trip and stay out of the id", run := fun _ => do
        let parse (args : List String) := ({} : Toolchain).parseFlags args
        let (tc, rest) := parse ["--cache-signers", "/k", "--cache-key-id", "rel-1",
                                  "--cache-min-generation", "7", "check", "x.wiz"]
        checkEq ["check", "x.wiz"] rest
        checkEq (some "/k") (tc.cacheSigners.map toString)
        checkEq (some "rel-1") tc.cacheKeyId
        check (tc.cacheMinGeneration == some 7) "the minimum generation did not parse"
        let (back, rest) := parse tc.toFlags
        checkEq [] rest
        checkEq (repr tc).pretty (repr back).pretty
        check (tc.id == ({ tc with cacheSigners := none, cacheKeyId := none,
                           cacheMinGeneration := none } : Toolchain).id)
          "the cache signer policy is in the toolchain id"
        check ((tc.render.splitOn "cache-signers /k").length > 1) tc.render
        match ({} : Toolchain).set "cache-min-generation" "8" with
        | some t => check (t.cacheMinGeneration == some 8) "the build-file setting did not parse"
        | none => throw (IO.userError "cache-min-generation is not a build-file setting") }
  ]

builtin_initialize registerGroup toolchainGroup

end Tests.Grail
