import Tests.Grail

namespace Tests.Grail
open Wiz Tests

/-- A dependency as a bare repository (no network): a package with a library, tagged
`v1`; returns the bare repository and the work tree it was pushed from. -/
def depRepo : IO (System.FilePath × System.FilePath) := do
  let work ← mkTree [("grail.wiz", "import Grail\ndef package : Package := Package.new \"greet\"\n  |> Package.lib \"greet\" \"src\"\n"),
                     ("src/Greet/Hello.wiz", "import Prelude\ndef hello : Nat := 1\n")]
  let bare ← IO.FS.createTempDir
  let _ ← gitIn bare ["init", "--quiet", "--bare"]
  let _ ← gitIn work ["init", "--quiet"]
  let _ ← gitIn work ["add", "."]
  let _ ← gitIn work ["commit", "--quiet", "-m", "v1"]
  let _ ← gitIn work ["tag", "v1"]
  let _ ← gitIn work ["push", "--quiet", bare.toString, "HEAD:refs/heads/main", "v1"]
  pure (bare, work)

/-- A package that depends on `greet` at `rev`. -/
def depPkg (url rev : String) : List (String × String) :=
  [("grail.wiz", s!"import Grail\ndef package : Package := Package.new \"app\"\n  |> Package.dep \"greet\" \"{url}\" \"{rev}\"\n  |> Package.check \"app\" \"app.wiz\"\n"),
   ("app.wiz", "import Greet.Hello\n#eval hello + 1\n")]

def setGrailWiz (dir : System.FilePath) (url rev : String) : IO Unit :=
  IO.FS.writeFile (dir / "grail.wiz") ((depPkg url rev).head!.2)

/-- `grail update`, in-process. -/
def updateDeps (dir : System.FilePath) (tc : Toolchain) : IO (Except String (List Grail.Locked)) := do
  match ← Grail.readConfig tc (← binId tc) "lib" dir with
  | .error e => pure (.error e)
  | .ok (pkg, _) => Grail.update (fun d => do pure ((← Grail.readConfig tc (← binId tc) "lib" d).map (·.1))) dir pkg

/-- `grail build`, with the dependencies' roots; also the notes. -/
def buildDeps (dir : System.FilePath) (tc : Toolchain) : IO (Except String (Grail.Stats × Bool × String)) := do
  match ← Grail.readConfig tc (← binId tc) "lib" dir with
  | .error e => pure (.error e)
  | .ok (pkg, _) =>
    let log ← IO.mkRef ""
    match ← Grail.lockedRoots (fun d => do pure ((← Grail.readConfig tc (← binId tc) "lib" d).map (·.1))) dir pkg
        (fun s => log.modify (· ++ s)) with
    | .error e => pure (.error e)
    | .ok roots =>
      let r ← runner dir tc pkg 2 log
      let r := { r with ctx := { r.ctx with libRoots := r.ctx.libRoots ++ roots } }
      let ok ← r.build pkg.targets pkg.targets
      pure (.ok (← r.stats.get, ok, ← log.get))

/-- The readPkg of the tests: a package directory's manifest. -/
def readPkg (tc : Toolchain) (d : System.FilePath) : IO (Except String Grail.Package) := do
  pure ((← Grail.readConfig tc (← binId tc) "lib" d).map (·.1))

/-- The checked-in local index fixture (`Tests/fixtures/grail-index`): one `index/`
directory of S-expressions, relative `source` paths and their archives. Hermetic: no git,
no network, no generated tarballs. -/
def indexFixture : IO System.FilePath := do
  let p ← IO.FS.realPath "Tests/fixtures/grail-index"
  unless ← (p / "index").isDir do
    throw (IO.userError s!"{p}: no index/ directory (run the tests from the repository root)")
  pure p

/-- Build a package archive at runtime: a fresh `NAME-work/pkg/a.txt`, `prep` may add a
link or a file, and `extra` are tar options placed after `-czf OUT` (e.g. `-P` and
`--transform=…`). Returns the archive and its SHA-256. Hostile tarballs are built here,
never stored in the repository. -/
def buildArchive (root : System.FilePath) (name : String) (extra : List String := [])
    (prep : System.FilePath → IO Unit := fun _ => pure ()) : IO (System.FilePath × String) := do
  let work := root / s!"{name}-work"
  IO.FS.createDirAll (work / "pkg")
  IO.FS.writeFile (work / "pkg" / "a.txt") "ok\n"
  prep work
  let out := root / s!"{name}.tar.gz"
  let _ ← runIn root "tar" (["-czf", out.toString] ++ extra ++ ["-C", work.toString, "pkg"])
  let sha := ((← runIn root "sha256sum" [out.toString]).splitOn " ").head!
  pure (out, sha)

/-- `untar` refuses the archive built from `name`, the message names `needle`, and nothing
was extracted. -/
def checkEscapes (root : System.FilePath) (name needle : String) (extra : List String := [])
    (prep : System.FilePath → IO Unit := fun _ => pure ()) : IO Unit := do
  let (tar, _) ← buildArchive root name extra prep
  let dest := root / s!"{name}-extract"
  IO.FS.createDirAll dest
  match ← Grail.Registry.untar tar dest with
  | .error e => check ((e.splitOn needle).length > 1) s!"{name}: {e}"
  | .ok () => throw (IO.userError s!"{name}: the archive was unpacked")
  checkEq 0 (← dest.readDir).size

def grailDepsGroup : Group where
  name := "grail-deps"
  exercise := "Stage 23h"
  parallel := true
  cases := [
    { name := "a git dependency: grail update writes the lock, builds use it", run := fun _ => do
        let (bare, work) ← depRepo
        let url := bare.toString
        let dir ← mkTree (depPkg url "v1")
        let tc : Toolchain := { cacheDir := some (← IO.FS.createTempDir) }
        -- no lock yet
        match ← buildDeps dir tc with
        | .error e => check ((e.splitOn "grail update").length > 1) e
        | .ok _ => throw (IO.userError "built without grail.lock")
        let .ok [l] ← updateDeps dir tc | throw (IO.userError "grail update failed")
        let v1 ← gitIn work ["rev-parse", "v1"]
        checkEq v1 l.commit
        let lock ← IO.FS.readFile (dir / "grail.lock")
        check ((Grail.parseLock lock |>.toOption) == some [l]) s!"grail.lock: {lock}"
        check ((lock.splitOn v1).length == 2) lock
        check (← (dir / ".grail/packages/greet/src/Greet/Hello.wiz").pathExists) "not fetched"
        let .ok (s, ok, log) ← buildDeps dir tc | throw (IO.userError "the build failed")
        check ok log
        checkEq 1 s.ran
        check ((log.splitOn "app.wiz:2:1: info: 2").length == 2) log
        -- again: nothing runs
        let .ok (s, _, _) ← buildDeps dir tc | throw (IO.userError "the second build failed")
        checkEq 0 s.ran
        -- a new tag upstream; grail.wiz asks for it, but the lock still has v1
        IO.FS.writeFile (work / "src/Greet/Hello.wiz") "import Prelude\ndef hello : Nat := 41\n"
        let _ ← gitIn work ["commit", "--quiet", "-am", "v2"]
        let _ ← gitIn work ["tag", "v2"]
        let _ ← gitIn work ["push", "--quiet", url, "HEAD:refs/heads/main", "v2"]
        setGrailWiz dir url "v2"
        let .ok (s, ok, log) ← buildDeps dir tc | throw (IO.userError "the build failed")
        check ok log
        checkEq 0 s.ran
        check ((log.splitOn "grail update").length > 1) s!"no note: {log}"
        checkEq v1 (← gitIn (dir / ".grail/packages/greet") ["rev-parse", "HEAD"])
        checkEq lock (← IO.FS.readFile (dir / "grail.lock"))
        -- grail update moves it
        let .ok [l2] ← updateDeps dir tc | throw (IO.userError "grail update failed")
        checkEq (← gitIn work ["rev-parse", "v2"]) l2.commit
        check (l2.content != l.content) "the content hash did not change"
        let .ok (s, ok, log) ← buildDeps dir tc | throw (IO.userError "the build failed")
        check ok log
        checkEq 1 s.ran
        check ((log.splitOn "app.wiz:2:1: info: 42").length == 2) log },
    { name := "a fresh checkout fetches the locked commit; edited files are refused", run := fun _ => do
        let (bare, _) ← depRepo
        let dir ← mkTree (depPkg bare.toString "main")
        let tc : Toolchain := { cacheDir := some (← IO.FS.createTempDir) }
        let .ok [l] ← updateDeps dir tc | throw (IO.userError "grail update failed")
        -- as if the package were cloned elsewhere: no .grail
        IO.FS.removeDirAll (dir / ".grail")
        let .ok (_, ok, log) ← buildDeps dir tc | throw (IO.userError "the build failed")
        check ok log
        checkEq l.commit (← gitIn (dir / ".grail/packages/greet") ["rev-parse", "HEAD"])
        IO.FS.writeFile (dir / ".grail/packages/greet/src/Greet/Hello.wiz") "import Prelude\ndef hello : Nat := 5\n"
        match ← buildDeps dir tc with
        | .error e => check ((e.splitOn "differs from").length > 1) e
        | .ok _ => throw (IO.userError "built with edited dependency files") },
    { name := "two commits of one dependency are refused", run := fun _ => do
        -- `mid` depends on greet at v1; the app on greet at main (a later commit) and on mid
        let (bare, work) ← depRepo
        IO.FS.writeFile (work / "src/Greet/Hello.wiz") "import Prelude\ndef hello : Nat := 2\n"
        let _ ← gitIn work ["commit", "--quiet", "-am", "later"]
        let _ ← gitIn work ["push", "--quiet", bare.toString, "HEAD:refs/heads/main"]
        let midWork ← mkTree [("grail.wiz", s!"import Grail\ndef package : Package := Package.new \"mid\"\n  |> Package.dep \"greet\" \"{bare}\" \"v1\"\n")]
        let midBare ← IO.FS.createTempDir
        let _ ← gitIn midBare ["init", "--quiet", "--bare"]
        let _ ← gitIn midWork ["init", "--quiet"]
        let _ ← gitIn midWork ["add", "."]
        let _ ← gitIn midWork ["commit", "--quiet", "-m", "mid"]
        let _ ← gitIn midWork ["push", "--quiet", midBare.toString, "HEAD:refs/heads/main"]
        let dir ← mkTree [("grail.wiz", s!"import Grail\ndef package : Package := Package.new \"app\"\n  |> Package.dep \"greet\" \"{bare}\" \"main\"\n  |> Package.dep \"mid\" \"{midBare}\" \"main\"\n")]
        let tc : Toolchain := { cacheDir := some (← IO.FS.createTempDir) }
        match ← updateDeps dir tc with
        | .error e => check ((e.splitOn "two commits of greet").length > 1) e
        | .ok ls => throw (IO.userError s!"resolved: {repr ls}") },
    { name := "a registry package: the lock, `fetch`, and the build imports it", run := fun _ => do
        let (root, dir, sha, tc) ← registryTree
        let .ok (pkg, _) ← Grail.readConfig tc (← binId tc) "lib" dir | throw (IO.userError "bad manifest")
        let idx := root / "index"
        let cache := tc.cacheDir.getD "."
        let .ok lock ← Grail.Registry.resolveLock cache idx.toString false (readPkg tc) dir pkg
          | throw (IO.userError "resolve failed")
        checkEq 1 lock.pkgs.length
        checkEq sha lock.pkgs.head!.sha256
        let text := Grail.Lock.render lock
        IO.FS.writeFile (dir / "grail.lock") text
        check ((Grail.Lock.parse text).toOption.isSome) text
        let .ok lines ← Grail.Registry.fetch cache dir lock | throw (IO.userError "fetch failed")
        check ((lines.head!.splitOn "fetched").length > 1) lines.head!
        checkEq (some sha) (← Grail.Registry.stamp (dir / ".grail/packages/greet"))
        -- a second fetch unpacks nothing
        let .ok lines ← Grail.Registry.fetch cache dir lock | throw (IO.userError "second fetch failed")
        check ((lines.head!.splitOn "up to date").length > 1) lines.head!
        -- the build gets the package's lib root and checks the import
        let .ok roots ← Grail.Registry.lockedRoots cache (readPkg tc) dir pkg (fun _ => pure ())
          | throw (IO.userError "lockedRoots failed")
        checkEq 1 roots.length
        let log ← IO.mkRef ""
        let r ← runner dir tc pkg 2 log
        let r := { r with ctx := { r.ctx with libRoots := r.ctx.libRoots ++ roots } }
        let ok ← r.build pkg.targets pkg.targets
        check ok (← log.get)
        check (((← log.get).splitOn "app.wiz:2:1: info: 42").length == 2) (← log.get) },
    { name := "a wrong sha256 is refused before anything is unpacked; a stale lock too", run := fun _ => do
        let (root, dir, sha, tc) ← registryTree
        let .ok (pkg, _) ← Grail.readConfig tc (← binId tc) "lib" dir | throw (IO.userError "bad manifest")
        let idx := root / "index"
        let cache := tc.cacheDir.getD "."
        let .ok lock ← Grail.Registry.resolveLock cache idx.toString false (readPkg tc) dir pkg
          | throw (IO.userError "resolve failed")
        let bad := { lock with pkgs := lock.pkgs.map fun p => { p with sha256 := String.ofList (List.replicate 64 '0') } }
        match ← Grail.Registry.fetch cache dir bad with
        | .error e => check ((e.splitOn "sha256").length > 1) e
        | .ok _ => throw (IO.userError "fetched an archive with a wrong hash")
        check (!(← (dir / ".grail/packages/greet").pathExists)) "something was unpacked"
        -- a requirement the lock does not satisfy
        checkEq sha lock.pkgs.head!.sha256
        let stale := s!"import Grail\ndef package : Package := Package.new \"app\"\n  |> Package.require \"greet\" \"^2\"\n"
        IO.FS.writeFile (dir / "grail.wiz") stale
        let .ok (pkg2, _) ← Grail.readConfig tc (← binId tc) "lib" dir | throw (IO.userError "bad manifest")
        match Grail.Registry.checkLocked lock pkg2 with
        | .error e => check ((e.splitOn "run `grail update`").length > 1) e
        | .ok _ => throw (IO.userError "a stale lock passed") },
    { name := "the resolver: highest version, yanks, conflicts, the toolchain", run := fun _ => do
        let sha := String.ofList (List.replicate 64 'a')
        let index := s!"(index (package \"p\" (version \"1.0.0\" (source \"x\") (sha256 \"{sha}\")) (version \"1.2.0\" (source \"y\") (sha256 \"{sha}\") (deps (dep \"q\" \"^1\"))) (version \"2.0.0\" (source \"z\") (sha256 \"{sha}\")) (version \"2.1.0\" (source \"w\") (sha256 \"{sha}\") (toolchain \">=9.0\")) (yanked \"2.0.0\" \"broken\")) (package \"q\" (version \"1.1.0\" (source \"q1\") (sha256 \"{sha}\")) (version \"1.5.0\" (source \"q2\") (sha256 \"{sha}\"))))"
        let .ok ps := Grail.Index.parse index | throw (IO.userError "bad index")
        let idx := ps.foldl (fun m p => m.insert p.name p) {}
        let resolved (roots : List Grail.Req) : Except String (List Grail.Resolved) :=
          Grail.Resolve.resolve idx roots "0.1.0-dev"
        -- highest satisfying, transitively
        let .ok rs := resolved [⟨"p", "^1"⟩] | throw (IO.userError "resolve failed")
        checkEq 2 rs.length
        checkEq "1.2.0" ((rs.find? (·.name == "p")).map (Grail.Version.render ·.version) |>.getD "?")
        checkEq "1.5.0" ((rs.find? (·.name == "q")).map (Grail.Version.render ·.version) |>.getD "?")
        -- another requirement on p narrows it (1.0.0 satisfies both)
        let .ok rs := resolved [⟨"p", "^1"⟩, ⟨"p", "1.0"⟩] | throw (IO.userError "resolve failed")
        checkEq "1.0.0" ((rs.find? (·.name == "p")).map (Grail.Version.render ·.version) |>.getD "?")
        -- `~1` is `>=1.0.0 <2.0.0`; `~1.0` is `>=1.0.0 <1.1.0`
        let .ok rs := resolved [⟨"p", "~1"⟩] | throw (IO.userError "resolve failed")
        checkEq "1.2.0" ((rs.find? (·.name == "p")).map (Grail.Version.render ·.version) |>.getD "?")
        let .ok rs := resolved [⟨"p", "~1.0"⟩] | throw (IO.userError "resolve failed")
        checkEq "1.0.0" ((rs.find? (·.name == "p")).map (Grail.Version.render ·.version) |>.getD "?")
        -- `^0` and `^0.0` follow Cargo/npm's leftmost-non-zero rule: `^0` is <1.0.0,
        -- `^0.0` is <0.1.0 (the prototype used to treat both as <0.0.1)
        let zeros := s!"(index (package \"p0\" (version \"0.0.3\" (source \"z0\") (sha256 \"{sha}\")) (version \"0.1.0\" (source \"z1\") (sha256 \"{sha}\")) (version \"0.2.0\" (source \"z2\") (sha256 \"{sha}\")) (version \"1.0.0\" (source \"z3\") (sha256 \"{sha}\"))))"
        let .ok zps := Grail.Index.parse zeros | throw (IO.userError "bad zero index")
        let zidx := zps.foldl (fun m p => m.insert p.name p) {}
        let zresolved (req : String) : Except String (List Grail.Resolved) :=
          Grail.Resolve.resolve zidx [⟨"p0", req⟩] "0.1.0-dev"
        let zver (rs : List Grail.Resolved) : String :=
          (rs.find? (·.name == "p0")).map (Grail.Version.render ·.version) |>.getD "?"
        let .ok z := zresolved "^0" | throw (IO.userError "^0 failed")
        checkEq "0.2.0" (zver z)
        let .ok z := zresolved "^0.0" | throw (IO.userError "^0.0 failed")
        checkEq "0.0.3" (zver z)
        let .ok z := zresolved "^0.1" | throw (IO.userError "^0.1 failed")
        checkEq "0.1.0" (zver z)
        let .ok z := zresolved "^0.0.3" | throw (IO.userError "^0.0.3 failed")
        checkEq "0.0.3" (zver z)
        -- 2.0.0 is yanked; 2.1.0 needs a newer toolchain
        match resolved [⟨"p", "^2"⟩] with
        | .error e => check ((e.splitOn "no version satisfies").length > 1) e
        | .ok _ => throw (IO.userError "a yanked/incompatible version was chosen")
        -- a requirement no version satisfies
        match resolved [⟨"p", "3"⟩] with
        | .error e => check ((e.splitOn "no version satisfies").length > 1) e
        | .ok _ => throw (IO.userError "resolved a missing version") },
    { name := "the CLI: update/fetch --locked and --offline", run := fun _ => do
        let (root, dir, sha, _tc) ← registryTree
        let idx := root / "index"
        let std ← IO.FS.realPath "lib"
        let run (args : List String) : IO UInt32 :=
          Grail.cliMain (["-C", dir.toString, "--std", std.toString,
            "--cache", (root / "cache").toString, "--index", idx.toString] ++ args)
        -- no lock yet: `update --locked` and `fetch --locked` fail; update writes one
        checkEq 1 (← run ["update", "--locked"])
        checkEq 0 (← run ["update"])
        checkEq 0 (← run ["update", "--locked"])
        -- a manifest requirement the lock does not satisfy
        let req2 := s!"import Grail\ndef package : Package := Package.new \"app\"\n  |> Package.set \"index\" \"{idx}\"\n  |> Package.require \"greet\" \"^2\"\n"
        IO.FS.writeFile (dir / "grail.wiz") req2
        checkEq 1 (← run ["update", "--locked"])
        checkEq 1 (← run ["fetch", "--locked"])
        -- back to ^1: update repairs the lock
        let req1 := s!"import Grail\ndef package : Package := Package.new \"app\"\n  |> Package.set \"index\" \"{idx}\"\n  |> Package.require \"greet\" \"^1\"\n"
        IO.FS.writeFile (dir / "grail.wiz") req1
        checkEq 0 (← run ["update"])
        -- fetch: --offline refuses to download an archive that is not cached
        checkEq 1 (← run ["fetch", "--locked", "--offline"])
        check (!(← (dir / ".grail/packages/greet").pathExists)) "an offline fetch unpacked something"
        checkEq 0 (← run ["fetch", "--locked"])
        let stamp := (← IO.FS.readFile (dir / ".grail/packages/greet/.grail-pkg")).trimAscii.toString
        checkEq sha stamp
        -- with the archive cached, an offline fetch works even after `.grail` is gone
        IO.FS.removeDirAll (dir / ".grail")
        checkEq 0 (← run ["fetch", "--locked", "--offline"])
        check (← (dir / ".grail/packages/greet/src/Greet/Hello.wiz").pathExists) "not unpacked"
        -- a package with no dependencies and no lock: both succeed and do nothing
        let empty ← mkTree [("grail.wiz", "import Grail\ndef package : Package := Package.new \"empty\"\n")]
        let runEmpty (args : List String) : IO UInt32 :=
          Grail.cliMain (["-C", empty.toString, "--std", std.toString] ++ args)
        checkEq 0 (← runEmpty ["fetch", "--locked"])
        checkEq 0 (← runEmpty ["update", "--locked"])
        check (!(← (empty / "grail.lock").pathExists)) "a lock was written for an empty package" },
    { name := "a git-backed index: the clone, --offline, and the lock's commit", run := fun _ => do
        let root ← IO.FS.createTempDir
        let cache := root / "cache"
        let idxWork ← IO.FS.createTempDir
        let idxBare := root / "index.git"
        let _ ← gitIn idxWork ["init", "--quiet"]
        IO.FS.createDirAll (idxWork / "index")
        let writeGreet (v tar sha : String) : IO Unit :=
          IO.FS.writeFile (idxWork / "index/greet.sexpr")
            s!"(index (package \"greet\" (version \"{v}\" (source \"file://{tar}\") (sha256 \"{sha}\") (toolchain \">=0.1.0\") (deps))))\n"
        let (tar1, sha1) ← tarballOf root "greet" "1.0.0"
          [("grail.wiz", "import Grail\ndef package : Package := Package.new \"greet\"\n  |> Package.version \"1.0.0\"\n  |> Package.lib \"greet\" \"src\"\n"),
           ("src/Greet/Hello.wiz", "import Prelude\ndef hello : Nat := 1\n")]
        writeGreet "1.0.0" tar1.toString sha1
        IO.FS.writeFile (idxWork / "registry.sexpr") "(registry (name \"test/grail-index\") (format 1))\n"
        let _ ← gitIn idxWork ["add", "."]
        let _ ← gitIn idxWork ["commit", "--quiet", "-m", "v1"]
        let _ ← runIn root "git" ["clone", "--quiet", "--bare", idxWork.toString, idxBare.toString]
        let _ ← gitIn idxBare ["symbolic-ref", "HEAD", "refs/heads/main"]
        let _ ← gitIn idxWork ["push", "--quiet", idxBare.toString, "HEAD:refs/heads/main"]
        let commit1 ← gitIn idxWork ["rev-parse", "HEAD"]
        -- a local git index is a URL: a plain path is a directory index
        let idxUrl := s!"file://{idxBare}"
        let dir ← mkTree [
          ("grail.wiz", s!"import Grail\ndef package : Package := Package.new \"app\"\n  |> Package.set \"index\" \"{idxUrl}\"\n  |> Package.require \"greet\" \"^1\"\n"),
          ("app.wiz", "import Greet.Hello\n#eval hello + 1\n")]
        let tc : Toolchain := { cacheDir := some cache }
        let .ok (pkg, _) ← Grail.readConfig tc (← binId tc) "lib" dir | throw (IO.userError "bad manifest")
        -- no cache yet: --offline cannot clone
        match ← Grail.Registry.resolveLock cache idxUrl true (readPkg tc) dir pkg with
        | .error e => check ((e.splitOn "--offline").length > 1) e
        | .ok _ => throw (IO.userError "resolved from an uncached git index offline")
        let .ok lock ← Grail.Registry.resolveLock cache idxUrl false (readPkg tc) dir pkg
          | throw (IO.userError "resolve from a git index failed")
        checkEq commit1 lock.indexCommit
        checkEq idxUrl lock.indexUrl
        checkEq "1.0.0" lock.pkgs.head!.version
        -- a bare repository path works too (it is cloned, not read as a directory index)
        let .ok viaPath ← Grail.Registry.resolveLock (root / "cache-path") idxBare.toString false (readPkg tc) dir pkg
          | throw (IO.userError "resolve from a bare repository path failed")
        checkEq commit1 viaPath.indexCommit
        -- a new version upstream; an offline resolve reads the cached clone (commit1)
        let (tar2, sha2) ← tarballOf root "greet" "1.2.0"
          [("grail.wiz", "import Grail\ndef package : Package := Package.new \"greet\"\n  |> Package.version \"1.2.0\"\n  |> Package.lib \"greet\" \"src\"\n"),
           ("src/Greet/Hello.wiz", "import Prelude\ndef hello : Nat := 41\n")]
        writeGreet "1.2.0" tar2.toString sha2
        let _ ← gitIn idxWork ["commit", "--quiet", "-am", "v2"]
        let _ ← gitIn idxWork ["push", "--quiet", idxBare.toString, "HEAD:refs/heads/main"]
        let commit2 ← gitIn idxWork ["rev-parse", "HEAD"]
        let .ok offline ← Grail.Registry.resolveLock cache idxUrl true (readPkg tc) dir pkg
          | throw (IO.userError "an offline resolve from the cached index failed")
        checkEq commit1 offline.indexCommit
        checkEq "1.0.0" offline.pkgs.head!.version
        let .ok online ← Grail.Registry.resolveLock cache idxUrl false (readPkg tc) dir pkg
          | throw (IO.userError "the second online resolve failed")
        checkEq commit2 online.indexCommit
        checkEq "1.2.0" online.pkgs.head!.version },
    { name := "a yanked version is skipped by update but kept by an existing lock", run := fun _ => do
        let root ← IO.FS.createTempDir
        let idx := root / "index"
        IO.FS.createDirAll idx
        let cache := root / "cache"
        let (tar1, sha1) ← tarballOf root "greet" "1.0.0"
          [("grail.wiz", "import Grail\ndef package : Package := Package.new \"greet\"\n  |> Package.version \"1.0.0\"\n  |> Package.lib \"greet\" \"src\"\n"),
           ("src/Greet/Hello.wiz", "import Prelude\ndef hello : Nat := 1\n")]
        let (tar2, sha2) ← tarballOf root "greet" "1.2.0"
          [("grail.wiz", "import Grail\ndef package : Package := Package.new \"greet\"\n  |> Package.version \"1.2.0\"\n  |> Package.lib \"greet\" \"src\"\n"),
           ("src/Greet/Hello.wiz", "import Prelude\ndef hello : Nat := 41\n")]
        let writeIndex (yanked : Bool) : IO Unit :=
          IO.FS.writeFile (idx / "greet.sexpr")
            s!"(index (package \"greet\" (version \"1.0.0\" (source \"file://{tar1}\") (sha256 \"{sha1}\") (toolchain \">=0.1.0\") (deps)) (version \"1.2.0\" (source \"file://{tar2}\") (sha256 \"{sha2}\") (toolchain \">=0.1.0\") (deps)){if yanked then " (yanked \"1.2.0\" \"wrong tarball\")" else ""}))\n"
        writeIndex false
        let dir ← mkTree [
          ("grail.wiz", s!"import Grail\ndef package : Package := Package.new \"app\"\n  |> Package.set \"index\" \"{idx}\"\n  |> Package.require \"greet\" \"^1\"\n  |> Package.check \"app\" \"app.wiz\"\n"),
          ("app.wiz", "import Greet.Hello\n#eval hello + 1\n")]
        let tc : Toolchain := { cacheDir := some cache }
        let .ok (pkg, _) ← Grail.readConfig tc (← binId tc) "lib" dir | throw (IO.userError "bad manifest")
        let .ok old ← Grail.Registry.resolveLock cache idx.toString false (readPkg tc) dir pkg
          | throw (IO.userError "resolve failed")
        checkEq "1.2.0" old.pkgs.head!.version
        -- yank 1.2.0: a new resolution moves to 1.0.0; the old lock is still fetchable
        writeIndex true
        let .ok fresh ← Grail.Registry.resolveLock cache idx.toString false (readPkg tc) dir pkg
          | throw (IO.userError "the post-yank resolve failed")
        checkEq "1.0.0" fresh.pkgs.head!.version
        match Grail.Registry.checkLocked old pkg with
        | .ok () => pure ()
        | .error e => throw (IO.userError s!"a lock on a yanked version was refused: {e}")
        let .ok lines ← Grail.Registry.fetch cache dir old | throw (IO.userError "fetch of the yanked lock failed")
        checkEq 1 lines.length
        checkEq (some sha2) (← Grail.Registry.stamp (dir / ".grail/packages/greet")) },
    { name := "transitive resolution: the lock is the closure, fetch and build use it", run := fun _ => do
        let root ← IO.FS.createTempDir
        let idx := root / "index"
        IO.FS.createDirAll idx
        let cache := root / "cache"
        let mkPkg (name version hello : String) : IO (System.FilePath × String) :=
          tarballOf root name version
            [("grail.wiz", s!"import Grail\ndef package : Package := Package.new \"{name}\"\n  |> Package.version \"{version}\"\n  |> Package.lib \"{name}\" \"src\"\n"),
             (s!"src/{name}/Hello.wiz", s!"import Prelude\ndef {name}Value : Nat := {hello}\n")]
        let (tarLeaf, shaLeaf) ← mkPkg "leaf" "1.0.0" "40"
        let (tarMid, shaMid) ← mkPkg "mid" "1.0.0" "41"
        let (tarTop, shaTop) ← mkPkg "top" "1.0.0" "42"
        IO.FS.writeFile (idx / "leaf.sexpr")
          s!"(index (package \"leaf\" (version \"1.0.0\" (source \"file://{tarLeaf}\") (sha256 \"{shaLeaf}\") (deps))))\n"
        IO.FS.writeFile (idx / "mid.sexpr")
          s!"(index (package \"mid\" (version \"1.0.0\" (source \"file://{tarMid}\") (sha256 \"{shaMid}\") (deps (dep \"leaf\" \"^1\")))))\n"
        IO.FS.writeFile (idx / "top.sexpr")
          s!"(index (package \"top\" (version \"1.0.0\" (source \"file://{tarTop}\") (sha256 \"{shaTop}\") (deps (dep \"mid\" \"^1\")))))\n"
        let dir ← mkTree [
          ("grail.wiz", s!"import Grail\ndef package : Package := Package.new \"app\"\n  |> Package.set \"index\" \"{idx}\"\n  |> Package.require \"top\" \"^1\"\n  |> Package.check \"app\" \"app.wiz\"\n"),
          ("app.wiz", "import top.Hello\nimport mid.Hello\nimport leaf.Hello\n#eval leafValue\n")]
        let tc : Toolchain := { cacheDir := some cache }
        let .ok (pkg, _) ← Grail.readConfig tc (← binId tc) "lib" dir | throw (IO.userError "bad manifest")
        let .ok lock ← Grail.Registry.resolveLock cache idx.toString false (readPkg tc) dir pkg
          | throw (IO.userError "resolve failed")
        checkEq ["leaf", "mid", "top"] (lock.pkgs.map (·.name))
        -- the lock round-trips (v2: the index and every pkg with its deps)
        let text := Grail.Lock.render lock
        let .ok parsed := Grail.Lock.parse text | throw (IO.userError s!"could not parse the lock: {text}")
        let pkgsText : List Grail.PkgLock → String := fun ps =>
          "\n".intercalate (ps.map fun p =>
            s!"{p.name} {p.version} {p.source} {p.sha256} " ++
              " ".intercalate (p.deps.map fun d => s!"{d.name}={d.req}"))
        checkEq (pkgsText lock.pkgs) (pkgsText parsed.pkgs)
        checkEq lock.indexUrl parsed.indexUrl
        checkEq lock.indexCommit parsed.indexCommit
        IO.FS.writeFile (dir / "grail.lock") text
        -- a missing member of the closure is refused before anything is fetched
        let incomplete := { lock with pkgs := lock.pkgs.filter (·.name != "leaf") }
        match Grail.Registry.checkLocked incomplete pkg with
        | .error e => check ((e.splitOn "incomplete").length > 1) e
        | .ok _ => throw (IO.userError "an incomplete lock passed checkLocked")
        let .ok lines ← Grail.Registry.fetch cache dir lock | throw (IO.userError "fetch failed")
        checkEq 3 lines.length
        let roots ← match ← Grail.Registry.lockedRoots cache (readPkg tc) dir pkg (fun _ => pure ()) with
          | .ok roots => pure roots
          | .error e => throw (IO.userError s!"lockedRoots failed: {e}")
        checkEq 3 roots.length
        let log ← IO.mkRef ""
        let r ← runner dir tc pkg 2 log
        let r := { r with ctx := { r.ctx with libRoots := r.ctx.libRoots ++ roots } }
        let ok ← r.build pkg.targets pkg.targets
        check ok (← log.get)
        check (((← log.get).splitOn "app.wiz:4:1: info: 40").length == 2) (← log.get) },
    { name := "a corrupt archive cache is re-fetched; --offline refuses a missing one", run := fun _ => do
        let (root, dir, sha, tc) ← registryTree
        let idx := root / "index"
        let cache := tc.cacheDir.getD "."
        let .ok (pkg, _) ← Grail.readConfig tc (← binId tc) "lib" dir | throw (IO.userError "bad manifest")
        let .ok lock ← Grail.Registry.resolveLock cache idx.toString false (readPkg tc) dir pkg
          | throw (IO.userError "resolve failed")
        -- a cache entry with the right name but the wrong bytes is re-fetched and verified
        let f := cache / "grail" / "downloads" / sha
        if let some d := f.parent then IO.FS.createDirAll d
        IO.FS.writeFile f "not the archive"
        let .ok _ ← Grail.Registry.fetch cache dir lock | throw (IO.userError "fetch did not repair the cache")
        let .ok h ← Grail.Registry.sha256File f | throw (IO.userError "could not hash the cache entry")
        checkEq sha h
        -- offline: a cached archive unpacks, a missing one is an error and nothing is written
        Grail.Registry.removePath (dir / ".grail/packages/greet")
        Grail.Registry.removePath (cache / "grail" / "packages" / sha)
        IO.FS.removeFile f
        match ← Grail.Registry.fetch cache dir lock true with
        | .error e => check ((e.splitOn "--offline").length > 1) e
        | .ok _ => throw (IO.userError "an offline fetch downloaded an archive")
        check (!(← (dir / ".grail/packages/greet").pathExists)) "an offline fetch unpacked something"
        let .ok _ ← Grail.Registry.fetch cache dir lock false | throw (IO.userError "the online fetch failed")
        Grail.Registry.removePath (dir / ".grail/packages/greet")
        let .ok _ ← Grail.Registry.fetch cache dir lock true | throw (IO.userError "the cached offline fetch failed")
        check (← (dir / ".grail/packages/greet/src/Greet/Hello.wiz").pathExists) "not unpacked offline" },
    { name := "a deterministic archive and the publish entry", run := fun _ => do
        let root ← IO.FS.createTempDir
        let work ← mkTree [
          ("grail.wiz", "import Grail\ndef package : Package := Package.new \"greet\"\n  |> Package.version \"1.0.0\"\n  |> Package.toolchain \">=0.1 <0.3\"\n  |> Package.require \"std\" \"^0.1\"\n  |> Package.lib \"greet\" \"src\"\n"),
          ("src/Greet/Hello.wiz", "import Prelude\ndef hello : Nat := 1\n")]
        let _ ← gitIn work ["init", "--quiet"]
        let _ ← gitIn work ["add", "."]
        let _ ← gitIn work ["commit", "--quiet", "-m", "release"]
        let archive (name : String) : IO System.FilePath := do
          let out := root / name
          let _ ← runIn work "sh" ["-c", s!"git archive --format=tar --prefix=greet-1.0.0/ HEAD | gzip -n > {out}"]
          pure out
        let a1 ← archive "a.tar.gz"
        let a2 ← archive "b.tar.gz"
        let sha1 ← runIn root "sha256sum" [a1.toString] |>.map (·.splitOn " " |>.head!)
        let sha2 ← runIn root "sha256sum" [a2.toString] |>.map (·.splitOn " " |>.head!)
        checkEq sha1 sha2
        let .ok (pkg, _) ← Grail.readConfig {} 7 "lib" work | throw (IO.userError "bad manifest")
        -- the publish entry hashes the archive and records the manifest's toolchain and deps
        let .ok entry ← Grail.Registry.publish (some a1) "https://example.org/greet-1.0.0.tar.gz" pkg
          | throw (IO.userError "publish failed")
        check ((entry.splitOn "1.0.0").length > 1) entry
        check ((entry.splitOn sha1).length > 1) entry
        check ((entry.splitOn ">=0.1 <0.3").length > 1) entry
        let .ok ps := Grail.Index.parse s!"(index (package \"greet\" {entry}))"
          | throw (IO.userError s!"the publish entry does not parse: {entry}")
        checkEq 1 ps.length
        checkEq "1.0.0" (Grail.Version.render ps.head!.versions.head!.version)
        checkEq sha1 ps.head!.versions.head!.sha256
        checkEq ["std ^0.1"] ((ps.head!.versions.head!.deps).map fun d => s!"{d.name} {d.req}")
        -- a version is immutable once in the index
        match Grail.Index.addVersion ps ps.head! ps.head!.versions.head! with
        | .error e => check ((e.splitOn "immutable").length > 1) e
        | .ok _ => throw (IO.userError "addVersion replaced an existing version")
        -- the archive layout is checked: one top directory, with grail.wiz in it
        let bad := root / "bad.tar.gz"
        let _ ← runIn work "tar" ["-czf", bad.toString, "."]
        match ← Grail.Registry.publish (some bad) "https://example.org/bad.tar.gz" pkg with
        | .error e => check ((e.splitOn "layout").length > 1 || (e.splitOn "top directory").length > 1) e
        | .ok _ => throw (IO.userError "publish accepted the wrong archive layout") },
    { name := "the local index fixture: exact, ranges, transitive deps, missing packages", run := fun _ => do
        let fixture ← indexFixture
        let cache ← IO.FS.createTempDir
        let .ok src ← Grail.Registry.loadIndex cache fixture.toString false
          | throw (IO.userError "the fixture index did not load")
        let resolve (reqs : List Grail.Req) := Grail.Resolve.resolve src.pkgs reqs "0.1.0-dev"
        let ver (rs : List Grail.Resolved) (n : String) : String :=
          (rs.find? (·.name == n)).map (fun r => Grail.Version.render r.version) |>.getD "?"
        -- an exact version
        let .ok exact := resolve [⟨"greet", "1.0.0"⟩] | throw (IO.userError "exact resolve failed")
        checkEq 3 exact.length
        checkEq "1.0.0" (ver exact "greet")
        checkEq "1.0.0" (ver exact "text")
        checkEq "0.1.0" (ver exact "std")
        -- relative `source`s are resolved against the index directory
        let some greetExact := exact.find? (·.name == "greet") | throw (IO.userError "no greet")
        check (greetExact.source.endsWith "packages/greet-1.0.0.tar.gz") greetExact.source
        check (← (System.FilePath.mk greetExact.source).pathExists) greetExact.source
        -- a caret range picks the highest 1.x and its transitive closure
        let .ok caret := resolve [⟨"greet", "^1"⟩] | throw (IO.userError "caret resolve failed")
        checkEq "1.2.0" (ver caret "greet")
        checkEq "1.1.0" (ver caret "text")
        checkEq "0.1.0" (ver caret "std")
        -- a tilde range stops at the next minor, which narrows the transitive dep too
        let .ok tilde := resolve [⟨"greet", "~1.0"⟩] | throw (IO.userError "tilde resolve failed")
        checkEq "1.0.0" (ver tilde "greet")
        checkEq "1.0.0" (ver tilde "text")
        -- `*` and `^2` pick the no-dependency release
        let .ok any := resolve [⟨"greet", "*"⟩] | throw (IO.userError "* resolve failed")
        checkEq "2.0.0" (ver any "greet")
        checkEq 1 any.length
        -- a package the index does not have, and a version no release satisfies
        match resolve [⟨"missing", "^1"⟩] with
        | .error e => check ((e.splitOn "no package missing").length > 1) e
        | .ok _ => throw (IO.userError "resolved a package that is not in the index")
        match resolve [⟨"greet", "1.1.0"⟩] with
        | .error e => check ((e.splitOn "no version satisfies").length > 1) e
        | .ok _ => throw (IO.userError "resolved a version that is not in the index") },
    { name := "fetch --locked against the fixture: a cold cache, a warm cache, repair", run := fun _ => do
        let fixture ← indexFixture
        let cache ← IO.FS.createTempDir
        let std ← IO.FS.realPath "lib"
        let dir ← mkTree [
          ("grail.wiz", s!"import Grail\ndef package : Package := Package.new \"app\"\n  |> Package.set \"index\" \"{fixture}\"\n  |> Package.require \"greet\" \"^1\"\n"),
          ("app.wiz", "import Greet.Hello\n#eval greetValue\n")]
        let run (args : List String) : IO UInt32 :=
          Grail.cliMain (["-C", dir.toString, "--std", std.toString, "--cache", cache.toString] ++ args)
        -- no lock yet: --locked refuses to write one; a plain update writes it
        checkEq 1 (← run ["fetch", "--locked"])
        checkEq 1 (← run ["update", "--locked"])
        checkEq 0 (← run ["update"])
        checkEq 0 (← run ["update", "--locked"])
        -- (R10) `update --locked` reads only the lock: a missing/unreachable index does not
        -- make it re-resolve (a new publication upstream must not fail CI)
        checkEq 0 (← run ["update", "--locked", "--index", "/nonexistent/grail-index"])
        -- a cold archive cache: offline fetches nothing
        checkEq 1 (← run ["fetch", "--locked", "--offline"])
        check (!(← (dir / ".grail/packages/greet").pathExists)) "a cold offline fetch unpacked something"
        -- a cold online fetch downloads all three packages, into one content-addressed cache
        checkEq 0 (← run ["fetch", "--locked"])
        let .ok lock := Grail.Lock.parse (← IO.FS.readFile (dir / "grail.lock"))
          | throw (IO.userError "bad grail.lock")
        checkEq 3 lock.pkgs.length
        for p in lock.pkgs do
          check (← (cache / "grail" / "downloads" / p.sha256).pathExists) s!"no cache file for {p.name}"
          checkEq (some p.sha256) (← Grail.Registry.stamp (dir / ".grail/packages" / p.name))
        check ((← IO.FS.readFile (dir / ".grail/packages/greet/src/Greet/Hello.wiz")).contains "120") "the 1.2.0 archive was not unpacked"
        -- a warm cache: the tree can be rebuilt with no network at all
        IO.FS.removeDirAll (dir / ".grail")
        checkEq 0 (← run ["fetch", "--locked", "--offline"])
        check (← (dir / ".grail/packages/text/src/Text/Value.wiz").pathExists) "not unpacked offline"
        -- a corrupt cache entry: offline refuses, online re-downloads and verifies
        let some greet := lock.pkgs.find? (·.name == "greet") | throw (IO.userError "no greet in the lock")
        IO.FS.writeFile (cache / "grail" / "downloads" / greet.sha256) "corrupt"
        if ← (dir / ".grail").pathExists then IO.FS.removeDirAll (dir / ".grail")
        IO.FS.removeDirAll (cache / "grail" / "packages")
        checkEq 1 (← run ["fetch", "--locked", "--offline"])
        check (!(← (dir / ".grail/packages/greet").pathExists)) "unpacked a corrupt archive"
        checkEq 0 (← run ["fetch", "--locked"])
        checkEq (some greet.sha256) (← Grail.Registry.stamp (dir / ".grail/packages/greet")) },
    { name := "an outdated lock and a hash mismatch: clear errors, nothing half-unpacked", run := fun _ => do
        let fixture ← indexFixture
        let cache ← IO.FS.createTempDir
        let std ← IO.FS.realPath "lib"
        let manifest (req : String) : String :=
          s!"import Grail\ndef package : Package := Package.new \"app\"\n  |> Package.set \"index\" \"{fixture}\"\n  |> Package.require \"greet\" \"{req}\"\n"
        let dir ← mkTree [("grail.wiz", manifest "^1")]
        let run (args : List String) : IO UInt32 :=
          Grail.cliMain (["-C", dir.toString, "--std", std.toString, "--cache", cache.toString] ++ args)
        checkEq 0 (← run ["update"])
        -- the manifest moves to ^2 but the lock still pins 1.x
        IO.FS.writeFile (dir / "grail.wiz") (manifest "^2")
        checkEq 1 (← run ["fetch", "--locked"])
        checkEq 1 (← run ["update", "--locked"])
        checkEq 0 (← run ["update"])
        let .ok lock := Grail.Lock.parse (← IO.FS.readFile (dir / "grail.lock"))
          | throw (IO.userError "bad grail.lock")
        checkEq ["greet"] (lock.pkgs.map (·.name))
        checkEq "2.0.0" lock.pkgs.head!.version
        -- a wrong hash (a hand-edited lock): refused before anything is unpacked
        let zero := String.ofList (List.replicate 64 '0')
        let bad := { lock with pkgs := lock.pkgs.map fun p => { p with sha256 := zero } }
        IO.FS.writeFile (dir / "grail.lock") (Grail.Lock.render bad)
        checkEq 1 (← run ["fetch", "--locked"])
        check (!(← (dir / ".grail/packages/greet").pathExists)) "a bad hash unpacked a package"
        check (!(← (cache / "grail" / "downloads" / zero).pathExists)) "a bad archive reached the cache"
        if ← (cache / "grail" / "downloads").isDir then
          let temps := (← (cache / "grail" / "downloads").readDir).filter fun e => e.fileName.contains ".tmp"
          checkEq 0 temps.size
        -- the same lock verifies once the hash is right
        IO.FS.writeFile (dir / "grail.lock") (Grail.Lock.render lock)
        checkEq 0 (← run ["fetch", "--locked"])
        checkEq (some lock.pkgs.head!.sha256) (← Grail.Registry.stamp (dir / ".grail/packages/greet")) },
    { name := "an index commit pin: update resolves from the chosen index revision", run := fun _ => do
        let fixture ← indexFixture
        let root ← IO.FS.createTempDir
        let work := root / "index-work"
        IO.FS.createDirAll work
        let _ ← runIn root "cp" ["-a", (fixture / "index").toString, (fixture / "packages").toString, work.toString]
        let _ ← gitIn work ["init", "--quiet"]
        let _ ← gitIn work ["add", "."]
        let _ ← gitIn work ["commit", "--quiet", "-m", "index v1"]
        let c1 ← gitIn work ["rev-parse", "HEAD"]
        let bare := root / "index.git"
        let _ ← runIn root "git" ["clone", "--quiet", "--bare", work.toString, bare.toString]
        let _ ← gitIn bare ["symbolic-ref", "HEAD", "refs/heads/main"]
        let _ ← gitIn work ["push", "--quiet", bare.toString, "HEAD:refs/heads/main"]
        -- commit 2 yanks greet 2.0.0, so the latest index resolves less than c1 does
        let greet := ← IO.FS.readFile (work / "index/greet.sexpr")
        let yanked := greet.replace "(deps))))" "(deps)) (yanked \"2.0.0\" \"test\")))"
        check (yanked != greet) "the fixture's greet entry did not look as expected"
        IO.FS.writeFile (work / "index/greet.sexpr") yanked
        let _ ← gitIn work ["commit", "--quiet", "-am", "yank"]
        let _ ← gitIn work ["push", "--quiet", bare.toString, "HEAD:refs/heads/main"]
        let c2 ← gitIn work ["rev-parse", "HEAD"]
        let url := s!"file://{bare}"
        let dir ← mkTree [
          ("grail.wiz", s!"import Grail\ndef package : Package := Package.new \"app\"\n  |> Package.set \"index\" \"{url}\"\n  |> Package.require \"greet\" \"*\"\n")]
        let tc : Toolchain := { cacheDir := some (root / "cache") }
        let .ok (pkg, _) ← Grail.readConfig tc (← binId tc) "lib" dir | throw (IO.userError "bad manifest")
        -- latest: 2.0.0 is yanked, so 1.2.0
        let .ok latest ← Grail.Registry.resolveLock (root / "cache") url false (readPkg tc) dir pkg
          | throw (IO.userError "latest resolve failed")
        checkEq c2 latest.indexCommit
        checkEq "1.2.0" latest.pkgs.head!.version
        -- pinned to c1: 2.0.0 is still published there
        let .ok pinned ← Grail.Registry.resolveLock (root / "cache") s!"{url}#{c1}" false (readPkg tc) dir pkg
          | throw (IO.userError "pinned resolve failed")
        checkEq c1 pinned.indexCommit
        checkEq "2.0.0" pinned.pkgs.head!.version
        -- the project's `index-commit` setting is checked against the lock
        IO.FS.writeFile (dir / "grail.wiz")
          s!"import Grail\ndef package : Package := Package.new \"app\"\n  |> Package.set \"index\" \"{url}\"\n  |> Package.set \"index-commit\" \"{c1}\"\n  |> Package.require \"greet\" \"*\"\n"
        let .ok (pkgPinned, _) ← Grail.readConfig tc (← binId tc) "lib" dir | throw (IO.userError "bad pinned manifest")
        match Grail.Registry.checkLocked latest pkgPinned with
        | .error e => check ((e.splitOn "pins").length > 1) e
        | .ok _ => throw (IO.userError "a lock from another index commit passed the pin check")
        match Grail.Registry.checkLocked pinned pkgPinned with
        | .error e => throw (IO.userError s!"the pinned lock was refused: {e}")
        | .ok () => pure () },
    { name := "the resolver retracts requirements of a version it replaced", run := fun _ => do
        let sha := String.ofList (List.replicate 64 'a')
        -- `a 2.0` needs `z`; `b` narrows `a` to <=1, so `a 1.5` is chosen next and the
        -- constraint on `z` (which only `a 2.0` introduced) must disappear with it.
        let index := s!"(index (package \"a\" (version \"1.5.0\" (source \"a15\") (sha256 \"{sha}\")) (version \"2.0.0\" (source \"a20\") (sha256 \"{sha}\") (deps (dep \"z\" \"^1\")))) (package \"b\" (version \"1.0.0\" (source \"b10\") (sha256 \"{sha}\") (deps (dep \"a\" \"<2\")))) (package \"z\" (version \"1.0.0\" (source \"z10\") (sha256 \"{sha}\"))))"
        let .ok ps := Grail.Index.parse index | throw (IO.userError "bad index")
        let idx := ps.foldl (fun m p => m.insert p.name p) {}
        let .ok rs := Grail.Resolve.resolve idx [⟨"a", "*"⟩, ⟨"b", "*"⟩] "0.1.0-dev"
          | throw (IO.userError "resolve failed")
        checkEq 2 rs.length
        checkEq "1.5.0" ((rs.find? (·.name == "a")).map (Grail.Version.render ·.version) |>.getD "?")
        checkEq "1.0.0" ((rs.find? (·.name == "b")).map (Grail.Version.render ·.version) |>.getD "?")
        check (!rs.any (·.name == "z")) "the retracted `a 2.0` dependency `z` is still in the selection" },
    { name := "lock v3 round-trips: toolchain, size/tree/commands, flat deps, sorted", run := fun _ => do
        let sha := String.ofList (List.replicate 64 'a')
        let tree := String.ofList (List.replicate 64 'b')
        let cmds := String.ofList (List.replicate 64 'c')
        let lock : Grail.Lock :=
          { format := 3, toolchain := "0.1.0-dev", revision := "abcdef",
            indexUrl := "https://example.org/grail-index", indexCommit := "123456",
            git := [
              { name := "zeta", url := "https://example.org/z.git", rev := "v1", commit := "c1", content := "d1" },
              { name := "alpha", url := "https://example.org/a.git", rev := "main", commit := "c2", content := "d2" } ],
            pkgs := [
              { name := "text", version := "1.0.0", source := "https://example.org/text.tgz",
                sha256 := sha, size := some 123, tree := tree, commands := cmds,
                deps := [{ name := "std", req := ">=0.1 <0.3" }, { name := "base", req := "~0.2" }] },
              { name := "alpha", version := "0.2.0", source := "https://example.org/a.tgz", sha256 := sha } ],
            overrides := [{ name := "local", path := "../local", hash := tree }] }
        let text := Grail.Lock.render lock
        -- the v3 header and fields are present, and dependencies are flat
        check ((text.splitOn "(version 3)").length > 1) text
        check ((text.splitOn "(toolchain 0.1.0-dev abcdef)").length > 1) text
        check ((text.splitOn "(size 123)").length > 1) text
        check ((text.splitOn s!"(tree {tree})").length > 1) text
        check ((text.splitOn s!"(commands {cmds})").length > 1) text
        check ((text.splitOn "(deps \"base ~0.2\" \"std >=0.1 <0.3\")").length > 1) text
        check ((text.splitOn "(override local \"../local\"").length > 1) text
        -- stable: the entries are sorted and a second render is byte-identical
        let .ok parsed := Grail.Lock.parse text | throw (IO.userError s!"could not parse v3: {text}")
        checkEq ["alpha", "text"] (parsed.pkgs.map (·.name))
        checkEq ["alpha", "zeta"] (parsed.git.map (·.name))
        checkEq ["local"] (parsed.overrides.map (·.name))
        checkEq text (Grail.Lock.render parsed)
        let some p := parsed.pkgs.find? (·.name == "text") | throw (IO.userError "no text package")
        checkEq (some 123) p.size
        checkEq tree p.tree
        checkEq cmds p.commands
        checkEq ["base ~0.2", "std >=0.1 <0.3"] (p.deps.map fun d => s!"{d.name} {d.req}")
        checkEq "0.1.0-dev" parsed.toolchain
        checkEq "abcdef" parsed.revision },
    { name := "old locks: v1 and v2 parse; a newer format is refused", run := fun _ => do
        let sha := String.ofList (List.replicate 64 'a')
        let v1 := "(lock\n  (dep \"greet\" \"https://example.org/greet.git\" \"v1\" \"abc\" \"def\"))\n"
        let .ok l1 := Grail.Lock.parse v1 | throw (IO.userError "v1 did not parse")
        checkEq 1 l1.format
        checkEq "greet" (l1.git.head!.name)
        -- a git-only lock written by `grail update` is v3 too
        let v1v3 := Grail.renderLock l1.git
        check ((v1v3.splitOn "(version 3)").length > 1) v1v3
        let .ok up := Grail.Lock.parse v1v3 | throw (IO.userError "the upgraded v1 lock did not parse")
        checkEq 3 up.format
        checkEq "greet" up.git.head!.name
        let v2 := s!"(lock\n  (index \"https://example.org/i\" \"abc\")\n  (pkg \"text\" \"1.0.0\" \"https://example.org/t.tgz\" \"{sha}\" (deps (dep \"std\" \"^1\")))\n  (pkg \"std\" \"0.1.0\" \"https://example.org/s.tgz\" \"{sha}\" (deps)))\n"
        let .ok l2 := Grail.Lock.parse v2 | throw (IO.userError "v2 did not parse")
        checkEq 2 l2.format
        checkEq "https://example.org/i" l2.indexUrl
        checkEq "text" l2.pkgs.head!.name
        checkEq "std ^1" (l2.pkgs.head!.deps.head!.name ++ " " ++ l2.pkgs.head!.deps.head!.req)
        -- a v2 lock still renders without the v3 header (a build/update may keep it)
        let v2Text := Grail.Lock.render l2
        let header := "(version"
        checkEq 1 (v2Text.splitOn header).length
        -- a lock from a newer grail is refused, never partly understood
        match Grail.Lock.parse "(lock (version 4) (dep \"x\" \"u\" \"r\" \"c\" \"h\"))" with
        | .error e => check ((e.splitOn "newer").length > 1) e
        | .ok _ => throw (IO.userError "a v4 lock was accepted") },
    { name := "an old lock is upgraded to v3 by update, and --locked still reads it", run := fun _ => do
        let fixture ← indexFixture
        let cache ← IO.FS.createTempDir
        let std ← IO.FS.realPath "lib"
        let dir ← mkTree [
          ("grail.wiz", s!"import Grail\ndef package : Package := Package.new \"app\"\n  |> Package.set \"index\" \"{fixture}\"\n  |> Package.require \"greet\" \"^1\"\n")]
        let run (args : List String) : IO UInt32 :=
          Grail.cliMain (["-C", dir.toString, "--std", std.toString, "--cache", cache.toString] ++ args)
        checkEq 0 (← run ["update"])
        let text ← IO.FS.readFile (dir / "grail.lock")
        check ((text.splitOn "(version 3)").length > 1) text
        let .ok v3 := Grail.Lock.parse text | throw (IO.userError "the written lock did not parse")
        checkEq Wiz.version v3.toolchain
        let some greet := v3.pkgs.find? (·.name == "greet") | throw (IO.userError "no greet")
        -- pretend the project committed a v2 lock (no version header, nested deps)
        let v2 := s!"(lock\n  (index \"{v3.indexUrl}\" \"{v3.indexCommit}\")\n  (pkg \"greet\" \"{greet.version}\" \"{greet.source}\" \"{greet.sha256}\" (deps)))\n"
        IO.FS.writeFile (dir / "grail.lock") v2
        checkEq 0 (← run ["update", "--locked"])
        checkEq v2 (← IO.FS.readFile (dir / "grail.lock"))
        checkEq 0 (← run ["update"])
        let upgraded ← IO.FS.readFile (dir / "grail.lock")
        check (upgraded != v2) upgraded
        check ((upgraded.splitOn "(version 3)").length > 1) upgraded
        check ((upgraded.splitOn "(toolchain").length > 1) upgraded
        let .ok again := Grail.Lock.parse upgraded | throw (IO.userError "the upgraded lock did not parse")
        checkEq 3 again.format
        checkEq "greet" (again.pkgs.head!.name)
        -- (R20) a tree hash that does not match the archive is refused before the stamp
        let zero := String.ofList (List.replicate 64 '0')
        let badTree := { again with pkgs := again.pkgs.map fun p => { p with tree := zero } }
        IO.FS.writeFile (dir / "grail.lock") (Grail.Lock.render badTree)
        checkEq 1 (← run ["fetch", "--locked"])
        check (!(← (dir / ".grail/packages/greet").pathExists)) "a bad tree hash unpacked a package" },
    { name := "a grail.local.wiz override: the lock records it, --locked refuses it", run := fun _ => do
        let (root, dir, _sha, tc) ← registryTree
        let std ← IO.FS.realPath "lib"
        let cache := root / "cache"
        let localPkg ← mkTree [
          ("grail.wiz", "import Grail\ndef package : Package := Package.new \"greet\"\n  |> Package.lib \"greet\" \"src\"\n"),
          ("src/Greet/Hello.wiz", "import Prelude\ndef hello : Nat := 7\n")]
        IO.FS.writeFile (dir / "grail.local.wiz")
          s!"import Grail\ndef settings : Settings := Settings.empty\n  |> Package.override \"greet\" \"{localPkg}\"\n"
        let run (args : List String) : IO UInt32 :=
          Grail.cliMain (["-C", dir.toString, "--std", std.toString, "--cache", cache.toString] ++ args)
        checkEq 0 (← run ["update"])
        let text ← IO.FS.readFile (dir / "grail.lock")
        check ((text.splitOn "(override greet \"").length > 1) text
        let .ok lock := Grail.Lock.parse text | throw (IO.userError "the override lock did not parse")
        checkEq 0 lock.pkgs.length
        checkEq 1 lock.overrides.length
        checkEq localPkg.toString lock.overrides.head!.path
        checkEq 64 lock.overrides.head!.hash.length
        -- --locked refuses a machine-local override: it is not reproducible
        checkEq 1 (← run ["update", "--locked"])
        checkEq 1 (← run ["fetch", "--locked"])
        -- a plain fetch checks the path and says nothing is downloaded
        checkEq 0 (← run ["fetch"])
        -- a build uses the path's roots and says so
        let .ok (pkg, _) ← Grail.readConfig tc (← binId tc) "lib" dir | throw (IO.userError "bad manifest")
        let note ← IO.mkRef ""
        let .ok roots ← Grail.Registry.lockedRoots cache (readPkg tc) dir pkg (fun s => note.modify (· ++ s))
          | throw (IO.userError "the override build did not resolve")
        checkEq 1 roots.length
        check (((← note.get).splitOn "using override greet from").length > 1) (← note.get)
        -- an edited override no longer matches the lock
        IO.FS.writeFile (localPkg / "src/Greet/Hello.wiz") "import Prelude\ndef hello : Nat := 8\n"
        match ← Grail.Registry.lockedRoots cache (readPkg tc) dir pkg (fun _ => pure ()) with
        | .error e => check ((e.splitOn "differs from").length > 1) e
        | .ok _ => throw (IO.userError "an edited override passed the lock check") },
    { name := "the index decoder is tolerant; the lock decoder is strict", run := fun _ => do

        let sha := String.ofList (List.replicate 64 'a')
        -- a newer publisher's unknown fields (`license`, `size`, `maintainer`) must not
        -- make an older grail reject the whole package/index
        let index := s!"(index (package \"u\" (maintainer \"someone\") (license \"MIT\") (version \"1.0.0\" (source \"x\") (sha256 \"{sha}\") (size 12) (license \"MIT\") (deps))))"
        let .ok ps := Grail.Index.parse index | throw (IO.userError "the tolerant index decoder rejected unknown fields")
        checkEq 1 ps.length
        checkEq "1.0.0" (Grail.Version.render ps.head!.versions.head!.version)
        checkEq sha ps.head!.versions.head!.sha256
        -- a lock is a local trust anchor: an unknown entry is a hard error, not ignored
        match Grail.Lock.parse "(lock (wat \"x\"))" with
        | .error _ => pure ()
        | .ok _ => throw (IO.userError "the strict lock decoder accepted an unknown entry")
        match Grail.Lock.parse "(lock (pkg \"u\" \"1.0.0\" \"x\" \"not-a-hash\" (deps)))" with
        | .error _ => pure ()
        | .ok l => match Grail.Registry.checkLocked l { name := "app", targets := [], settings := [] } with
          | .error _ => pure ()
          | .ok () => throw (IO.userError "checkLocked accepted a malformed lock") },
    { name := "the index reader sees scoped packages in index/@org/name.sexpr", run := fun _ => do
        let root ← IO.FS.createTempDir
        let dir := root / "index" / "@acme"
        IO.FS.createDirAll dir
        let sha := String.ofList (List.replicate 64 'b')
        IO.FS.writeFile (dir / "tool.sexpr")
          s!"(index (package \"tool\" (version \"0.1.0\" (source \"../../packages/tool-0.1.0.tar.gz\") (sha256 \"{sha}\") (deps))))\n"
        -- a scoped package literally named `snapshot` is not the root snapshot file
        IO.FS.writeFile (dir / "snapshot.sexpr")
          s!"(index (package \"snapshot\" (version \"0.1.0\" (source \"../../packages/snapshot-0.1.0.tar.gz\") (sha256 \"{sha}\") (deps))))\n"
        let .ok src ← Grail.Registry.loadIndex (root / "cache") root.toString false
          | throw (IO.userError "the scoped index did not load")
        check (src.pkgs.contains "@acme/tool") "the scoped package is not keyed by its path"
        check (src.pkgs.contains "@acme/snapshot") "a scoped package named snapshot was skipped"
        checkEq "@acme/tool" (src.pkgs["@acme/tool"]?.map (·.name) |>.getD "?")
        let .ok rs := Grail.Resolve.resolve src.pkgs [⟨"@acme/tool", "^0.1"⟩] "0.1.0-dev"
          | throw (IO.userError "resolve of the scoped package failed")
        checkEq "0.1.0" ((rs.find? (·.name == "@acme/tool")).map (Grail.Version.render ·.version) |>.getD "?") },
    { name := "index rollback: a rewritten index history is refused unless --allow-rewind", run := fun _ => do
        let fixture ← indexFixture
        let root ← IO.FS.createTempDir
        let work := root / "work"
        IO.FS.createDirAll work
        let _ ← runIn root "cp" ["-a", (fixture / "index").toString, (fixture / "packages").toString, work.toString]
        let _ ← gitIn work ["init", "--quiet"]
        let _ ← gitIn work ["add", "."]
        let _ ← gitIn work ["commit", "--quiet", "-m", "index v1"]
        let bare := root / "index.git"
        let _ ← runIn root "git" ["clone", "--quiet", "--bare", work.toString, bare.toString]
        let _ ← gitIn bare ["symbolic-ref", "HEAD", "refs/heads/main"]
        let _ ← gitIn work ["push", "--quiet", bare.toString, "HEAD:refs/heads/main"]
        let url := s!"file://{bare}"
        let dir ← mkTree [
          ("grail.wiz", s!"import Grail\ndef package : Package := Package.new \"app\"\n  |> Package.set \"index\" \"{url}\"\n  |> Package.require \"greet\" \"^1\"\n")]
        let cache := root / "cache"
        let tc : Toolchain := { cacheDir := some cache }
        let .ok (pkg, _) ← Grail.readConfig tc (← binId tc) "lib" dir | throw (IO.userError "bad manifest")
        let .ok c1 ← Grail.Registry.resolveLock cache url false (readPkg tc) dir pkg
          | throw (IO.userError "the first resolve failed")
        IO.FS.writeFile (dir / "grail.lock") (Grail.Lock.render c1)
        -- a normal fast-forward is accepted
        IO.FS.writeFile (work / "index/greet.sexpr")
          ((← IO.FS.readFile (work / "index/greet.sexpr")).replace "\"Hello, in Wiz\"" "\"Hello, again\"")
        let _ ← gitIn work ["commit", "--quiet", "-am", "index v2"]
        let _ ← gitIn work ["push", "--quiet", bare.toString, "HEAD:refs/heads/main"]
        let .ok c2 ← Grail.Registry.resolveLock cache url false (readPkg tc) dir pkg
          | throw (IO.userError "the fast-forward resolve failed")
        check (c1.indexCommit != c2.indexCommit) "the fast-forward did not move the index commit"
        IO.FS.writeFile (dir / "grail.lock") (Grail.Lock.render c2)
        -- an unrelated (force-pushed) history is a rollback and is refused
        let work2 := root / "work2"
        IO.FS.createDirAll work2
        let _ ← runIn root "cp" ["-a", (fixture / "index").toString, (fixture / "packages").toString, work2.toString]
        let _ ← gitIn work2 ["init", "--quiet"]
        let _ ← gitIn work2 ["add", "."]
        let _ ← gitIn work2 ["commit", "--quiet", "-m", "rewritten index"]
        let _ ← gitIn work2 ["push", "--quiet", "--force", bare.toString, "HEAD:refs/heads/main"]
        match ← Grail.Registry.resolveLock cache url false (readPkg tc) dir pkg with
        | .error e => check ((e.splitOn "history was rewritten").length > 1) e
        | .ok _ => throw (IO.userError "a rewritten index history was accepted")
        match ← Grail.Registry.resolveLock cache url false (readPkg tc) dir pkg true with
        | .error e => throw (IO.userError s!"--allow-rewind still failed: {e}")
        | .ok l => check (l.indexCommit != c2.indexCommit) "the rewrite did not change the index commit" },
    { name := "an archive member that escapes the extraction root is refused before extraction", run := fun _ => do
        let root ← IO.FS.createTempDir
        checkEscapes (root := root) (name := "dotdot") (needle := "outside the extraction directory")
          (extra := ["--transform=s|^pkg/a.txt$|pkg/../escaped.txt|"])
        check (!(← (root / "escaped.txt").pathExists)) "a `..` member wrote outside the root"
        -- an absolute member (tar stores it only with -P; the pre-scan must still refuse it)
        let absTarget := root / "escaped-abs.txt"
        checkEscapes (root := root) (name := "absolute") (needle := "outside the extraction directory")
          (extra := ["-P", s!"--transform=s|^pkg/a.txt$|{absTarget}|"])
        -- a symlink whose target leaves the tree, and a device node (type `c`)
        checkEscapes (root := root) (name := "symlink") (needle := "not a regular file")
          (prep := fun work => do
            let _ ← runIn root "ln" ["-s", "../../../escaped.txt", (work / "pkg" / "link").toString]
            pure ())
        let rootDev ← IO.FS.createTempDir
        let dev := rootDev / "device.tar.gz"
        let _ ← runIn rootDev "tar" ["-czf", dev.toString, "-C", "/dev", "null"]
        let dest := rootDev / "extract"
        IO.FS.createDirAll dest
        match ← Grail.Registry.untar dev dest with
        | .error e => check ((e.splitOn "not a regular file").length > 1) e
        | .ok () => throw (IO.userError "a device node was unpacked")
        -- the control: a normal archive still unpacks, with its top directory stripped
        let goodRoot ← IO.FS.createTempDir
        let good := goodRoot / "good.tar.gz"
        let work := goodRoot / "work"
        IO.FS.createDirAll (work / "pkg")
        IO.FS.writeFile (work / "pkg" / "a.txt") "ok\n"
        let _ ← runIn goodRoot "tar" ["-czf", good.toString, "-C", work.toString, "pkg"]
        let out := goodRoot / "extract"
        IO.FS.createDirAll out
        match ← Grail.Registry.untar good out with
        | .error e => throw (IO.userError s!"a normal archive was refused: {e}")
        | .ok () => checkEq "ok\n" (← IO.FS.readFile (out / "a.txt")) },
    { name := "a hostile archive with the locked hash is still refused by fetch", run := fun _ => do
        let root ← IO.FS.createTempDir
        let (hostile, sha) ← buildArchive root "hostile"
          ["--transform=s|^pkg/a.txt$|pkg/../escaped.txt|"]
        let dir ← mkTree [("grail.wiz", "import Grail\ndef package : Package := Package.new \"app\"\n")]
        let cache ← IO.FS.createTempDir
        -- the hash is correct: the archive is exactly what the lock names, and the member
        -- check is what refuses it. The hash stays the gate; the content is still untrusted.
        let p : Grail.PkgLock := { name := "evil", version := "1.0.0", source := hostile.toString,
                                   sha256 := sha, deps := [] }
        match ← Grail.Registry.fetch cache dir { pkgs := [p] } with
        | .error e => check ((e.splitOn "outside the extraction directory").length > 1) e
        | .ok _ => throw (IO.userError "a hostile archive with the locked hash was unpacked")
        check (!(← (dir / ".grail/packages/evil").pathExists)) "a hostile package reached .grail/packages"
        check (!(← (Grail.Registry.storeDir cache sha).pathExists)) "a hostile package reached the shared store"
        check (!(← (root / "escaped.txt").pathExists)) "a hostile archive wrote outside the extraction root" },
    { name := "a download refuses an option-shaped URL and an empty transfer", run := fun _ => do
        let url := "--nope://example.org/x"
        let args := Grail.Registry.curlArgs url "/tmp/grail-download-test.tgz"
        -- `--` ends curl's options, so a URL beginning with `-` is an address, not a flag
        checkEq url args[args.size - 1]!
        checkEq "--" args[args.size - 2]!
        checkEq "/tmp/grail-download-test.tgz" args[args.size - 3]!
        let dir ← IO.FS.createTempDir
        let empty := dir / "empty.tgz"
        IO.FS.writeFile empty ""
        let dest := dir / "copy.tgz"
        match ← Grail.Registry.download s!"file://{empty}" dest with
        | .error e => check ((e.splitOn "empty").length > 1) e
        | .ok () => throw (IO.userError "an empty download was accepted")
        -- the curl path: the bad scheme is rejected as a URL, not parsed as a curl option
        let dest2 := dir / "curl.tgz"
        match ← Grail.Registry.download url dest2 with
        | .error e =>
          check ((e.splitOn "is unknown").length == 1) s!"the URL was parsed as a curl option: {e}"
          check (!(← dest2.pathExists)) "a failed download left a partial file"
        | .ok () => throw (IO.userError "an invalid URL was downloaded") }
  ]

builtin_initialize registerGroup grailDepsGroup

end Tests.Grail
