import Tests.Grail

namespace Tests.Grail
open Wiz Tests

/-- The checked-in example index (`examples/grail-index`): the `grail-index` repository
layout (23m), with `index.wiz`, three packages and their deterministic archives. -/
def exampleIndex : IO System.FilePath := do
  let p ← IO.FS.realPath "examples/grail-index"
  unless ← (p / "index").isDir do
    throw (IO.userError s!"{p}: no index/ directory (run the tests from the repository root)")
  pure p

/-- A module conflict the checker reports for `checkDir`. -/
def hasModuleConflict (r : Grail.CheckResult) : Bool :=
  r.errors.any fun e => (e.splitOn "module conflict").length > 1

/-- `ssh-keygen` signs and verifies the index snapshots; a machine without it skips the
signed-index cases (as the toolchain cases skip without a C compiler). -/
def haveSshKeygen : IO Bool := do
  try
    let _ ← IO.Process.output { cmd := "ssh-keygen", args := #["-h"] }
    pure true
  catch _ => pure false

/-- `SHA256:…` fingerprint of a public key file (`ssh-keygen -lf -E sha256`). -/
def fingerprintOf (pub : System.FilePath) : IO String := do
  let out ← runIn (pub.parent.getD ".") "ssh-keygen" ["-lf", pub.toString, "-E", "sha256"]
  match out.splitOn " " with
  | _ :: fp :: _ => pure fp
  | _ => throw (IO.userError s!"ssh-keygen -lf {pub}: {out}")

/-- Write an index snapshot; `pkgs` are `(name, version, sha256, size)` (size 0: unknown).
The tests write it directly (the CLI's `index snapshot` is covered separately). -/
def writeSnapshot (idx : System.FilePath) (name : String) (seq : Nat) (updated expires fp : String)
    (pkgs : List (String × String × String × UInt64)) : IO Unit := do
  let entry (n v sha : String) (size : UInt64) : String :=
    s!"  (package \"{n}\" \"{v}\" \"{sha}\"" ++ (if size == 0 then ")" else s!" (size {size}))")
  let text := "(snapshot\n" ++
    s!"  (name \"{name}\")\n  (seq {seq})\n  (updated \"{updated}\")\n  (key \"{fp}\")\n  (expires \"{expires}\")\n" ++
    "\n".intercalate (pkgs.map fun (n, v, sha, size) => entry n v sha size) ++ ")\n"
  IO.FS.writeFile (idx / "index" / "snapshot.sexpr") text

/-- Sign `index/snapshot.sexpr` with `key` (removing an old signature first, since
`ssh-keygen` would otherwise ask before overwriting it). -/
def signSnapshot (idx key : System.FilePath) : IO Unit := do
  let _ ← runIn idx "rm" ["-f", (idx / "index" / "snapshot.sexpr.sig").toString]
  let _ ← runIn idx "ssh-keygen" ["-Y", "sign", "-q", "-n", "grail-index", "-f", key.toString,
    (idx / "index" / "snapshot.sexpr").toString]

/-- A one-package index (`greet` 1.0.0) with a snapshot signed by a throwaway Ed25519 key.
Returns `(index dir, private key, allowed_signers, archive sha256, key fingerprint)`. -/
def signedGreetIndex (root : System.FilePath) (seq : Nat)
    (expires : String := "2030-01-01T00:00:00Z") :
    IO (System.FilePath × System.FilePath × System.FilePath × String × String) := do
  IO.FS.createDirAll (root / "index")
  let (tar, sha) ← tarballOf root "greet" "1.0.0"
    [("grail.wiz", "import Grail\ndef package : Package := Package.new \"greet\"\n  |> Package.version \"1.0.0\"\n  |> Package.lib \"greet\" \"src\"\n"),
     ("src/Greet/Hello.wiz", "import Prelude\ndef hello : Nat := 1\n")]
  IO.FS.writeFile (root / "index" / "greet.sexpr")
    s!"(index (package \"greet\" (version \"1.0.0\" (source \"file://{tar}\") (sha256 \"{sha}\") (toolchain \">=0.1.0\") (deps))))\n"
  IO.FS.writeFile (root / "registry.sexpr") "(registry (name \"test/grail-index\") (format 1))\n"
  let key := root / "key"
  let _ ← runIn root "ssh-keygen"
    ["-q", "-t", "ed25519", "-N", "", "-C", "grail index test", "-f", key.toString]
  let pub : System.FilePath := System.FilePath.mk (key.toString ++ ".pub")
  let fp ← fingerprintOf pub
  let size := (← tar.metadata).byteSize
  writeSnapshot root "test/grail-index" seq "2026-11-15T00:00:00Z" expires fp
    [("greet", "1.0.0", sha, size)]
  signSnapshot root key
  let allowed := root / "allowed_signers"
  IO.FS.writeFile allowed s!"test {(← IO.FS.readFile pub)}"
  pure (root, key, allowed, sha, fp)

def grailIndexGroup : Group where
  name := "grail-index"
  exercise := "Stage 23m"
  cases := [
    { name := "the example grail-index validates offline", run := fun _ => do
        let ex ← exampleIndex
        let cache ← IO.FS.createTempDir
        match ← Grail.checkDir cache {} 7 "lib" ex.toString false with
        | .error e => throw (IO.userError e)
        | .ok r =>
          checkEq 3 r.packages
          checkEq 4 r.versions
          checkEq 4 r.archives
          checkEq 0 r.remote
          checkEq ([] : List String) r.errors
          checkEq ([] : List String) r.warnings },
    { name := "grail index check: offline by default, and an error exits 1", run := fun _ => do
        let ex ← exampleIndex
        let cache ← IO.FS.createTempDir
        let run (args : List String) : IO UInt32 :=
          Grail.cliMain (["--cache", cache.toString, "index", "check"] ++ args)
        checkEq 0 (← run [ex.toString])
        -- a non-local spec is refused without --fetch, so a CI run cannot clone by accident
        checkEq 1 (← run ["https://example.invalid/grail-index"])
        -- a malformed entry exits 1
        let root ← IO.FS.createTempDir
        let idx := root / "index"
        IO.FS.createDirAll idx
        IO.FS.writeFile (idx / "bad.sexpr")
          "(index (package \"bad\" (version \"1.0.0\" (source \"x\") (sha256 \"short\") (deps))))\n"
        checkEq 1 (← run [root.toString]) },
    { name := "a changed archive, a bad requirement and a missing entry are errors", run := fun _ => do
        let ex ← exampleIndex
        let root ← IO.FS.createTempDir
        let work := root / "idx"
        IO.FS.createDirAll work
        for f in ["index", "packages", "index.wiz", "registry.sexpr"] do
          let _ ← runIn work "cp" ["-a", (ex / f).toString, (work / f).toString]
        IO.FS.writeFile (work / "packages/text-1.1.0.tar.gz") "not a tarball"
        let hello := ← IO.FS.readFile (work / "index/hello.sexpr")
        IO.FS.writeFile (work / "index/hello.sexpr") (hello.replace "^1" "^^1")
        IO.FS.removeFile (work / "index/base.sexpr")
        let cache ← IO.FS.createTempDir
        match ← Grail.checkDir cache {} 7 "lib" work.toString false with
        | .error e => throw (IO.userError e)
        | .ok r =>
          check r.hasErrors "the broken index passed"
          check (r.errors.any fun e => (e.splitOn "sha256").length > 1) s!"no hash error: {r.errors}"
          check (r.errors.any fun e =>
            (e.splitOn "requirement").length > 1 || (e.splitOn "not a version").length > 1) s!"no requirement error: {r.errors}"
          check (r.errors.any fun e => (e.splitOn "base.sexpr is missing").length > 1) s!"no missing-entry error: {r.errors}" },
    { name := "module-prefix conflicts are an index error and a resolver error", run := fun _ => do
        let root ← IO.FS.createTempDir
        let idx := root / "index"
        IO.FS.createDirAll idx
        let sha := String.ofList (List.replicate 64 'a')
        IO.FS.writeFile (idx / "alpha.sexpr")
          s!"(index (package \"alpha\" (version \"1.0.0\" (source \"packages/alpha-1.0.0.tar.gz\") (sha256 \"{sha}\") (modules \"Ddr3\" \"Ddr3.Ctrl\") (deps))))\n"
        IO.FS.writeFile (idx / "beta.sexpr")
          s!"(index (package \"beta\" (version \"1.0.0\" (source \"packages/beta-1.0.0.tar.gz\") (sha256 \"{sha}\") (modules \"Ddr3.Ctrl\" \"Ddr3.Mem\") (deps))))\n"
        let cache ← IO.FS.createTempDir
        match ← Grail.checkDir cache {} 7 "lib" root.toString false with
        | .error e => throw (IO.userError e)
        | .ok r => check (hasModuleConflict r) s!"no module conflict: {r.errors}"
        let .ok src ← Grail.Registry.loadIndex cache root.toString true
          | throw (IO.userError "the index did not load")
        match Grail.Resolve.resolve src.pkgs [⟨"alpha", "^1"⟩, ⟨"beta", "^1"⟩] "0.1.0-dev" with
        | .error e =>
          check ((e.splitOn "module conflict").length > 1) e
          check ((e.splitOn "alpha").length > 1 && (e.splitOn "beta").length > 1) e
        | .ok _ => throw (IO.userError "resolved two packages that both own Ddr3") },
    { name := "index.wiz lists exactly the packages on disk", run := fun _ => do
        let ex ← exampleIndex
        let root ← IO.FS.createTempDir
        let work := root / "idx"
        IO.FS.createDirAll work
        for f in ["index", "packages", "index.wiz", "registry.sexpr"] do
          let _ ← runIn work "cp" ["-a", (ex / f).toString, (work / f).toString]
        IO.FS.removeFile (work / "index/hello.sexpr")
        let sha := String.ofList (List.replicate 64 'b')
        IO.FS.writeFile (work / "index/extra.sexpr")
          s!"(index (package \"extra\" (version \"1.0.0\" (source \"packages/base-0.1.0.tar.gz\") (sha256 \"{sha}\") (deps))))\n"
        let cache ← IO.FS.createTempDir
        match ← Grail.checkDir cache {} 7 "lib" work.toString false with
        | .error e => throw (IO.userError e)
        | .ok r =>
          check (r.errors.any fun e =>
            (e.splitOn "hello").length > 1 && (e.splitOn "missing").length > 1) s!"no missing-package error: {r.errors}"
          check (r.errors.any fun e =>
            (e.splitOn "extra").length > 1 && (e.splitOn "not listed").length > 1) s!"no unlisted-package error: {r.errors}" },
    { name := "grail update reads the example index as a directory, a file and a git URL", run := fun _ => do
        let ex ← exampleIndex
        let std ← IO.FS.realPath "lib"
        let cache ← IO.FS.createTempDir
        let mkApp (spec : String) : IO System.FilePath := mkTree [
          ("grail.wiz", s!"import Grail\ndef package : Package := Package.new \"app\"\n  |> Package.set \"index\" \"{spec}\"\n  |> Package.require \"hello\" \"^1\"\n"),
          ("app.wiz", "import Hello.Main\n#eval helloValue\n")]
        let grailIn (dir : System.FilePath) (args : List String) : IO UInt32 :=
          Grail.cliMain (["-C", dir.toString, "--std", std.toString, "--cache", cache.toString] ++ args)
        let names (dir : System.FilePath) : IO (List String) := do
          let .ok lock := Grail.Lock.parse (← IO.FS.readFile (dir / "grail.lock"))
            | throw (IO.userError "bad grail.lock")
          pure (lock.pkgs.map (·.name))
        let d1 ← mkApp ex.toString
        checkEq 0 (← grailIn d1 ["update"])
        checkEq ["base", "hello", "text"] (← names d1)
        -- one file holding every package
        let d2 ← mkApp (ex / "index.sexpr").toString
        checkEq 0 (← grailIn d2 ["update"])
        checkEq ["base", "hello", "text"] (← names d2)
        -- a git URL: a bare clone of the example
        let root ← IO.FS.createTempDir
        let work := root / "work"
        IO.FS.createDirAll work
        for f in ["index", "packages", "entries", "sources", "index.wiz", "registry.sexpr", "index.sexpr"] do
          let _ ← runIn work "cp" ["-a", (ex / f).toString, (work / f).toString]
        let _ ← gitIn work ["init", "--quiet"]
        let _ ← gitIn work ["add", "."]
        let _ ← gitIn work ["commit", "--quiet", "-m", "index"]
        let bare := root / "index.git"
        let _ ← runIn root "git" ["clone", "--quiet", "--bare", work.toString, bare.toString]
        let _ ← gitIn bare ["symbolic-ref", "HEAD", "refs/heads/main"]
        let _ ← gitIn work ["push", "--quiet", bare.toString, "HEAD:refs/heads/main"]
        let d3 ← mkApp s!"file://{bare}"
        checkEq 0 (← grailIn d3 ["update"])
        checkEq ["base", "hello", "text"] (← names d3)
        let .ok lock := Grail.Lock.parse (← IO.FS.readFile (d3 / "grail.lock"))
          | throw (IO.userError "bad grail.lock")
        checkEq "1.1.0" ((lock.pkgs.find? (·.name == "text")).map (·.version) |>.getD "?")
        checkEq 40 lock.indexCommit.length
        -- `index check --fetch` on the same URL (a local clone: still no network)
        match ← Grail.checkDir cache {} 7 "lib" s!"file://{bare}" true with
        | .error e => throw (IO.userError e)
        | .ok r =>
          checkEq 3 r.packages
          checkEq 4 r.archives
          checkEq ([] : List String) r.errors },
    { name := "publish records the archive's module names", run := fun _ => do
        let root ← IO.FS.createTempDir
        let files : List (String × String) :=
          [("grail.wiz", "import Grail\ndef package : Package := Package.new \"greet\"\n  |> Package.version \"1.0.0\"\n  |> Package.lib \"greet\" \"src\"\n"),
           ("src/Greet/Hello.wiz", "import Prelude\ndef hello : Nat := 1\n")]
        let work ← mkTree files
        let (tar, _) ← tarballOf root "greet" "1.0.0" files
        let .ok (pkg, _) ← Grail.readConfig {} 7 "lib" work | throw (IO.userError "bad manifest")
        let .ok entry ← Grail.Registry.publish (some tar) "https://example.org/greet-1.0.0.tar.gz" pkg
          | throw (IO.userError "publish failed")
        check ((entry.splitOn "(modules Greet.Hello)").length > 1) entry },
    { name := "a signed index snapshot is verified offline and pinned in the lock", run := fun _ => do
        unless ← haveSshKeygen do
          skip "no ssh-keygen"
          return
        let root ← IO.FS.createTempDir
        let (idx, _key, allowed, _sha, fp) ← signedGreetIndex root 1
        let std ← IO.FS.realPath "lib"
        let cache := root / "cache"
        let dir ← mkTree [
          ("grail.wiz", s!"import Grail\ndef package : Package := Package.new \"app\"\n  |> Package.set \"index\" \"{idx}\"\n  |> Package.require \"greet\" \"^1\"\n")]
        let run (args : List String) : IO UInt32 :=
          Grail.cliMain (["-C", dir.toString, "--std", std.toString, "--cache", cache.toString] ++ args)
        checkEq 0 (← run ["update", "--require-signature", "--allowed-signers", allowed.toString])
        let .ok lock := Grail.Lock.parse (← IO.FS.readFile (dir / "grail.lock"))
          | throw (IO.userError "bad grail.lock")
        let some sig := lock.indexSignature | throw (IO.userError "the lock has no index signature")
        checkEq fp sig.fingerprint
        checkEq 1 sig.seq
        check (sig.key.startsWith "ssh-ed25519") sig.key
        -- `--locked` validates the recorded signature fields without reading the index
        checkEq 0 (← run ["update", "--locked", "--require-signature"])
        -- and a registry lock whose index/signature lines were stripped is not signed
        let lockText ← IO.FS.readFile (dir / "grail.lock")
        let kept := (lockText.splitOn "\n").filter fun l => !l.startsWith "  (index"
        IO.FS.writeFile (dir / "grail.lock") ("\n".intercalate kept)
        checkEq 1 (← run ["update", "--locked", "--require-signature"])
        IO.FS.writeFile (dir / "grail.lock") lockText
        -- the lock's pinned key makes verification offline on the next run
        checkEq 0 (← run ["index", "verify", idx.toString, "--locked"])
        -- a first use needs a trust root from outside the index; without one, refuse
        checkEq 1 (← run ["index", "verify", idx.toString])
        checkEq 0 (← run ["index", "verify", idx.toString, "--allowed-signers", allowed.toString])
        match ← Grail.checkDir cache {} 7 "lib" idx.toString false true (some allowed.toString) with
        | .error e => throw (IO.userError e)
        | .ok r =>
          checkEq 1 r.signatures
          checkEq ([] : List String) r.errors
        -- the generator writes the document the helper above wrote by hand
        let gen := root / "gen"
        IO.FS.createDirAll (gen / "index")
        IO.FS.writeFile (gen / "index" / "greet.sexpr") (← IO.FS.readFile (idx / "index" / "greet.sexpr"))
        checkEq 0 (← Grail.cliMain ["--cache", cache.toString, "index", "snapshot", gen.toString,
          "--seq", "7", "--updated", "2026-11-15T00:00:00Z", "--key", fp,
          "--expires", "2030-01-01T00:00:00Z"])
        let generated ← IO.FS.readFile (gen / "index" / "snapshot.sexpr")
        check ((generated.splitOn "(seq 7)").length > 1) generated
        check ((generated.splitOn "(package greet 1.0.0").length > 1) generated
        -- without a snapshot, --require-signature refuses (a fresh app, so no lock pins one)
        IO.FS.removeFile (idx / "index" / "snapshot.sexpr")
        IO.FS.removeFile (idx / "index" / "snapshot.sexpr.sig")
        let dir2 ← mkTree [
          ("grail.wiz", s!"import Grail\ndef package : Package := Package.new \"app2\"\n  |> Package.set \"index\" \"{idx}\"\n  |> Package.require \"greet\" \"^1\"\n")]
        let run2 (args : List String) : IO UInt32 :=
          Grail.cliMain (["-C", dir2.toString, "--std", std.toString, "--cache", cache.toString] ++ args)
        checkEq 1 (← run2 ["update", "--require-signature", "--allowed-signers", allowed.toString])
        -- ... and --allow-unsigned is the explicit escape for a registry without one
        checkEq 0 (← run2 ["update", "--allow-unsigned"]) },
    { name := "an edited entry, snapshot or expiry is refused", run := fun _ => do
        unless ← haveSshKeygen do
          skip "no ssh-keygen"
          return
        let root ← IO.FS.createTempDir
        let (idx, key, allowed, sha, fp) ← signedGreetIndex root 1
        let std ← IO.FS.realPath "lib"
        let cache := root / "cache"
        let dir ← mkTree [
          ("grail.wiz", s!"import Grail\ndef package : Package := Package.new \"app\"\n  |> Package.set \"index\" \"{idx}\"\n  |> Package.require \"greet\" \"^1\"\n")]
        let run (args : List String) : IO UInt32 :=
          Grail.cliMain (["-C", dir.toString, "--std", std.toString, "--cache", cache.toString] ++ args)
        let updated := ["update", "--require-signature", "--allowed-signers", allowed.toString]
        checkEq 0 (← run updated)
        -- an edited entry no longer matches the signed snapshot
        let entryPath := idx / "index" / "greet.sexpr"
        let entry ← IO.FS.readFile entryPath
        let zeros := String.ofList (List.replicate 64 '0')
        IO.FS.writeFile entryPath (entry.replace sha zeros)
        checkEq 1 (← run updated)
        IO.FS.writeFile entryPath entry
        -- an edited snapshot without a new signature
        let snapPath := idx / "index" / "snapshot.sexpr"
        let snap ← IO.FS.readFile snapPath
        IO.FS.writeFile snapPath (snap.replace "(seq 1)" "(seq 2)")
        checkEq 1 (← run updated)
        -- re-signing a snapshot that disagrees with the index is still refused
        IO.FS.writeFile snapPath (snap.replace sha zeros)
        signSnapshot idx key
        checkEq 1 (← run updated)
        -- an expired key
        writeSnapshot idx "test/grail-index" 1 "2026-11-15T00:00:00Z" "2020-01-01T00:00:00Z" fp
          [("greet", "1.0.0", sha, 0)]
        signSnapshot idx key
        checkEq 1 (← run updated)
        checkEq 1 (← run ["index", "verify", idx.toString, "--allowed-signers", allowed.toString])
        match ← Grail.checkDir cache {} 7 "lib" idx.toString false true (some allowed.toString) with
        | .error e => throw (IO.userError e)
        | .ok r => check r.hasErrors s!"the expired snapshot passed: {r.errors}" },
    { name := "a lower snapshot seq is a rollback; a same-seq rewrite is refused", run := fun _ => do
        unless ← haveSshKeygen do
          skip "no ssh-keygen"
          return
        let root ← IO.FS.createTempDir
        let (idx, key, allowed, sha, fp) ← signedGreetIndex root 1
        let std ← IO.FS.realPath "lib"
        let cache := root / "cache"
        let dir ← mkTree [
          ("grail.wiz", s!"import Grail\ndef package : Package := Package.new \"app\"\n  |> Package.set \"index\" \"{idx}\"\n  |> Package.require \"greet\" \"^1\"\n")]
        let run (args : List String) : IO UInt32 :=
          Grail.cliMain (["-C", dir.toString, "--std", std.toString, "--cache", cache.toString] ++ args)
        let updated := ["update", "--require-signature", "--allowed-signers", allowed.toString]
        checkEq 0 (← run updated)
        -- seq 2 is an ordinary update
        writeSnapshot idx "test/grail-index" 2 "2026-11-16T00:00:00Z" "2030-01-01T00:00:00Z" fp
          [("greet", "1.0.0", sha, 0)]
        signSnapshot idx key
        checkEq 0 (← run updated)
        let .ok lock := Grail.Lock.parse (← IO.FS.readFile (dir / "grail.lock"))
          | throw (IO.userError "bad grail.lock")
        checkEq 2 (lock.indexSignature.map (·.seq) |>.getD 0)
        -- seq 1 is a rollback: refused, unless deliberately accepted
        writeSnapshot idx "test/grail-index" 1 "2026-11-15T00:00:00Z" "2030-01-01T00:00:00Z" fp
          [("greet", "1.0.0", sha, 0)]
        signSnapshot idx key
        checkEq 1 (← run ["index", "verify", idx.toString, "--locked"])
        checkEq 1 (← run updated)
        checkEq 0 (← run (updated ++ ["--allow-rewind"]))
        -- a rewrite at the same sequence is refused even with --allow-rewind
        writeSnapshot idx "test/grail-index" 1 "2026-11-16T00:00:00Z" "2030-01-01T00:00:00Z" fp
          [("greet", "1.0.0", sha, 0)]
        signSnapshot idx key
        checkEq 1 (← run (updated ++ ["--allow-rewind"])) }
  ]

builtin_initialize registerGroup grailIndexGroup

end Tests.Grail
