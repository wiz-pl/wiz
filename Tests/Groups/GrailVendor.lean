import Tests.Grail

namespace Tests.Grail
open Wiz Tests

def grailVendorGroup : Group where
  name := "grail-vendor"
  exercise := "Stage 23n"
  cases := [
    { name := "grail vendor: content-addressed files, a stable lock, and one archive", run := fun _ => do
        let (root, dir, sha, tc) ← registryTree
        let idx := root / "index"
        let cache := tc.cacheDir.getD "."
        let std ← IO.FS.realPath "lib"
        let run (args : List String) : IO UInt32 :=
          Grail.cliMain (["-C", dir.toString, "--std", std.toString,
            "--cache", cache.toString, "--index", idx.toString] ++ args)
        checkEq 0 (← run ["update"])
        let lock0 ← IO.FS.readFile (dir / "grail.lock")
        checkEq 0 (← run ["vendor"])
        let vend := dir / "vendor"
        let file := vend / (sha ++ ".tar.gz")
        check (← file.pathExists) s!"no {file}"
        let vidx ← IO.FS.readFile (vend / "index.sexpr")
        check ((vidx.splitOn sha).length > 1) vidx
        check ((vidx.splitOn "greet").length > 1) vidx
        -- vendoring never rewrites the lock: its `source` stays the published URL
        checkEq lock0 (← IO.FS.readFile (dir / "grail.lock"))
        checkEq 0 (← run ["vendor"])
        let archives := (← vend.readDir).filter (fun e => e.fileName != "index.sexpr")
        checkEq 1 archives.size
        let .ok h ← Grail.Registry.sha256File file | throw (IO.userError "could not hash the vendored archive")
        checkEq sha h },
    { name := "an offline --locked fetch from the vendor directory, through the shared store", run := fun _ => do
        let (root, dir, sha, tc) ← registryTree
        let idx := root / "index"
        let cache := tc.cacheDir.getD "."
        let std ← IO.FS.realPath "lib"
        -- the manifest names vendor/ (so the offline fetch needs no flag)
        IO.FS.writeFile (dir / "grail.wiz")
          s!"import Grail\ndef package : Package := Package.new \"app\"\n  |> Package.set \"index\" \"{idx}\"\n  |> Package.set \"vendor\" \"vendor\"\n  |> Package.require \"greet\" \"^1\"\n  |> Package.check \"app\" \"app.wiz\"\n"
        let run (args : List String) : IO UInt32 :=
          Grail.cliMain (["-C", dir.toString, "--std", std.toString,
            "--cache", cache.toString, "--index", idx.toString] ++ args)
        checkEq 0 (← run ["update"])
        checkEq 0 (← run ["vendor"])
        let lock0 ← IO.FS.readFile (dir / "grail.lock")
        -- no .grail, no download cache, no source archive: the vendor directory is enough
        if ← (dir / ".grail").pathExists then IO.FS.removeDirAll (dir / ".grail")
        IO.FS.removeDirAll (cache / "grail" / "downloads")
        IO.FS.removeFile (root / "greet-1.2.0.tar.gz")
        checkEq 0 (← run ["fetch", "--locked", "--offline"])
        check (← (dir / ".grail/packages/greet/src/Greet/Hello.wiz").pathExists) "not unpacked"
        let localTree ← IO.FS.realPath (dir / ".grail/packages/greet")
        let shared ← IO.FS.realPath (cache / "grail" / "packages" / sha)
        checkEq shared localTree
        checkEq lock0 (← IO.FS.readFile (dir / "grail.lock"))
        -- without the vendor directory, the cache and the shared store, --offline refuses
        if ← (dir / ".grail").pathExists then IO.FS.removeDirAll (dir / ".grail")
        IO.FS.removeDirAll (cache / "grail" / "downloads")
        IO.FS.removeDirAll (cache / "grail" / "packages")
        IO.FS.removeDirAll (dir / "vendor")
        checkEq 1 (← run ["fetch", "--locked", "--offline"]) },
    { name := "one archive, two packages: one download and one unpack", run := fun _ => do
        let (root, dir, sha, _tc) ← registryTree
        let cache := root / "cache"
        let src := root / "greet-1.2.0.tar.gz"
        let mk (name : String) : Grail.PkgLock :=
          { name, version := "1.2.0", source := src.toString, sha256 := sha, deps := [] }
        let .ok _ ← Grail.Registry.fetch cache dir { pkgs := [mk "alpha"] }
          | throw (IO.userError "the first fetch failed")
        -- a second download would fail now; the content-addressed cache and store have it
        IO.FS.removeFile src
        let .ok lines ← Grail.Registry.fetch cache dir { pkgs := [mk "alpha", mk "beta"] }
          | throw (IO.userError "a duplicate download was attempted")
        checkEq 2 lines.length
        let archives := (← (cache / "grail" / "downloads").readDir).filter
          (fun e => !e.fileName.contains ".tmp")
        checkEq 1 archives.size
        let stores := (← (cache / "grail" / "packages").readDir).filter
          (fun e => !e.fileName.contains ".tmp")
        checkEq 1 stores.size
        let a ← IO.FS.realPath (dir / ".grail/packages/alpha")
        let b ← IO.FS.realPath (dir / ".grail/packages/beta")
        checkEq a b
        -- the vendor directory has the bytes once too, for both names
        let .ok vlines ← Grail.Registry.vendor cache (dir / "vendor")
          { pkgs := [mk "alpha", mk "beta"] }
          | throw (IO.userError "vendoring two packages failed")
        checkEq 2 vlines.length
        let vfiles := (← (dir / "vendor").readDir).filter (fun e => e.fileName != "index.sexpr")
        checkEq 1 vfiles.size },
    { name := "grail cache: path, list and verify (a corrupt archive is an error)", run := fun _ => do
        let (root, dir, sha, tc) ← registryTree
        let idx := root / "index"
        let cache := tc.cacheDir.getD "."
        let std ← IO.FS.realPath "lib"
        let run (args : List String) : IO UInt32 :=
          Grail.cliMain (["-C", dir.toString, "--std", std.toString,
            "--cache", cache.toString, "--index", idx.toString] ++ args)
        checkEq 0 (← run ["update"])
        checkEq 0 (← run ["fetch", "--locked"])
        let lines ← Grail.Registry.cacheList cache
        check (lines.any fun l =>
          (l.splitOn "archive\t").length > 1 && (l.splitOn sha).length > 1) s!"no archive in {lines}"
        check (lines.any fun l =>
          (l.splitOn "package\t").length > 1 && (l.splitOn sha).length > 1) s!"no package in {lines}"
        let cacheMain (args : List String) : IO UInt32 :=
          Grail.cliMain (["--cache", cache.toString, "cache"] ++ args)
        checkEq 0 (← cacheMain ["path"])
        checkEq 0 (← cacheMain ["list"])
        checkEq 0 (← cacheMain ["verify"])
        IO.FS.writeFile (cache / "grail" / "downloads" / sha) "not the archive"
        checkEq 1 (← cacheMain ["verify"])
        -- the next fetch repairs the archive (once the unpacked trees are gone too)
        Grail.Registry.removePath (dir / ".grail" / "packages" / "greet")
        Grail.Registry.removePath (cache / "grail" / "packages" / sha)
        checkEq 0 (← run ["fetch", "--locked"])
        checkEq 0 (← cacheMain ["verify"]) },
    { name := "vendor --locked needs a lock; --offline needs the archive cache", run := fun _ => do
        let (root, dir, _sha, tc) ← registryTree
        let idx := root / "index"
        let cache := tc.cacheDir.getD "."
        let std ← IO.FS.realPath "lib"
        let run (args : List String) : IO UInt32 :=
          Grail.cliMain (["-C", dir.toString, "--std", std.toString,
            "--cache", cache.toString, "--index", idx.toString] ++ args)
        checkEq 1 (← run ["vendor", "--locked"])
        checkEq 1 (← run ["vendor", "--offline"])
        checkEq 0 (← (dir / "vendor").readDir).size
        checkEq 0 (← run ["vendor"])
        checkEq 0 (← run ["vendor", "--locked"])
        checkEq 0 (← run ["vendor", "--locked", "--offline"])
        -- an explicit --vendor DIR is relative to -C, and needs neither cache nor store
        if ← (dir / ".grail").pathExists then IO.FS.removeDirAll (dir / ".grail")
        if ← (cache / "grail" / "downloads").pathExists then
          IO.FS.removeDirAll (cache / "grail" / "downloads")
        if ← (cache / "grail" / "packages").pathExists then
          IO.FS.removeDirAll (cache / "grail" / "packages")
        checkEq 0 (← run ["fetch", "--locked", "--offline", "--vendor", "vendor"]) },
    { name := "a wrong tree hash is refused before it enters the store", run := fun _ => do
        let (root, dir, _sha, _tc) ← registryTree
        let idx := root / "index"
        let entryPath := idx / "greet.sexpr"
        let entry ← IO.FS.readFile entryPath
        let wrong := String.ofList (List.replicate 64 'f')
        IO.FS.writeFile entryPath (entry.replace " (deps))" s!" (tree \"{wrong}\") (deps))")
        let cache := root / "cache"
        let std ← IO.FS.realPath "lib"
        let run (args : List String) : IO UInt32 :=
          Grail.cliMain (["-C", dir.toString, "--std", std.toString,
            "--cache", cache.toString, "--index", idx.toString] ++ args)
        -- update records the (wrong) tree; the archive is only unpacked by a fetch/build
        checkEq 0 (← run ["update"])
        checkEq 1 (← run ["fetch", "--locked"])
        let .ok lock := Grail.Lock.parse (← IO.FS.readFile (dir / "grail.lock"))
          | throw (IO.userError "bad grail.lock")
        match ← Grail.Registry.fetch cache dir lock with
        | .error e =>
          check ((e.splitOn "unpacked tree").length > 1) e
          check ((e.splitOn "the lock says").length > 1) e
        | .ok _ => throw (IO.userError "fetched a package whose tree disagrees with the lock")
        -- nothing was installed under the wrong tree identity
        let stores := if ← (cache / "grail" / "packages").pathExists then
            (← (cache / "grail" / "packages").readDir).size else 0
        checkEq 0 stores }
  ]

builtin_initialize registerGroup grailVendorGroup

end Tests.Grail
