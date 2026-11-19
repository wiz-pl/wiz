import Tests.Grail

/-!
## The package lifecycle, end to end

One temporary directory: `grail new` writes the packages, a local git repository is the
`Package.dep` source, a directory index is the registry, and the archives, the lock, the
vendor directory and the shared cache all live under it. No URL is fetched: the only
"remote" is a path.

The second package consumes the same vendored archive with `--locked` and `--offline`,
after the index and the cache have been removed.
-/

namespace Tests.Grail
open Wiz Tests

/-- Run grail in `dir` with the tests' standard library and a private cache. -/
def e2eGrail (dir cache : System.FilePath) (args : List String) : IO UInt32 := do
  let std ← IO.FS.realPath "lib"
  Grail.cliMain (["-C", dir.toString, "--std", std.toString, "--cache", cache.toString] ++ args)

/-- The manifest of a package that is only a library. -/
def e2eLibManifest (name : String) : String :=
  s!"import Grail\n\ndef package : Package :=\n" ++
  s!"  Package.new \"{name}\"\n" ++
  s!"    |> Package.version \"1.0.0\"\n" ++
  s!"    |> Package.lib \"{name}-lib\" \"src\"\n"

/-- The manifest of `app`: a local git dependency (`base`) and a registry dependency
(`shapes`), plus one command whose output is the artifact we run. -/
def e2eAppManifest (index baseDir : String) : String :=
  "import Grail\n\ndef package : Package :=\n" ++
  "  Package.new \"app\"\n" ++
  s!"    |> Package.set \"index\" \"{index}\"\n" ++
  "    |> Package.set \"vendor\" \"vendor\"\n" ++
  s!"    |> Package.dep \"base\" \"{baseDir}\" \"v1\"\n" ++
  "    |> Package.require \"shapes\" \"^1\"\n" ++
  "    |> Package.lib \"app-lib\" \"src\"\n" ++
  "    |> Package.command (Command.new \"artifact\" (Tool.path \"sh\")\n" ++
  "        |> Command.arg \"-c\"\n" ++
  "        |> Command.arg \"test -f .grail/packages/base/src/Base/Hello.wiz && test -f .grail/packages/shapes/src/Shapes/Hello.wiz && printf '#!/bin/sh\\\\necho app-artifact\\\\n' > \\\"$1\\\" && chmod +x \\\"$1\\\"\"\n" ++
  "        |> Command.arg \"sh\"\n" ++
  "        |> Command.output \"build/artifact.sh\")\n"

def grailE2EGroup : Group where
  name := "grail-e2e"
  exercise := "Stage 23d–o"
  cases := [
    { name := "new → dep → lock → build → vendor → publish → consume offline", run := fun _ => do
        -- The packages are libraries and `command` targets only: no C toolchain is
        -- needed, and nothing below reaches a network.
        let root ← IO.FS.createTempDir
        let cache := root / "cache"
        let pkgs := root / "pkgs"
        let self ← IO.appPath
        let std ← IO.FS.realPath "lib"

        -- 1. `grail new` writes the two packages and the second consumer.
        let baseDir := pkgs / "base"
        checkEq 0 (← e2eGrail root cache ["new", "base", "--dir", baseDir.toString])
        let shapesDir := pkgs / "shapes"
        checkEq 0 (← e2eGrail root cache ["new", "shapes", "--dir", shapesDir.toString])
        let appDir := root / "app"
        checkEq 0 (← e2eGrail root cache ["new", "app", "--dir", appDir.toString])
        let consumerDir := root / "consumer"
        checkEq 0 (← e2eGrail root cache ["new", "consumer", "--dir", consumerDir.toString])

        -- 2. The local path package: an ordinary git repository under the temporary root.
        IO.FS.writeFile (baseDir / "grail.wiz") (e2eLibManifest "base")
        IO.FS.createDirAll (baseDir / "src" / "Base")
        IO.FS.writeFile (baseDir / "src/Base/Hello.wiz")
          "import Prelude\ndef baseValue : Nat := 1\n"
        let _ ← gitIn baseDir ["init", "--quiet"]
        let _ ← gitIn baseDir ["add", "."]
        let _ ← gitIn baseDir ["commit", "--quiet", "-m", "v1"]
        let _ ← gitIn baseDir ["tag", "v1"]
        let baseV1 ← gitIn baseDir ["rev-parse", "v1"]

        -- 3. The registry package: make it, publish its archive, and put the printed
        --    entry in a directory index. `publish` only prints; the index is a file.
        IO.FS.writeFile (shapesDir / "grail.wiz") (e2eLibManifest "shapes")
        IO.FS.createDirAll (shapesDir / "src" / "Shapes")
        IO.FS.writeFile (shapesDir / "src/Shapes/Hello.wiz")
          "import Prelude\ndef shapesValue : Nat := 41\n"
        IO.FS.createDirAll (root / "dist")
        let (tar, sha) ← tarballOf (root / "dist") "shapes" "1.0.0"
          [("grail.wiz", e2eLibManifest "shapes"),
           ("src/Shapes/Hello.wiz", "import Prelude\ndef shapesValue : Nat := 41\n")]
        let source := s!"file://{tar}"
        let published ← IO.Process.output {
          cmd := self.toString,
          args := #["--grail", "-C", shapesDir.toString, "--std", std.toString,
                    "--cache", cache.toString, "publish", tar.toString, "--source", source] }
        checkEq 0 published.exitCode
        let entry := published.stdout.trimAscii.toString
        check ((entry.splitOn "(modules Shapes.Hello)").length > 1) entry
        check ((entry.splitOn s!"(sha256 {sha})").length > 1) entry
        check ((entry.splitOn "(size ").length > 1) entry
        check ((entry.splitOn "(tree ").length > 1) entry
        let idx := root / "index"
        IO.FS.createDirAll idx
        IO.FS.writeFile (idx / "shapes.sexpr")
          s!"(index (package \"shapes\"\n  {entry}))\n"
        checkEq 0 (← e2eGrail root cache ["index", "check", idx.toString])

        -- 4. The consumer package: a local path `dep` and a registry `require`.
        IO.FS.writeFile (appDir / "grail.wiz") (e2eAppManifest idx.toString baseDir.toString)
        IO.FS.writeFile (appDir / "src/Main.wiz")
          "import Base.Hello\nimport Shapes.Hello\nimport IO\n\ndef main : IO Unit := do\n  IO.println (Nat.toString (baseValue + shapesValue))\n"

        -- 5. Resolve and lock. The lock is v3 and records both kinds of dependency.
        checkEq 0 (← e2eGrail appDir cache ["update"])
        let lockPath := appDir / "grail.lock"
        let lockText ← IO.FS.readFile lockPath
        let .ok lock := Grail.Lock.parse lockText
          | throw (IO.userError s!"bad grail.lock:\n{lockText}")
        checkEq 3 lock.format
        check ((lockText.splitOn "(version 3)").length == 2) ("lock version: " ++ lockText)
        check ((lockText.splitOn s!"(toolchain {Wiz.version}").length > 1) ("lock toolchain: " ++ lockText)
        checkEq idx.toString lock.indexUrl
        checkEq "" lock.indexCommit
        checkEq 1 lock.git.length
        checkEq 1 lock.pkgs.length
        let dep := lock.git.head!
        checkEq "base" dep.name
        checkEq baseDir.toString dep.url
        checkEq "v1" dep.rev
        checkEq baseV1 dep.commit
        let pkg := lock.pkgs.head!
        checkEq "shapes" pkg.name
        checkEq "1.0.0" pkg.version
        checkEq source pkg.source
        checkEq sha pkg.sha256
        checkEq (some (← tar.metadata).byteSize.toNat) pkg.size
        checkEq 64 pkg.tree.length
        checkEq "" pkg.commands
        check pkg.deps.isEmpty "shapes has dependencies"
        check ((lockText.splitOn s!"(pkg shapes 1.0.0 \"{source}\" {sha}").length > 1) ("lock pkg: " ++ lockText)
        check ((lockText.splitOn "(size ").length > 1) ("lock size: " ++ lockText)
        check ((lockText.splitOn "(tree ").length > 1) ("lock tree: " ++ lockText)
        check ((lockText.splitOn "(deps)").length > 1) ("lock deps: " ++ lockText)

        -- 6. Build the library (both imports must be resolvable) and the artifact; run it.
        checkEq 0 (← e2eGrail appDir cache ["build", "app-lib", "artifact"])
        check (← (appDir / ".grail/packages/base/src/Base/Hello.wiz").pathExists) "base not fetched"
        check (← (appDir / ".grail/packages/shapes/src/Shapes/Hello.wiz").pathExists) "shapes not fetched"
        let artifact := appDir / "build/artifact.sh"
        check (← artifact.pathExists) "the artifact was not built"
        let ran ← IO.Process.output { cmd := artifact.toString }
        checkEq 0 ran.exitCode
        checkEq "app-artifact\n" ran.stdout
        -- a second build runs nothing
        checkEq 0 (← e2eGrail appDir cache ["build", "app-lib", "artifact"])

        -- 7. A changed requirement makes the lock stale: --locked and the build refuse it.
        let stale := (e2eAppManifest idx.toString baseDir.toString).replace
          "Package.require \"shapes\" \"^1\"" "Package.require \"shapes\" \"^2\""
        IO.FS.writeFile (appDir / "grail.wiz") stale
        match ← Grail.readConfig {} 7 "lib" appDir with
        | .error e => throw (IO.userError e)
        | .ok (pkg2, _) =>
          match Grail.Registry.checkLocked lock pkg2 with
          | .error e => check (has e "run `grail update`") e
          | .ok _ => throw (IO.userError "a changed requirement passed checkLocked")
        checkEq 1 (← e2eGrail appDir cache ["update", "--locked"])
        checkEq lockText (← IO.FS.readFile lockPath)
        checkEq 1 (← e2eGrail appDir cache ["build", "app-lib"])
        IO.FS.writeFile (appDir / "grail.wiz") (e2eAppManifest idx.toString baseDir.toString)
        checkEq 0 (← e2eGrail appDir cache ["update", "--locked"])

        -- 8. A changed git revision is still governed by the lock: --locked does not
        --    resolve, the build keeps the locked commit, and a plain `update` moves it.
        IO.FS.writeFile (baseDir / "src/Base/Hello.wiz")
          "import Prelude\ndef baseValue : Nat := 2\n"
        let _ ← gitIn baseDir ["commit", "--quiet", "-am", "v2"]
        let _ ← gitIn baseDir ["tag", "v2"]
        let baseV2 ← gitIn baseDir ["rev-parse", "v2"]
        IO.FS.writeFile (appDir / "grail.wiz")
          ((e2eAppManifest idx.toString baseDir.toString).replace "\"v1\"" "\"v2\"")
        checkEq 0 (← e2eGrail appDir cache ["update", "--locked"])
        checkEq baseV1 (← gitIn (appDir / ".grail/packages/base") ["rev-parse", "HEAD"])
        checkEq 0 (← e2eGrail appDir cache ["build", "app-lib"])
        checkEq baseV1 (← gitIn (appDir / ".grail/packages/base") ["rev-parse", "HEAD"])
        checkEq 0 (← e2eGrail appDir cache ["update"])
        let lock2Text ← IO.FS.readFile lockPath
        let .ok lock2 := Grail.Lock.parse lock2Text
          | throw (IO.userError s!"bad grail.lock after update:\n{lock2Text}")
        checkEq 3 lock2.format
        check ((lock2Text.splitOn "(version 3)").length == 2) "the second lock is not v3"
        checkEq baseV2 lock2.git.head!.commit
        check (lock2.git.head!.content != dep.content)
          "the dependency's content hash did not change"
        check (lock2Text != lockText) "the lock did not change when the revision did"
        checkEq 0 (← e2eGrail appDir cache ["build", "app-lib"])

        -- 9. Vendor: the lock's registry archive goes into vendor/, content-addressed;
        --    the lock is not rewritten, and a git dep has no archive to vendor.
        checkEq 0 (← e2eGrail appDir cache ["vendor"])
        let vend := appDir / "vendor"
        let archive := vend / (sha ++ ".tar.gz")
        check (← archive.pathExists) s!"no {archive}"
        let .ok vidx := Grail.VendorIndex.parse (← IO.FS.readFile (vend / "index.sexpr"))
          | throw (IO.userError "bad vendor/index.sexpr")
        checkEq 1 vidx.entries.length
        checkEq "shapes" vidx.entries.head!.name
        checkEq sha vidx.entries.head!.sha256
        checkEq lock2Text (← IO.FS.readFile lockPath)
        checkEq 0 (← e2eGrail appDir cache ["vendor", "--locked"])
        checkEq 0 (← e2eGrail appDir cache ["vendor", "--offline"])

        -- 10. The second package consumes the same archive with --locked and --offline.
        --     It has its own cache; its vendor directory is a copy of app's.
        IO.FS.writeFile (consumerDir / "grail.wiz")
          ("import Grail\n\ndef package : Package :=\n  Package.new \"consumer\"\n" ++
           s!"    |> Package.set \"index\" \"{idx}\"\n" ++
           "    |> Package.set \"vendor\" \"vendor\"\n" ++
           "    |> Package.require \"shapes\" \"^1\"\n" ++
           "    |> Package.lib \"consumer-lib\" \"src\"\n")
        IO.FS.writeFile (consumerDir / "src/Main.wiz")
          "import Shapes.Hello\nimport IO\n\ndef main : IO Unit := do\n  IO.println (Nat.toString shapesValue)\n"
        let ccache := root / "consumer-cache"
        checkEq 0 (← e2eGrail consumerDir ccache ["update"])
        let consumerLockText ← IO.FS.readFile (consumerDir / "grail.lock")
        let .ok consumerLock := Grail.Lock.parse consumerLockText
          | throw (IO.userError s!"bad consumer grail.lock:\n{consumerLockText}")
        checkEq 3 consumerLock.format
        checkEq 1 consumerLock.pkgs.length
        checkEq pkg.sha256 consumerLock.pkgs.head!.sha256
        checkEq pkg.tree consumerLock.pkgs.head!.tree
        checkEq pkg.size consumerLock.pkgs.head!.size
        let _ ← runIn root "cp" ["-a", vend.toString, (consumerDir / "vendor").toString]
        -- `--locked` reads no index: removing it changes nothing.
        IO.FS.removeDirAll idx
        checkEq 0 (← e2eGrail consumerDir ccache ["update", "--locked"])
        checkEq consumerLockText (← IO.FS.readFile (consumerDir / "grail.lock"))
        -- The cache is empty and `.grail` is absent: the vendor directory is the only source.
        checkEq 0 (← e2eGrail consumerDir ccache ["fetch", "--locked", "--offline"])
        check (← (consumerDir / ".grail/packages/shapes/src/Shapes/Hello.wiz").pathExists)
          "the offline fetch unpacked nothing"
        -- Build from the vendor directory alone, after deleting even that unpacked tree.
        IO.FS.removeDirAll (consumerDir / ".grail")
        IO.FS.removeDirAll ccache
        checkEq 0 (← e2eGrail consumerDir ccache ["build", "consumer-lib", "--offline"])
        check (← (consumerDir / ".grail/packages/shapes/src/Shapes/Hello.wiz").pathExists)
          "the offline build unpacked nothing"

        -- 11. --offline fails when the vendor entry is missing: no cache, no archive.
        IO.FS.removeDirAll (consumerDir / ".grail")
        IO.FS.removeDirAll ccache
        let consumerArchive := consumerDir / "vendor" / (sha ++ ".tar.gz")
        IO.FS.removeFile consumerArchive
        checkEq 1 (← e2eGrail consumerDir ccache ["fetch", "--locked", "--offline"])
        match ← Grail.Registry.fetch ccache consumerDir consumerLock true
            (some (consumerDir / "vendor")) with
        | .error e =>
          check (has e "--offline") e
          check (has e "archive cache") e
        | .ok _ => throw (IO.userError "an offline fetch without the vendor archive succeeded")
        -- put it back: the same command now succeeds
        let _ ← runIn root "cp" ["-a", archive.toString, consumerArchive.toString]
        checkEq 0 (← e2eGrail consumerDir ccache ["fetch", "--locked", "--offline"])

        IO.FS.removeDirAll root }
  ]

builtin_initialize registerGroup grailE2EGroup

end Tests.Grail
