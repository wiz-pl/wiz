import Tests.Harness
import Wiz.Version

/-!
Stage 26: tower, the toolchain manager, in Wiz (`tower/`). No network: the "upstream" is
a local bare git repository (a tiny Lake project whose `wiz` and `grail` print their
arguments), a release directory made by `scripts/release-tarball.sh`, and a local flake
whose package is a plain directory (no nixpkgs).
-/

namespace Tests.Tower
open Tests

def mkTree (files : List (String × String)) : IO System.FilePath := do
  let dir ← IO.FS.createTempDir
  for (p, text) in files do
    let f := dir / p
    if let some d := f.parent then IO.FS.createDirAll d
    IO.FS.writeFile f text
  pure dir

def gitIn (dir : System.FilePath) (args : List String) : IO String := do
  let o ← IO.Process.output {
    cmd := "git", cwd := dir,
    args := #["-c", "user.name=tower", "-c", "user.email=tower@example.com", "-c", "init.defaultBranch=main",
              "-c", "commit.gpgsign=false", "-c", "tag.gpgsign=false"] ++ args.toArray }
  if o.exitCode != 0 then throw (IO.userError s!"git {args}: {o.stderr}")
  pure o.stdout.trimAscii.toString

def fakeMain (tool version : String) : String :=
  s!"def main (args : List String) : IO Unit := IO.println s!\"{tool} {version} \{args}\"\n"

/-- A tower home whose shims call the tower under test. -/
structure Env where
  home : System.FilePath
  /-- the command a shim runs to reach tower (a path, then arguments) -/
  self : List String
  deriving Inhabited

def Env.toolchains (e : Env) : System.FilePath := e.home / "toolchains"
def Env.binDir (e : Env) : System.FilePath := e.home / "bin"

/-- A toolchain's directory name: its spec, with `/` (a branch like `agent/x`) as `--`. -/
def tcName (spec : String) : String := (spec.replace "/" "--").replace " " "-"

def Env.tcDir (e : Env) (spec : String) : System.FilePath := e.toolchains / tcName spec

def makeExecutable (f : System.FilePath) : IO Unit :=
  IO.setAccessRights f { user := { read := true, write := true, execution := true },
                         group := { read := true, execution := true },
                         other := { read := true, execution := true } }

/-- The machine's architecture, as the release tarballs name it. -/
def arch : IO String := do
  let o ← IO.Process.output { cmd := "uname", args := #["-m"] }
  pure (if o.exitCode == 0 then o.stdout.trimAscii.toString else "x86_64")

def tarballName (a : String) : String := s!"wiz-{a}-linux.tar.gz"

/-- Is there an executable `cmd` on `PATH`? -/
def have? (cmd : String) (args : List String := ["--version"]) : IO Bool := do
  try
    let o ← IO.Process.output { cmd, args := args.toArray }
    pure (o.exitCode == 0)
  catch _ => pure false

/-- An upstream: a Lake project with `wiz` and `grail` executables, tagged `v1` (version
1) and with `main` at version 2. (bare repository, work tree) -/
def upstream : IO (System.FilePath × System.FilePath) := do
  let work ← mkTree [
    ("lakefile.toml", "name = \"fakewiz\"\n\n[[lean_exe]]\nname = \"wiz\"\nroot = \"FakeWiz\"\n\n[[lean_exe]]\nname = \"grail\"\nroot = \"FakeGrail\"\n"),
    ("lean-toolchain", ← IO.FS.readFile "lean-toolchain"),
    ("FakeWiz.lean", fakeMain "wiz" "1"), ("FakeGrail.lean", fakeMain "grail" "1"),
    ("lib/Prelude.wiz", "-- fake prelude\n")]
  let bare ← IO.FS.createTempDir
  let _ ← gitIn bare ["init", "--quiet", "--bare"]
  let _ ← gitIn work ["init", "--quiet"]
  let _ ← gitIn work ["add", "."]
  let _ ← gitIn work ["commit", "--quiet", "-m", "v1"]
  let _ ← gitIn work ["tag", "v1"]
  IO.FS.writeFile (work / "FakeWiz.lean") (fakeMain "wiz" "2")
  let _ ← gitIn work ["commit", "--quiet", "-am", "v2"]
  let _ ← gitIn work ["push", "--quiet", bare.toString, "HEAD:refs/heads/main", "v1"]
  pure (bare, work)

/-- A tower to test: the command that runs it (a program, then its first arguments).
The Wiz tower (`tower/`) is built by grail (stage 26e) and run as a process, so the cases
only see the CLI and the files it writes. -/
structure Impl where
  cmd : List String

/-- Build `tower/` (the Wiz tower) with grail, in `.lake/build/tower-wiz` (a copy of the
sources: grail's cache makes the second build of the same sources run no jobs, so only the
first case of the group pays for it). -/
def wizImpl : IO Impl := do
  let root ← IO.FS.realPath "."
  let dir := root / ".lake/build/tower-wiz"
  IO.FS.createDirAll dir
  let o ← IO.Process.output { cmd := "cp", args := #["-R", "tower/.", dir.toString] }
  if o.exitCode != 0 then throw (IO.userError s!"cp tower: {o.stderr}")
  let start ← IO.monoMsNow
  let o ← IO.Process.output {
    cmd := (root / ".lake/build/bin/grail").toString, cwd := dir,
    args := #["build", "tower"] ++ (← toolchain).toFlags.toArray }
  if o.exitCode != 0 then throw (IO.userError s!"grail build tower:\n{o.stderr}{o.stdout}")
  let ran := !((o.stdout ++ o.stderr).splitOn "0 jobs run").length > 1
  if ran then note s!"built tower-wiz {showMs ((← IO.monoMsNow) - start)}"
  note "uses tower-wiz"
  pure { cmd := [(dir / ".grail/bin/tower").toString] }

/-- A fresh home for one case. -/
def mkEnv (impl : Impl) : IO Env := do
  let home ← IO.FS.createTempDir
  pure { home, self := impl.cmd }

/-- The arguments that make the tower under test use the home `e` and write shims that call it. -/
def towerArgs (e : Env) (args : List String) : Array String :=
  (e.self.tail ++ ["--home", e.home.toString, "--self", e.self.head!] ++
    e.self.tail.flatMap (["--self-arg", ·]) ++ args).toArray

/-- Run the tower under test: exit code, stdout, stderr. -/
def towerOut (e : Env) (args : List String) (cwd : Option System.FilePath := none) : IO (UInt32 × String × String) := do
  let o ← IO.Process.output { cmd := e.self.head!, args := towerArgs e args, cwd }
  pure (o.exitCode, o.stdout, o.stderr)

def tower (e : Env) (args : List String) (cwd : Option System.FilePath := none) : IO Unit := do
  let (r, out, err) ← towerOut e args cwd
  unless r == 0 do throw (IO.userError s!"tower {args}: exit {r}\n{err}{out}")

/-- A tower command that must fail: its stderr. -/
def towerFails (e : Env) (args : List String) : IO String := do
  let (r, out, err) ← towerOut e args
  if r == 0 then throw (IO.userError s!"tower {args} succeeded:\n{out}")
  pure err

/-- Run a program; its trimmed stdout (it must succeed). -/
def runOut (cmd : String) (args : List String) (cwd : Option System.FilePath := none) : IO String := do
  let o ← IO.Process.output { cmd, args := args.toArray, cwd }
  if o.exitCode != 0 then throw (IO.userError s!"{cmd} {args}: exit {o.exitCode}\n{o.stderr}{o.stdout}")
  pure o.stdout.trimAscii.toString

def contains (s t : String) : Bool := (s.splitOn t).length > 1

def checkHas (out t : String) : IO Unit := check (contains out t) s!"expected {t} in: {out}"

def readFile? (f : System.FilePath) : IO String := do
  if ← f.pathExists then IO.FS.readFile f else pure ""

/-- `tower show` in a directory: the toolchain and why (`none` when it fails). -/
def showIn (e : Env) (dir : System.FilePath) : IO (Option (String × String)) := do
  let (r, out, _) ← towerOut e ["show"] dir
  if r != 0 then return none
  match out.splitOn "\n" with
  | spec :: why :: _ =>
    let why := why.trimAscii.toString
    pure (some (spec, if why.startsWith "from " then (why.drop 5).toString else why))
  | _ => throw (IO.userError s!"tower show: {out}")

/-- The cases, against the Wiz tower. -/
def cases (impl : IO Impl) : List Case := [
    { name := "settings, wiz-toolchain files, overrides and the default", run := fun _ => do
        let e ← mkEnv (← impl)
        tower e ["set", "cflags", "-I/x y"]
        tower e ["set", "override", "v1 /a b"]
        let (_, text, _) ← towerOut e ["settings"]
        checkHas text "cflags -I/x y\n"
        checkHas text "override v1 /a b\n"
        checkEq text (← IO.FS.readFile (e.home / "settings"))
        checkEq "/a b  v1" (← runOut e.self.head! (towerArgs e ["override", "list"]).toList)
        checkHas (← towerFails e ["set", "colour", "blue"]) "unknown setting colour"
        let e ← mkEnv (← impl)
        let proj ← IO.FS.realPath (← mkTree [("wiz-toolchain", "-- the toolchain\nv1\n"), ("sub/deep/x.wiz", ""), ("other/y", "")])
        -- nothing anywhere: no toolchain
        checkEq none (← showIn e (← IO.FS.createTempDir))
        tower e ["set", "default", "nightly"]
        checkEq (some ("v1", (proj / "wiz-toolchain").toString)) (← showIn e (proj / "sub/deep"))
        tower e ["override", "set", "branch-x", (proj / "sub").toString]
        checkEq (some "branch-x") ((← showIn e (proj / "sub/deep")).map (·.1))
        checkEq (some "v1") ((← showIn e (proj / "other")).map (·.1))
        tower e ["override", "unset", (proj / "sub").toString]
        checkEq (some "v1") ((← showIn e (proj / "sub/deep")).map (·.1))
        let tmp ← IO.FS.createTempDir
        checkEq (some ("nightly", "the default toolchain")) (← showIn e tmp) },
    { name := "wiz-toolchain.local: a spec or a path, over wiz-toolchain; bad paths; the shims", run := fun _ => do
        let e ← mkEnv (← impl)
        tower e ["set", "cflags", "-I/opt/x"]
        tower e ["self", "shims"]
        -- a toolchain directory (bin/wiz, bin/grail) and a built checkout (.lake/build/bin, lib/)
        let root ← IO.FS.realPath (← mkTree [
          ("tc/bin/wiz", "#!/bin/sh\necho tc wiz \"$@\"\n"), ("tc/bin/grail", "#!/bin/sh\necho tc grail \"$@\"\n"),
          ("co/.lake/build/bin/wiz", "#!/bin/sh\necho co wiz \"$@\"\n"), ("co/.lake/build/bin/grail", "#!/bin/sh\necho co grail \"$@\"\n"),
          ("co/lib/Prelude.wiz", ""), ("empty/x", ""),
          ("proj/wiz-toolchain", "v1\n"), ("proj/sub/x.wiz", "")])
        for b in ["tc/bin/wiz", "tc/bin/grail", "co/.lake/build/bin/wiz", "co/.lake/build/bin/grail"] do
          makeExecutable (root / b)
        let proj := root / "proj"
        let lf := proj / "wiz-toolchain.local"
        let wiz := (e.binDir / "wiz").toString
        let grail := (e.binDir / "grail").toString
        -- a spec: it beats wiz-toolchain, and show says so
        IO.FS.writeFile lf "# mine\nnightly\n"
        checkEq (some ("nightly", s!"{lf} (local override: wiz-toolchain names v1)")) (← showIn e (proj / "sub"))
        -- an absolute path to a toolchain directory: the shims run it
        IO.FS.writeFile lf s!"{root / "tc"}\n"
        checkEq (some ((root / "tc").toString, s!"{lf} (local override: wiz-toolchain names v1)")) (← showIn e (proj / "sub"))
        checkEq "tc wiz check a.wiz" (← runOut wiz ["check", "a.wiz"] (proj / "sub"))
        checkEq "tc grail build" (← runOut grail ["build"] proj)
        checkHas (← runOut e.self.head! (towerArgs e ["which", "wiz"]).toList proj) "/bin/wiz"
        -- a relative path (to the file's directory) to a checkout: wrappers with the flags
        IO.FS.writeFile lf "../co\n"
        checkEq (some (root / "co").toString) ((← showIn e proj).map (·.1))
        let out ← runOut wiz ["check"] (proj / "sub")
        checkEq s!"co wiz --cflags -I/opt/x -I {root / "co/lib"} check" out
        checkEq "co grail --cflags -I/opt/x test" (← runOut grail ["test"] proj)
        -- ... which is listed as a linked toolchain, here
        let (_, l, _) ← towerOut e ["toolchain", "list"] proj
        checkHas l s!"{root / "co"}  [link {root / "co"}] (here)"
        -- without the local file, wiz-toolchain again
        IO.FS.removeFile lf
        checkEq (some ("v1", (proj / "wiz-toolchain").toString)) (← showIn e proj)
        -- a missing path, and a directory that isn't a toolchain: errors naming the file
        for (entry, msg) in [("./nope", s!"{lf}: ./nope: no such directory"),
                             ("../empty", s!"{lf}: {root / "empty"} is not a toolchain")] do
          IO.FS.writeFile lf s!"{entry}\n"
          let (r, _, err) ← towerOut e ["show"] proj
          check (r != 0) s!"show with {entry} succeeded"
          checkHas err msg
          let o ← IO.Process.output { cmd := wiz, args := #["check"], cwd := proj / "sub" }
          check (o.exitCode != 0) s!"the shim ran with {entry}"
          checkHas o.stderr msg
          -- toolchain list still works
          tower e ["toolchain", "list"] proj },
    { name := "from source: install, channels, update, shims, +SPEC, run", run := fun _ => do
        let (bare, work) ← upstream
        let e ← mkEnv (← impl)
        tower e ["set", "git", bare.toString]
        tower e ["set", "nightly-ref", "main"]
        tower e ["set", "source", "source"]
        tower e ["set", "cflags", "-I/opt/gmp/include"]
        tower e ["toolchain", "install", "v1"]
        let tc := e.tcDir "v1"
        let out ← runOut (tc / "bin/wiz").toString ["check", "a.wiz"]
        checkHas out "wiz 1"
        checkHas out "--cflags, -I/opt/gmp/include"
        checkHas out s!"-I, {tc / "share/wiz/lib"}, check, a.wiz"
        check (← (tc / "share/wiz/lib/Prelude.wiz").pathExists) "no lib"
        checkHas (← runOut (tc / "bin/grail").toString ["build"]) "grail 1"
        -- shims: the project says v1; a directory without one gets the default
        tower e ["self", "shims"]
        let proj ← IO.FS.realPath (← mkTree [("wiz-toolchain", "v1\n"), ("sub/x", "")])
        let shim := (e.binDir / "wiz").toString
        checkHas (← runOut shim ["check"] proj) "wiz 1"
        -- +SPEC, and installing on first use (nightly = main = version 2)
        checkHas (← runOut shim ["+nightly", "check"] (proj / "sub")) "wiz 2"
        let nightly ← readFile? (e.tcDir "nightly" / "tower.info")
        checkHas nightly s!"commit {← gitIn work ["rev-parse", "HEAD"]}"
        -- an override beats the file
        tower e ["override", "set", "nightly", (proj / "sub").toString]
        checkHas (← runOut shim ["check"] (proj / "sub")) "wiz 2"
        checkHas (← runOut shim ["check"] proj) "wiz 1"
        -- run puts the toolchain's bin/ first on PATH
        let sh ← IO.FS.realPath (← mkTree [("t.sh", "wiz from-run\n")])
        let (_, o, _) ← towerOut e ["run", "v1", "--", "sh", (sh / "t.sh").toString]
        checkHas o "wiz 1 [--cflags"
        checkHas o "from-run]"
        -- nightly moves: update reinstalls it, v1 (a tag) stays
        IO.FS.writeFile (work / "FakeWiz.lean") (fakeMain "wiz" "3")
        let _ ← gitIn work ["commit", "--quiet", "-am", "v3"]
        let _ ← gitIn work ["push", "--quiet", bare.toString, "HEAD:refs/heads/main"]
        tower e ["update"]
        checkHas (← runOut shim ["check"] (proj / "sub")) "wiz 3"
        checkHas (← runOut shim ["check"] proj) "wiz 1"
        -- with a tag `nightly`, every source installs the tag's commit, not the branch's
        -- tip: a channel names the same commit whatever the source
        let _ ← gitIn work ["push", "--quiet", bare.toString, "HEAD~1:refs/tags/nightly"]
        tower e ["update"]
        checkHas (← runOut shim ["check"] (proj / "sub")) "wiz 2"
        checkHas (← readFile? (e.tcDir "nightly" / "tower.info")) s!"commit {← gitIn work ["rev-parse", "HEAD~1"]}"
        let _ ← gitIn work ["push", "--quiet", "--force", bare.toString, "HEAD:refs/tags/nightly"]
        tower e ["update"]
        checkHas (← runOut shim ["check"] (proj / "sub")) "wiz 3"
        -- uninstall; without auto-install the shim says how to install it
        tower e ["toolchain", "uninstall", "v1"]
        tower e ["set", "auto-install", "false"]
        let o ← IO.Process.output { cmd := shim, args := #["check"], cwd := proj }
        check (o.exitCode != 0) "ran an uninstalled toolchain"
        checkHas o.stderr "tower toolchain install v1" },
    { name := "from a release tarball (scripts/release-tarball.sh), and linked toolchains", run := fun _ => do
        let (bare, _) ← upstream
        let fake ← mkTree [("wiz", "#!/bin/sh\necho release wiz \"$@\"\n"), ("grail", "#!/bin/sh\necho release grail \"$@\"\n"),
                           ("tower", "#!/bin/sh\necho tower\n")]
        for b in ["wiz", "grail", "tower"] do makeExecutable (fake / b)
        let rel ← IO.FS.createTempDir
        IO.FS.createDirAll (rel / "v1")
        let a ← arch
        let _ ← runOut "sh" ["scripts/release-tarball.sh", (rel / "v1" / tarballName a).toString, fake.toString, "abc123"]
        -- the tarball works on its own
        let x ← IO.FS.createTempDir
        let _ ← runOut "tar" ["-xzf", (rel / "v1" / tarballName a).toString, "-C", x.toString]
        checkHas (← runOut (x / s!"wiz-{a}-linux/bin/wiz").toString ["check"]) s!"wiz-{a}-linux/share/wiz/lib check"
        let e ← mkEnv (← impl)
        tower e ["set", "git", bare.toString]
        tower e ["set", "releases", rel.toString]
        tower e ["toolchain", "install", "v1", "--source", "release", "--cc", "gcc"]
        let tc := e.tcDir "v1"
        checkHas (← runOut (tc / "bin/wiz").toString ["check"]) s!"release wiz --cc gcc -I {tc / "share/wiz/lib"} check"
        checkHas (← readFile? (tc / "tower.info")) "commit abc123"
        -- a corrupt download is refused
        IO.FS.writeFile (rel / "v1" / (tarballName a ++ ".sha256")) "0000  x\n"
        checkHas (← towerFails e ["toolchain", "install", "v1", "--source", "release", "--force"]) "sha256"
        -- a branch's commit has no snapshot here
        let m ← towerFails e ["toolchain", "install", "main", "--source", "release"]
        checkHas m "no release snapshot"; checkHas m "--source source"
        -- link the unpacked tarball (a toolchain layout) and use it by name
        tower e ["toolchain", "link", "mine", (x / s!"wiz-{a}-linux").toString]
        tower e ["self", "shims"]
        checkHas (← runOut (e.binDir / "wiz").toString ["+mine", "x"]) "release wiz -I"
        tower e ["default", "mine"]
        checkHas (← runOut (e.binDir / "grail").toString ["y"] (← IO.FS.createTempDir)) "release grail y" },
    { name := "release snapshots: per-commit tarballs, nightly by its tag, pruned commits", run := fun _ => do
        let (bare, work) ← upstream
        let a ← arch
        let fake ← mkTree [("wiz", "#!/bin/sh\necho snapshot wiz \"$@\"\n"), ("grail", "#!/bin/sh\necho snapshot grail\n")]
        for b in ["wiz", "grail"] do makeExecutable (fake / b)
        let rel ← IO.FS.createTempDir
        let c1 ← gitIn work ["rev-parse", "v1^{commit}"]
        let c2 ← gitIn work ["rev-parse", "HEAD"]
        -- what release.yml publishes for a master commit: snapshot-SHA, its tag, and nightly
        let snapshot (c : String) : IO Unit := do
          IO.FS.createDirAll (rel / s!"snapshot-{c}")
          let _ ← runOut "sh" ["scripts/release-tarball.sh", (rel / s!"snapshot-{c}" / tarballName a).toString, fake.toString, c]
          let _ ← gitIn work ["push", "--quiet", bare.toString, s!"{c}:refs/tags/snapshot-{c}"]
        snapshot c1; snapshot c2
        let _ ← gitIn work ["push", "--quiet", bare.toString, s!"{c2}:refs/tags/nightly", s!"{c1}:refs/tags/keep/demo"]
        let e ← mkEnv (← impl)
        tower e ["set", "git", bare.toString]
        tower e ["set", "releases", rel.toString]
        tower e ["set", "nightly-ref", "main"]
        tower e ["set", "source", "release"]
        -- a pinned commit (full sha: no ls-remote needed) and a short one (found by its tag)
        tower e ["toolchain", "install", s!"main@{c2}"]
        checkHas (← readFile? (e.tcDir s!"main@{c2}" / "tower.info")) s!"commit {c2}"
        checkHas (← runOut (e.tcDir s!"main@{c2}" / "bin/wiz").toString ["x"]) "snapshot wiz"
        tower e ["toolchain", "install", s!"main@{c1.take 9}"]
        checkHas (← readFile? (e.tcDir s!"main@{c1.take 9}" / "tower.info")) s!"commit {c1}"
        -- a bare commit, with auto: no nix here means the release comes first
        tower e ["toolchain", "install", c1, "--source", "auto"]
        checkHas (← readFile? (e.tcDir c1 / "tower.info")) "source release"
        -- a keep/ tag is a spec for its commit's snapshot, not a release of its own
        tower e ["toolchain", "install", "keep/demo"]
        checkHas (← readFile? (e.tcDir "keep/demo" / "tower.info")) s!"commit {c1}"
        -- a snapshot is only installed with its checksum
        IO.FS.removeFile (rel / s!"snapshot-{c1}" / (tarballName a ++ ".sha256"))
        checkHas (← towerFails e ["toolchain", "install", s!"main@{c1}", "--force"]) "sha256"
        -- nightly: the commit of the tag nightly, which may be behind the branch
        IO.FS.writeFile (work / "FakeWiz.lean") (fakeMain "wiz" "3")
        let _ ← gitIn work ["commit", "--quiet", "-am", "v3"]
        let c3 ← gitIn work ["rev-parse", "HEAD"]
        let _ ← gitIn work ["push", "--quiet", bare.toString, "HEAD:refs/heads/main"]
        tower e ["toolchain", "install", "nightly"]
        checkHas (← readFile? (e.tcDir "nightly" / "tower.info")) s!"commit {c2}"
        -- ... so update leaves it alone until the tag moves (it would fail: no snapshot of c3)
        tower e ["update", "nightly"]
        checkHas (← readFile? (e.tcDir "nightly" / "tower.info")) s!"commit {c2}"
        -- a commit with no snapshot (unpublished, pruned or off master): what is retained, and the alternatives
        let m ← towerFails e ["toolchain", "install", s!"main@{c3}"]
        checkHas m s!"no release snapshot of commit {c3}"
        checkHas m s!"nightly (master@{c2})"
        checkHas m s!"keep/demo (master@{c1})"
        checkHas m "--source source"
        checkHas m "--source nix"
        checkHas m s!"workflow_dispatch with commit={c3}"
        let m ← towerFails e ["toolchain", "install", s!"main@{(c3.take 8)}"]
        checkHas m "no snapshot"; checkHas m "keep/demo" },
    { name := "from Nix: a flake's package, linked as a GC root", run := fun _ => do
        unless ← have? "nix" do skip "no nix"; return
        let (bare, _) ← upstream
        let flake ← mkTree [
          ("flake.nix", "{ outputs = { self }: let p = builtins.path { path = ./tc; name = \"fake-wiz\"; }; in\n" ++
                        "  { packages.x86_64-linux.wiz = p; packages.aarch64-linux.wiz = p; }; }\n"),
          ("tc/bin/wiz", "#!/bin/sh\necho nix wiz \"$@\"\n"), ("tc/share/wiz/lib/Prelude.wiz", "")]
        makeExecutable (flake / "tc/bin/wiz")
        let _ ← gitIn flake ["init", "--quiet"]
        let _ ← gitIn flake ["add", "."]
        let _ ← gitIn flake ["commit", "--quiet", "-m", "flake"]
        let e ← mkEnv (← impl)
        tower e ["set", "git", bare.toString]
        tower e ["set", "flake", s!"git+file://{flake}"]
        -- the flake's own commit stands in for the wiz commit
        let c ← gitIn flake ["rev-parse", "HEAD"]
        tower e ["toolchain", "install", s!"main@{c}", "--source", "nix"]
        let tc := e.tcDir s!"main@{c}"
        checkHas (← runOut (tc / "bin/wiz").toString ["check"]) "nix wiz check"
        let target ← runOut "readlink" [(tc / "nix").toString]
        check (target.startsWith "/nix/store/") s!"nix -> {target}"
        let roots ← runOut "nix-store" ["--query", "--roots", target]
        checkHas roots (tc / "nix").toString
        tower e ["toolchain", "uninstall", s!"main@{c}"]
        check (← System.FilePath.pathExists target) "uninstall removed the store path" }
  ]

/-- The tower group: the Wiz tower (`tower/`, stage 26e) as a process, plus its own pure
tests (`grail test` in `tower/`). It is not parallel: the first case builds the shared
`.lake/build/tower-wiz`, which N processes would build N times. -/
def group : Group where
  name := "tower"
  exercise := "Stage 26"
  cases :=
    { name := "the Wiz functions: grail test in tower/", run := fun _ => do
        let _ ← wizImpl
        let root ← IO.FS.realPath "."
        let o ← IO.Process.output {
          cmd := (root / ".lake/build/bin/grail").toString, cwd := root / ".lake/build/tower-wiz",
          args := #["test"] ++ (← toolchain).toFlags.toArray }
        if o.exitCode != 0 then throw (IO.userError s!"grail test in tower/:\n{o.stdout}{o.stderr}")
        checkHas o.stdout "1 passed, 0 failed" } ::
    { name := "self install: the Wiz tower and shims in the home", run := fun _ => do
        let impl ← wizImpl
        let e ← mkEnv impl
        tower e ["self", "install"]
        let installed := e.binDir / "tower"
        check (← installed.pathExists) "self install did not copy tower"
        checkEq s!"tower {Wiz.version}" (← runOut installed.toString ["--version"])
        let shim ← IO.FS.readFile (e.binDir / "wiz")
        checkHas shim s!"'{installed}'"
        checkHas shim s!"--home '{e.home}'"
        -- the installed copy runs
        let (r, out, err) ← towerOut { e with self := [installed.toString] } ["settings"]
        check (r == 0) s!"the installed tower failed: {err}{out}"
        checkHas out "source auto" } ::
    cases wizImpl

/-- This module's test groups, which `Tests/Main.lean` runs: one per line, in sorted
order, so that branches adding groups rarely touch the same lines. A new group also
needs a shard in `.github/test-shards.json` (CI checks). -/
def groups : List Group :=
  group ::
  []

end Tests.Tower
