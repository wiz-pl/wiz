import Grail.Graph
import Grail.Deps
import Grail.Lsp
import Wiz.Version

/-!
# grail, a build tool for Wiz

`grail build [TARGET…]` builds the targets of the package in the current directory
(all of them by default), as described by its `grail.wiz`. See docs/stages/23-grail.md.
-/

namespace Grail
open Wiz

def usage : String := "usage:
  grail build [TARGET…]   build the package's targets (by default all but the
                          bootstrap check, which takes minutes)
  grail test [FILTER…] [--update]
                          run the tests (of `tests` targets) whose path contains a
                          filter; --update writes the actual output to .expected
  grail update            resolve the git dependencies again and write grail.lock
                          (builds use the lock only)
  grail run TARGET [-- ARGS…]
                          build an exe or command target's needs and run it with
                          ARGS, its input and output grail's own; exits with its code
  grail lsp [OPTIONS…]     the language server (`wiz lsp OPTIONS…`) with the package's
                          module roots (its lib targets' and its dependencies') and
                          its toolchain; --wiz PATH picks the wiz (default: the one
                          beside grail, else wiz on PATH)
  grail doc [TARGET…] [-o OUT] [--source-url URL] [--title T]
                          documentation of the package's lib targets (all by
                          default): `wiz doc` with the package's module roots, into
                          .grail/doc (see `wiz doc`)
  grail targets           list the targets
  grail config            print the toolchain grail would use
  grail --version         print the version
  grail clean             remove .grail/build, .grail/bin, .grail/tmp, .grail/log and
                          the command outputs grail installed (unless changed since)
options: -C DIR (the package directory), --std DIR (the standard library),
  -j N (jobs at once; default: the number of cores, at most 4),
  --timeout SECS (a job's time limit, default 1800), --test-timeout SECS (default 300),
  --cc X --cflags \"…\" --ldflags \"…\" --libs \"…\" --llc X --gc-cflags \"…\" --gc-ldflags \"…\" -I DIR,
  --cache DIR (the elaboration cache, default ~/.cache/wiz), --cache-ro DIR (repeatable:
  a read-only cache, searched in order after the write cache), --no-cache (both),
  --trust-native (27a: allow `native_refl`, passed on to every check and to `wiz lsp`), --native-fuel N
Machine settings (where GMP lives) go in an uncommitted grail.local.wiz:
  import Grail
  def settings : Settings := Settings.empty |> Settings.set \"cflags\" \"-I…\""

/-- What identifies this binary (so a new elaborator or backend rebuilds everything):
`Cache.binaryId`, remembered under the write cache directory (never a read-only one). -/
def binaryId (cacheDir : Option System.FilePath) : IO UInt64 := Cache.binaryId cacheDir

structure Opts where
  dir : Option String := none
  std : Option String := none
  jobs : Option Nat := none
  timeout : Option Nat := none
  testTimeout : Option Nat := none
  /-- `grail lsp`: the `wiz` to run -/
  wiz : Option String := none

/-- `-C DIR`, `--std DIR`, `-j N`, `--timeout SECS`, `--test-timeout SECS`, taken out of the arguments. -/
partial def grailOpts (o : Opts) : List String → Opts × List String
  | "-C" :: d :: rest => grailOpts { o with dir := some d } rest
  | "--std" :: d :: rest => grailOpts { o with std := some d } rest
  | "-j" :: n :: rest => grailOpts { o with jobs := n.toNat? } rest
  | "--timeout" :: n :: rest => grailOpts { o with timeout := n.toNat? } rest
  | "--test-timeout" :: n :: rest => grailOpts { o with testTimeout := n.toNat? } rest
  | "--wiz" :: w :: rest => grailOpts { o with wiz := some w } rest
  | a :: rest =>
    if a.startsWith "-j" && (a.drop 2).toString.toNat?.isSome then grailOpts { o with jobs := (a.drop 2).toString.toNat? } rest
    else let (o, r) := grailOpts o rest; (o, a :: r)
  | [] => (o, [])

/-- The standard library: `--std`, else `lib/` of the checkout this binary was built in
(`.lake/build/bin/grail`), else `./lib`. -/
def findStd (opt : Option String) : IO System.FilePath := do
  if let some d := opt then return d
  let exe ← IO.appPath
  let guess := ((((exe.parent.bind (·.parent)).bind (·.parent)).bind (·.parent)).getD ".") / "lib"
  if ← (guess / "Prelude.wiz").pathExists then return guess
  pure "lib"

def cliMain (args : List String) : IO UInt32 := do
  -- (after the toolchain flags: tower's wrapper puts its flags before the user's arguments)
  if ((({} : Toolchain).parseFlags args).2) == ["--version"] then
    IO.println (← Wiz.versionLine "grail"); return 0
  -- (23k) the supervisor of a job process
  if let "--grail-exec" :: rest := args then return ← execMain rest
  -- a `panic!` (a kernel-internal failure) ends the build, as it ends `wiz check`
  Wiz.exitOnPanic
  let home := (← IO.getEnv "HOME").getD "."
  -- (26f) a release toolchain's own C compiler, GMP and GC are the defaults
  let defaults ← ({ cacheDir := some (System.FilePath.mk home / ".cache" / "wiz") } : Toolchain).withBundled
  -- a job of a build, in its own process (`Grail/Graph.lean`)
  if let "--grail-job" :: job :: flags := args then
    return ← jobMain (defaults.parseFlags flags).1 job
  -- `grail run TARGET -- ARGS…`: what follows `--` is the program's
  let (args, runArgs) := match args.idxOf? "--" with
    | some i => (args.take i, (args.drop (i + 1)).toArray)
    | none => (args, #[])
  let (opts, args) := grailOpts {} args
  let dir : System.FilePath := opts.dir.getD "."
  let std ← findStd opts.std
  let jobs := opts.jobs.getD (max 1 (min 4 (System.Platform.Internal.getHardwareConcurrency ()).toNat))
  let mkRunner (ctx : Ctx) : IO Runner := do
    pure { ctx, stats := ← IO.mkRef {}, memo := ← IO.mkRef {}, jobs, self := ← IO.appPath,
           timeoutMs := 1000 * opts.timeout.getD 1800, testTimeoutMs := 1000 * opts.testTimeout.getD 300 }
  -- the flags win over the build files; read them now, apply them last
  let raw := args
  let (flagged, args) := defaults.parseFlags args
  let binId ← binaryId flagged.cacheDir
  match args with
  | ["clean"] =>
    -- (23i) the outputs grail installed in the package, unless they were changed since
    IO.print (← cleanInstalled { dir, std, tc := defaults, binId })
    for d in ["build", "bin", "tmp", "log"] do
      if ← (dir / ".grail" / d).pathExists then IO.FS.removeDirAll (dir / ".grail" / d)
    pure 0
  -- the language server, with the package's module roots (Grail/Lsp.lean)
  | "lsp" :: lspOpts =>
    let wiz ← wizExe opts.wiz
    let dirAbs ← absolute dir
    match ← readConfig flagged binId std dir with
    | .error e =>
      -- a broken grail.wiz must still be editable: the server starts without the roots
      IO.eprintln s!"{e}\ngrail lsp: starting {wiz} lsp with only the package directory as a module root"
      runLsp wiz (lspArgs flagged [dirAbs] lspOpts) dirAbs
    | .ok (pkg, localSettings) =>
      let mut tc := defaults
      for (k, v) in pkg.settings ++ localSettings do
        match tc.set k v with
        | some t => tc := t
        | none => IO.eprintln s!"grail lsp: unknown setting {k} (ignored)"
      tc := (tc.parseFlags raw).1
      let readPkg (d : System.FilePath) : IO (Except String Package) := do
        pure ((← readConfig tc binId std d).map (·.1))
      let deps ← match ← lockedRoots readPkg dir pkg IO.eprint with
        | .ok rs => rs.mapM absolute
        | .error e => do IO.eprintln s!"grail lsp: {e} (the dependencies' modules are not found)"; pure []
      runLsp wiz (lspArgs tc ([dirAbs] ++ libRootsOf dirAbs pkg.targets ++ deps) lspOpts) dirAbs
  -- (11s) the documentation of the lib targets: `wiz doc` with the package's roots
  | "doc" :: docOpts =>
    let wiz ← wizExe opts.wiz
    let dirAbs ← absolute dir
    let (pkg, localSettings) ← match ← readConfig flagged binId std dir with
      | .ok r => pure r
      | .error e => do IO.eprintln e; return 1
    let mut tc := defaults
    for (k, v) in pkg.settings ++ localSettings do
      match tc.set k v with
      | some t => tc := t
      | none => IO.eprintln s!"unknown setting {k}"; return 1
    tc := (tc.parseFlags raw).1
    let readPkg (d : System.FilePath) : IO (Except String Package) := do
      pure ((← readConfig tc binId std d).map (·.1))
    let deps ← match ← lockedRoots readPkg dir pkg IO.eprint with
      | .ok rs => rs.mapM absolute
      | .error e => do IO.eprintln e; return 1
    -- TARGET… (lib targets) and wiz doc's own options
    let rec split : List String → List String × List String
      | o :: v :: rest => if ["-o", "--source-url", "--title", "--web"].contains o then
          let (ts, os) := split rest; (ts, o :: v :: os) else
          let (ts, os) := split (v :: rest); (o :: ts, os)
      | [o] => if o.startsWith "-" then ([], [o]) else ([o], [])
      | [] => ([], [])
    let (wanted, wizOpts) := split docOpts
    let libs := pkg.targets.filterMap fun | .lib n r => some (n, r) | _ => none
    for w in wanted do
      unless libs.any (·.1 == w) do IO.eprintln s!"no lib target {w}"; return 1
    let chosen := if wanted.isEmpty then libs else libs.filter (wanted.contains ·.1)
    if chosen.isEmpty then IO.eprintln "grail doc: the package has no lib targets"; return 1
    let wizOpts := if wizOpts.contains "-o" then wizOpts else wizOpts ++ ["-o", (dirAbs / ".grail" / "doc").toString]
    let wizOpts := if wizOpts.contains "--title" then wizOpts else wizOpts ++ ["--title", pkg.name]
    let roots := libRootsOf dirAbs pkg.targets ++ deps
    let rest := tc.searchPath.filter (!roots.contains ·)
    let args := ({ tc with searchPath := roots ++ rest }.toFlags ++ "doc" :: (chosen.map fun (_, r) => (dirAbs / r).toString) ++ wizOpts).toArray
    let child ← try IO.Process.spawn { cmd := wiz, args, cwd := dirAbs }
      catch e => IO.eprintln s!"grail doc: {wiz}: {e}"; return 127
    child.wait
  | "build" :: _ | "test" :: _ | ["targets"] | ["config"] | ["update"] | ["run", _] =>
    let (pkg, localSettings) ← match ← readConfig flagged binId std dir with
      | .ok r => pure r
      | .error e => do IO.eprintln e; return 1
    let mut tc := defaults
    for (k, v) in pkg.settings ++ localSettings do
      match tc.set k v with
      | some t => tc := t
      | none => IO.eprintln s!"unknown setting {k}"; return 1
    -- the flags again, over the build files
    tc := (tc.parseFlags raw).1
    -- a dependency's build file
    let readPkg (d : System.FilePath) : IO (Except String Package) := do
      pure ((← readConfig tc binId std d).map (·.1))
    let depRoots : IO (Option (List System.FilePath)) := do
      match ← lockedRoots readPkg dir pkg IO.eprint with
      | .ok rs => pure (some rs)
      | .error e => IO.eprintln e; pure none
    match args with
    | ["config"] => IO.print tc.render; pure 0
    | ["update"] =>
      match ← update readPkg dir pkg with
      | .error e => IO.eprintln e; pure 1
      | .ok ls =>
        for l in ls do IO.println s!"{l.name}\t{l.url} {l.rev}\t{l.commit}"
        pure 0
    | ["targets"] =>
      for t in pkg.targets do
        match t with
        | .command c =>
          let tool := match c.tool with | .path n => n | .exe n => s!"exe {n}"
          let kind := if c.phony then "phony command" else if c.manual then "command (manual)" else "command"
          IO.println s!"{t.name}\t{kind}: {tool}, {c.inputs.length} inputs, outputs {c.outputPaths}"
        | _ => IO.println s!"{t.name}\t{repr t}"
      pure 0
    | "test" :: rest =>
      let update := rest.contains "--update"
      let filters := rest.filter (· != "--update")
      let some roots ← depRoots | return 1
      let r ← mkRunner { dir, std, tc, binId, libRoots := libRootsOf dir pkg.targets ++ roots }
      let results ← r.tests pkg.targets filters update
      let passed := results.filter (·.ok) |>.size
      let cached := results.filter (·.cached) |>.size
      IO.println s!"{passed} passed, {results.size - passed} failed ({cached} recorded passes)"
      pure (if passed == results.size then 0 else 1)
    | ["run", name] =>
      let some t := pkg.targets.find? (·.name == name) | IO.eprintln s!"no target {name}"; return 1
      let some roots ← depRoots | return 1
      -- the build's report goes to stderr: stdout is the program's
      let r ← mkRunner { dir, std, tc, binId, libRoots := libRootsOf dir pkg.targets ++ roots }
      let r := { r with out := IO.eprint }
      r.runTarget pkg.targets t runArgs
    | _ =>
      let wanted := args.drop 1
      let targets := if wanted.isEmpty then pkg.targets.filter (·.isDefault)
        else pkg.targets.filter (wanted.contains ·.name)
      for w in wanted do
        unless pkg.targets.any (·.name == w) do IO.eprintln s!"no target {w}"; return 1
      let some roots ← depRoots | return 1
      let r ← mkRunner { dir, std, tc, binId, libRoots := libRootsOf dir pkg.targets ++ roots }
      let ok ← r.build pkg.targets targets
      let st ← r.stats.get
      IO.println s!"{st.ran} jobs run, {st.upToDate} up to date{if st.failed > 0 then s!", {st.failed} failed" else ""}{if st.skipped > 0 then s!", {st.skipped} skipped" else ""}"
      pure (if ok then 0 else 1)
  | _ => IO.println usage; pure 0

end Grail
