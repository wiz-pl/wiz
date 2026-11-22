import Grail.Graph
import Grail.Deps
import Grail.Registry
import Grail.IndexCheck
import Grail.Lsp
import Grail.New
import Wiz.Attest
import Wiz.Version

/-!
# grail, a build tool for Wiz

`grail build [TARGET…]` builds the targets of the package in the current directory
(all of them by default), as described by its `grail.wiz`. See docs/stages/23-grail.md.
-/

namespace Grail
open Wiz

def usage : String := "usage:
  grail new NAME [--dir DIR]
                          write a minimal package (grail.wiz with a lib, an exe and
                          a tests target, src/Main.wiz, a README and a .gitignore)
                          into DIR (default: ./NAME); an existing non-empty
                          directory is refused, the name must be a letter then
                          letters, digits, '_' or '-'
  grail build [TARGET…] [--attest DIR]
                          build the package's targets (by default all but the
                          bootstrap check, which takes minutes); --attest DIR also
                          writes one unsigned build attestation per executable
  grail test [FILTER…] [--update] [--rerun]
                          run the tests (of `tests` targets) whose path contains a
                          filter; --update writes the actual output to .expected;
                          --rerun runs tests with a recorded pass again (and records
                          the new result: a pass, or no pass)
  grail update [--locked] resolve the dependencies again and write grail.lock
                          (builds use the lock only); --locked fails if the lock
                          would change
  grail fetch [--locked] [--offline] [--vendor DIR]
                          make every package of grail.lock present and verified,
                          without building; --locked never writes the lock,
                          --offline uses the cache only, --vendor DIR uses a
                          vendored directory of content-addressed archives
  grail vendor [DIR] [--locked] [--offline]
                          copy grail.lock's registry archives into DIR (default vendor/),
                          content-addressed, with DIR/index.sexpr; --locked never
                          resolves or writes the lock
  grail cache [path|list|verify]
                          the shared cache: content-addressed archives and
                          unpacked packages (and the index clone)
  grail index resolve [--index URL] [--offline]
                          print the versions `grail update` would pick
  grail index show NAME   print a package's index entry
  grail index check [INDEX] [--fetch] [--require-signature]
                          validate an index repository offline (names, versions,
                          SHA-256s of local archives, semver ranges, module-prefix
                          conflicts, index.wiz, a signed snapshot); --fetch downloads
                          remote archives and clones a git index
  grail index verify [INDEX] [--locked] [--allowed-signers FILE]
                          verify the index's signed snapshot offline; --locked also
                          requires it to match grail.lock (fingerprint, seq, digest)
  grail index snapshot [INDEX] [--seq N] [--updated T] [--key FP] [--expires T]
                          write index/snapshot.sexpr from the entries (then sign it
                          with ssh-keygen -Y sign -n grail-index)
  grail publish ARCHIVE --source URL [--commit SHA]
                          hash a release archive and print its index entry (after
                          checking the manifest and the archive layout); --commit
                          records the release commit the signed entry binds
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
options: -C DIR (the package directory), --dir DIR (with `new`: where to write the
  package, instead of ./NAME), --std DIR (the standard library),
  -j N (jobs at once; default: the number of cores, at most 4),
  --timeout SECS (a job's time limit, default 1800), --test-timeout SECS (default 300;
  a test's `-- test: run timeout SECS` line may ask for more),
  --cc X --cflags \"…\" --ldflags \"…\" --libs \"…\" --llc X --gc-cflags \"…\" --gc-ldflags \"…\" -I DIR,
  --cache DIR (the elaboration cache, default ~/.cache/wiz), --cache-ro DIR (repeatable:
  a read-only cache, searched in order after the write cache; refused unless
  --cache-ro-unsigned, because its manifests are self-signed), --cache-ro-unsigned,
  --no-cache (both),
  --index URL (the package index: a directory, a file, or a git URL; default: the
  `index` setting of grail.wiz), --index-commit COMMIT (pin a git index),
  --require-signature (require a verified signed index snapshot; CI and the install
  docs pass it), --allow-unsigned (the explicit escape: accept an index with no signed
  snapshot), --allowed-signers FILE
  (the trust root for the snapshot; default: the key a grail.lock pinned),
  --allow-rewind (accept a rewritten index history or a lower snapshot seq),
  --offline (never touch the network),
  --vendor DIR (a directory of vendored archives; default: the `vendor` setting),
  --source URL (grail publish: the archive's public URL),
  --region-cache (experimental: serve module effects from mmap'ed .wizr regions in the
  same cache layers; the text entries remain the authority and the fallback),
  --region-stats (print what those regions served, per job),
  --trust-native (27a: allow `native_refl`, passed on to every check and to `wiz lsp`), --native-fuel N
Machine settings (where GMP lives) go in an uncommitted grail.local.wiz:
  import Grail
  def settings : Settings := Settings.empty |> Settings.set \"cflags\" \"-I…\""

/-- What identifies this binary (so a new elaborator or backend rebuilds everything):
`Cache.binaryId`, remembered under the write cache directory (never a read-only one). -/
def binaryId (cacheDir : Option System.FilePath) : IO UInt64 := Cache.binaryId cacheDir

structure Opts where
  dir : Option String := none
  /-- `grail new`: the directory to write the package into (default: `./NAME`) -/
  newDir : Option String := none
  std : Option String := none
  jobs : Option Nat := none
  timeout : Option Nat := none
  testTimeout : Option Nat := none
  /-- `grail lsp`: the `wiz` to run -/
  wiz : Option String := none
  /-- (23m) the package index: a directory, a file, or a git URL -/
  index : Option String := none
  /-- (23m) pin a git index to one commit -/
  indexCommit : Option String := none
  /-- (23m) accept a rewritten index history (R22) or a lower signed snapshot sequence -/
  allowRewind : Bool := false
  /-- (23m, Stage 1) require a verified signed snapshot of the index -/
  requireSignature : Bool := false
  /-- (23m, Stage 1) the allowed_signers file that authorises the index's key -/
  allowedSigners : Option String := none
  /-- (23m) `grail index check`: also download remote archives and clone a git index -/
  fetch : Bool := false
  /-- (23m) never touch the network -/
  offline : Bool := false
  /-- (23m) fail instead of writing grail.lock -/
  locked : Bool := false
  /-- (23n) a directory of vendored, content-addressed archives -/
  vendor : Option String := none
  /-- (23m) `grail publish`: the archive's public URL -/
  source : Option String := none
  /-- (P0) `grail publish`: the release commit the signed entry binds -/
  commit : Option String := none
  /-- `grail build --attest DIR`: write one statement per built executable -/
  attest : Option String := none

/-- `-C DIR`, `--dir DIR`, `--std DIR`, `-j N`, `--timeout SECS`, `--test-timeout SECS`, taken out of the arguments. -/
partial def grailOpts (o : Opts) : List String → Opts × List String
  | "-C" :: d :: rest => grailOpts { o with dir := some d } rest
  | "--dir" :: d :: rest => grailOpts { o with newDir := some d } rest
  | "--std" :: d :: rest => grailOpts { o with std := some d } rest
  | "-j" :: n :: rest => grailOpts { o with jobs := n.toNat? } rest
  | "--timeout" :: n :: rest => grailOpts { o with timeout := n.toNat? } rest
  | "--test-timeout" :: n :: rest => grailOpts { o with testTimeout := n.toNat? } rest
  | "--wiz" :: w :: rest => grailOpts { o with wiz := some w } rest
  | "--index" :: i :: rest => grailOpts { o with index := some i } rest
  | "--index-commit" :: c :: rest => grailOpts { o with indexCommit := some c } rest
  | "--vendor" :: v :: rest => grailOpts { o with vendor := some v } rest
  | "--allow-rewind" :: rest => grailOpts { o with allowRewind := true } rest
  | "--require-signature" :: rest => grailOpts { o with requireSignature := true } rest
  | "--allow-unsigned" :: rest => grailOpts { o with requireSignature := false } rest
  | "--allowed-signers" :: f :: rest => grailOpts { o with allowedSigners := some f } rest
  | "--source" :: s :: rest => grailOpts { o with source := some s } rest
  | "--commit" :: c :: rest => grailOpts { o with commit := some c } rest
  | "--fetch" :: rest => grailOpts { o with fetch := true } rest
  | "--offline" :: rest => grailOpts { o with offline := true } rest
  | "--locked" :: rest => grailOpts { o with locked := true } rest
  | "--attest" :: d :: rest => grailOpts { o with attest := some d } rest
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

/-- A path given on the command line, relative to the package directory (`grail -C P`
makes `vendor` `P/vendor`). An absolute path is used as it is. -/
def inPackage (dir : System.FilePath) (p : String) : System.FilePath :=
  if p.startsWith "/" then System.FilePath.mk p else dir / p

/-- Where this build's vendor directory is: `--vendor DIR` wins, then the `vendor`
setting of `grail.wiz`/`grail.local.wiz` (a relative path is under the package). -/
def vendorOf (dir : System.FilePath) (opt : Option String) (pkg : Package)
    (localSettings : List (String × String)) : Option System.FilePath :=
  let v : Option String := match opt with
    | some v => some v
    | none =>
      let found := (pkg.settings ++ localSettings).reverse.find?
        (fun kv : String × String => kv.1 == "vendor")
      found.map (fun kv : String × String => kv.2)
  v.map (inPackage dir)

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
  let mkRunner (ctx : Ctx) (testTimeoutMs : Nat := 1000 * opts.testTimeout.getD 300) : IO Runner := do
    pure { ctx, stats := ← IO.mkRef {}, memo := ← IO.mkRef {}, jobs, self := ← IO.appPath,
           timeoutMs := 1000 * opts.timeout.getD 1800, testTimeoutMs }
  -- the flags win over the build files; read them now, apply them last
  let raw := args
  let (flagged, args) := defaults.parseFlags args
  let binId ← binaryId flagged.cacheDir
  -- (23m) the registry cache (archives, the index) shares --cache with elaboration
  let cache : System.FilePath := flagged.cacheDir.getD (System.FilePath.mk home / ".cache" / "wiz")
  -- (23m) `grail index check`: validate an index repository. It needs no grail.wiz
  -- (the index repository is not a package) and touches no network unless --fetch.
  if let "index" :: "check" :: rest := args then
    let spec := rest.find? (fun a => !a.startsWith "-") |>.getD (opts.index.getD dir.toString)
    match ← checkDir cache flagged binId std spec opts.fetch opts.requireSignature opts.allowedSigners with
    | .error e => IO.eprintln e; return 1
    | .ok r =>
      for line in r.lines do IO.println line
      IO.println r.summary
      return (if r.hasErrors then 1 else 0)
  -- (23n) the shared cache needs no grail.wiz
  if let "cache" :: rest := args then
    match rest with
    | [] | ["path"] =>
      for line in Registry.cachePathLines cache do IO.println line
      return 0
    | ["list"] =>
      for line in ← Registry.cacheList cache do IO.println line
      return 0
    | ["verify"] =>
      let (errs, ok) ← Registry.cacheVerify cache
      for e in errs do IO.println e
      IO.println (if ok then "cache ok" else s!"{errs.length} cache error(s)")
      return (if ok then 0 else 1)
    | _ =>
      IO.eprintln "usage: grail cache [path|list|verify]"
      return 2

  -- (23m, Stage 1) verify the index's signed snapshot offline; with --locked, against
  -- the key/sequence/digest grail.lock recorded.
  if let "index" :: "verify" :: rest := args then
    let spec := rest.find? (fun a => !a.startsWith "-") |>.getD (opts.index.getD dir.toString)
    let pinned ←
      if opts.locked then
        match ← Registry.lockSignature dir with
        | some s => pure (some s)
        | none => IO.eprintln "grail.lock has no index signature (run `grail update --require-signature`)"; return 1
      else pure none
    match ← Registry.loadIndex cache spec true "" opts.allowRewind true opts.allowedSigners pinned with
    | .error e => IO.eprintln e; return 1
    | .ok src =>
      match src.signature with
      | none => IO.eprintln "the index is not signed"; return 1
      | some s =>
        IO.println s!"signed by {s.identity} {s.fingerprint}"
        IO.println s!"snapshot seq {s.seq}, updated {s.updated}, expires {s.expires}"
        IO.println s!"snapshot sha256 {s.sha256}"
        return 0
  -- (23m, Stage 1) generate the unsigned snapshot; the maintainer then signs it with
  -- `ssh-keygen -Y sign -n grail-index -f KEY index/snapshot.sexpr`.
  if let "index" :: "snapshot" :: rest := args then
    let spec := rest.find? (fun a => !a.startsWith "-") |>.getD (opts.index.getD dir.toString)
    let rec flags (seq : Option Nat) (updated key expires : String) : List String → Option Nat × String × String × String
      | "--seq" :: n :: t => flags (n.toNat?) updated key expires t
      | "--updated" :: u :: t => flags seq u key expires t
      | "--key" :: k :: t => flags seq updated k expires t
      | "--expires" :: e :: t => flags seq updated key e t
      | _ :: t => flags seq updated key expires t
      | [] => (seq, updated, key, expires)
    let (seqOpt, updatedOpt, key, expires) := flags none "" "" "" rest
    let p : System.FilePath := spec
    unless ← (p / "index").isDir do
      IO.eprintln s!"grail index snapshot: {spec}: not a local index directory (it writes index/snapshot.sexpr)"
      return 1
    if key.isEmpty || expires.isEmpty then
      IO.eprintln "grail index snapshot: --key FP and --expires T are required (a snapshot without them cannot be verified)"
      return 1
    if !Sign.validUtc expires then
      IO.eprintln s!"grail index snapshot: --expires {expires} is not UTC (YYYY-MM-DDTHH:MM:SSZ)"
      return 1
    match ← Registry.readIndexDir p with
    | .error e => IO.eprintln e; return 1
    | .ok pkgs =>
      let seq ← match seqOpt with | some n => pure n | none => Sign.nextSeq p
      if seq == 0 then
        IO.eprintln "grail index snapshot: --seq must be positive (rollback protection)"
        return 1
      let updated ← if !updatedOpt.isEmpty then pure updatedOpt else
        match ← Sign.nowUtc with
        | .ok t => pure t
        | .error e => IO.eprintln e; return 1
      if !Sign.validUtc updated then
        IO.eprintln s!"grail index snapshot: --updated {updated} is not UTC (YYYY-MM-DDTHH:MM:SSZ)"
        return 1
      let name ← Sign.registryName p
      let snap ← Sign.ofIndex p name pkgs seq updated key expires
      let path := p / "index" / "snapshot.sexpr"
      -- an old signature cannot cover the new bytes; remove it so the next sign cannot
      -- leave a stale .sig in place
      let oldSig : System.FilePath := System.FilePath.mk (path.toString ++ ".sig")
      if ← oldSig.pathExists then IO.FS.removeFile oldSig
      Cache.writeAtomic path (Snapshot.render snap)
      IO.println s!"wrote {path} (seq {seq}, {snap.packages.length} packages)"
      IO.println s!"sign it with: ssh-keygen -Y sign -n grail-index -f KEY {path}"
      return 0
  match args with
  | "new" :: rest =>
    -- (23o) the smallest package; an existing non-empty directory is refused
    match rest with
    | [name] =>
      let base : System.FilePath := opts.newDir.getD name
      let target := if base.isAbsolute then base else dir / base
      match ← newPackage name target with
      | .error e => IO.eprintln e; pure 1
      | .ok () =>
        IO.println s!"grail new: wrote {target} (grail.wiz, src/Main.wiz, tests/hello.wiz, README.md, .gitignore)"
        IO.println s!"  cd {target} && grail build && grail run {name}"
        pure 0
    | _ =>
      IO.eprintln "grail new: expected NAME [--dir DIR]"
      IO.eprintln usage
      pure 2
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
        if k == "index" || k == "index-commit" || k == "vendor" then continue
        match tc.set k v with
        | some t => tc := t
        | none => IO.eprintln s!"grail lsp: unknown setting {k} (ignored)"
      tc := (tc.parseFlags raw).1
      let readPkg (d : System.FilePath) : IO (Except String Package) := do
        pure ((← readConfig tc binId std d).map (·.1))
      let deps ← match ← Registry.lockedRoots cache readPkg dir pkg IO.eprint opts.offline
          (vendorOf dir opts.vendor pkg localSettings) with
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
      if k == "index" || k == "index-commit" || k == "vendor" then continue
      match tc.set k v with
      | some t => tc := t
      | none => IO.eprintln s!"unknown setting {k}"; return 1
    tc := (tc.parseFlags raw).1
    let readPkg (d : System.FilePath) : IO (Except String Package) := do
      pure ((← readConfig tc binId std d).map (·.1))
    let deps ← match ← Registry.lockedRoots cache readPkg dir pkg IO.eprint opts.offline
        (vendorOf dir opts.vendor pkg localSettings) with
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
  | "build" :: _ | "test" :: _ | ["targets"] | ["config"] | "update" :: _ | "fetch" :: _
  | "vendor" :: _ | "index" :: _ | "publish" :: _ | ["run", _] =>
    let (pkg, localSettings) ← match ← readConfig flagged binId std dir with
      | .ok r => pure r
      | .error e => do IO.eprintln e; return 1
    let mut tc := defaults
    for (k, v) in pkg.settings ++ localSettings do
      if k == "index" || k == "index-commit" || k == "vendor" then continue
      match tc.set k v with
      | some t => tc := t
      | none => IO.eprintln s!"unknown setting {k}"; return 1
    -- the flags again, over the build files
    tc := (tc.parseFlags raw).1
    -- a dependency's build file
    let readPkg (d : System.FilePath) : IO (Except String Package) := do
      pure ((← readConfig tc binId std d).map (·.1))
    -- (23m) the index: --index wins, then the `index` setting of grail.wiz/grail.local.wiz;
    -- --index-commit (or the `index-commit` setting) appends `#COMMIT` to pin a git index
    let indexBase : String :=
      match opts.index with
      | some i => i
      | none => ((pkg.settings ++ localSettings).reverse.find? (·.1 == "index")).map (·.2) |>.getD ""
    let indexPin : String :=
      match opts.indexCommit with
      | some c => c
      | none => ((pkg.settings ++ localSettings).reverse.find? (·.1 == "index-commit")).map (·.2) |>.getD ""
    let indexSpec : String :=
      if indexPin.isEmpty || indexBase.contains "#" then indexBase else indexBase ++ "#" ++ indexPin
    let lockPin : String :=
      if !indexPin.isEmpty then indexPin
      else match indexBase.splitOn "#" with | [_, p] => p | _ => ""
    let vendorOpt : Option System.FilePath := vendorOf dir opts.vendor pkg localSettings
    let readLock : IO (Except String Lock) := do
      if ← (lockFile dir).pathExists then
        pure (Lock.parse (← IO.FS.readFile (lockFile dir)))
      else pure (.error s!"no {lockFile dir}: run `grail update`")
    let depRoots : IO (Option (List System.FilePath)) := do
      match ← Registry.lockedRoots cache readPkg dir pkg IO.eprint opts.offline vendorOpt with
      | .ok rs => pure (some rs)
      | .error e => IO.eprintln e; pure none
    -- `fetch`/`vendor` share this: `--locked` never writes the lock, and fails if it is
    -- missing or out of date; without it, a missing lock is resolved (and written)
    let getLock : IO (Except String Lock) := do
      let noDeps := pkg.deps.isEmpty && pkg.requires.isEmpty && pkg.overrides.isEmpty
      match ← readLock with
      | .ok l =>
        match Registry.checkLocked l pkg lockPin (strictOverride := opts.locked)
            (requireSignature := opts.requireSignature) with
        | .ok () => pure (.ok l)
        | .error e => pure (.error e)
      | .error e =>
        if noDeps then pure (.ok {})
        else if opts.locked then pure (.error e) else
          match ← Registry.resolveLock cache indexSpec opts.offline readPkg dir pkg opts.allowRewind
              opts.requireSignature opts.allowedSigners with
          | .error e => pure (.error e)
          | .ok l =>
            Cache.writeAtomic (lockFile dir) (Lock.render l)
            pure (.ok l)
    match args with
    | ["config"] => IO.print tc.render; pure 0
    | "update" :: _ =>
      if opts.locked then
        -- (R10) `--locked` is a *check*, not a re-resolution: it reads the lock only and
        -- never touches the index, so publishing a new version cannot make CI fail.
        let noDeps := pkg.deps.isEmpty && pkg.requires.isEmpty && pkg.overrides.isEmpty
        match ← readLock with
        | .error e => if noDeps then pure 0 else IO.eprintln e; pure 1
        | .ok l =>
          match Registry.checkLocked l pkg lockPin (strictOverride := true)
              (requireSignature := opts.requireSignature) with
          | .error e => IO.eprintln e; pure 1
          | .ok () =>
            for p in l.pkgs do IO.println s!"{p.name}\t{p.version}\t{p.source}"
            for g in l.git do IO.println s!"{g.name}\t{g.url} {g.rev}\t{g.commit}"
            for o in l.overrides do IO.println s!"{o.name}\toverride {o.path}\t{o.hash}"
            pure 0
      else
        match ← Registry.resolveLock cache indexSpec opts.offline readPkg dir pkg opts.allowRewind
            opts.requireSignature opts.allowedSigners with
        | .error e => IO.eprintln e; pure 1
        | .ok l =>
          let text := Lock.render l
          let old ← if ← (lockFile dir).pathExists then some <$> IO.FS.readFile (lockFile dir) else pure none
          let empty := l.git.isEmpty && l.pkgs.isEmpty && l.overrides.isEmpty
          if old != some text && (!empty || old.isSome) then Cache.writeAtomic (lockFile dir) text
          for p in l.pkgs do IO.println s!"{p.name}\t{p.version}\t{p.source}"
          for g in l.git do IO.println s!"{g.name}\t{g.url} {g.rev}\t{g.commit}"
          for o in l.overrides do IO.println s!"{o.name}\toverride {o.path}\t{o.hash}"
          pure 0
    | "fetch" :: _ =>
      match ← getLock with
      | .error e => IO.eprintln e; pure 1
      | .ok l =>
        match ← Registry.fetch cache dir l opts.offline vendorOpt with
        | .error e => IO.eprintln e; pure 1
        | .ok lines =>
          for line in lines do IO.println line
          pure 0
    | "vendor" :: rest =>
      -- the archives of the lock, in DIR (default vendor/), content-addressed; the lock
      -- itself is never rewritten (its `source` stays the published URL)
      let vdir := rest.find? (fun a => !a.startsWith "-") |>.map (inPackage dir)
        |>.getD (vendorOpt.getD (dir / "vendor"))
      match ← getLock with
      | .error e => IO.eprintln e; pure 1
      | .ok l =>
        match ← Registry.vendor cache vdir l opts.offline with
        | .error e => IO.eprintln e; pure 1
        | .ok lines =>
          for line in lines do IO.println line
          pure 0
    | "publish" :: rest =>
      let archive := rest.find? (fun a => !a.startsWith "-")
      match ← Registry.publish (archive.map System.FilePath.mk) (opts.source.getD "") pkg
          (opts.commit.getD "") with
      | .error e => IO.eprintln e; pure 1
      | .ok entry => IO.println entry; pure 0
    | "index" :: "resolve" :: _ =>
      if pkg.requires.isEmpty then pure 0 else
        let pinned ← Registry.lockSignature dir
        match ← Registry.loadIndex cache indexSpec opts.offline "" opts.allowRewind
            opts.requireSignature opts.allowedSigners pinned with
      | .error e => IO.eprintln e; pure 1
      | .ok src =>
        match Resolve.resolve src.pkgs pkg.requires Wiz.version with
        | .error e => IO.eprintln e; pure 1
        | .ok rs =>
          for r in rs do IO.println s!"{r.name}\t{Version.render r.version}\t{r.sha256}\t{r.source}"
          pure 0
    | "index" :: "show" :: name :: _ =>
      let pinned ← Registry.lockSignature dir
      match ← Registry.loadIndex cache indexSpec opts.offline "" opts.allowRewind
          opts.requireSignature opts.allowedSigners pinned with
      | .error e => IO.eprintln e; pure 1
      | .ok src =>
        match src.pkgs[name]? with
        | none => IO.eprintln s!"no package {name} in the index"; pure 1
        | some p =>
          IO.println s!"{p.name}\t{p.summary}"
          for v in p.versions do
            IO.println s!"  {Version.render v.version}\t{v.sha256}\t{v.toolchain}\t{v.source}{if v.yanked.isEmpty then "" else " (yanked: " ++ v.yanked ++ ")"}"
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
      -- Flags after the subcommand are not seen by the parser above (it stops at `test`),
      -- so `grail test --test-timeout 900 …` used to leave the flag in `filters` and the
      -- runner at its 300 s default — a "timed out (300 s)" that no flag could raise.
      let (topts, rest) := grailOpts {} rest
      let update := rest.contains "--update"
      let rerun := rest.contains "--rerun"
      let filters := rest.filter (fun a => a != "--update" && a != "--rerun")
      let some roots ← depRoots | return 1
      let r ← mkRunner { dir, std, tc, binId, libRoots := libRootsOf dir pkg.targets ++ roots }
          (1000 * (topts.testTimeout.getD 300))
      let r : Runner := { r with rerunTests := rerun }
      let results ← r.tests pkg.targets filters update
      let skipped := results.filter (·.skipped) |>.size
      let passed := results.filter (fun x => x.ok && !x.skipped) |>.size
      let failed := results.size - passed - skipped
      let cached := results.filter (·.cached) |>.size
      IO.println s!"{passed} passed, {failed} failed{if skipped > 0 then s!", {skipped} skipped" else ""} ({cached} recorded passes)"
      pure (if failed == 0 then 0 else 1)
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
      let mut ok ← r.build pkg.targets targets
      if let some a := opts.attest then do
        let adir := System.FilePath.mk a
        IO.FS.createDirAll adir
        for t in targets do
          if let .exe n f := t then do
            let bin := dir / ".grail" / "bin" / n
            if ← bin.pathExists then do
              let src := if System.FilePath.isAbsolute f then System.FilePath.mk f else dir / f
              let out := adir / (n ++ ".attest.json")
              match ← Wiz.Attest.emit tc src.toString bin false false false 0 out (some r.ctx.roots) with
              | .ok () => IO.eprintln s!"grail: attestation written to {out}"
              | .error e => IO.eprintln s!"grail attest: {e}"; ok := false
          else pure ()
      let st ← r.stats.get
      IO.println s!"{st.ran} jobs run, {st.upToDate} up to date{if st.failed > 0 then s!", {st.failed} failed" else ""}{if st.skipped > 0 then s!", {st.skipped} skipped" else ""}"
      pure (if ok then 0 else 1)
  | _ => IO.println usage; pure 0

end Grail
