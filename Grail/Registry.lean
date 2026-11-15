import Grail.Deps
import Grail.Index
import Wiz.Version
import Wiz.Smt.Sha256

/-!
# The registry: index source, lock file, fetch (stage 23m, prototype)

The index is read by `grail update` only; builds read `grail.lock`, which records the exact
version, archive URL and SHA-256 of every registry package, so a build needs no index and
no network unless something is missing from the cache.

    (lock
      (index "https://github.com/wiz-pl/grail-index" "<commit>")
      (dep "greet" "https://example.org/greet.git" "v1" "<commit>" "<content>")
      (pkg "std" "0.1.2" "https://…/std-0.1.2.tar.gz" "<sha256>"
           (deps (dep "unused" "^0"))))

`grail fetch --locked` is the offline/strict path: it never writes the lock, downloads
each archive into `<cache>/grail/downloads/<sha256>`, checks the hash of every archive
before it is unpacked, and unpacks into `.grail/packages/<name>`.
-/

namespace Grail
open Wiz Cache

/-- The SHA-256 of a byte array, as lowercase hex (the pure implementation in
`Wiz/Smt/Sha256.lean`: no external `sha256sum` for a lock's tree or command digest). -/
def sha256Bytes (b : ByteArray) : String := Wiz.Smt.Sha256.hexBytes b

/-- The SHA-256 of a string's UTF-8 bytes. -/
def sha256String (s : String) : String := Wiz.Smt.Sha256.hex s

/-- One archive of a vendor directory: a lock package and the file that holds its bytes. -/
structure VendorEntry where
  name : String
  version : String
  sha256 : String
  file : String
  deriving Repr, Inhabited, BEq

/-- `vendor/index.sexpr`: which content-addressed file holds each `name@version` of the
lock. The vendor directory is a *copy* of the lock's archives; it does not change the
lock (whose `source` still names the published URL) and it is not an index for the
resolver. Two packages with the same bytes share one file. -/
structure VendorIndex where
  entries : List VendorEntry := []
  deriving Repr, Inhabited, BEq

namespace VendorIndex

def render (v : VendorIndex) : String :=
  let es := (v.entries.toArray.qsort fun a b =>
    a.name < b.name || (a.name == b.name && a.version < b.version)).toList
  "(vendor\n  (format 1)" ++
    (if es.isEmpty then "" else "\n  " ++ "\n  ".intercalate (es.map fun e =>
      (node "archive" [str e.name, str e.version, str e.sha256, str e.file]).render)) ++
    ")\n"

/-- Parse `vendor/index.sexpr`; unknown fields are ignored (it is grail's own file, but a
future grail may add one). -/
def parse (s : String) : Except String VendorIndex := do
  let some (.l xs) := Sx.parse s | throw "vendor/index.sexpr: expected (vendor …)"
  match xs.toList with
  | .a "vendor" :: fields =>
    let mut out : VendorIndex := {}
    for f in fields do
      match f with
      | .l #[.a "archive", .a name, .a version, .a sha256, .a file] =>
        out := { out with entries := out.entries ++ [{ name, version, sha256, file }] }
      | _ => pure ()
    pure out
  | _ => throw "vendor/index.sexpr: expected (vendor …)"

def find (v : VendorIndex) (sha256 : String) : Option VendorEntry :=
  v.entries.find? (·.sha256 == sha256)

end VendorIndex

/-- (R20) The SHA-256 of a package tree: sorted `path NUL sha256(content) LF` lines,
hashed. The same construction is used for a published archive and for
`.grail/packages/NAME`, so a hand-edited file inside a fetched package changes the hash
and the lock refuses it (Go's `dirhash` is the model). -/
def treeHash (root : System.FilePath) : IO (Except String String) := do
  let nul := String.singleton (Char.ofNat 0)
  try
    let mut text := ""
    for f in ← packageFiles root do
      text := text ++ f ++ nul ++ sha256Bytes (← IO.FS.readBinFile (root / f)) ++ "\n"
    pure (.ok (sha256String text))
  catch e => pure (.error s!"{root}: {e}")

namespace Lock

/-- (R36) The digest of a package's declared `Package.command` set. Empty when the package
has no command targets. It covers every field of a command (tool, arguments, declared
inputs/outputs, stdout, environment, working directory, used tools, phony/manual), so a
version that silently gains or changes a build-time command is a visible lock change. -/
def commandDigest (ts : List Target) : String :=
  let tool (t : Tool) : Cache.Sx := match t with
    | .path n => Cache.node "path" [Cache.str n]
    | .exe n => Cache.node "exe" [Cache.str n]
  let part (p : Part) : Cache.Sx := match p with
    | .text s => Cache.node "text" [Cache.str s]
    | .input f => Cache.node "in" [Cache.str f]
    | .output f => Cache.node "out" [Cache.str f]
  let command (c : Command) : Cache.Sx :=
    Cache.node "command" [
      Cache.str c.name, tool c.tool,
      Cache.list (c.args.map fun ps => Cache.list (ps.map part)),
      Cache.list (c.inputs.map Cache.str),
      Cache.list (c.outputs.map fun (p, dir) => Cache.node (if dir then "dir" else "file") [Cache.str p]),
      (match c.stdout with | some p => Cache.node "stdout" [Cache.str p] | none => .a "-"),
      Cache.list (c.env.map fun (k, v) => Cache.node "env" [Cache.str k, Cache.str v]),
      .a (if c.inOutDir then "1" else "0"),
      Cache.list (c.uses.map tool),
      .a (if c.phony then "1" else "0"),
      .a (if c.manual then "1" else "0")]
  let cmds := ts.filterMap fun | .command c => some c | _ => none
  if cmds.isEmpty then "" else
    sha256String ("\n".intercalate (cmds.map fun c => (command c).render))

namespace Registry

/-! ## Verifying and unpacking an archive -/

/-- The SHA-256 of a file, as lowercase hex (`sha256sum`, or `shasum -a 256`). -/
def sha256File (f : System.FilePath) : IO (Except String String) := do
  for cmd in [("sha256sum", #[]), ("shasum", #["-a", "256"])] do
    try
      let o ← IO.Process.output { cmd := cmd.1, args := cmd.2.push f.toString }
      if o.exitCode == 0 then
        match o.stdout.trimAscii.toString.splitOn " " with
        | h :: _ => return .ok h
        | [] => pure ()
    catch _ => pure ()
  pure (.error s!"no sha256sum (or shasum) to hash {f}")

/-- Copy a file's bytes (archives are binary; `Cache.writeAtomic` is for text). -/
def copyBin (src dest : System.FilePath) : IO (Except String Unit) := do
  try
    IO.FS.writeBinFile dest (← IO.FS.readBinFile src)
    pure (.ok ())
  catch e => pure (.error s!"{src}: {e}")

/-- Remove a file, a symlink or a directory tree (a stale `.grail/packages/NAME` may be
any of them). `removeFile` first, so a symlink is unlinked rather than followed. -/
def removePath (p : System.FilePath) : IO Unit := do
  if ← p.pathExists then
    try IO.FS.removeFile p
    catch _ => IO.FS.removeDirAll p

/-- A recursive copy, for a platform without `ln` (the shared store is linked when it
can be, and copied when it cannot). -/
def copyTree (src dest : System.FilePath) : IO (Except String Unit) := do
  removePath dest
  if let some parent := dest.parent then IO.FS.createDirAll parent
  try
    let o ← IO.Process.output { cmd := "cp", args := #["-a", src.toString, dest.toString] }
    pure (if o.exitCode == 0 then .ok ()
      else .error s!"cp {src} {dest}: {o.stderr.trimAscii}")
  catch e => pure (.error s!"cp: {e}")

/-- The extension an archive's file keeps in a vendor directory (all grail unpacks today
is `.tar.gz`; the others are copied faithfully if a future fetcher learns them). -/
def archiveExt (source : String) : String :=
  let path := (source.splitOn "?").head!
  match [".tar.gz", ".tgz", ".tar.xz", ".tar.bz2", ".zip"].find? (path.endsWith ·) with
  | some e => e
  | none => ".tar.gz"

/-- Find `sha256`'s archive in a vendor directory: `vendor/index.sexpr` first, then the
content-addressed names (`<sha256>.tar.gz`, `<sha256>`, …). A lock's `source` is never
rewritten; the hash is what identifies the bytes (so a vendor directory works with the
same lock on every machine). -/
def lookupVendor (dir : System.FilePath) (sha256 : String) : IO (Option System.FilePath) := do
  if ← (dir / "index.sexpr").pathExists then
    match VendorIndex.parse (← IO.FS.readFile (dir / "index.sexpr")) with
    | .ok v =>
      if let some e := v.find sha256 then
        let f := dir / e.file
        if ← f.pathExists then return some f
    | .error _ => pure ()
  for ext in ["", ".tar.gz", ".tgz", ".tar.xz", ".tar.bz2", ".zip"] do
    let f := dir / (sha256 ++ ext)
    if ← f.pathExists then return some f
  if ← dir.isDir then
    for e in ← dir.readDir do
      if e.fileName.startsWith (sha256 ++ ".") then return some e.path
  pure none

/-- Download `url` to `dest` (`curl` for http/https, a copy for a path or `file://`). -/
def download (url : String) (dest : System.FilePath) : IO (Except String Unit) := do
  if url.startsWith "file://" then
    if let .error e ← copyFile (url.drop 7).toString dest then return .error e
    return .ok ()
  if !url.contains "://" then
    return (← copyFile url dest).map (fun _ => ())
  try
    let o ← IO.Process.output { cmd := "curl", args :=
      #["-fsSL", "--retry", "2", "--connect-timeout", "20", "-o", dest.toString, url] }
    pure (if o.exitCode == 0 then .ok ()
      else .error s!"curl {url}: {o.stderr.trimAscii}")
  catch e => pure (.error s!"curl: {e}")

where
  copyFile (src : String) (dest : System.FilePath) : IO (Except String Unit) := do
    if !(← (System.FilePath.mk src).pathExists) then return .error s!"{src}: no such file"
    try
      IO.FS.writeBinFile dest (← IO.FS.readBinFile src)
      pure (.ok ())
    catch e => pure (.error s!"{src}: {e}")

/-- Unpack a `.tar.gz` into `dest`, dropping its single top-level directory. -/
def untar (tar : System.FilePath) (dest : System.FilePath) : IO (Except String Unit) := do
  try
    let o ← IO.Process.output { cmd := "tar", args :=
      #["-xzf", tar.toString, "-C", dest.toString, "--strip-components=1", "--no-same-owner"] }
    pure (if o.exitCode == 0 then .ok ()
      else .error s!"tar {tar}: {o.stderr.trimAscii}")
  catch e => pure (.error s!"tar: {e}")

/-- The tree hash of an archive's contents: unpack into a temporary directory (the same
`--strip-components=1` layout `fetch` uses) and hash the tree. -/
def unpackTreeHash (tar : System.FilePath) : IO (Except String String) := do
  let tmp ← IO.FS.createTempDir
  let d := tmp / "tree"
  IO.FS.createDirAll d
  match ← untar tar d with
  | .error e => IO.FS.removeDirAll tmp; return .error e
  | .ok () =>
    let r ← treeHash d
    IO.FS.removeDirAll tmp
    pure r

/-- The cached archive for `p`, downloading and verifying it if needed. A `vendor`
directory is searched first (by hash, so the lock's source URL is not rewritten); a
missing or corrupt cache entry is fetched again. With `offline`, a missing or corrupt
entry (in the cache and in the vendor directory) is an error: nothing is downloaded. -/
def archive (cache : System.FilePath) (p : PkgLock) (offline : Bool := false)
    (vendor : Option System.FilePath := none) :
    IO (Except String System.FilePath) := do
  let dir := cache / "grail" / "downloads"
  IO.FS.createDirAll dir
  let f := dir / p.sha256
  if ← f.pathExists then
    match ← sha256File f with
    | .ok h => if h == p.sha256 then return .ok f
    | .error _ => pure ()
    -- a corrupt or wrongly named archive: fetch it again
    IO.FS.removeFile f
  if let some vd := vendor then
    match ← lookupVendor vd p.sha256 with
    | some vf =>
      match ← sha256File vf with
      | .ok h =>
        if h == p.sha256 then
          -- offline can use the vendor file in place; online still fills the shared cache,
          -- so a later fetch needs neither the vendor directory nor the network
          if offline then return .ok vf
          let tmp := dir / s!"{p.sha256}.tmp{← IO.Process.getPID}"
          match ← copyBin vf tmp with
          | .error e => return .error e
          | .ok () =>
            IO.FS.rename tmp f
            return .ok f
        else if offline then
          return .error s!"--offline: the vendor archive {vf} is not {p.name} {p.version} (sha256 {h}, the lock says {p.sha256})"
      | .error e => if offline then return .error e else pure ()
    | none => pure ()
  if offline then
    return .error s!"--offline: {p.name} {p.version} is not in the archive cache ({f}); run `grail fetch` without --offline"
  let tmp := dir / s!"{p.sha256}.tmp{← IO.Process.getPID}"
  match ← download p.source tmp with
  | .error e =>
    if ← tmp.pathExists then IO.FS.removeFile tmp
    return .error s!"{p.name} {p.version}: {e}"
  | .ok () =>
    match ← sha256File tmp with
    | .error e =>
      if ← tmp.pathExists then IO.FS.removeFile tmp
      return .error s!"{p.name} {p.version}: {e}"
    | .ok h =>
      if h != p.sha256 then
        IO.FS.removeFile tmp
        return .error s!"{p.name} {p.version}: {p.source} has sha256 {h}, the lock says {p.sha256}"
      IO.FS.rename tmp f
      pure (.ok f)

/-- The stamp a fetched package carries: the hash of the archive it came from. -/
def stampFile (dir : System.FilePath) : System.FilePath := dir / ".grail-pkg"

def stamp (dir : System.FilePath) : IO (Option String) := do
  let f := stampFile dir
  if !(← f.pathExists) then return none
  pure (some (← IO.FS.readFile f).trimAscii.toString)

/-- The shared package store: one unpacked tree per archive hash, under the cache, so two
projects (or two package names in one lock, if they share bytes) unpack it once. -/
def storeDir (cache : System.FilePath) (sha256 : String) : System.FilePath :=
  cache / "grail" / "packages" / sha256

/-- Make `dir` point at `src`: a symlink when `ln` works, a copy otherwise. Both are
content-addressed by the caller, so a copy is still one unpack and no second download. -/
def linkTree (src dir : System.FilePath) : IO (Except String Unit) := do
  if let some parent := dir.parent then IO.FS.createDirAll parent
  removePath dir
  let o ← IO.Process.output { cmd := "ln", args := #["-s", src.toString, dir.toString] }
  if o.exitCode == 0 then return .ok ()
  -- no `ln` here (or it failed): copy the shared tree into the project
  copyTree src dir

/-- Make `.grail/packages/NAME` be the unpacked `p`, through the shared store. `false`
when the project already had it (no archive read, no unpack). -/
def ensurePkg (cache : System.FilePath) (packagesDir : System.FilePath) (p : PkgLock)
    (offline : Bool := false) (vendor : Option System.FilePath := none) :
    IO (Except String Bool) := do
  let dir := packagesDir / p.name
  if (← stamp dir) == some p.sha256 then return .ok false
  let shared := storeDir cache p.sha256
  let fresh : Except String Bool ←
    if (← stamp shared) == some p.sha256 then pure (.ok false)
    else
      match ← archive cache p offline vendor with
      | .error e => pure (.error e)
      | .ok tar =>
        let parent := cache / "grail" / "packages"
        IO.FS.createDirAll parent
        let tmp := parent / s!"{p.sha256}.tmp{← IO.Process.getPID}"
        removePath tmp
        IO.FS.createDirAll tmp
        match ← untar tar tmp with
        | .error e => removePath tmp; pure (.error e)
        | .ok () =>
          -- (R20) the lock may carry a tree hash: check the unpacked bytes before the
          -- stamp, so a bad tree never enters the shared store
          if !p.tree.isEmpty then
            match ← treeHash tmp with
            | .error e => removePath tmp; return .error e
            | .ok h =>
              if h != p.tree then
                removePath tmp
                return .error s!"{p.name} {p.version}: unpacked tree has sha256 {h}, the lock says {p.tree}"
          IO.FS.writeFile (stampFile tmp) (p.sha256 ++ "\n")
          removePath shared
          IO.FS.rename tmp shared
          pure (.ok true)
  match fresh with
  | .error e => pure (.error e)
  | .ok fresh =>
    match ← linkTree shared dir with
    | .error e => pure (.error e)
    | .ok () => pure (.ok fresh)

/-! ## Reading the index -/

/-- A `source` is either an absolute URL/path or a path relative to the index it was read
from. Relative paths make a local mirror or a checked-out index self-contained (the test
fixture uses them); a published index should use absolute `https://` URLs. -/
def resolveSource (base : System.FilePath) (s : String) : String :=
  if s.isEmpty || s.contains "://" || s.startsWith "/" then s
  else (base / s).toString

def IxPackage.resolveSources (base : System.FilePath) (p : IxPackage) : IxPackage :=
  { p with versions := p.versions.map fun v => { v with source := resolveSource base v.source } }

/-- Read every `*.sexpr` of an index directory (`index/` under it, if there is one),
including one level of scoped subdirectories: `index/@org/name.sexpr` is the package
`@org/name` (R5 in `wiz-notes/prior-art/registries-build-systems.md`). The file name wins
over the `(package NAME …)` node inside, so the path and the resolver key cannot disagree;
a duplicate key within one registry is still an error. -/
def readIndexDir (dir : System.FilePath) : IO (Except String (Std.HashMap String IxPackage)) := do
  let root := dir
  let dir := if ← (dir / "index").isDir then dir / "index" else dir
  let m ← IO.mkRef ({} : Std.HashMap String IxPackage)
  let rec visit (dir : System.FilePath) (scope : String) (depth : Nat) : IO (Except String Unit) := do
    for e in ← dir.readDir do
      if e.fileName == "registry.sexpr" then continue
      if e.fileName.endsWith ".sexpr" then
        match Index.parse (← IO.FS.readFile e.path) with
        | .error err => return .error s!"{e.path}: {err}"
        | .ok ps =>
          let base := e.fileName.replace ".sexpr" ""
          let key := if scope.isEmpty then base else s!"{scope}/{base}"
          for p in ps do
            let name := if scope.isEmpty then p.name else key
            if scope.isEmpty && p.name != base then
              return .error s!"{e.path}: contains package {p.name}, expected {base} (one file, one package)"
            let cur ← m.get
            if cur.contains name then return .error s!"{e.path}: two entries for {name}"
            m.set (cur.insert name ({ IxPackage.resolveSources root p with name } : IxPackage))
      else if depth < 1 then
        if ← e.path.isDir then
          if let .error err ← visit e.path e.fileName (depth + 1) then return .error err
    return .ok ()
  match ← visit dir "" 0 with
  | .error e => pure (.error e)
  | .ok () => pure (.ok (← m.get))

/-- Where the index came from (for the lock) and the packages it lists. -/
structure Source where
  url : String
  commit : String := ""
  pkgs : Std.HashMap String IxPackage

/-- Load the index from a directory, a file, or a git URL (cloned to the cache). A
`URL#COMMIT` spec pins the index to one commit (the lock records it, so a project can
commit both `grail.lock` and the pin); a plain directory or file has no commit.
`previous` is the index commit the existing lock recorded: a URL index must move forward
from it (a rewritten history is refused unless `allowRewind`, R22). -/
def loadIndex (cache : System.FilePath) (spec : String) (offline : Bool)
    (previous : String := "") (allowRewind : Bool := false) :
    IO (Except String Source) := do
  let (spec, pin) := match spec.splitOn "#" with
    | [u, c] => (u, c)
    | _ => (spec, "")
  let p : System.FilePath := spec
  if ← p.isDir then
    -- a bare git repository is a URL-like index (clone it); an ordinary directory is
    -- read in place (index/*.sexpr or *.sexpr)
    let bare := (← (p / "HEAD").pathExists) && (← (p / "objects").isDir)
    unless bare do
      if pin != "" then
        return .error s!"--index-commit: {spec} is a directory index, not a git URL to pin"
      return (← readDir p spec)
  else
    if ← p.pathExists then
      if pin != "" then
        return .error s!"--index-commit: {spec} is a file index, not a git URL to pin"
      match Index.parse (← IO.FS.readFile p) with
      | .error e => return .error s!"{spec}: {e}"
      | .ok ps =>
        let base := p.parent.getD "."
        return .ok { url := spec
                     pkgs := ps.foldl (fun m p => m.insert p.name (IxPackage.resolveSources base p)) {} }
  -- a URL: a git index cloned into the cache, at the tip of its default branch (or at
  -- the pinned commit)
  let dir := cache / "grail" / "index"
  if offline then
    unless ← dir.pathExists do
      return .error s!"--offline: no index at {dir} (load {spec} once without --offline)"
    unless (← git #["remote", "get-url", "origin"] (some dir)).toOption == some spec do
      return .error s!"--offline: {dir} is a clone of another index (run without --offline to switch to {spec})"
    if pin != "" then
      if let .error e ← checkoutCached dir pin then return .error e
  else
    if let .error e ← ensureClone dir spec then return .error e
    if let .error e ← git #["fetch", "--quiet", "--tags", "--force", "origin"] (some dir) then
      return .error e
    if pin != "" then
      if let .error e ← checkoutPin dir pin then return .error e
    else
      if let .error e ← git #["reset", "--hard", "--quiet", "FETCH_HEAD"] (some dir) then
        return .error e
  let commit := (← git #["rev-parse", "HEAD"] (some dir)).toOption.getD ""
  if let .error e ← checkRewind dir previous commit allowRewind then return .error e
  return (← readDir dir spec).map fun m => { m with commit }
where
  /-- TUF's rollback protection over git's Merkle DAG: a lock's index commit must be an
  ancestor of the commit `grail update` would now read (fast-forward). A force-push that
  drops or rewrites a published entry is refused until the caller passes `--allow-rewind`
  (R22). -/
  checkRewind (dir : System.FilePath) (previous current : String) (allow : Bool) :
      IO (Except String Unit) := do
    if previous.isEmpty || previous == current || allow then return .ok ()
    match ← git #["merge-base", "--is-ancestor", previous, current] (some dir) with
    | .ok _ => pure (.ok ())
    | .error _ =>
      pure (.error s!"the index history was rewritten (locked at {previous}, now at {current}); pass --allow-rewind to accept")
  /-- Check out `pin` from the fetched clone, fetching that commit explicitly if it is
  not reachable from the default refs (a commit on a release tag is normally fetched by
  `--tags`). -/
  checkoutPin (dir : System.FilePath) (pin : String) : IO (Except String Unit) := do
    if (← git #["cat-file", "-e", s!"{pin}^\{commit}"] (some dir)).toOption.isSome then
      return (← git #["checkout", "--quiet", "--force", "--detach", pin] (some dir)).map fun _ => ()
    if let .error e ← git #["fetch", "--quiet", "origin", pin] (some dir) then return .error e
    return (← git #["checkout", "--quiet", "--force", "--detach", pin] (some dir)).map fun _ => ()
  readDir (dir : System.FilePath) (what : String) : IO (Except String Source) := do
    match ← readIndexDir dir with
    | .error e => pure (.error e)
    | .ok m =>
      if m.isEmpty then
        pure (.error s!"{what}: no packages in the index (expected index/*.sexpr)")
      else pure (.ok { url := what, pkgs := m })

/-! ## Update, fetch, and the build's roots -/

/-- (R37) Resolve the manifest's local overrides: `NAME` is taken from `PATH` (relative to
the package directory), and its tree hash is recorded in the lock. An override is
machine-local (it lives in the uncommitted `grail.local.wiz`), so the hash is an accident
detector for the checkout, not a registry guarantee. -/
def resolveOverrides (dir : System.FilePath) (pkg : Package) :
    IO (Except String (List LockOverride)) := do
  let mut out := []
  for (name, path) in pkg.overrides do
    let p := if (System.FilePath.mk path).isAbsolute then System.FilePath.mk path else dir / path
    unless ← p.pathExists do
      return .error s!"override {name}: {p} does not exist (from grail.local.wiz)"
    match ← treeHash p with
    | .error e => return .error s!"override {name}: {e}"
    | .ok h => out := out ++ [{ name, path, hash := h }]
  pure (.ok out)

/-- Resolve the manifest's registry requirements through the index (and its git
dependencies), and return the lock they give. Writes nothing. A `Package.override` in
`grail.local.wiz` takes its name out of the registry/git resolution: the lock records the
path and tree hash instead (v3, R37). -/
def resolveLock (cache : System.FilePath) (indexSpec : String) (offline : Bool)
    (readPkg : System.FilePath → IO (Except String Package)) (dir : System.FilePath)
    (pkg : Package) (allowRewind : Bool := false) : IO (Except String Lock) := do
  let overridden := pkg.overrides.map (·.1)
  let requires := pkg.requires.filter fun r => !overridden.contains r.name
  let deps := pkg.deps.filter fun d => !overridden.contains d.name
  let overrides ← match ← resolveOverrides dir pkg with
    | .error e => return .error e
    | .ok os => pure os
  -- the existing lock's index commit is the rollback baseline (R22); a directory or
  -- file index has no commit and is not checked
  let previous : String ←
    if ← (lockFile dir).pathExists then
      match Lock.parse (← IO.FS.readFile (lockFile dir)) with
      | .ok l => pure l.indexCommit
      | .error _ => pure ""
    else pure ""
  let src ←
    if requires.isEmpty then pure (.ok { url := "", pkgs := {} })
    else if indexSpec.isEmpty then
      pure (.error s!"{pkg.name} requires packages from the registry: give one with --index URL (or `Package.set \"index\" \"URL\"`)")
    else loadIndex cache indexSpec offline previous allowRewind
  match src with
  | .error e => pure (.error e)
  | .ok src =>
    match Resolve.resolve src.pkgs requires Wiz.version with
    | .error e => pure (.error e)
    | .ok resolved =>
      match ← resolveDeps readPkg dir deps [] offline with
      | .error e => pure (.error e)
      | .ok git =>
        let pkgs : List PkgLock := resolved.map fun r =>
          ({ name := r.name, version := Version.render r.version, source := r.source,
             sha256 := r.sha256, size := r.size, tree := r.tree, commands := r.commands,
             deps := r.deps } : PkgLock)
        pure (.ok { format := 3, toolchain := Wiz.version,
                    revision := (← Wiz.revision?).getD "",
                    indexUrl := src.url, indexCommit := src.commit, git := git,
                    pkgs := pkgs, overrides := overrides })

/-- 64 lowercase hex digits: the shape of a SHA-256 in the index and the lock. -/
def isSha256 (s : String) : Bool :=
  s.length == 64 && s.toList.all fun c =>
    ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')

/-- Is every requirement of the manifest pinned in `lock` (and satisfied), is every git
dependency pinned, and is the lock's registry graph complete? A lock holds the transitive
closure, so a `pkg` entry whose dependency is absent or not satisfied is a stale or
hand-edited lock. With `indexCommit` (or `Package.set "index-commit"`), the lock must
also have been resolved from that index commit. `strictOverride` is `--locked`: a lock
that records a machine-local override is refused rather than silently built from a path
(R37). -/
def checkLocked (lock : Lock) (pkg : Package) (indexCommit : String := "")
    (strictOverride : Bool := false) : Except String Unit := do
  let pin := if indexCommit.isEmpty then
    (pkg.settings.find? (·.1 == "index-commit")).map (·.2) |>.getD ""
  else indexCommit
  if pin != "" && !(lock.indexCommit.startsWith pin) then
    throw s!"grail.lock was resolved from index commit {lock.indexCommit}, but this package pins {pin}: run `grail update`"
  if strictOverride && (!lock.overrides.isEmpty || !pkg.overrides.isEmpty) then
    let os := if lock.overrides.isEmpty then
        " ".intercalate (pkg.overrides.map fun (n, p) => s!"{n} ({p})")
      else " ".intercalate (lock.overrides.map fun o => s!"{o.name} ({o.path})")
    throw s!"a machine-local override is in effect ({os}), but --locked refuses overrides: remove it from grail.local.wiz or run without --locked"
  let overridden := pkg.overrides.map (·.1)
  let isOverride (n : String) : Bool := overridden.contains n
  for r in pkg.requires do
    if isOverride r.name then continue
    match lock.pkgs.find? (·.name == r.name) with
    | none => throw s!"{r.name} is not in grail.lock: run `grail update`"
    | some p =>
      let req ← Requirement.parse r.req
      let v ← Version.parse p.version
      if !Requirement.satisfies req v then
        throw s!"grail.lock has {p.name} {p.version}, grail.wiz asks for {r.req}: run `grail update`"
  for d in pkg.deps do
    if isOverride d.name then continue
    if !lock.git.any (·.name == d.name) then
      throw s!"{d.name} is not in grail.lock: run `grail update`"
  -- (R37) an override is recorded in its own section, with the hash of the path
  for o in lock.overrides do
    if o.name.isEmpty then throw "grail.lock: an override has no name: run `grail update`"
    if o.path.isEmpty then throw s!"grail.lock: override {o.name} has no path: run `grail update`"
    if !isSha256 o.hash then
      throw s!"grail.lock: override {o.name}: tree hash is not 64 lowercase hex digits: run `grail update`"
  let mut seen : List String := []
  for p in lock.pkgs do
    if seen.contains p.name then
      throw s!"grail.lock lists {p.name} twice: run `grail update`"
    seen := p.name :: seen
    if lock.overrides.any (·.name == p.name) then
      throw s!"grail.lock lists {p.name} both as a package and as an override: run `grail update`"
    if !isSha256 p.sha256 then
      throw s!"grail.lock: {p.name} {p.version}: sha256 is not 64 lowercase hex digits: run `grail update`"
    if p.source.isEmpty then
      throw s!"grail.lock: {p.name} {p.version}: no source: run `grail update`"
    -- (R19/R20/R36) the v3 optional fields have the shape the format promises
    if !p.tree.isEmpty && !isSha256 p.tree then
      throw s!"grail.lock: {p.name} {p.version}: tree hash is not 64 lowercase hex digits: run `grail update`"
    if !p.commands.isEmpty && !isSha256 p.commands then
      throw s!"grail.lock: {p.name} {p.version}: command digest is not 64 lowercase hex digits: run `grail update`"
    let _ ← Version.parse p.version
    for d in p.deps do
      match lock.pkgs.find? (·.name == d.name) with
      | none =>
        if lock.overrides.any (·.name == d.name) then continue
        throw s!"grail.lock is incomplete: {p.name} depends on {d.name}, which is not in it: run `grail update`"
      | some q =>
        let req ← Requirement.parse d.req
        let v ← Version.parse q.version
        if !Requirement.satisfies req v then
          throw s!"grail.lock has {q.name} {q.version}, but {p.name} asks for {d.req}: run `grail update`"

/-- `grail fetch`: make every package of the lock present and verified. Returns the
lines to print. With `offline`, a missing archive or clone is an error (nothing is
downloaded). -/
def fetch (cache : System.FilePath) (dir : System.FilePath) (lock : Lock)
    (offline : Bool := false) (vendor : Option System.FilePath := none) :
    IO (Except String (List String)) := do
  let mut out := []
  let overridden := lock.overrides.map (·.name)
  for p in lock.pkgs do
    if overridden.contains p.name then continue
    match ← ensurePkg cache (dir / ".grail" / "packages") p offline vendor with
    | .error e => return .error e
    | .ok fresh =>
      out := out ++ [s!"{p.name} {p.version}\t{p.sha256}\t{if fresh then "fetched" else "up to date"}"]
  for g in lock.git do
    if overridden.contains g.name then continue
    let d := packageDir dir g.name
    if offline then
      if let .error e ← ensureCloneCached d g.url then return .error e
      if let .error e ← checkoutCached d g.commit then return .error e
    else
      if let .error e ← ensureClone d g.url then return .error e
      if let .error e ← checkout d g.commit then return .error e
    let content ← contentHash d
    if content != g.content then
      return .error s!"{d} differs from grail.lock (content {content}, locked {g.content}): edited? remove it, or `grail update`"
    out := out ++ [s!"{g.name}\t{g.commit}\t{content}"]
  -- (R37) an override is not fetched: check that the local path still has the locked tree
  for o in lock.overrides do
    let p := if (System.FilePath.mk o.path).isAbsolute then System.FilePath.mk o.path else dir / o.path
    unless ← p.pathExists do
      return .error s!"override {o.name}: {p} does not exist (grail.lock records it; run `grail update`)"
    match ← treeHash p with
    | .error e => return .error e
    | .ok h =>
      if h != o.hash then
        return .error s!"override {o.name}: {p} differs from grail.lock (tree {h}, locked {o.hash}): run `grail update`"
      out := out ++ [s!"{o.name}\toverride {o.path}\t{o.hash}"]
  pure (.ok out)

/-- `grail vendor [DIR]`: copy the lock's registry archives into `DIR` (default
`vendor/`) as content-addressed files (`<sha256>.tar.gz`) and write `DIR/index.sexpr`
(`name@version → file`). The lock is *not* rewritten: its `source` stays the published URL, so the same
lock works with and without the vendor directory, and two packages with the same bytes
share one file. `--offline` uses the archive cache (or an existing vendor file) only. -/
def vendor (cache : System.FilePath) (vendorDir : System.FilePath) (lock : Lock)
    (offline : Bool := false) : IO (Except String (List String)) := do
  IO.FS.createDirAll vendorDir
  let mut out := []
  let mut entries : List VendorEntry := []
  for p in lock.pkgs do
    let file : String := match entries.find? (·.sha256 == p.sha256) with
      | some e => e.file
      | none => s!"{p.sha256}{archiveExt p.source}"
    let dest := vendorDir / System.FilePath.mk file
    let upToDate ←
      if ← dest.pathExists then
        match ← sha256File dest with
        | .ok h => pure (h == p.sha256)
        | .error _ => pure false
      else pure false
    if upToDate then
      out := out ++ [s!"{p.name} {p.version}\t{p.sha256}\tup to date"]
    else
      match ← archive cache p offline none with
      | .error e => return .error e
      | .ok src =>
        let tmp := vendorDir / s!"{file}.tmp{← IO.Process.getPID}"
        match ← copyBin src tmp with
        | .error e => return .error e
        | .ok () =>
          removePath dest
          IO.FS.rename tmp dest
          out := out ++ [s!"{p.name} {p.version}\t{p.sha256}\tvendored"]
    entries := entries ++ [{ name := p.name, version := p.version, sha256 := p.sha256, file }]
  Cache.writeAtomic (vendorDir / "index.sexpr") (VendorIndex.render { entries })
  pure (.ok out)

/-! ## The shared cache (`grail cache`) -/

def cacheRoot (cache : System.FilePath) : System.FilePath := cache / "grail"
def downloadsDir (cache : System.FilePath) : System.FilePath := cacheRoot cache / "downloads"
def storeRoot (cache : System.FilePath) : System.FilePath := cacheRoot cache / "packages"
def indexCloneDir (cache : System.FilePath) : System.FilePath := cacheRoot cache / "index"

/-- `grail cache path`: where the shared cache keeps each kind of thing. -/
def cachePathLines (cache : System.FilePath) : List String :=
  [s!"downloads\t{downloadsDir cache}",
   s!"packages\t{storeRoot cache}",
   s!"index\t{indexCloneDir cache}"]

/-- `grail cache list`: every archive (by hash) and every unpacked package tree. -/
def cacheList (cache : System.FilePath) : IO (List String) := do
  let mut out := []
  let dl := downloadsDir cache
  if ← dl.isDir then
    for e in ← dl.readDir do
      if e.fileName.contains ".tmp" then continue
      let md ← e.path.metadata
      out := out ++ [s!"archive\t{e.fileName}\t{md.byteSize}"]
  let pk := storeRoot cache
  if ← pk.isDir then
    for e in ← pk.readDir do
      if e.fileName.contains ".tmp" then continue
      if ← e.path.isDir then
        let st ← stamp e.path
        out := out ++ [s!"package\t{e.fileName}\t{st.getD "no stamp"}"]
  pure ((out.toArray.qsort (· < ·)).toList)

/-- `grail cache verify`: re-hash every archive and check every unpacked tree's stamp
against its content address. Errors are reported, not repaired: the next fetch repairs
an archive, and a missing or wrong stamp just means the tree will be unpacked again. -/
def cacheVerify (cache : System.FilePath) : IO (List String × Bool) := do
  let mut errs : List String := []
  let dl := downloadsDir cache
  if ← dl.isDir then
    for e in ← dl.readDir do
      if e.fileName.contains ".tmp" then continue
      if !isSha256 e.fileName then
        errs := errs ++ [s!"archive {e.path}: the name is not a sha256"]
      else
        match ← sha256File e.path with
        | .ok h => if h != e.fileName then
            errs := errs ++ [s!"archive {e.path}: sha256 {h}, expected {e.fileName}"]
        | .error err => errs := errs ++ [s!"archive {e.path}: {err}"]
  let pk := storeRoot cache
  if ← pk.isDir then
    for e in ← pk.readDir do
      if e.fileName.contains ".tmp" then continue
      if ← e.path.isDir then
        if !isSha256 e.fileName then
          errs := errs ++ [s!"package {e.path}: the name is not a sha256"]
        else
          match ← stamp e.path with
          | some s => if s != e.fileName then
              errs := errs ++ [s!"package {e.path}: stamp {s}, expected {e.fileName}"]
          | none => errs := errs ++ [s!"package {e.path}: no .grail-pkg stamp"]
  pure (errs, errs.isEmpty)

/-- Build the index entry for one release from its manifest and archive: the checks a
publisher (and the index's reviewer) can make locally. The archive layout must be the
fixed one: one top-level `NAME-VERSION/` with the package's `grail.wiz` in it. `modules`
are the package's module names (from `archiveModules`), recorded so the resolver can
refuse two packages that would collide at `import` (R32). `size`, `tree` and `commands`
are the v3 integrity fields (R19/R20/R36). -/
def publishEntry (pkg : Package) (source sha : String) (modules : List String := [])
    (size : Option Nat := none) (tree : String := "") (commands : String := "") :
    Except String IxVersion := do
  if !validName pkg.name then throw s!"package name {pkg.name}: expected [a-z][a-z0-9-]* (at most 64)"
  if pkg.version.isEmpty then throw "grail.wiz has no Package.version: a published package needs one"
  let v ← Version.parse pkg.version
  if Version.render v != pkg.version then
    throw s!"Package.version {pkg.version}: expected a normalised version like 1.2.3"
  if source.isEmpty then throw "no --source URL for the archive"
  if !isSha256 sha then throw s!"sha256 {sha}: expected 64 lowercase hex digits"
  if !tree.isEmpty && !isSha256 tree then throw s!"tree {tree}: expected 64 lowercase hex digits"
  if !commands.isEmpty && !isSha256 commands then
    throw s!"command digest {commands}: expected 64 lowercase hex digits"
  if !pkg.toolchain.isEmpty then
    if let .error e := Requirement.parse pkg.toolchain then
      throw s!"Package.toolchain {pkg.toolchain}: {e}"
  for r in pkg.requires do
    if let .error e := Requirement.parse r.req then
      throw s!"Package.require {r.name} {r.req}: {e}"
  pure { version := v, source, sha256 := sha, toolchain := pkg.toolchain, modules,
         size, tree, commands, deps := pkg.requires }

/-- The members of a `.tar.gz` (`tar -tzf`), one path per line. -/
def archiveMembers (archive : System.FilePath) : IO (Except String (List String)) := do
  try
    let o ← IO.Process.output { cmd := "tar", args := #["-tzf", archive.toString] }
    if o.exitCode != 0 then
      return .error s!"tar -tzf {archive}: {o.stderr.trimAscii}"
    pure (.ok (o.stdout.splitOn "\n" |>.filter (!·.isEmpty)))
  catch e => pure (.error s!"tar: {e}")

/-- The module names an archive provides, from the package's `lib` roots: a member
`NAME-V/src/Greet/Hello.wiz` under the root `src` is the module `Greet.Hello`. This is
what `grail publish` records (`(modules …)`), and what makes the resolve-time module
check possible (R32). -/
def archiveModules (archive : System.FilePath) (name version : String) (roots : List String) :
    IO (Except String (List String)) := do
  match ← archiveMembers archive with
  | .error e => pure (.error e)
  | .ok members =>
    let top := s!"{name}-{version}/"
    let mut mods : List String := []
    for root in roots do
      let root := if root.endsWith "/" then (root.drop 0).dropEnd 1 |>.toString else root
      let pre := s!"{top}{root}/"
      for m in members do
        if m.startsWith pre && m.endsWith ".wiz" then
          let rel := (m.drop pre.length).toString
          let mod := ((rel.drop 0).dropEnd 4).toString.replace "/" "."
          if !mod.isEmpty && !mods.contains mod then mods := mods ++ [mod]
    pure (.ok (mods.mergeSort (· ≤ ·)))

/-- Check that `archive` is a tar.gz of the fixed layout (`NAME-VERSION/` at the top,
with a `grail.wiz` in it). -/
def checkArchiveLayout (archive : System.FilePath) (name version : String) : IO (Except String Unit) := do
  match ← archiveMembers archive with
  | .error e => pure (.error e)
  | .ok members =>
    let top := s!"{name}-{version}"
    if members.isEmpty then return .error s!"{archive}: empty archive"
    if let some bad := members.find? (fun m => !(m == top || m.startsWith (top ++ "/"))) then
      return .error s!"{archive}: member {bad} is not under {top}/ (the archive layout is one top directory)"
    unless members.contains s!"{top}/grail.wiz" do
      return .error s!"{archive}: no {top}/grail.wiz (wrong version in the archive?)"
    pure (.ok ())

/-- `grail publish ARCHIVE --source URL`: hash the release archive and print the index
entry, after checking the manifest and the archive layout. Printing (not writing) is the
MVP: publishing is a reviewed pull request to the index repository. -/
def publish (archive : Option System.FilePath) (source : String) (pkg : Package) :
    IO (Except String String) := do
  let some ar := archive | return .error "usage: grail publish ARCHIVE --source URL"
  unless ← ar.pathExists do return .error s!"{ar}: no such archive"
  if let .error e ← checkArchiveLayout ar pkg.name pkg.version then return .error e
  let roots := pkg.targets.filterMap fun | .lib _ r => some r | _ => none
  let modules ← match ← archiveModules ar pkg.name pkg.version roots with
    | .error e => return .error e
    | .ok ms => pure ms
  match ← sha256File ar with
  | .error e => pure (.error e)
  | .ok sha =>
    let size := some (← ar.metadata).byteSize.toNat
    let tree ← match ← unpackTreeHash ar with
      | .error e => return .error e
      | .ok h => pure h
    let commands := commandDigest pkg.targets
    match publishEntry pkg source sha modules size tree commands with
    | .error e => pure (.error e)
    | .ok v => pure (.ok (Index.renderVersion v))

/-- Before a build: check the lock out (registry packages unpacked and verified, git
dependencies at their commits) and return the module roots they give (their `lib`
targets'). Notes (a `REV` changed since the lock) go to `note`. With `offline`, a
missing archive or clone is an error instead of a download. -/
def lockedRoots (cache : System.FilePath) (readPkg : System.FilePath → IO (Except String Package))
    (dir : System.FilePath) (pkg : Package) (note : String → IO Unit) (offline : Bool := false)
    (vendor : Option System.FilePath := none) :
    IO (Except String (List System.FilePath)) := do
  let lock := lockFile dir
  if !(← lock.pathExists) then
    return if pkg.deps.isEmpty && pkg.requires.isEmpty && pkg.overrides.isEmpty then .ok []
      else .error s!"no {lock}: run `grail update`"
  let l ← match Lock.parse (← IO.FS.readFile lock) with
    | .ok l => pure l
    | .error e => return .error e
  if let .error e := checkLocked l pkg then
    return .error e
  -- (R14) the lock remembers the toolchain it was solved for; a different one is a note,
  -- not an error (a newer grail may still build an old lock)
  if !l.toolchain.isEmpty && l.toolchain != Wiz.version then
    note s!"note: {lock} was resolved by grail {l.toolchain}{if l.revision.isEmpty then "" else s!" ({l.revision})"}; this is {Wiz.version}\n"
  let overridden := l.overrides.map (·.name)
  for d in pkg.deps do
    if overridden.contains d.name then continue
    match l.git.find? (·.name == d.name) with
    | none => return .error s!"{d.name} is not in {lock}: run `grail update`"
    | some g =>
      if g.url != d.url || g.rev != d.rev then
        note s!"note: {lock} has {d.name} at {g.commit} ({g.url} {g.rev}); grail.wiz asks for {d.url} {d.rev}: `grail update` moves it\n"
  let mut roots := #[]
  for p in l.pkgs do
    if overridden.contains p.name then continue
    match ← ensurePkg cache (dir / ".grail" / "packages") p offline vendor with
    | .error e => return .error e
    | .ok _ => pure ()
    let d := dir / ".grail" / "packages" / p.name
    if ← (d / "grail.wiz").pathExists then
      match ← readPkg d with
      | .error e => return .error s!"{p.name}: {e}"
      | .ok dp => roots := roots ++ (libRootsOf d dp.targets).toArray
  for g in l.git do
    if overridden.contains g.name then continue
    let d := packageDir dir g.name
    if offline then
      if let .error e ← ensureCloneCached d g.url then return .error e
      if let .error e ← checkoutCached d g.commit then return .error e
    else
      if let .error e ← ensureClone d g.url then return .error e
      if let .error e ← checkout d g.commit then return .error e
    let content ← contentHash d
    if content != g.content then
      return .error s!"{d} differs from {lock} (content {content}, locked {g.content}): edited? remove it, or `grail update`"
    if ← (d / "grail.wiz").pathExists then
      match ← readPkg d with
      | .error e => return .error s!"{g.name}: {e}"
      | .ok dp => roots := roots ++ (libRootsOf d dp.targets).toArray
  -- (R37) machine-local overrides: the lock and grail.local.wiz must agree, and the path
  -- must still have the locked tree; a plain build says which path it used
  for (name, path) in pkg.overrides do
    match l.overrides.find? (·.name == name) with
    | none => return .error s!"{lock} does not record override {name}: run `grail update`"
    | some o =>
      if o.path != path then
        return .error s!"{lock} records override {name} from {o.path}, grail.local.wiz says {path}: run `grail update`"
      let p := if (System.FilePath.mk path).isAbsolute then System.FilePath.mk path else dir / path
      unless ← p.pathExists do
        return .error s!"override {name}: {p} does not exist (grail.lock records it; run `grail update`)"
      match ← treeHash p with
      | .error e => return .error e
      | .ok h =>
        if h != o.hash then
          return .error s!"override {name}: {p} differs from {lock} (tree {h}, locked {o.hash}): run `grail update`"
      note s!"using override {name} from {path}\n"
      if ← (p / "grail.wiz").pathExists then
        match ← readPkg p with
        | .error e => return .error s!"override {name}: {e}"
        | .ok dp => roots := roots ++ (libRootsOf p dp.targets).toArray
  for o in l.overrides do
    unless pkg.overrides.any (·.1 == o.name) do
      return .error s!"{lock} records override {o.name} from {o.path}, but grail.local.wiz has none: run `grail update`"
  pure (.ok roots.toList)

end Registry
end Grail
