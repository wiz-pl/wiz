import Grail.Deps
import Grail.Index
import Wiz.Version

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

/-- One registry package, pinned: name, version, archive, hash, and its dependencies -/
structure PkgLock where
  name : String
  version : String
  source : String
  sha256 : String
  deps : List Req := []
  deriving Repr, Inhabited, BEq

/-- `grail.lock`: registry packages and (23h) git dependencies -/
structure Lock where
  /-- (23m) where the versions came from, and the commit that was read -/
  indexUrl : String := ""
  indexCommit : String := ""
  git : List Locked := []
  pkgs : List PkgLock := []
  deriving Repr, Inhabited

namespace Lock

def render (l : Lock) : String :=
  let idx := if l.indexUrl.isEmpty then "" else
    "\n  " ++ (node "index" [str l.indexUrl, str l.indexCommit]).render
  let git := if l.git.isEmpty then "" else
    "\n  " ++ "\n  ".intercalate (l.git.map fun d =>
      (node "dep" [str d.name, str d.url, str d.rev, str d.commit, str d.content]).render)
  let pkgs := if l.pkgs.isEmpty then "" else
    "\n  " ++ "\n  ".intercalate (l.pkgs.map fun p =>
      (node "pkg" [str p.name, str p.version, str p.source, str p.sha256,
        node "deps" (p.deps.map fun d => node "dep" [str d.name, str d.req])]).render)
  "(lock" ++ idx ++ git ++ pkgs ++ ")\n"

/-- Parse `grail.lock`, v1 (`(lock (dep …) …)`) or v2 (with `(pkg …)` and `(index …)`). -/
def parse (s : String) : Except String Lock := do
  let some (.l xs) := Sx.parse s | throw "grail.lock: expected (lock …)"
  match xs.toList with
  | .a "lock" :: entries =>
    let mut l : Lock := {}
    for e in entries do
      let .l ys := e | throw s!"grail.lock: unexpected entry {e.render}"
      match ys.toList with
      | .a "dep" :: .a name :: .a url :: .a rev :: .a commit :: .a content :: [] =>
        l := { l with git := l.git ++ [{ name, url, rev, commit, content }] }
      | .a "index" :: .a url :: .a commit :: [] =>
        l := { l with indexUrl := url, indexCommit := commit }
      | .a "pkg" :: .a name :: .a version :: .a source :: .a sha256 :: rest =>
        let deps ← match rest with
          | [] => pure []
          | [.l ds] => ds.toList.drop 1 |>.mapM fun
            | .l ys =>
              match ys.toList with
              | .a "dep" :: .a n :: .a r :: [] => pure { name := n, req := r : Req }
              | _ => throw "grail.lock: bad dependency"
            | x => throw s!"grail.lock: bad dependency {x.render}"
          | _ => throw s!"grail.lock: bad package {e.render}"
        l := { l with pkgs := l.pkgs ++ [{ name, version, source, sha256, deps }] }
      | _ => throw s!"grail.lock: unexpected entry {e.render}"
    pure l
  | _ => throw "grail.lock: expected (lock …)"

end Lock

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

/-- The cached archive for `sha256`, downloading and verifying it if needed. -/
def archive (cache : System.FilePath) (p : PkgLock) : IO (Except String System.FilePath) := do
  let dir := cache / "grail" / "downloads"
  IO.FS.createDirAll dir
  let f := dir / p.sha256
  if ← f.pathExists then
    match ← sha256File f with
    | .ok h => if h == p.sha256 then return .ok f
    | .error _ => pure ()
    -- a corrupt or wrongly named archive: fetch it again
    IO.FS.removeFile f
  let tmp := dir / s!"{p.sha256}.tmp{← IO.Process.getPID}"
  match ← download p.source tmp with
  | .error e => IO.FS.removeFile tmp; return .error s!"{p.name} {p.version}: {e}"
  | .ok () =>
    match ← sha256File tmp with
    | .error e => IO.FS.removeFile tmp; return .error s!"{p.name} {p.version}: {e}"
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

/-- Make `.grail/packages/NAME` the unpacked `p`; `false` when it already was. -/
def ensurePkg (cache : System.FilePath) (packagesDir : System.FilePath) (p : PkgLock) :
    IO (Except String Bool) := do
  let dir := packagesDir / p.name
  if (← stamp dir) == some p.sha256 then return .ok false
  match ← archive cache p with
  | .error e => pure (.error e)
  | .ok tar =>
    let tmp := packagesDir / s!"{p.name}.tmp{← IO.Process.getPID}"
    if ← tmp.pathExists then IO.FS.removeDirAll tmp
    IO.FS.createDirAll tmp
    match ← untar tar tmp with
    | .error e => IO.FS.removeDirAll tmp; return .error e
    | .ok () =>
      IO.FS.writeFile (stampFile tmp) (p.sha256 ++ "\n")
      if ← dir.pathExists then IO.FS.removeDirAll dir
      IO.FS.rename tmp dir
      pure (.ok true)

/-! ## Reading the index -/

/-- Read every `*.sexpr` of an index directory (`index/` under it, if there is one). -/
def readIndexDir (dir : System.FilePath) : IO (Except String (Std.HashMap String IxPackage)) := do
  let dir := if ← (dir / "index").isDir then dir / "index" else dir
  let mut m : Std.HashMap String IxPackage := {}
  for e in ← dir.readDir do
    if !e.fileName.endsWith ".sexpr" then continue
    match Index.parse (← IO.FS.readFile e.path) with
    | .error err => return .error s!"{e.path}: {err}"
    | .ok ps =>
      for p in ps do
        if m.contains p.name then return .error s!"{e.path}: two entries for {p.name}"
        m := m.insert p.name p
  pure (.ok m)

/-- Where the index came from (for the lock) and the packages it lists. -/
structure Source where
  url : String
  commit : String := ""
  pkgs : Std.HashMap String IxPackage

/-- Load the index from a directory, a file, or a git URL (cloned to the cache). -/
def loadIndex (cache : System.FilePath) (spec : String) (offline : Bool) :
    IO (Except String Source) := do
  let p : System.FilePath := spec
  if ← p.isDir then
    return (← readDir p spec)
  if ← p.pathExists then
    match Index.parse (← IO.FS.readFile p) with
    | .error e => return .error s!"{spec}: {e}"
    | .ok ps => pure (.ok { url := spec, pkgs := ps.foldl (fun m p => m.insert p.name p) {} })
  else
    -- a URL: a git index cloned into the cache, at the tip of its default branch
    let dir := cache / "grail" / "index"
    if offline then
      unless ← dir.pathExists do
        return .error s!"--offline: no index at {dir} (load {spec} once without --offline)"
    else
      if let .error e ← ensureClone dir spec then return .error e
      if let .error e ← git #["fetch", "--quiet", "--tags", "--force", "origin"] (some dir) then
        return .error e
      if let .error e ← git #["reset", "--hard", "--quiet", "FETCH_HEAD"] (some dir) then
        return .error e
    let commit := (← git #["rev-parse", "HEAD"] (some dir)).toOption.getD ""
    return (← readDir dir spec).map fun m => { m with commit }
where
  readDir (dir : System.FilePath) (what : String) : IO (Except String Source) := do
    match ← readIndexDir dir with
    | .error e => pure (.error e)
    | .ok m =>
      if m.isEmpty then
        pure (.error s!"{what}: no packages in the index (expected index/*.sexpr)")
      else pure (.ok { url := what, pkgs := m })

/-! ## Update, fetch, and the build's roots -/

/-- Resolve the manifest's registry requirements through the index (and its git
dependencies), and return the lock they give. Writes nothing. -/
def resolveLock (cache : System.FilePath) (indexSpec : String) (offline : Bool)
    (readPkg : System.FilePath → IO (Except String Package)) (dir : System.FilePath)
    (pkg : Package) : IO (Except String Lock) := do
  let src ←
    if pkg.requires.isEmpty then pure (.ok { url := "", pkgs := {} })
    else if indexSpec.isEmpty then
      pure (.error s!"{pkg.name} requires packages from the registry: give one with --index URL (or `Package.set \"index\" \"URL\"`)")
    else loadIndex cache indexSpec offline
  match src with
  | .error e => pure (.error e)
  | .ok src =>
    match Resolve.resolve src.pkgs pkg.requires Wiz.version with
    | .error e => pure (.error e)
    | .ok resolved =>
      match ← resolveDeps readPkg dir pkg.deps [] with
      | .error e => pure (.error e)
      | .ok git =>
        let pkgs : List PkgLock := resolved.map fun r =>
          ({ name := r.name, version := Version.render r.version, source := r.source,
             sha256 := r.sha256, deps := r.deps } : PkgLock)
        pure (.ok { indexUrl := src.url, indexCommit := src.commit, git := git, pkgs := pkgs })

/-- Is every requirement of the manifest pinned in `lock`, and every git dependency? -/
def checkLocked (lock : Lock) (pkg : Package) : Except String Unit := do
  for r in pkg.requires do
    match lock.pkgs.find? (·.name == r.name) with
    | none => throw s!"{r.name} is not in grail.lock: run `grail update`"
    | some p =>
      let req ← Requirement.parse r.req
      let v ← Version.parse p.version
      if !Requirement.satisfies req v then
        throw s!"grail.lock has {p.name} {p.version}, grail.wiz asks for {r.req}: run `grail update`"
  for d in pkg.deps do
    if !lock.git.any (·.name == d.name) then
      throw s!"{d.name} is not in grail.lock: run `grail update`"

/-- `grail fetch`: make every package of the lock present and verified. Returns the
lines to print. -/
def fetch (cache : System.FilePath) (dir : System.FilePath) (lock : Lock) :
    IO (Except String (List String)) := do
  let mut out := []
  for p in lock.pkgs do
    match ← ensurePkg cache (dir / ".grail" / "packages") p with
    | .error e => return .error e
    | .ok fresh =>
      out := out ++ [s!"{p.name} {p.version}\t{p.sha256}\t{if fresh then "fetched" else "up to date"}"]
  for g in lock.git do
    let d := packageDir dir g.name
    if let .error e ← ensureClone d g.url then return .error e
    if let .error e ← checkout d g.commit then return .error e
    let content ← contentHash d
    if content != g.content then
      return .error s!"{d} differs from grail.lock (content {content}, locked {g.content}): edited? remove it, or `grail update`"
    out := out ++ [s!"{g.name}\t{g.commit}\t{content}"]
  pure (.ok out)

/-- Before a build: check the lock out (registry packages unpacked and verified, git
dependencies at their commits) and return the module roots they give (their `lib`
targets'). Notes (a `REV` changed since the lock) go to `note`. -/
def lockedRoots (cache : System.FilePath) (readPkg : System.FilePath → IO (Except String Package))
    (dir : System.FilePath) (pkg : Package) (note : String → IO Unit) :
    IO (Except String (List System.FilePath)) := do
  let lock := lockFile dir
  if !(← lock.pathExists) then
    return if pkg.deps.isEmpty && pkg.requires.isEmpty then .ok []
      else .error s!"no {lock}: run `grail update`"
  let l ← match Lock.parse (← IO.FS.readFile lock) with
    | .ok l => pure l
    | .error e => return .error e
  if let .error e := checkLocked l pkg then
    return .error e
  for d in pkg.deps do
    match l.git.find? (·.name == d.name) with
    | none => return .error s!"{d.name} is not in {lock}: run `grail update`"
    | some g =>
      if g.url != d.url || g.rev != d.rev then
        note s!"note: {lock} has {d.name} at {g.commit} ({g.url} {g.rev}); grail.wiz asks for {d.url} {d.rev}: `grail update` moves it\n"
  let mut roots := #[]
  for p in l.pkgs do
    match ← ensurePkg cache (dir / ".grail" / "packages") p with
    | .error e => return .error e
    | .ok _ => pure ()
    let d := dir / ".grail" / "packages" / p.name
    if ← (d / "grail.wiz").pathExists then
      match ← readPkg d with
      | .error e => return .error s!"{p.name}: {e}"
      | .ok dp => roots := roots ++ (libRootsOf d dp.targets).toArray
  for g in l.git do
    let d := packageDir dir g.name
    if let .error e ← ensureClone d g.url then return .error e
    if let .error e ← checkout d g.commit then return .error e
    let content ← contentHash d
    if content != g.content then
      return .error s!"{d} differs from {lock} (content {content}, locked {g.content}): edited? remove it, or `grail update`"
    if ← (d / "grail.wiz").pathExists then
      match ← readPkg d with
      | .error e => return .error s!"{g.name}: {e}"
      | .ok dp => roots := roots ++ (libRootsOf d dp.targets).toArray
  pure (.ok roots.toList)

end Registry
end Grail
