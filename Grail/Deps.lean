import Grail.Build
import Grail.Signature

/-!
# Git dependencies and the lock file (stage 23h)

`Package.dep NAME URL REV` in `grail.wiz` asks for the package at `URL` (anything
`git clone` takes: a path, a `file://`, an `https://` URL), at `REV` (a tag, a branch or a
commit). `grail update` resolves every dependency (and theirs, read from their own
`grail.wiz`) to a commit, fetches it to `.grail/packages/NAME`, and writes `grail.lock`:

    (lock
      (dep "NAME" "URL" "REV" "COMMIT" "CONTENT"))

where `CONTENT` hashes the checked-out files. The lock is committed; builds use it only:
they check each dependency out at its locked commit (fetching it if needed), refuse one
whose files don't match `CONTENT`, and leave a changed `REV` alone until `grail update`
(with a note). The roots of a dependency's `lib` targets become module roots of the
package. Module keys hash module texts, so a dependency needs nothing extra in them.

Two different commits of one dependency name are refused.
-/

namespace Grail
open Wiz Cache

structure Locked where
  name : String
  url : String
  rev : String
  commit : String
  content : String
  deriving Repr, BEq, Inhabited

/-- (23m, v2/v3) One pinned registry package: name, version, archive, hash, and its
dependencies. v3 adds the archive's size (`(size N)`), the SHA-256 of the unpacked tree
(`(tree …)`, R20) and a digest of the package's declared commands (`(commands …)`, R36);
all three are optional, so a v2 entry parses unchanged. -/
structure PkgLock where
  name : String
  version : String
  source : String
  sha256 : String
  size : Option Nat := none
  tree : String := ""
  commands : String := ""
  deps : List Req := []
  deriving Repr, Inhabited, BEq

/-- (v3, R37) A machine-local override recorded in the lock: `NAME` was taken from `PATH`,
whose tree hash is `hash`. A build prints one line; `--locked` refuses it. -/
structure LockOverride where
  name : String
  path : String
  hash : String
  deriving Repr, Inhabited, BEq

/-- `grail.lock`: registry packages, (23h) git dependencies, and (v3) the toolchain and
local overrides. `format` is 1 for a git-only lock, 2 for a registry lock without the
header, and 3 for a written-by-v3 lock (`(version 3)`). -/
structure Lock where
  format : Nat := 1
  /-- (R14) the toolchain that resolved the lock (`Wiz.version`) -/
  toolchain : String := ""
  /-- (R14) the release commit, when the toolchain knows it (`Wiz.revision?`) -/
  revision : String := ""
  /-- (23m) where the versions came from, and the commit that was read -/
  indexUrl : String := ""
  indexCommit : String := ""
  /-- (23m, Stage 1) the verified index signature; a later update must match it -/
  indexSignature : Option Signature := none
  git : List Locked := []
  pkgs : List PkgLock := []
  overrides : List LockOverride := []
  deriving Repr, Inhabited

namespace Lock

/-- Sorted, one entry per line, so a resolution that changes nothing writes nothing and a
change reads as a one-line diff (R15). Dependencies are a flat list of `"NAME REQ"`
strings, never nested (v3). -/
def renderPkg (p : PkgLock) : String :=
  let deps := (p.deps.toArray.qsort fun a b =>
    a.name < b.name || (a.name == b.name && a.req < b.req)).toList
  let fields : List Sx :=
    [str p.name, str p.version, str p.source, str p.sha256]
      ++ (match p.size with | some n => [node "size" [.a (toString n)]] | none => [])
      ++ (if p.tree.isEmpty then [] else [node "tree" [str p.tree]])
      ++ (if p.commands.isEmpty then [] else [node "commands" [str p.commands]])
      ++ [node "deps" (deps.map fun d => str s!"{d.name} {d.req}")]
  (node "pkg" fields).render

def render (l : Lock) : String :=
  let version := if l.format >= 3 then "\n  " ++ (node "version" [.a (toString l.format)]).render else ""
  let toolchain := if l.toolchain.isEmpty then "" else
    "\n  " ++ (node "toolchain"
      ([str l.toolchain] ++ (if l.revision.isEmpty then [] else [str l.revision]))).render
  let idx := if l.indexUrl.isEmpty then "" else
    "\n  " ++ (node "index" [str l.indexUrl, str l.indexCommit]).render
  let sig := match l.indexSignature with
    | none => ""
    | some s => "\n  " ++ (Signature.node s).render
  let git := if l.git.isEmpty then "" else
    "\n  " ++ "\n  ".intercalate ((l.git.toArray.qsort fun a b => a.name < b.name).toList.map fun d =>
      (node "dep" [str d.name, str d.url, str d.rev, str d.commit, str d.content]).render)
  let pkgs := if l.pkgs.isEmpty then "" else
    "\n  " ++ "\n  ".intercalate ((l.pkgs.toArray.qsort fun a b => a.name < b.name).toList.map renderPkg)
  let overrides := if l.overrides.isEmpty then "" else
    "\n  " ++ "\n  ".intercalate ((l.overrides.toArray.qsort fun a b => a.name < b.name).toList.map fun o =>
      (node "override" [str o.name, str o.path, str o.hash]).render)
  "(lock" ++ version ++ toolchain ++ idx ++ sig ++ git ++ pkgs ++ overrides ++ ")\n"

/-- Decode the body of a `(deps …)`: v3 writes flat `"NAME REQ"` strings; v2 wrote
`(dep "NAME" "REQ")` nodes, which stay accepted. -/
def parseDeps (ds : List Sx) : Except String (List Req) := do
  ds.mapM fun d =>
    match d with
    | .a s =>
      match s.splitOn " " with
      | [] => throw s!"grail.lock: bad dependency {d.render}"
      | name :: rest => pure { name, req := " ".intercalate rest }
    | .l ys =>
      match ys.toList with
      | [.a "dep", .a n, .a r] => pure { name := n, req := r }
      | _ => throw s!"grail.lock: bad dependency {d.render}"

/-- Parse `grail.lock`: v1 (`(lock (dep …) …)`), v2 (`(index …)`, `(pkg …)` entries and
nested `(deps (dep …) …)`), or v3 (`(version 3)`, `(toolchain …)`, flat `(deps "…")`,
`(override …)`). A newer `(version N)` is refused with a clear message: a lock is a local
trust anchor, so it fails closed rather than being partially understood. -/
def parse (s : String) : Except String Lock := do
  let some (.l xs) := Sx.parse s | throw "grail.lock: expected (lock …)"
  match xs.toList with
  | .a "lock" :: entries =>
    let mut l : Lock := {}
    let mut sawVersion := false
    for e in entries do
      let .l ys := e | throw s!"grail.lock: unexpected entry {e.render}"
      match ys.toList with
      | [.a "version", .a n] =>
        let some k := n.toNat? | throw s!"grail.lock: bad version {n}"
        if k > 3 then throw s!"grail.lock: format {k} is newer than this grail (3); upgrade grail"
        sawVersion := true
        l := { l with format := k }
      | [.a "toolchain", .a v] => l := { l with toolchain := v }
      | [.a "toolchain", .a v, .a r] => l := { l with toolchain := v, revision := r }
      | [.a "dep", .a name, .a url, .a rev, .a commit, .a content] =>
        l := { l with git := l.git ++ [{ name, url, rev, commit, content }] }
      | [.a "index", .a url, .a commit] =>
        l := { l with indexUrl := url, indexCommit := commit }
      | .a "index-signature" :: _ =>
        l := { l with indexSignature := some (← Signature.parse e) }
      | [.a "override", .a name, .a path, .a hash] =>
        l := { l with overrides := l.overrides ++ [{ name, path, hash }] }
      | .a "pkg" :: .a name :: .a version :: .a source :: .a sha256 :: rest =>
        let mut p : PkgLock := { name, version, source, sha256 }
        for f in rest do
          match f with
          | .l #[.a "size", .a n] =>
            let some k := n.toNat? | throw s!"grail.lock: {name}: bad size {n}"
            p := { p with size := some k }
          | .l #[.a "tree", .a h] => p := { p with tree := h }
          | .l #[.a "commands", .a h] => p := { p with commands := h }
          | .l ys =>
            match ys.toList with
            | .a "deps" :: ds => p := { p with deps := ← parseDeps ds }
            | _ => throw s!"grail.lock: bad package {e.render}"
          | _ => throw s!"grail.lock: bad package {e.render}"
        l := { l with pkgs := l.pkgs ++ [p] }
      | _ => throw s!"grail.lock: unexpected entry {e.render}"
    -- (R13) a file without `(version …)` is v1 or v2 by inspection
    if !sawVersion then
      let v2 := !l.indexUrl.isEmpty || !l.pkgs.isEmpty || !l.overrides.isEmpty
      l := { l with format := if v2 then 2 else 1 }
    pure l
  | _ => throw "grail.lock: expected (lock …)"

end Lock

/-- Render a git-only lock as v3 (`(version 3)` and its `dep` entries). -/
def renderLock (ls : List Locked) : String :=
  Lock.render { format := 3, toolchain := Wiz.version, git := ls }

/-- Parse a lock and return its git dependencies (v1/v2/v3 all parse). -/
def parseLock (s : String) : Except String (List Locked) := do
  pure (← Lock.parse s).git

def lockFile (dir : System.FilePath) : System.FilePath := dir / "grail.lock"
def packageDir (dir : System.FilePath) (name : String) : System.FilePath := dir / ".grail" / "packages" / name

/-- Run git; its trimmed output. -/
def git (args : Array String) (cwd : Option System.FilePath := none) : IO (Except String String) := do
  try
    let o ← IO.Process.output { cmd := "git", args, cwd }
    pure (if o.exitCode == 0 then .ok o.stdout.trimAscii.toString
      else .error s!"git {" ".intercalate args.toList}: {o.stderr.trimAscii}")
  catch e => pure (.error s!"git: {e}")

/-- The files of a checked-out package, relative paths, sorted (not `.git`, `.grail`, a
`grail.local.wiz` by basename, or a `.grail-pkg` stamp). -/
partial def packageFiles (root : System.FilePath) (rel : String := "") : IO (Array String) := do
  let mut out := #[]
  for e in ← (if rel.isEmpty then root else root / rel).readDir do
    let r := if rel.isEmpty then e.fileName else s!"{rel}/{e.fileName}"
    if [".git", ".grail"].contains r || [".grail-pkg", "grail.local.wiz"].contains e.fileName then continue
    if ← e.path.isDir then out := out ++ (← packageFiles root r) else out := out.push r
  pure (out.qsort (· < ·))

/-- A hash of a package's files: their paths and contents. -/
def contentHash (root : System.FilePath) : IO String := do
  let mut h : UInt64 := hash "grail-content"
  for f in ← packageFiles root do
    h := mixHash h (mixHash (hash f) (hash (← IO.FS.readBinFile (root / f))))
  pure (hex h)

/-- Make `d` a clone of `url` (cloning again if it was a clone of something else). -/
def ensureClone (d : System.FilePath) (url : String) : IO (Except String Unit) := do
  if ← (d / ".git").pathExists then
    if (← git #["remote", "get-url", "origin"] d).toOption == some url then return .ok ()
  if ← d.pathExists then IO.FS.removeDirAll d
  if let some p := d.parent then IO.FS.createDirAll p
  pure ((← git #["clone", "--quiet", url, d.toString]).map fun _ => ())

/-- Check out `commit` in `d` (fetching it if the clone doesn't have it). -/
def checkout (d : System.FilePath) (commit : String) : IO (Except String Unit) := do
  if (← git #["rev-parse", "HEAD"] d).toOption == some commit then return .ok ()
  unless (← git #["cat-file", "-e", s!"{commit}^\{commit}"] d) matches .ok _ do
    if let .error e ← git #["fetch", "--quiet", "--tags", "origin"] d then return .error e
  pure ((← git #["checkout", "--quiet", "--force", "--detach", commit] d).map fun _ => ())

/-- `--offline` versions of `ensureClone`/`checkout`: use the cache, never the network. -/
def ensureCloneCached (d : System.FilePath) (url : String) : IO (Except String Unit) := do
  unless ← (d / ".git").pathExists do
    return .error s!"--offline: {d} is not cloned (run `grail update` once without --offline)"
  if (← git #["remote", "get-url", "origin"] d).toOption == some url then return .ok ()
  pure (.error s!"--offline: {d} is a clone of another URL (run `grail update` without --offline)")

def checkoutCached (d : System.FilePath) (commit : String) : IO (Except String Unit) := do
  if (← git #["rev-parse", "HEAD"] d).toOption == some commit then return .ok ()
  if (← git #["cat-file", "-e", s!"{commit}^\{commit}"] d).toOption.isSome then
    return (← git #["checkout", "--quiet", "--force", "--detach", commit] d).map fun _ => ()
  pure (.error s!"--offline: {d} has no commit {commit} (run `grail update` without --offline)")

/-- Resolve `deps` (after the ones in `acc`), fetching each to `.grail/packages/NAME`, and
their dependencies after them. With `offline`, only the existing clones and refs are
used. -/
partial def resolveDeps (readPkg : System.FilePath → IO (Except String Package)) (dir : System.FilePath)
    (deps : List Dep) (acc : List Locked) (offline : Bool := false) : IO (Except String (List Locked)) := do
  let mut acc := acc
  for dep in deps do
    let d := packageDir dir dep.name
    if offline then
      if let .error e ← ensureCloneCached d dep.url then return .error e
    else
      if let .error e ← ensureClone d dep.url then return .error e
      if let .error e ← git #["fetch", "--quiet", "--tags", "--force", "origin"] d then return .error e
    let commit ← match ← git #["rev-parse", "--verify", "--quiet", s!"refs/remotes/origin/{dep.rev}^\{commit}"] d with
      | .ok c => pure c
      | .error _ => match ← git #["rev-parse", "--verify", "--quiet", s!"{dep.rev}^\{commit}"] d with
        | .ok c => pure c
        | .error _ => return .error s!"{dep.name}: no revision {dep.rev} in {dep.url}"
    if let some l := acc.find? (·.name == dep.name) then
      if l.commit == commit then continue
      return .error s!"two commits of {dep.name}: {l.commit} ({l.url} {l.rev}) and {commit} ({dep.url} {dep.rev})"
    if let .error e ← (if offline then checkoutCached d commit else checkout d commit) then return .error e
    acc := acc ++ [{ name := dep.name, url := dep.url, rev := dep.rev, commit, content := ← contentHash d }]
    if ← (d / "grail.wiz").pathExists then
      match ← readPkg d with
      | .error e => return .error s!"{dep.name}: {e}"
      | .ok p =>
        match ← resolveDeps readPkg dir p.deps acc offline with
        | .error e => return .error e
        | .ok a => acc := a
  pure (.ok acc)

/-- `grail update`: resolve the dependencies again and write `grail.lock`. -/
def update (readPkg : System.FilePath → IO (Except String Package)) (dir : System.FilePath) (pkg : Package) :
    IO (Except String (List Locked)) := do
  match ← resolveDeps readPkg dir pkg.deps [] with
  | .error e => pure (.error e)
  | .ok ls =>
    let text := renderLock ls
    let old ← if ← (lockFile dir).pathExists then some <$> IO.FS.readFile (lockFile dir) else pure none
    if old != some text then Cache.writeAtomic (lockFile dir) text
    pure (.ok ls)

/-- Before a build: check the dependencies out at their locked commits and return the
module roots they give (their `lib` targets'). Notes (a `REV` changed since the lock) go
to `note`. -/
def lockedRoots (readPkg : System.FilePath → IO (Except String Package)) (dir : System.FilePath) (pkg : Package)
    (note : String → IO Unit) : IO (Except String (List System.FilePath)) := do
  let lock := lockFile dir
  if !(← lock.pathExists) then
    return if pkg.deps.isEmpty then .ok [] else .error s!"no {lock}: run `grail update`"
  let ls ← match parseLock (← IO.FS.readFile lock) with
    | .ok ls => pure ls
    | .error e => return .error e
  for dep in pkg.deps do
    match ls.find? (·.name == dep.name) with
    | none => return .error s!"{dep.name} is not in {lock}: run `grail update`"
    | some l =>
      if l.url != dep.url || l.rev != dep.rev then
        note s!"note: {lock} has {dep.name} at {l.commit} ({l.url} {l.rev}); grail.wiz asks for {dep.url} {dep.rev}: `grail update` moves it\n"
  let mut roots := #[]
  for l in ls do
    let d := packageDir dir l.name
    if let .error e ← ensureClone d l.url then return .error e
    if let .error e ← checkout d l.commit then return .error e
    let content ← contentHash d
    if content != l.content then
      return .error s!"{d} differs from {lock} (content {content}, locked {l.content}): edited? remove it, or `grail update`"
    if ← (d / "grail.wiz").pathExists then
      match ← readPkg d with
      | .error e => return .error s!"{l.name}: {e}"
      | .ok p => roots := roots ++ (libRootsOf d p.targets).toArray
  pure (.ok roots.toList)

end Grail
