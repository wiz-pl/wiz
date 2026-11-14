import Grail.Build

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

def renderLock (ls : List Locked) : String :=
  "(lock" ++ String.join (ls.map fun l =>
    "\n  " ++ (node "dep" [str l.name, str l.url, str l.rev, str l.commit, str l.content]).render) ++ ")\n"

def parseLock (s : String) : Except String (List Locked) := do
  let some (.l xs) := Sx.parse s | throw "grail.lock: expected (lock (dep …) …)"
  let some (.a "lock") := xs[0]? | throw "grail.lock: expected (lock (dep …) …)"
  xs.toList.drop 1 |>.mapM fun
    | .l #[.a "dep", .a name, .a url, .a rev, .a commit, .a content] => pure { name, url, rev, commit, content }
    | x => throw s!"grail.lock: expected (dep name url rev commit content), got {x.render}"

def lockFile (dir : System.FilePath) : System.FilePath := dir / "grail.lock"
def packageDir (dir : System.FilePath) (name : String) : System.FilePath := dir / ".grail" / "packages" / name

/-- Run git; its trimmed output. -/
def git (args : Array String) (cwd : Option System.FilePath := none) : IO (Except String String) := do
  try
    let o ← IO.Process.output { cmd := "git", args, cwd }
    pure (if o.exitCode == 0 then .ok o.stdout.trimAscii.toString
      else .error s!"git {" ".intercalate args.toList}: {o.stderr.trimAscii}")
  catch e => pure (.error s!"git: {e}")

/-- The files of a checked-out package, relative paths, sorted (not `.git`, `.grail`, or
the machine's `grail.local.wiz`). -/
partial def packageFiles (root : System.FilePath) (rel : String := "") : IO (Array String) := do
  let mut out := #[]
  for e in ← (if rel.isEmpty then root else root / rel).readDir do
    let r := if rel.isEmpty then e.fileName else s!"{rel}/{e.fileName}"
    if [".git", ".grail", "grail.local.wiz"].contains r then continue
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
