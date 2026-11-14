import Grail.Registry
import Grail.Config

/-!
# Checking a static index (stage 23m)

`grail index check INDEX` validates a `grail-index` repository **offline** by default:
the entries' names and versions, the SHA-256 of every archive it can reach locally, every
version requirement, module-prefix conflicts, and the repository manifest (`index.wiz`).
Absolute `https://` archives are *counted but not fetched* unless `--fetch` is given, so a
CI job can run it with no network at all (`scripts/grail-index-check.sh`).

The same checks are available as declarations for the test driver:

    IndexCheck.checkDir cache tc salt std "examples/grail-index" false

The resolver's own module check (R32) lives in `Grail/Index.lean` (`Resolve.resolve`);
this file is the whole-index audit, which can catch a conflict before anyone resolves the
two packages together.
-/

namespace Grail
open Wiz Cache

/-- What one `grail index check` found. `archives` counts the local (or `--fetch`ed)
archives whose SHA-256 was recomputed; `remote` counts entries whose source is a URL that
was not touched. -/
structure CheckResult where
  packages : Nat := 0
  versions : Nat := 0
  archives : Nat := 0
  remote : Nat := 0
  errors : List String := []
  warnings : List String := []
  deriving Repr, Inhabited

namespace CheckResult

def hasErrors (r : CheckResult) : Bool := !r.errors.isEmpty

/-- The detail lines, errors first. -/
def lines (r : CheckResult) : List String :=
  r.errors.map (fun e => "error: " ++ e) ++ r.warnings.map (fun w => "warning: " ++ w)

def summary (r : CheckResult) : String :=
  s!"{r.packages} packages, {r.versions} versions, {r.archives} archives verified, \
     {r.remote} remote not verified, {r.errors.length} errors, {r.warnings.length} warnings"

end CheckResult

def addError (r : CheckResult) (who msg : String) : CheckResult :=
  { r with errors := r.errors ++ [s!"{who}: {msg}"] }

def addWarning (r : CheckResult) (who msg : String) : CheckResult :=
  { r with warnings := r.warnings ++ [s!"{who}: {msg}"] }

/-- The registry's own name rule (`validName`), plus the scoped layout the reader
already accepts: `@org/name`. -/
def validIndexName (s : String) : Bool :=
  match s.splitOn "/" with
  | [n] => validName n
  | [scope, n] =>
    scope.startsWith "@" && scope.length > 1 && validName n &&
      (scope.drop 1).toString.toList.all fun c =>
        ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9') || c == '-'
  | _ => false

/-- A module name as Wiz spells it: dot-separated identifier segments (`A`, `A.B`). -/
def validModuleName (s : String) : Bool :=
  let segs := s.splitOn "."
  !segs.isEmpty && segs.all fun seg =>
    !seg.isEmpty && seg.toList.all fun c =>
      ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || ('0' ≤ c && c ≤ '9') || c == '_'

/-- A source that can be checked without a network: a plain path or `file://` URL.
`none` for `https://…` and the like. `loadIndex` has already resolved relative paths
against the index root. -/
def localArchive? (source : String) : Option String :=
  if source.startsWith "file://" then some (source.drop 7).toString
  else if source.contains "://" then none
  else some source

/-- Recompute an archive's SHA-256 and check its layout. -/
def verifyArchive (r : CheckResult) (who source : String) (f : System.FilePath)
    (name version sha : String) : IO CheckResult := do
  match ← Registry.sha256File f with
  | .error e => pure (addError r who e)
  | .ok h =>
    let r := if h != sha then addError r who s!"sha256 of {source} is {h}, the entry says {sha}" else r
    match ← Registry.checkArchiveLayout f name version with
    | .error e => pure (addError r who e)
    | .ok () => pure r

/-- One version: hash shape, requirements, module names, and its archive. -/
def checkVersion (r : CheckResult) (name : String) (v : IxVersion) (fetch : Bool)
    (tmp : System.FilePath) : IO CheckResult := do
  let who := s!"{name} {Version.render v.version}"
  let mut r := r
  if !Registry.isSha256 v.sha256 then
    r := addError r who s!"sha256 {v.sha256} is not 64 lowercase hex digits"
  if !v.toolchain.isEmpty then
    match Requirement.parse v.toolchain with
    | .error e => r := addError r who s!"toolchain {v.toolchain}: {e}"
    | .ok _ => pure ()
  for d in v.deps do
    if !validIndexName d.name then
      r := addError r who s!"dependency name {d.name}: expected [a-z][a-z0-9-]*"
    match Requirement.parse d.req with
    | .error e => r := addError r who s!"dependency {d.name} {d.req}: {e}"
    | .ok _ => pure ()
  for m in v.claims do
    if !validModuleName m then
      r := addError r who s!"module {m}: expected a dotted name (A or A.B)"
  match localArchive? v.source with
  | none =>
    if fetch then
      let f := tmp / s!"{name}-{Version.render v.version}.tar.gz"
      match ← Registry.download v.source f with
      | .error e => r := addError r who e
      | .ok () =>
        r := { r with archives := r.archives + 1 }
        r := ← verifyArchive r who v.source f name (Version.render v.version) v.sha256
      if ← f.pathExists then IO.FS.removeFile f
    else
      -- counted, not downloaded: `archives` only names what this run actually hashed
      r := { r with remote := r.remote + 1 }
  | some path =>
    let f : System.FilePath := path
    if !(← f.pathExists) then
      r := addError r who s!"source {v.source} does not exist"
    else
      r := { r with archives := r.archives + 1 }
      r := ← verifyArchive r who v.source f name (Version.render v.version) v.sha256
  pure r

/-- One package: its name, version list, and every version. -/
def checkPackage (r : CheckResult) (name : String) (p : IxPackage) (fetch : Bool)
    (tmp : System.FilePath) : IO CheckResult := do
  let mut r := r
  if !validIndexName name then
    r := addError r name "package name: expected [a-z][a-z0-9-]* (or @org/name)"
  if p.versions.isEmpty then
    r := addError r name "no versions (an index entry with no release is useless)"
  let mut seen : List String := []
  for v in p.versions do
    let ver := Version.render v.version
    if seen.contains ver then r := addError r name s!"version {ver} appears twice"
    seen := ver :: seen
    r := { r with versions := r.versions + 1 }
    r := ← checkVersion r name v fetch tmp
  pure r

/-- The first module clash between the (non-yanked) versions of two packages. Checking
*yanked* versions too would report a conflict that no new resolution can pick; an old
lock can still contain it, which is a build-time `one name, one declaration` error. -/
def firstClash (a b : IxPackage) : Option (IxVersion × IxVersion × String × String) :=
  let live := fun (p : IxPackage) => p.versions.filter (·.yanked.isEmpty)
  (live a).findSome? fun v =>
    (live b).findSome? fun w =>
      (v.firstClash w).map fun (x, y) => (v, w, x, y)

/-- Every pair of distinct packages in the index: a module prefix they both claim is a
conflict, because a future resolution may select both (Wiz has one global module
namespace). One report per package pair (the first clash). -/
partial def checkConflicts (r : CheckResult) (entries : List (String × IxPackage)) :
    CheckResult :=
  match entries with
  | [] => r
  | (n, p) :: rest =>
    let r := rest.foldl (fun r (m, q) =>
      match firstClash p q with
      | none => r
      | some (v, w, x, y) =>
        addError r s!"{n} {Version.render v.version} / {m} {Version.render w.version}"
          s!"module conflict: {x} and {y} overlap; Wiz has one global module namespace") r
    checkConflicts r rest

/-- Read `registry.sexpr` (metadata; not needed to resolve, but part of the layout) and
return its name and format. -/
def checkRegistry (r : CheckResult) (dir : System.FilePath) : IO (CheckResult × String × Nat) := do
  let f := dir / "registry.sexpr"
  if !(← f.pathExists) then return (r, "", 0)
  match Sx.parse (← IO.FS.readFile f) with
  | none => pure (addError r "registry.sexpr" "not an S-expression", "", 0)
  | some x =>
    match x with
    | .l xs =>
      match xs.toList with
      | .a "registry" :: fields =>
        let mut r := r
        let mut name := ""
        let mut format := 0
        for field in fields do
          match field with
          | .l #[.a "name", .a s] => name := s
          | .l #[.a "format", .a n] =>
            match n.toNat? with
            | some k => format := k
            | none => r := addError r "registry.sexpr" s!"format {n} is not a number"
          | .l #[.a "updated", .a _] => pure ()
          | _ => r := addWarning r "registry.sexpr" s!"unknown field {field.render}"
        if name.isEmpty then r := addError r "registry.sexpr" "no (name …)"
        if format == 0 then r := addError r "registry.sexpr" "no (format N)"
        else if format > 1 then
          r := addError r "registry.sexpr" s!"format {format}: this grail reads format 1"
        pure (r, name, format)
      | _ => pure (addError r "registry.sexpr" s!"expected (registry …), got {x.render}", "", 0)
    | _ => pure (addError r "registry.sexpr" s!"expected (registry …), got {x.render}", "", 0)

/-- Validate an index given as a local directory or file, or (with `fetch`) a git URL.
Offline by default: without `fetch`, a non-local spec is refused and remote archives are
counted, never downloaded. -/
def checkDir (cache : System.FilePath) (tc : Toolchain) (salt : UInt64)
    (std : System.FilePath) (spec : String) (fetch : Bool := false) :
    IO (Except String CheckResult) := do
  let p : System.FilePath := spec
  let isLocal := ← p.pathExists
  if !isLocal && !fetch then
    return .error s!"{spec}: not a local directory or file; pass --fetch to clone a git index (the check is offline by default)"
  -- a bare repository path is cloned by `loadIndex`; the checkout (and its index.wiz and
  -- registry.sexpr) is then in the cache, not at the bare path
  let isBare := isLocal && (← (p / "HEAD").pathExists) && (← (p / "objects").isDir)
  let rootDir : System.FilePath := if isLocal && !isBare then p else cache / "grail" / "index"
  match ← Registry.loadIndex cache spec (!fetch) with
  | .error e => pure (.error e)
  | .ok src =>
    let tmp ← IO.FS.createTempDir
    let mut r : CheckResult := { packages := src.pkgs.size }
    let (r0, regName, _) ← checkRegistry r rootDir
    r := r0
    let manifest ← readIndexManifest tc salt std rootDir
    match manifest with
    | .error e => r := addError r "index.wiz" e
    | .ok none => pure ()
    | .ok (some m) =>
      if m.format != 1 then
        r := addError r "index.wiz" s!"format {m.format}: this grail reads format 1"
      if !regName.isEmpty && regName != m.name then
        r := addError r "index.wiz" s!"name {m.name}, but registry.sexpr says {regName}"
      for name in m.packages do
        unless src.pkgs.contains name do
          r := addError r "index.wiz" s!"lists {name}, but index/{name}.sexpr is missing"
    let entries := (src.pkgs.toList.toArray.qsort (fun a b => a.1 < b.1)).toList
    for (name, pkg) in entries do
      r := ← checkPackage r name pkg fetch tmp
    r := checkConflicts r entries
    match manifest with
    | .error _ => pure ()  -- already reported above
    | .ok none => pure ()
    | .ok (some m) =>
      for (name, _) in entries do
        unless m.packages.contains name do
          r := addError r "index.wiz" s!"index/{name}.sexpr is not listed in index.wiz"
    -- dependencies on packages this index does not contain are a warning: an overlay
    -- (R6) may leave them to another index.
    for (name, pkg) in entries do
      for v in pkg.versions do
        for d in v.deps do
          unless src.pkgs.contains d.name do
            r := addWarning r s!"{name} {Version.render v.version}"
              s!"depends on {d.name}, which is not in this index"
    IO.FS.removeDirAll tmp
    pure (.ok r)

end Grail
