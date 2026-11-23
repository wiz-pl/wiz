import Grail.Config
import Wiz.Smt.Sha256

/-!
# The package index (stage 23m, prototype)

A **static index** is text: one S-expression file per package name, in a git repository
(so a mirror, a fork or a private index is just another URL). This file is the pure part:
versions and version requirements, the index format, and the resolver. `Grail/Registry.lean`
reads the index and the lock, and fetches.

    (index
      (package "greet"
        (summary "Hello, in Wiz")
        (repo "https://github.com/example/greet")
        (version "1.2.0"
          (source "https://github.com/example/greet/releases/download/v1.2.0/greet-1.2.0.tar.gz")
          (sha256 "9f2c…")
          (toolchain ">=0.1.0 <0.3.0")
          (modules "Greet" "Greet.Hello")
          (deps (dep "std" "^0.1")))
        (yanked "1.2.0" "wrong tarball; use 1.2.1")))

Versions are semver (`1.2.3`, `1.2.3-rc.1`) and requirements are `1.2.3`, `^1.2.3`,
`~1.2.3`, `>=1.2.3 <2.0.0`, or `*`. There is one version of a name in a build (Wiz has one
global name space), so the resolver picks the highest version that satisfies *every*
requirement on that name, and errors when none does.
-/

namespace Grail

/-- A version: `major.minor.patch[-pre]` -/
structure Version where
  major : Nat
  minor : Nat
  patch : Nat
  /-- `""` for a release; `rc.1`, `dev` for a pre-release (sorts before the release) -/
  pre : String := ""
  deriving Repr, Inhabited, BEq

namespace Version

def render (v : Version) : String :=
  s!"{v.major}.{v.minor}.{v.patch}" ++ (if v.pre.isEmpty then "" else "-" ++ v.pre)

def ofParts (core pre : String) : Except String Version := do
  let parts := core.splitOn "."
  if parts.length > 3 then throw s!"not a version: {core}"
  let nums ← parts.mapM fun p => match p.toNat? with
    | some n => pure n
    | none => throw s!"not a version: {core}"
  match nums with
  | [a] => pure { major := a, minor := 0, patch := 0, pre }
  | [a, b] => pure { major := a, minor := b, patch := 0, pre }
  | [a, b, c] => pure { major := a, minor := b, patch := c, pre }
  | _ => throw s!"not a version: {core}"

/-- Parse `1.2.3`, `1.2`, `1`, `1.2.3-rc.1`. -/
def parse (s : String) : Except String Version := do
  let s := s.trimAscii.toString
  if s.isEmpty then throw "empty version"
  match s.splitOn "-" with
  | [core] => ofParts core ""
  | core :: pre => ofParts core ("-".intercalate pre)
  | [] => throw s!"not a version: {s}"

/-- Pre-release identifiers compared field by field: a numeric one numerically, an
alphanumeric one as text; a release sorts after its pre-releases. -/
def cmpPre (a b : String) : Ordering :=
  if a == b then .eq
  else if a.isEmpty then .gt
  else if b.isEmpty then .lt
  else
    let rec go (xs ys : List String) : Ordering :=
      match xs, ys with
      | [], [] => .eq
      | [], _ => .lt
      | _, [] => .gt
      | x :: xs, y :: ys =>
        match x.toNat?, y.toNat? with
        | some m, some n => if m == n then go xs ys else if m < n then .lt else .gt
        | none, none => if x == y then go xs ys else if x < y then .lt else .gt
        | some _, none => .lt
        | none, some _ => .gt
    go (a.splitOn ".") (b.splitOn ".")

def cmp (a b : Version) : Ordering :=
  if a.major != b.major then (if a.major < b.major then .lt else .gt)
  else if a.minor != b.minor then (if a.minor < b.minor then .lt else .gt)
  else if a.patch != b.patch then (if a.patch < b.patch then .lt else .gt)
  else cmpPre a.pre b.pre

def lt (a b : Version) : Bool := cmp a b == .lt
def le (a b : Version) : Bool := cmp a b != .gt

end Version

/-- One comparison of a requirement -/
inductive Op where
  | eq | ge | gt | le | lt
  /-- `^1.2.3`: `>=1.2.3`, below the next major (below the next minor when major is 0) -/
  | caret
  /-- `~1.2.3`: `>=1.2.3`, below the next minor -/
  | tilde
  deriving Repr, Inhabited, BEq

structure Clause where
  op : Op
  v : Version
  /-- how many components the requirement was written with (`~1`, `~1.2`, `~1.2.3`):
  `~1` means `<2.0.0`, `~1.2` and `~1.2.3` mean `<1.3.0` -/
  components : Nat := 3
  deriving Repr, Inhabited, BEq

/-- A version requirement: every clause must hold; no clause means any version. -/
abbrev Requirement := List Clause

namespace Requirement

def parseOne (tok : String) : Except String Clause := do
  let (op, rest) :=
    if tok.startsWith ">=" then (Op.ge, (tok.drop 2).toString)
    else if tok.startsWith "<=" then (Op.le, (tok.drop 2).toString)
    else if tok.startsWith ">" then (Op.gt, (tok.drop 1).toString)
    else if tok.startsWith "<" then (Op.lt, (tok.drop 1).toString)
    else if tok.startsWith "^" then (Op.caret, (tok.drop 1).toString)
    else if tok.startsWith "~" then (Op.tilde, (tok.drop 1).toString)
    else if tok.startsWith "=" then (Op.eq, (tok.drop 1).toString)
    else (Op.eq, tok)
  let core := (rest.splitOn "-").head!
  pure { op, v := ← Version.parse rest, components := (core.splitOn ".").length }

/-- `^1.2`, `~1.2.3`, `>=0.1 <0.3`, `1.2.3`, `*`. -/
def parse (s : String) : Except String Requirement := do
  let s := s.trimAscii.toString
  if s.isEmpty || s == "*" then return []
  let toks := (s.splitOn " ").filter (!·.isEmpty)
  toks.mapM parseOne

/-- The exclusive upper bound a `^` or `~` clause implies. `^` follows Cargo/npm: the
leftmost non-zero component decides, and a one-component `^0`/`^1` means "< the next
major" (`^0` is `<1.0.0`, `^0.0` is `<0.1.0`, `^0.2.3` is `<0.3.0`, `^0.0.3` is
`<0.0.4`). `~` keeps the documented npm semantics (`~1` is `<2.0.0`, `~1.2` is
`<1.3.0`). -/
def upper (c : Clause) : Version :=
  let v := c.v
  match c.op with
  | .caret =>
    if c.components <= 1 then { v with major := v.major + 1, minor := 0, patch := 0, pre := "" }
    else if c.components == 2 && v.major == 0 then
      { v with minor := v.minor + 1, patch := 0, pre := "" }
    else if v.major != 0 then { v with major := v.major + 1, minor := 0, patch := 0, pre := "" }
    else if v.minor != 0 then { v with minor := v.minor + 1, patch := 0, pre := "" }
    else { v with patch := v.patch + 1, pre := "" }
  | .tilde =>
    if c.components <= 1 then { v with major := v.major + 1, minor := 0, patch := 0, pre := "" }
    else { v with minor := v.minor + 1, patch := 0, pre := "" }
  | _ => v

/-- How a requirement prints in messages. -/
def render (r : Requirement) : String :=
  if r.isEmpty then "*" else
    " ".intercalate (r.map fun c =>
      (match c.op with
       | .eq => "" | .ge => ">=" | .gt => ">" | .le => "<=" | .lt => "<"
       | .caret => "^" | .tilde => "~") ++ Version.render c.v)

end Requirement

/-- Whether `c` holds of `v`. `allowPre`: the toolchain's own version (`0.1.0-dev`) is a
pre-release, and a range like `>=0.1.0 <0.3.0` should still admit it. -/
def Clause.holds (c : Clause) (v : Version) (allowPre : Bool := false) : Bool :=
  -- a `-dev` toolchain (the unreleased X.Y.Z) counts as X.Y.Z
  let v := if allowPre && v.pre != "" then { v with pre := "" } else v
  if v.pre != "" && !allowPre && c.op != .eq && c.v.pre == "" then false
  else
    match c.op with
    | .eq => v == c.v
    | .ge => Version.le c.v v
    | .gt => Version.lt c.v v
    | .le => Version.le v c.v
    | .lt => Version.lt v c.v
    | .caret | .tilde => Version.le c.v v && Version.lt v (Requirement.upper c)

/-- Whether every clause of `r` holds of `v`. -/
def Requirement.satisfies (r : Requirement) (v : Version) (allowPre : Bool := false) : Bool :=
  r.all (Clause.holds · v allowPre)

/-- One published version of a package -/
structure IxVersion where
  version : Version
  /-- the immutable source archive (a URL `curl` takes; `file://` works too) -/
  source : String
  /-- the SHA-256 of that archive, 64 lowercase hex digits -/
  sha256 : String
  /-- the toolchain the author tested with (a requirement; `""` means any) -/
  toolchain : String := ""
  /-- its dependencies, as the index records them (authoritative for resolution) -/
  deps : List Req := []
  /-- (R32) the module names the package provides (`Greet`, `Greet.Hello`). Wiz has one
  global module namespace, so two selected packages may not claim overlapping names.
  Optional: an entry without it is not checked (and old indexes keep decoding). -/
  modules : List String := []
  /-- (R32) module prefixes the package reserves for future modules (`Greet`). A prefix
  conflicts with any other package's module or prefix below it. -/
  prefixes : List String := []
  /-- (R19) the archive's size in bytes, when the publisher recorded it -/
  size : Option Nat := none
  /-- (R20) SHA-256 of the unpacked tree (sorted paths and file hashes); optional -/
  tree : String := ""
  /-- (R36) SHA-256 of the package's declared `Package.command` set; optional -/
  commands : String := ""
  /-- (P0) the release commit in `repo`; the source identity behind the archive. A tag
  is only a hint at update time: the commit is what the signed entry binds. -/
  commit : String := ""
  /-- why it is yanked; `""` when it isn't -/
  yanked : String := ""
  deriving Repr, Inhabited, BEq

/-- Every module name one version claims: the modules it provides and the prefixes it
reserves. -/
def IxVersion.claims (v : IxVersion) : List String := v.modules ++ v.prefixes

/-- Whether two dotted module names overlap: they are equal, or one is a prefix of the
other at a dot (`Ddr3` and `Ddr3.Ctrl`). Because Wiz's module names live in one global
namespace (23b), two packages that own overlapping prefixes cannot be selected together:
one may grow a module that collides with the other. This is deliberately conservative;
an entry that lists only its exact modules still conflicts with a package that reserves
their common prefix. -/
def moduleOverlap (a b : String) : Bool :=
  a == b || b.startsWith (a ++ ".") || a.startsWith (b ++ ".")

/-- The first pair of module names two versions disagree on, if any. -/
def IxVersion.firstClash (a b : IxVersion) : Option (String × String) := Id.run do
  for x in a.claims do
    for y in b.claims do
      if moduleOverlap x y then return some (x, y)
  return none

/-- A package's index entry -/
structure IxPackage where
  name : String
  summary : String := ""
  repo : String := ""
  versions : List IxVersion := []
  deriving Repr, Inhabited

/-- Package names are global and lowercase: a letter, then letters, digits and `-`
(at most 64 characters). -/
def validName (s : String) : Bool :=
  let cs := s.toList
  !cs.isEmpty && s.length ≤ 64 &&
    (match cs.head? with
     | some c => 'a' ≤ c && c ≤ 'z'
     | none => false) &&
    cs.all fun c => ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9') || c == '-'

namespace Index

open Wiz.Cache

def versionNode (v : IxVersion) : Sx :=
  let fields : List Sx :=
    [node "source" [str v.source], node "sha256" [str v.sha256]]
      ++ (match v.size with | some n => [node "size" [nat n]] | none => [])
      ++ (if v.tree.isEmpty then [] else [node "tree" [str v.tree]])
      ++ (if v.commands.isEmpty then [] else [node "commands" [str v.commands]])
      ++ (if v.commit.isEmpty then [] else [node "commit" [str v.commit]])
      ++ (if v.toolchain.isEmpty then [] else [node "toolchain" [str v.toolchain]])
      ++ (if v.modules.isEmpty then [] else [node "modules" (v.modules.map str)])
      ++ (v.prefixes.map fun p => node "prefix" [str p])
      ++ (if v.deps.isEmpty then []
          else [node "deps" (v.deps.map fun d => node "dep" [str d.name, str d.req])])
  node "version" (str (Version.render v.version) :: fields)

def renderVersion (v : IxVersion) : String := (versionNode v).render

/-- The **entry digest**: SHA-256 over the canonical version node, which is exactly what
the signed snapshot binds. It covers the archive hash, `size`, `tree`, `commands`,
`commit`, the toolchain range, module claims and dependency edges — everything a
`sha256`-only comparison missed. `Index.versionNode` never renders `(yanked …)`, which
lives at package level and is signed separately by the snapshot (`SnapshotEntry.yanked`).

The construction is deliberately the same bytes the index file uses for its `(version …)`
node after parsing, so a hand-edited field changes the digest even when the formatting
does not. -/
def entryDigest (v : IxVersion) : String := Wiz.Smt.Sha256.hex (versionNode v).render

def IxPackage.render (p : IxPackage) : String :=
  let fields : List Sx :=
    (if p.summary.isEmpty then [] else [node "summary" [str p.summary]])
      ++ (if p.repo.isEmpty then [] else [node "repo" [str p.repo]])
      ++ p.versions.map versionNode
      ++ (p.versions.filterMap fun v =>
           if v.yanked.isEmpty then none else some (node "yanked" [str (Version.render v.version), str v.yanked]))
  (node "package" (str p.name :: fields)).render

/-- Render a whole index document, packages and versions in a stable (sorted) order. -/
def render (ps : List IxPackage) : String :=
  let sorted := (ps.toArray.qsort fun a b => a.name < b.name).toList
  "(index\n  " ++ "\n  ".intercalate (sorted.map IxPackage.render) ++ ")\n"

/-- Add one published version to an index. `name@version` is immutable: an existing
version is refused, not replaced (publish a corrected release instead). -/
def addVersion (ps : List IxPackage) (p : IxPackage) (v : IxVersion) : Except String (List IxPackage) := do
  match ps.find? (·.name == p.name) with
  | none => pure (ps ++ [{ p with versions := [v] }])
  | some old =>
    if old.versions.any (fun x => Version.render x.version == Version.render v.version) then
      throw s!"{p.name} {Version.render v.version} is already in the index: a version is immutable (publish a new version)"
    pure (ps.map fun x => if x.name == p.name then { x with versions := x.versions ++ [v] } else x)

def decodeReq (x : Sx) : Except String Req :=
  match x with
  | .l #[.a "dep", .a n, .a r] => pure { name := n, req := r }
  | x => throw s!"bad requirement {x.render}"

def decodeVersion (x : Sx) : Except String IxVersion := do
  let .l xs := x | throw s!"bad version {x.render}"
  let mut out : IxVersion := { version := { major := 0, minor := 0, patch := 0 }, source := "", sha256 := "" }
  let (v, fields) ← match xs.toList with
    | .a "version" :: .a v :: rest => pure (v, rest)
    | _ => throw s!"bad version {x.render}"
  out := { out with version := ← Version.parse v }
  for f in fields do
    match f with
    | .l #[.a "source", .a s] => out := { out with source := s }
    | .l #[.a "sha256", .a s] => out := { out with sha256 := s }
    | .l #[.a "size", .a s] =>
      -- (R19) a publisher records the archive's size; old entries have none
      out := { out with size := s.toNat? }
    | .l #[.a "tree", .a s] => out := { out with tree := s }
    | .l #[.a "commands", .a s] => out := { out with commands := s }
    | .l #[.a "commit", .a s] => out := { out with commit := s }
    | .l #[.a "toolchain", .a s] => out := { out with toolchain := s }
    | .l ys =>
      match ys.toList with
      | .a "deps" :: rest => out := { out with deps := ← rest.mapM decodeReq }
      | .a "modules" :: rest =>
        out := { out with modules := rest.filterMap fun
          | .a m => some m
          | _ => none }
      | .a "prefix" :: rest =>
        out := { out with prefixes := rest.filterMap fun
          | .a p => some p
          | _ => none }
      -- (R3) the index is a shared, long-lived artifact: an unknown field added by a
      -- newer publisher is ignored here (the *lock* decoder stays strict), so an old
      -- grail can still read a package whose entry gained `(license …)`, `(size …)`, …
      | _ => pure ()
    | _ => pure ()
  if out.source.isEmpty then throw s!"version {v}: no source"
  if out.sha256.length != 64 then throw s!"version {v}: sha256 must be 64 hex digits"
  pure out

/-- A `(version …)` node, without the fields it doesn't need (`deps`, `toolchain`). -/
def decodePackage (x : Sx) : Except String IxPackage := do
  let .l xs := x | throw s!"bad package {x.render}"
  let (name, fields) ← match xs.toList with
    | .a "package" :: .a name :: rest => pure (name, rest)
    | _ => throw s!"bad package {x.render}"
  let mut out : IxPackage := { name }
  let mut yanked : List (String × String) := []
  for f in fields do
    match f with
    | .l #[.a "summary", .a s] => out := { out with summary := s }
    | .l #[.a "repo", .a s] => out := { out with repo := s }
    | .l #[.a "yanked", .a v, .a why] => yanked := yanked ++ [(v, why)]
    | .l ys =>
      match ys.toList with
      | .a "version" :: _ => out := { out with versions := out.versions ++ [← decodeVersion f] }
      -- (R3) forward compatibility: ignore fields this grail does not know
      | _ => pure ()
    | _ => pure ()
  for (v, why) in yanked do
    let isIt (iv : IxVersion) : Bool := Version.render iv.version == v
    if out.versions.any isIt then
      out := { out with versions := out.versions.map fun iv => if isIt iv then { iv with yanked := why } else iv }
    else throw s!"package {name}: yanked version {v} is not in the index"
  out := { out with versions := (out.versions.toArray.qsort fun a b => Version.lt a.version b.version).toList }
  pure out

/-- Parse one index document: `(index (package …) …)`. -/
def parse (s : String) : Except String (List IxPackage) := do
  let some (.l xs) := Sx.parse s | throw "expected (index (package …) …)"
  let some (.a "index") := xs[0]? | throw "expected (index (package …) …)"
  xs.toList.drop 1 |>.mapM fun f =>
    match f with
    | .l ys =>
      match ys.toList with
      | .a "package" :: _ => decodePackage f
      | _ => throw s!"index: expected a package, got {f.render}"
    | x => throw s!"index: expected a package, got {x.render}"

end Index

/-- A resolved package: one version of one name, with the archive to fetch -/
structure Resolved where
  name : String
  version : Version
  source : String
  sha256 : String
  toolchain : String := ""
  size : Option Nat := none
  tree : String := ""
  commands : String := ""
  commit : String := ""
  deps : List Req := []
  deriving Repr, Inhabited

namespace Resolve

/-- A requirement on a name, and who asked for it (for messages) -/
abbrev Ask := String × String

/-- Whether the running `toolchain` satisfies a version's `toolchain` field. -/
def toolchainOk (toolchain : String) (v : IxVersion) : Bool :=
  if v.toolchain.isEmpty then true
  else match Requirement.parse v.toolchain with
    | .error _ => false
    | .ok r => match Version.parse toolchain with
      | .error _ => true
      | .ok tc => Requirement.satisfies r tc (allowPre := true)

/-- Ask the index for `name`'s highest version that satisfies every one of `asks` and the
running toolchain. -/
def pick (p : IxPackage) (asks : List Ask) (toolchain : String) : Except String IxVersion := do
  let reqs ← asks.mapM fun (r, who) => do pure (← Requirement.parse r, who)
  let want := reqs.map (·.1)
  let ok (v : IxVersion) : Bool :=
    v.yanked.isEmpty && want.all (fun r => Requirement.satisfies r v.version) && toolchainOk toolchain v
  match (p.versions.filter ok).getLast? with
  | some v => pure v
  | none =>
    -- an exact requirement on a yanked version gets the reason, not a generic conflict
    if let some y := p.versions.find? fun v =>
        !v.yanked.isEmpty && want.any fun r => r.any fun c =>
          c.op == .eq && c.v == v.version && Requirement.satisfies [c] v.version then
      throw s!"{p.name} {Version.render y.version} is yanked ({y.yanked}); choose another version"
    let asked := " ".intercalate (reqs.map fun (r, who) => s!"{Requirement.render r} (from {who})")
    let avail := " ".intercalate (p.versions.map fun v =>
      Version.render v.version ++ (if v.yanked.isEmpty then "" else " (yanked)"))
    throw s!"{p.name}: no version satisfies {asked}; the index has {avail}"

def sortedAsks (m : Std.HashMap String (List Ask)) : List (String × List Ask) :=
  (m.toList.toArray.qsort (fun a b => a.1 < b.1)).toList.map fun (n, a) =>
    (n, (a.toArray.qsort (fun x y => x.1 < y.1)).toList)

/-- The constraints implied by the roots and by the *current* selection: every root
requirement, plus every dependency of every chosen version. Rebuilding this map each round
(rather than only appending) is R9 in `docs/prior-art/registries-build-systems.md`:
when a chosen version is replaced, the requirements that only the old version introduced
are retracted instead of lingering. -/
def constraintsOf (roots : List Req) (selection : List (String × IxVersion)) :
    Std.HashMap String (List Ask) := Id.run do
  let mut cons : Std.HashMap String (List Ask) := {}
  for r in roots do
    let cur := cons.getD r.name []
    unless cur.contains (r.req, "this package") do
      cons := cons.insert r.name (cur ++ [(r.req, "this package")])
  for (name, v) in selection do
    for d in v.deps do
      let cur := cons.getD d.name []
      unless cur.contains (d.req, name) do
        cons := cons.insert d.name (cur ++ [(d.req, name)])
  return cons

/-- The fixpoint: choose a version per name from the constraints of the roots and the
current selection, then rebuild the constraints from that selection and repeat until the
selection is unchanged. (One version per name, so a change can only appear when a
newly-reachable package asks for something stricter, or when replacing a version retracts
a requirement it alone introduced.) -/
partial def step (index : Std.HashMap String IxPackage) (toolchain : String)
    (fuel : Nat) (roots : List Req) (selection : List (String × IxVersion)) :
    Except String (List (String × IxVersion)) := do
  if fuel == 0 then throw "dependency resolution does not settle (a cycle whose requirements change?)"
  let cons := constraintsOf roots selection
  let mut chosen : List (String × IxVersion) := []
  for (name, asks) in sortedAsks cons do
    let some p := index[name]? | throw s!"no package {name} in the index (asked for by {asks.head!.2})"
    let v ← pick p asks toolchain
    chosen := chosen ++ [(name, v)]
  if chosen == selection then pure chosen
  else step index toolchain (fuel - 1) roots chosen

/-- Refuse a selection in which two packages claim overlapping module names. This is
23b's "one name, one declaration" checked before a build: two packages can have valid,
distinct registry names and still collide at `import` (R32). The lock does not record
modules, so the check lives in the resolver, not in the lock. -/
def moduleConflicts (sel : List (String × IxVersion)) : Except String Unit := do
  let arr := sel.toArray
  for i in [0:arr.size] do
    for j in [i + 1:arr.size] do
      let (n, v) := arr[i]!
      let (m, w) := arr[j]!
      match v.firstClash w with
      | some (x, y) =>
        throw s!"module conflict: {n} {Version.render v.version} and {m} {Version.render w.version} claim overlapping module namespaces ({x} and {y}); Wiz has one global module namespace"
      | none => pure ()

/-- Resolve `roots` against `index`: the highest version of each reachable name that
satisfies every requirement on it. Flat: one version per name (Wiz has one global name
space, and grail refuses two commits of one dependency name). -/
def resolve (index : Std.HashMap String IxPackage) (roots : List Req) (toolchain : String) :
    Except String (List Resolved) := do
  let rootAsks : List Req := roots
  let chosen ← step index toolchain 64 rootAsks []
  moduleConflicts chosen
  pure (chosen.map fun (name, v) => {
    name := name, version := v.version, source := v.source, sha256 := v.sha256,
    toolchain := v.toolchain, size := v.size, tree := v.tree, commands := v.commands,
    commit := v.commit, deps := v.deps })

end Resolve

end Grail

