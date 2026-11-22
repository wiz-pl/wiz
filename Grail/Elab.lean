import Wiz
import Wiz.Toolchain

/-!
# Elaborating files for grail

grail elaborates in-process, through the shared elaboration cache (`Wiz/Cache.lean`).
Modules are found by path under the roots (`Wiz/Module.lean`); C headers are
preprocessed with the toolchain's compiler (the frontend is pure).
-/

namespace Grail
open Wiz

/-- `--region-stats`' counters, per process (a grail job is one process). -/
initialize regionStats : IO.Ref Cache.RegionCounts ← IO.mkRef {}

/-- Preprocess the headers (`import_c "h"`) of some sources with the toolchain's C compiler. -/
def preprocessHeaders (tc : Toolchain) (srcs : List String) : IO (Std.HashMap String String) := do
  let mut m : Std.HashMap String String := {}
  for src in srcs do
    for h in Module.headersOf src do
      if m.contains h then continue
      let dir ← IO.FS.createTempDir
      IO.FS.writeFile (dir / "h.c") s!"#include <{h}>\n"
      let out ← IO.Process.output { cmd := tc.cc, args := #["-E", "-P", (dir / "h.c").toString] ++ tc.cflags.toArray }
      IO.FS.removeDirAll dir
      if out.exitCode == 0 then m := m.insert h out.stdout
  pure m

/-- A file ready to elaborate: what it can import, its headers, and its key. -/
structure Loaded where
  src : String
  init : CommandState ZeroOneMany
  /-- the file's key: as for a module (`Cache.moduleKey`), its text, headers and imports,
  and (9f) which of its `link_c` files exist, where -/
  key : UInt64
  /-- the SHA-256 version of `key`, for the manifest/region namespace -/
  keyStrong : String

/-- The name a file that isn't itself imported goes by in the key computation. -/
def mainName : Name := "main✝"

def load (tc : Toolchain) (roots : List System.FilePath) (salt : UInt64) (src : String)
    (dir : System.FilePath := ".") : IO Loaded := do
  let closure ← Module.loadClosure roots src
  let lib := closure.fold (fun m n (_, s) => m.insert n s) ({} : Std.HashMap Name String)
  let headers ← preprocessHeaders tc (src :: lib.values)
  -- (9f) the `link_c` files, relative to their files (`dir` is the main file's)
  let sources ← Module.cSourceTable dir src closure
  -- (include-str) the `include_str` files, relative to their files
  let includes ← Module.includeTable dir src closure
  let loader : Name → Option String := (lib[·]?)
  -- `builtin` registrations are trusted only in the toolchain's library, the first root
  let own := Module.fromFirstRoot roots closure
  let init : CommandState ZeroOneMany :=
    { loader, cHeaders := (headers[·]?), cSources := some (Module.cSourceResolver sources),
      includes := some (Module.includeResolver includes),
      trustedModule := own.contains, trustNative := tc.trustNative,
      nativeFuel := tc.nativeFuel.getD NativeRun.defaultFuel, smt := ← tc.smt.resolve }
  let includesResolver := Module.includeResolver includes
  let key := Cache.moduleKey (fun n => if n == mainName then some src else loader n) (headers[·]?) salt mainName
    own.contains includesResolver
  let keyStrong := Cache.moduleKeyStrong (fun n => if n == mainName then some src else loader n)
    (headers[·]?) salt mainName own.contains (strongToolchain := tc.tag) (targetTag := tc.targetTag)
    (includes := includesResolver)
  -- a `link_c` file that appears or disappears changes the check: the key names it by
  -- its module name as written. Its contents do not enter the check (they cannot change
  -- the elaborated result; the link job's key hashes them), and its resolved absolute
  -- path does not either (that would tie the key to where the checkout is).
  let sourceTag := toString ((sources.toList.map (·.1)).toArray.qsort (· < ·))
  let key := mixHash key (hash sourceTag)
  let keyStrong := Smt.Sha256.hexFramed "wiz-cache/grail-link-v1" [keyStrong, sourceTag]
  -- (27a) `--trust-native` changes what a check accepts: its jobs are others
  let key := if tc.trustNative then mixHash key (hash s!"trust-native {init.nativeFuel}") else key
  let keyStrong := if tc.trustNative then
      Smt.Sha256.hexFramed "wiz-cache/grail-native-v1" [keyStrong, toString init.nativeFuel]
    else keyStrong
  -- (28) so do the solver settings
  let key := match Cache.smtKey init.smt with | some k => mixHash key k | none => key
  let keyStrong := match Cache.smtKey init.smt with
    | some k => Smt.Sha256.hexFramed "wiz-cache/grail-smt-v1" [keyStrong, toString k]
    | none => keyStrong
  pure { src, init, key, keyStrong }

/-- Elaborate a loaded file (through the cache when there is one: a write directory and
any read-only ones). With `--region-cache` (`tc.regionCache`), module effects are also
read from and written to `.wizr` regions in the same layers as the `.wizc` entries; the
text entries stay the authority, and a missing or corrupt region is a miss.
With `--region-stats` (`tc.regionStats`) the regions' counters are collected for this
process; `printRegionStats` reports them (zeros when the cache is off). -/
def elaborate (tc : Toolchain) (salt : UInt64) (l : Loaded) : IO (CommandState ZeroOneMany) := do
  match tc.cacheDir, tc.readCaches with
  | none, [] => Cache.elaborateUncached l.src l.init salt
  | write, reads =>
    let region := if tc.regionCache then
        some ({ rig := RigTag.tag (R := ZeroOneMany),
                stats := if tc.regionStats then some regionStats else none } :
          Cache.RegionOptions)
      else none
    pure (← Cache.elaborateCached write reads l.src l.init l.key salt (region := region)
      (verify := (Cache.VerifyMode.ofString? tc.cacheVerify).getD .warn)
      (rig := RigTag.tag (R := ZeroOneMany))
      (strongToolchain := tc.tag) (targetTag := tc.targetTag) (rootTag := l.keyStrong)).1

/-- `--region-stats`: one line for this process (a grail job). Without `--region-cache`
there is no region store and the counters are zero, so a job says so instead of staying
silent. -/
def printRegionStats (tc : Toolchain) : IO Unit := do
  if tc.regionStats then
    let c ← regionStats.get
    IO.println s!"region-stats: hits={c.hits} misses={c.misses} commands={c.commands}"

/-- The messages of a state, rendered `path:line:col: severity: text`. -/
def render (path : String) (l : Loaded) (s : CommandState ZeroOneMany) : String :=
  String.join (s.messages.toList.map fun m => s!"{path}:{m.render l.src}\n")

def hasErrors (s : CommandState ZeroOneMany) : Bool := s.messages.any (·.severity == .error)

/-- Evaluate the global `n : String` in the interpreter. -/
def evalString (s : CommandState ZeroOneMany) (n : Name) : Except String String := do
  let code ← (compileReachable s.globals s.builtins [n]).mapError toString
  match run code [] (.global n) with
  | .stuck m => throw s!"{n} did not evaluate: {m}"
  | v => match v.toString? with
    | some str => pure str
    | none => throw s!"{n} did not evaluate to a string"

end Grail
