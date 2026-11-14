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
  let key := Cache.moduleKey (fun n => if n == mainName then some src else loader n) (headers[·]?) salt mainName
    own.contains (Module.includeResolver includes)
  -- a `link_c` file that appears or disappears changes the check (its contents enter
  -- only the link's key)
  let key := mixHash key (hash (toString ((sources.toList.map fun (k, v) => k ++ "=" ++ v).toArray.qsort (· < ·))))
  -- (27a) `--trust-native` changes what a check accepts: its jobs are others
  let key := if tc.trustNative then mixHash key (hash s!"trust-native {init.nativeFuel}") else key
  -- (28) so do the solver settings
  let key := match Cache.smtKey init.smt with | some k => mixHash key k | none => key
  pure { src, init, key }

/-- Elaborate a loaded file (through the cache when there is one). -/
def elaborate (tc : Toolchain) (salt : UInt64) (l : Loaded) : IO (CommandState ZeroOneMany) := do
  match tc.cacheDir with
  | none => Cache.elaborateUncached l.src l.init salt
  | some dir => pure (← Cache.elaborateCached dir l.src l.init l.key salt).1

/-- The messages of a state, rendered `path:line:col: severity: text`. -/
def render (path : String) (l : Loaded) (s : CommandState ZeroOneMany) : String :=
  String.join (s.messages.toList.map fun m => s!"{path}:{m.render l.src}\n")

def hasErrors (s : CommandState ZeroOneMany) : Bool := s.messages.any (·.severity == .error)

/-- Evaluate the global `n : String` in the interpreter. -/
def evalString (s : CommandState ZeroOneMany) (n : Name) : Except String String := do
  let code ← (compileReachable s.globals s.builtins [n]).mapError toString
  match (run code [] (.global n)).toString? with
  | some str => pure str
  | none => throw s!"{n} did not evaluate to a string"

end Grail
