import Wiz

/-!
# One loader for the test suite's Wiz sources

Every group that elaborates against the library (and, for the Scry groups, the Scry
sources) used to carry its own copy of the same directory walk and file read: eleven
copies under `Tests/`, and a fourth copy of `wizStr`. They all resolve module names the
same way — `lib/Foo.wiz` is `Foo`, `lib/Dir/Bar.wiz` is `Dir.Bar`, and
`scry/src/Scry/Baz.wiz` is `Scry.Baz` — so changes to the layout (a new depth, a new
package root) had to be made everywhere or the copies silently disagreed.

There is now one implementation, and its result is cached for the process lifetime:
the walk and the reads happen once per `(root, prefix)`, and later calls reuse the list
while the files' names, sizes and modification times are unchanged. A test case is its
own process (`Group.run` starts `tests --run-case`), so the cache saves the repeated
loads *within* a case — the Desc sweep and every `runProbe`-style helper call the loader
once per probe — and the single implementation is what keeps the copies from drifting.
-/

namespace Tests

open Wiz

/-- The modules of one root: the import name and the source of each `.wiz` file. -/
abbrev LoadedModules := List (Name × String)

/-- `root`'s `.wiz` files, with the module name each one is imported as:
`root/*.wiz` as `NAME`, `root/DIR/*.wiz` as `DIR.NAME`, prefixed by `pfx`. Sorted by
module name, so a loader's behaviour does not depend on the directory order. -/
private def moduleFiles (root : String) (pfx : String) : IO (List (String × System.FilePath)) := do
  let mut out : Array (String × System.FilePath) := #[]
  for e in ← System.FilePath.readDir root do
    if e.path.extension == some "wiz" then
      out := out.push (pfx ++ e.path.fileStem.getD "", e.path)
    else if ← e.path.isDir then
      for f in ← System.FilePath.readDir e.path do
        if f.path.extension == some "wiz" then
          out := out.push (pfx ++ e.fileName ++ "." ++ f.path.fileStem.getD "", f.path)
  pure ((out.qsort (fun a b => a.1 < b.1)).toList)

/-- A fingerprint of a root's files: their names, sizes and modification times. A cached
load is reused while this is unchanged, so a test that writes a module into a root between
two loads sees the new one. -/
private def moduleStamp (fs : List (String × System.FilePath)) : IO UInt64 := do
  let mut h : UInt64 := 1469598103934665603
  for (n, p) in fs do
    let md ← p.metadata
    h := mixHash h (hash n)
    h := mixHash h md.byteSize
    h := mixHash h md.modified.sec.toNat.toUInt64
    h := mixHash h md.modified.nsec.toUInt64
  pure h

/-- The process-lifetime cache: `(root, prefix)` to the fingerprint and modules it was
loaded from. -/
initialize loaderCache : IO.Ref (Std.HashMap (String × String) (UInt64 × LoadedModules)) ← IO.mkRef {}

/-- The sources of `fs`, by module name. -/
private def readModules (fs : List (String × System.FilePath)) : IO LoadedModules :=
  fs.mapM fun (n, p) => do
    let src ← IO.FS.readFile p
    pure (n, src)

/-- The modules of `root`, with `pfx` prepended to each name. Cached by
`(root, prefix)` and the fingerprint of the files (see `moduleStamp`). -/
def loadedModules (root : String) (pfx : String := "") : IO LoadedModules := do
  let fs ← moduleFiles root pfx
  let stamp ← moduleStamp fs
  let key := (root, pfx)
  let ms ← match (← loaderCache.get).get? key with
    | some (s, ms) => if s == stamp then pure ms else readModules fs
    | none => readModules fs
  loaderCache.modify (·.insert key (stamp, ms))
  pure ms

/-- A loader for several roots: every `(root, prefix)`'s modules, by import name. One
module name must have one source; a later root wins if the names collide. -/
def moduleLoader (roots : List (String × String)) : IO (Name → Option String) := do
  let mut ms : LoadedModules := []
  for (root, pfx) in roots do
    ms := (← loadedModules root pfx) ++ ms
  pure fun n => ms.lookup n

/-- Every module of `lib/` (`lib/Dir/Mod.wiz` is `Dir.Mod`), by import name. -/
def libLoader : IO (Name → Option String) := moduleLoader [("lib", "")]

/-- Every module of `lib/` and of the Scry package (`scry/src/Scry/Mod.wiz` is
`Scry.Mod`): the Scry groups elaborate the lowering they test against both roots. -/
def scryLoader : IO (Name → Option String) :=
  moduleLoader [("lib", ""), ("scry/src/Scry", "Scry.")]

/-- A Wiz string literal for `s` (the escapes the Wiz lexer reads). -/
def wizStr (s : String) : String :=
  "\"" ++ s.foldl (fun acc c => acc ++ match c with
    | '"' => "\\\""
    | '\\' => "\\\\"
    | '\n' => "\\n"
    | '\t' => "\\t"
    | c => c.toString) "" ++ "\""

end Tests
