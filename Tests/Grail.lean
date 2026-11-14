import Tests.Harness
import Wiz
import Grail
import Tests.Elab

/-!
Stage 23: modules by path (23b), per-module cache keys and atomic writes (23c), and
grail, the build tool (23d).
-/

namespace Tests.Grail
open Wiz Tests

/-- A fresh directory with these files in it. -/
def mkTree (files : List (String × String)) : IO System.FilePath := do
  let dir ← IO.FS.createTempDir
  for (p, text) in files do
    let f := dir / p
    if let some d := f.parent then IO.FS.createDirAll d
    IO.FS.writeFile f text
  pure dir

def loaderOf (m : Std.HashMap Name (System.FilePath × String)) : Name → Option String := fun n => (m[n]?).map (·.2)

/-- Every file under `dir`, as (path relative to `root`, modification time, hash of the
contents), sorted by path: a read-only cache must leave this unchanged. The contents are
read as bytes (a `.wizr` region is not UTF-8). -/
partial def snapshotAt (root dir : System.FilePath) : IO (List (String × String × UInt64)) := do
  let mut out := []
  for e in ← dir.readDir do
    if ← e.path.isDir then
      out := out ++ (← snapshotAt root e.path)
    else
      let md ← e.path.metadata
      let bytes ← IO.FS.readBinFile e.path
      let rel := (e.path.toString.drop root.toString.length).toString
      out := out ++ [(rel, s!"{md.modified.sec}.{md.modified.nsec}", hash bytes.toList)]
  pure out

def snapshot (dir : System.FilePath) : IO (List (String × String × UInt64)) := do
  pure ((← snapshotAt dir dir).mergeSort (fun a b => a.1 < b.1))

/-- A digest of one cached effect, for comparing the text path with the region path
(the effect types have no `BEq`: terms are not compared structurally). -/
def effectSig (e : Cache.Effect ZeroOneMany) : String :=
  s!"{e.decls.toList.map (·.name)}|{e.messages.toList.map (·.text)}|{e.infos.size}|" ++
  s!"{e.sites.size}|{e.docs.size}|{e.instances.size}|{e.builtins.length}"

def effectSigs (es : Array (Cache.Effect ZeroOneMany)) : List String := es.toList.map effectSig

/-- The `.wizr` module regions in a cache directory. -/
def regionFiles (cache : System.FilePath) : IO (Array System.FilePath) := do
  let entries ← cache.readDir
  pure (entries.filter (fun e => e.fileName.endsWith ".wizr") |>.map (·.path))

/-- A small library: `Data.Two` (in a subdirectory) imports `Prelude`; `Use` imports it. -/
def libFiles : List (String × String) :=
  [("Data/Two.wiz", "import Prelude\ndef two : Nat := 2\n"),
   ("Use.wiz", "import Data.Two\ndef four : Nat := two + two\n"),
   ("Other.wiz", "import Prelude\ndef one : Nat := 1\n")]

def modulesGroup : Group where
  name := "modules"
  parallel := true
  exercise := "Stage 23b–c"
  cases := [
    { name := "dotted names are paths", run := fun _ => do
        checkEq "A/B/C.wiz" (Module.relPath "A.B.C").toString
        checkEq "A.B" (Module.nameOf "A/B.wiz")
        checkEq ["Prelude", "Data.Two"] (Module.importsOf "import Prelude\n-- c\n  import Data.Two\nimport_c \"m.h\"\ndef x := 1\n")
        checkEq ["m.h"] (Module.headersOf "import_c \"m.h\" (pure)\n") },
    { name := "a file reaches modules in subdirectories", run := fun _ => do
        let dir ← mkTree libFiles
        let ms ← Module.loadClosure ["lib", dir] "import Use\n#eval four\n"
        checkEq ["Data.Two", "Prelude", "Use"] (ms.toList.map (·.1) |>.toArray.qsort (· < ·)).toList
        let s := runFrontend (R := ZeroOneMany) "import Use\n#eval four\n" { trustedModule := Tests.libModule, loader := loaderOf ms }
        checkEq "[2:1: info: 4]" (toString (s.messages.toList.map (·.render "import Use\n#eval four\n")))
        let all ← Module.listRoot dir
        checkEq #["Data.Two", "Other", "Use"] (all.map (·.1)) },
    { name := "a module's key changes with it and with what it imports, only", run := fun _ => do
        let dir ← mkTree libFiles
        let keys (dir : System.FilePath) : IO (Std.HashMap Name UInt64) := do
          let ms ← Module.loadAll ["lib", dir]
          pure (Cache.moduleKeys (loaderOf ms) (fun _ => none) 0 ["Use", "Other", "Data.Two"])
        let k1 ← keys dir
        IO.FS.writeFile (dir / "Data/Two.wiz") "import Prelude\ndef two : Nat := 1 + 1\n"
        let k2 ← keys dir
        check (k1["Data.Two"]? != k2["Data.Two"]?) "the edited module kept its key"
        check (k1["Use"]? != k2["Use"]?) "its importer kept its key"
        checkEq k1["Other"]? k2["Other"]?
        checkEq k1["Prelude"]? k2["Prelude"]?
        -- the toolchain enters every key
        let ms ← Module.loadAll ["lib", dir]
        check (Cache.moduleKey (loaderOf ms) (fun _ => none) 0 "Other" != Cache.moduleKey (loaderOf ms) (fun _ => none) 1 "Other")
          "the toolchain is not in the key" },
    { name := "the isolated-module key has the proof marker's options (strictProofs, proofSteps, traceProofSteps)", run := fun _ => do
        -- a module elaborated in isolation is kept per process under `isoKey`: a module kept
        -- under one setting must not be replayed under another
        let loader : Name → Option String := fun n => if n == "M" then some "def x : Unit := ()\n" else none
        let base (g : Globals ZeroOneMany) : CommandState ZeroOneMany := { loader, globals := g }
        let g0 : Globals ZeroOneMany := {}
        let k0 := isoKey (base g0) "M"
        check k0.isSome "the module has no isolated key"
        checkEq k0 (isoKey (base g0) "M")
        for (what, g) in [("strictProofs", { g0 with strictProofs := true }),
                          ("proofSteps", { g0 with proofSteps := g0.proofSteps + 1 }),
                          ("traceProofSteps", { g0 with traceProofSteps := true })] do
          check (isoKey (base g) "M" != k0) s!"{what} is not in the isolated-module key"
          -- and on a warm cache (`M` kept under the defaults) the other setting elaborates
          -- `M` itself, with the same result here
          let s0 := runFrontend (R := ZeroOneMany) "import M\n" (base g0)
          let s1 := runFrontend (R := ZeroOneMany) "import M\n" (base g)
          check (s0.messages.isEmpty && s1.messages.isEmpty) s!"{what}: importing M reports {s1.messages.toList.map (·.text)}" },
    { name := "a module is cached once, for every file that imports it", run := fun _ => do
        let dir ← mkTree libFiles
        let cache ← IO.FS.createTempDir
        let ms ← Module.loadAll ["lib", dir]
        let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, loader := loaderOf ms }
        let (_, h1) ← Cache.elaborateCached (some cache) [] "import Data.Two\ndef a : Nat := two\n" init 0
        checkEq 0 h1
        -- another file: the modules come from the cache (Prelude's commands, and `two`)
        let (s, h2) ← Cache.elaborateCached (some cache) [] "import Use\ndef b : Nat := four\n" init 0
        check s.messages.isEmpty s!"messages: {s.messages.toList.map (·.text)}"
        check (h2 > 100) s!"only {h2} commands came from the cache"
        -- no temporary files are left behind
        for e in ← cache.readDir do
          check ((e.fileName.splitOn ".tmp").length == 1) s!"left behind: {e.fileName}" },
    { name := "a layered cache: write shadows reads, reads in order, misses and corruption fall through", run := fun _ => do
        let binary : UInt64 := 11
        let k : UInt64 := 4242
        let e (tag : String) : Cache.Effect ZeroOneMany := { cCode := #[tag] }
        let tag (o : Option (Cache.Effect ZeroOneMany)) : Option String := o.bind fun e => e.cCode.toList.head?
        let write ← IO.FS.createTempDir
        let r1 ← IO.FS.createTempDir
        let r2 ← IO.FS.createTempDir
        let name := s!"{mixHash binary k}.wizc"
        IO.FS.writeFile (r1 / name) (e "r1").toSx.render
        IO.FS.writeFile (r2 / name) (e "r2").toSx.render
        let store ← Cache.Store.layered (R := ZeroOneMany) (some write) [r1, r2] binary
        -- the write cache shadows a stale read cache; reads are searched in order
        checkEq (some "r1") (tag (← store.get k))
        store.put k (e "write")
        checkEq (some "write") (tag (← store.get k))
        IO.FS.removeFile (write / name)
        checkEq (some "r1") (tag (← store.get k))
        IO.FS.removeFile (r1 / name)
        checkEq (some "r2") (tag (← store.get k))
        -- an unparsable entry is a miss, not an error
        IO.FS.writeFile (r1 / name) "(this is not an effect"
        checkEq (some "r2") (tag (← store.get k))
        IO.FS.removeFile (r2 / name)
        checkEq (none : Option String) (tag (← store.get k))
        IO.FS.writeFile (write / name) "garbage"
        IO.FS.writeFile (r2 / name) (e "r2").toSx.render
        checkEq (some "r2") (tag (← store.get k))
        store.put k (e "again")
        checkEq (some "again") (tag (← store.get k))
        -- a store with no write cache writes nowhere (put is a no-op)
        let before ← snapshot r1
        let roStore ← Cache.Store.layered (R := ZeroOneMany) none [r1] binary
        roStore.put k (e "nowhere")
        checkEq (repr before).pretty (repr (← snapshot r1)).pretty
        checkEq (none : Option String) (tag (← roStore.get k))
        -- seen: a marker in any cache; markSeen: only the write cache (or memory)
        let k2 : UInt64 := 777
        IO.FS.writeFile (r2 / s!"{mixHash binary k2}.wizm") "M"
        checkEq true (← store.seen k2)
        checkEq false (← store.seen 778)
        checkEq (repr before).pretty (repr (← snapshot r1)).pretty
        let memory ← Cache.Store.layered (R := ZeroOneMany) none [] binary
        checkEq false (← memory.seen 779)
        memory.markSeen 779 "M"
        checkEq true (← memory.seen 779) },
    { name := "a read-only cache replays modules and is never written", run := fun _ => do
        let ms ← Module.loadAll ["lib"]
        let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, loader := loaderOf ms }
        let src := "import Prelude\ndef a : Nat := 1 + 1\n#eval a\n"
        let ro ← IO.FS.createTempDir
        let (_, h0) ← Cache.elaborateCached (some ro) [] src init 0 (binary := some 1)
        checkEq 0 h0
        let before ← snapshot ro
        -- only a read cache: modules replay, nothing errors, nothing is written
        let (s1, h1) ← Cache.elaborateCached none [ro] src init 0 (binary := some 1)
        check (h1 > 0) "nothing came from the read-only cache"
        check (!s1.messages.any (·.severity == .error)) s!"messages: {s1.messages.toList.map (·.text)}"
        checkEq (repr before).pretty (repr (← snapshot ro)).pretty
        -- with a write cache too: the read cache still stays as it was, and the new
        -- entries land only in the write cache
        let write ← IO.FS.createTempDir
        let src2 := src ++ "def extra : Nat := 7\n#eval extra\n"
        let (s2, h2) ← Cache.elaborateCached (some write) [ro] src2 init 0 (binary := some 1)
        check (h2 > 0) "nothing came from the read-only cache"
        check (!s2.messages.any (·.severity == .error)) s!"messages: {s2.messages.toList.map (·.text)}"
        checkEq (repr before).pretty (repr (← snapshot ro)).pretty
        checkEq (repr ((runFrontend src2 init).messages.toList.map (·.render src2))).pretty
          (repr (s2.messages.toList.map (·.render src2))).pretty
        check ((← write.readDir).size > 0) "nothing was written to the write cache"
        for entry in ← write.readDir do
          check (!(← (ro / entry.fileName).pathExists)) s!"also written to the read-only cache: {entry.fileName}" },
    { name := "the command line: a warm and an empty read-only cache plus a write cache match --no-cache", run := fun _ => do
        let wiz := ((← IO.appPath).parent.getD ".") / "wiz"
        unless ← wiz.pathExists do skip "no wiz binary"; return
        let dir ← mkTree [("main.wiz", "import M\ndef n : Nat := two + 3\n#eval n\n"),
                          ("M.wiz", "import Prelude\ndef two : Nat := 2\n")]
        let ro := dir / "ro"
        IO.FS.createDirAll ro
        let empty := dir / "empty"
        IO.FS.createDirAll empty
        let write := dir / "write"
        let run (args : List String) : IO IO.Process.Output :=
          IO.Process.output { cmd := wiz.toString, args := args.toArray, cwd := some dir }
        let base := ["check", "main.wiz", "-I", "."]
        let cold ← run (["--cache", ro.toString] ++ base)
        checkEq 0 cold.exitCode
        check ((cold.stdout.splitOn "info: 5").length > 1) s!"cold: {cold.stdout}{cold.stderr}"
        let before ← snapshot ro
        let cached ← run (["--cache-ro", ro.toString, "--cache-ro", empty.toString, "--cache", write.toString] ++ base)
        let plain ← run (["--no-cache"] ++ base)
        checkEq 0 cached.exitCode
        checkEq plain.exitCode cached.exitCode
        checkEq plain.stdout cached.stdout
        checkEq plain.stderr cached.stderr
        checkEq (repr before).pretty (repr (← snapshot ro)).pretty
        check ((← write.readDir).size > 0) "the write cache stayed empty" },
    { name := "editing a module re-elaborates only it and what imports it", run := fun _ => do
        let dir ← mkTree libFiles
        let cache ← IO.FS.createTempDir
        let elabSrc (src : String) : IO Nat := do
          let ms ← Module.loadAll ["lib", dir]
          let (s, h) ← Cache.elaborateCached (some cache) [] src ({ trustedModule := Tests.libModule, loader := loaderOf ms } : CommandState ZeroOneMany) 0
          check (!s.messages.any (·.severity == .error)) s!"messages: {s.messages.toList.map (·.text)}"
          pure h
        let src := "import Use\nimport Other\ndef c : Nat := four + one\n"
        let _ ← elabSrc src
        let warm ← elabSrc src
        IO.FS.writeFile (dir / "Data/Two.wiz") "import Prelude\ndef two : Nat := 1 + 1\n"
        let after ← elabSrc src
        -- Prelude and Other still come from the cache; Data.Two, Use and `c` don't
        check (after + 3 ≤ warm) s!"{after} hits after the edit, {warm} before"
        check (after + 10 ≥ warm) s!"{after} hits after the edit, {warm} before: too much was redone" },
    { name := "a module sees only what it imports (with the cache)", run := fun _ => do
        let dir ← mkTree [("Sneaky.wiz", "def three : Nat := 3\n")]
        let ms ← Module.loadAll ["lib", dir]
        let cache ← IO.FS.createTempDir
        let (s, _) ← Cache.elaborateCached (some cache) [] "import Prelude\nimport Sneaky\n" ({ trustedModule := Tests.libModule, loader := loaderOf ms } : CommandState ZeroOneMany) 0
        check (s.messages.any fun m => (m.text.splitOn "module Sneaky has errors").length > 1)
          s!"Sneaky used Nat without importing Prelude: {s.messages.toList.map (·.text)}" },
    { name := "without the cache too", run := fun _ => do
        let dir ← mkTree [("Sneaky.wiz", "def three : Nat := 3\n")]
        let ms ← Module.loadAll ["lib", dir]
        let s ← Cache.elaborateUncached "import Prelude\nimport Sneaky\n" ({ trustedModule := Tests.libModule, loader := loaderOf ms } : CommandState ZeroOneMany)
        check (s.messages.any fun m => (m.text.splitOn "module Sneaky has errors").length > 1)
          s!"Sneaky used Nat without importing Prelude: {s.messages.toList.map (·.text)}"
        let ms ← Module.loadAll ["lib"]
        let s ← Cache.elaborateUncached "import Std\ndef n : Nat := 2 + 2\n" ({ trustedModule := Tests.libModule, loader := loaderOf ms } : CommandState ZeroOneMany)
        check s.messages.isEmpty s!"messages: {s.messages.toList.map (·.text)}" },
    { name := "a module sees only what it imports (the frontend and the language server too)", run := fun _ => do
        let dir ← mkTree [("Sneaky.wiz", "def three : Nat := 3\n"), ("Fine.wiz", "import Prelude\ndef three : Nat := 3\n")]
        let ms ← Module.loadAll ["lib", dir]
        let sneaky (s : CommandState ZeroOneMany) : Bool :=
          s.messages.any fun m => (m.text.splitOn "module Sneaky has errors").length > 1
        let src := "import Prelude\nimport Sneaky\n"
        let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := loaderOf ms }
        check (sneaky s) s!"runFrontend: Sneaky used Nat without importing Prelude: {s.messages.toList.map (·.text)}"
        let s := runFrontend (R := ZeroOneMany) ("import Prelude\ndef two : Nat := 2\nimport Sneaky\n") { trustedModule := Tests.libModule, loader := loaderOf ms }
        check (sneaky s) s!"runFrontend, after a definition: {s.messages.toList.map (·.text)}"
        let (s, _) := Query.elaborate (R := ZeroOneMany) {} src { trustedModule := Tests.libModule, loader := loaderOf ms, termInfo := true }
        check (sneaky s) s!"the language server's engine: {s.messages.toList.map (·.text)}"
        -- through the server: the diagnostic is at the import
        let srv : LSP.Server := { libs := ms.fold (fun m k (p, t) => m.insert k (p.toString, t)) {}, trusted := ["Prelude"] }
        let (_, out) := LSP.handle srv (Lean.Json.mkObj [("jsonrpc", "2.0"), ("method", "textDocument/didOpen"),
          ("params", Lean.Json.mkObj [("textDocument", Lean.Json.mkObj [("uri", "file:///t.wiz"), ("text", src)])])])
        check ((out[0]!.compress.splitOn "module Sneaky has errors").length > 1) s!"diagnostics: {out[0]!.compress}"
        -- a module that imports what it uses is fine, and its declarations are seen
        let s := runFrontend (R := ZeroOneMany) "import Prelude\nimport Fine\n#eval three\n" { trustedModule := Tests.libModule, loader := loaderOf ms }
        checkEq "[3:1: info: 3]" (toString (s.messages.toList.map (·.render "import Prelude\nimport Fine\n#eval three\n"))) },
    { name := "two modules declaring one name: an error at the import, whatever the path or order", run := fun _ => do
        -- wiz-notes/soundness-probes/is-import-shadowing: M.A's `pa : b = true` was checked
        -- against its own `b`; with M.B's `b := false` replacing it, `pa` proved `false = true`
        let dir ← mkTree [
          ("M/Base.wiz", "inductive Bool where\n  | true\n  | false\ninductive Empty where\n"),
          ("M/A.wiz", "import M.Base\ndef b : Bool := Bool.true\ndef pa : b = Bool.true := refl Bool.true\n"),
          ("M/B.wiz", "import M.Base\ndef b : Bool := Bool.false\ndef pb : b = Bool.false := refl Bool.false\n"),
          ("M/C.wiz", "import M.A\ndef c : Bool := b\n"),
          ("M/D.wiz", "import M.B\ndef d : Bool := b\n"),
          ("M/E.wiz", "import M.Base\ndef e0 : Bool := Bool.false\n")]
        let ms ← Module.loadAll [dir]
        let init : CommandState ZeroOneMany := { loader := loaderOf ms }
        let cache ← IO.FS.createTempDir
        let boomA := "def e : Bool.false = Bool.true := pa\ndef boom : Empty := absurd e.1\n"
        let boomB := "def e : Bool.true = Bool.false := pb\ndef boom : Empty := absurd e.1\n"
        -- every way a file is elaborated: wiz check (cold and warm cache, no cache), the
        -- frontend, the language server's engine
        let paths (src : String) : IO (List (String × CommandState ZeroOneMany)) := do
          let cold := (← Cache.elaborateCached (some cache) [] src init 0).1
          let warm := (← Cache.elaborateCached (some cache) [] src init 0).1
          pure [("cold cache", cold), ("warm cache", warm), ("no cache", ← Cache.elaborateUncached src init),
                ("runFrontend", runFrontend src init), ("Query", (Query.elaborate {} src { init with termInfo := true }).1)]
        let clash (s : CommandState ZeroOneMany) : Bool := s.messages.any fun m =>
          -- (one message, at the import, on every path: not inside "module … has errors")
          m.severity == .error && m.text.startsWith "'b' is declared by both"
        for src in ["import M.A\nimport M.B\n" ++ boomA, "import M.B\nimport M.A\n" ++ boomB,
                    "import M.A\nimport M.D\n" ++ boomA, "import M.A\nimport M.D\n" ++ boomB,
                    "import M.C\nimport M.B\n" ++ boomA, "import M.Base\ndef b : Bool := Bool.false\nimport M.A\n" ++ boomA,
                    "import M.A\ndef b : Bool := Bool.false\n" ++ boomA] do
          for (how, s) in ← paths src do
            check (clash s) s!"{how}: no clash reported for\n{src}\n{s.messages.toList.map (·.text)}"
            check (!s.globals.contains "boom") s!"{how}: boom : Empty was accepted for\n{src}"
        -- the message names both modules
        let (s, _) ← Cache.elaborateCached (some cache) [] "import M.A\nimport M.B\n" init 0
        check (s.messages.any fun m => m.text == "'b' is declared by both module M.A and module M.B")
          s!"{s.messages.toList.map (·.text)}"
        for (how, s) in ← paths "import M.A\ndef b : Bool := Bool.false\n" do
          check (s.messages.any fun m => m.text == "'b' is declared by both module M.A and this file")
            s!"{how}: {s.messages.toList.map (·.text)}"
        for (how, s) in ← paths "import M.B\nimport M.C\n" do
          check (s.messages.any fun m => m.text == "'b' is declared by both module M.B and module M.A")
            s!"{how}: {s.messages.toList.map (·.text)}"
        -- one module reached by two paths (a diamond) is fine
        for src in ["import M.A\nimport M.C\nimport M.Base\n#eval c\n", "import M.A\nimport M.E\n#eval e0\n",
                    "import M.E\nimport M.C\n#eval c\n"] do
          for (how, s) in ← paths src do
            check (!s.messages.any (·.severity == .error)) s!"{how}: diamond {src}: {s.messages.toList.map (·.text)}"
            check (s.globals.contains "pa" && s.globals.contains "Bool.true") s!"{how}: diamond lost declarations"
        -- the language server re-elaborating a file after an edit (the engine reused)
        let src := "import M.A\nimport M.E\ndef x : Bool := b\n"
        let (s₁, eng) := Query.elaborate (R := ZeroOneMany) {} src { init with termInfo := true }
        let (s₂, eng) := Query.elaborate eng src { init with termInfo := true }
        let (s₃, _) := Query.elaborate eng (src ++ "def y : Bool := x\n") { init with termInfo := true }
        for s in [s₁, s₂, s₃] do
          check (!s.messages.any (·.severity == .error)) s!"re-elaboration: {s.messages.toList.map (·.text)}"
        -- a module whose dependency changed is elaborated again, not replayed from the
        -- cache: M.A's `pa` no longer holds once its `b` is `false`
        let src := "import M.A\n" ++ boomA
        let (s, _) ← Cache.elaborateCached (some cache) [] src init 0
        check (s.messages.any (·.severity == .error)) "pa : false = true with b = true"
        let ms' := ms.insert "M.A" (dir / "M/A.wiz", "import M.Base\ndef b : Bool := Bool.false\ndef pa : b = Bool.true := refl Bool.true\n")
        let (s, _) ← Cache.elaborateCached (some cache) [] src { init with loader := loaderOf ms' } 0
        check (s.messages.any fun m => (m.text.splitOn "module M.A has errors").length > 1)
          s!"the changed M.A was replayed: {s.messages.toList.map (·.text)}"
        check (!s.globals.contains "boom") "boom accepted after M.A changed" },
    { name := "private names are per module: two modules' private helpers don't clash (13b)", run := fun _ => do
        let dir ← mkTree [
          ("P/A.wiz", "import Prelude\nprivate def helper : Nat := 1\nprivate def Nat.twice (n : Nat) : Nat := Nat.add n n\n" ++
                      "private def count : Nat → Nat\n  | .zero => 0\n  | .succ n => Nat.add (count n) 1\n" ++
                      "def fa : Nat := Nat.add helper (Nat.add (count 3) helper.twice)\n"),
          ("P/B.wiz", "import Prelude\nprivate def helper : Nat := 10\nprivate def Nat.twice (n : Nat) : Nat := Nat.mul n 3\n" ++
                      "def fb : Nat := Nat.add helper helper.twice\n")]
        let ms ← Module.loadAll ["lib", dir]
        let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, loader := loaderOf ms }
        let cache ← IO.FS.createTempDir
        let paths (src : String) : IO (List (String × CommandState ZeroOneMany)) := do
          let cold := (← Cache.elaborateCached (some cache) [] src init 0).1
          let warm := (← Cache.elaborateCached (some cache) [] src init 0).1
          pure [("cold cache", cold), ("warm cache", warm), ("no cache", ← Cache.elaborateUncached src init),
                ("runFrontend", runFrontend src init), ("Query", (Query.elaborate {} src { init with termInfo := true }).1)]
        let src := "import P.A\nimport P.B\n#eval fa\n#eval fb\ndef helper : Nat := 5\n#eval helper\n"
        for (how, s) in ← paths src do
          checkEq (how, "[3:1: info: 6, 4:1: info: 40, 6:1: info: 5]") (how, toString (s.messages.toList.map (·.render src)))
        -- still private: elsewhere the name is unknown, with the module named
        let src := "import P.A\ndef x : Nat := helper\n"
        for (how, s) in ← paths src do
          check (s.messages.any fun m => (m.text.splitOn "'helper' is private to module P.A").length > 1)
            s!"{how}: {s.messages.toList.map (·.text)}" },
    { name := "private types are per module too: two modules' private Color, Pt, Sz, Sig coexist (13b)", run := fun _ => do
        let dir ← mkTree [("Q/A.wiz", "import Prelude\nimport Deriving\nprivate inductive Color where\n  | red\n  | blue\n  deriving Repr, BEq\nprivate structure Pt where\n  x : Nat\n  y : Nat\nprivate class Sz (A : Type) where\n  size : A → Nat\ninstance : Sz Color := Sz.mk (fun c => match c with\n  | .red => 1\n  | Color.blue => 2)\nprivate def Color.code (c : Color) : Nat := Sz.size c\nprivate def Pt.sum (p : Pt) : Nat := Nat.add p.x p.y\nprivate coinductive Sig where\n  head : Nat\n  tail : Sig\nprivate def Sig.const (n : Nat) : Sig\n  | .head => n\n  | .tail => Sig.const n\nprivate def pick : Color → Pt\n  | .red => Pt.mk 1 2\n  | Color.blue => Pt.mk 3 4\nprivate def useDot (c : Color) (p : Pt) (s : Sig) : Nat := Nat.add c.code (Nat.add (Pt.sum p) s.tail.head)\ndef fa : Nat := useDot Color.blue (pick Color.blue) (Sig.const 100)\ndef ra : String := Repr.repr Color.red\ndef qa : Bool := BEq.beq Color.red Color.blue\ndef favA : Color := Color.red\n"), ("Q/B.wiz", "import Prelude\nimport Deriving\nprivate inductive Color where\n  | red\n  | blue\n  deriving Repr, BEq\nprivate structure Pt where\n  x : Nat\n  y : Nat\nprivate class Sz (A : Type) where\n  size : A → Nat\ninstance : Sz Color := Sz.mk (fun c => match c with\n  | .red => 10\n  | Color.blue => 20)\nprivate def Color.code (c : Color) : Nat := Sz.size c\nprivate def Pt.sum (p : Pt) : Nat := Nat.add p.x p.y\nprivate coinductive Sig where\n  head : Nat\n  tail : Sig\nprivate def Sig.const (n : Nat) : Sig\n  | .head => n\n  | .tail => Sig.const n\nprivate def pick : Color → Pt\n  | .red => Pt.mk 1 2\n  | Color.blue => Pt.mk 30 40\nprivate def useDot (c : Color) (p : Pt) (s : Sig) : Nat := Nat.add c.code (Nat.add (Pt.sum p) s.tail.head)\ndef fb : Nat := useDot Color.blue (pick Color.blue) (Sig.const 1000)\ndef rb : String := Repr.repr Color.blue\n")]
        let ms ← Module.loadAll ["lib", dir]
        let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, loader := loaderOf ms }
        let cache ← IO.FS.createTempDir
        let paths (src : String) : IO (List (String × CommandState ZeroOneMany)) := do
          let cold := (← Cache.elaborateCached (some cache) [] src init 0).1
          let warm := (← Cache.elaborateCached (some cache) [] src init 0).1
          pure [("cold cache", cold), ("warm cache", warm), ("no cache", ← Cache.elaborateUncached src init),
                ("runFrontend", runFrontend src init), ("Query", (Query.elaborate {} src { init with termInfo := true }).1)]
        -- (the importer may have a `Color` of its own)
        let src := "import Q.A\nimport Q.B\n#eval fa\n#eval fb\n#eval ra\n#eval rb\n#eval qa\ninductive Color where\n  | green\n#check Color.green\n"
        for (how, s) in ← paths src do
          checkEq (how, "[3:1: info: 109, 4:1: info: 1090, 5:1: info: \"Color.red\", 6:1: info: \"Color.blue\", 7:1: info: .false, 10:1: info: Color.green : Color]")
            (how, toString (s.messages.toList.map (·.render src)))
        -- still private: elsewhere the names are unknown, with the module named
        for (bad, what) in [("def x := Color.red", "'Color.red'"), ("def x (p : Pt) : Nat := 0", "'Pt'"),
                            ("def x := @Sig.const", "'Sig.const'")] do
          let src := "import Q.A\n" ++ bad ++ "\n"
          for (how, s) in ← paths src do
            check (s.messages.any fun m => (m.text.splitOn s!"{what} is private to module Q.A").length > 1)
              s!"{how}: {bad}: {s.messages.toList.map (·.text)}"
        -- hovers and messages show the source name
        let src := "import Q.A\ndef h := favA\ndef n : Nat := favA\n"
        let (s, _) := Query.elaborate (R := ZeroOneMany) {} src { init with termInfo := true }
        checkEq (some ("favA", "Color")) (Query.hoverAt s 21)
        check (s.messages.any fun m => (m.text.splitOn "inferred: Color").length > 1) s!"{s.messages.toList.map (·.text)}" },
    { name := "a private mutual block's constructors are named per type (Ev.s, Od.s) and private (13b)", run := fun _ => do
        let dir ← mkTree [("Q/M.wiz", "import Prelude\nimport Deriving\nprivate mutual\ninductive Ev where\n  | z\n  | s (o : Od)\n  deriving Repr\ninductive Od where\n  | s (e : Ev)\nend\nprivate mutual\ndef evN : Ev → Nat\n  | .z => 0\n  | Ev.s o => Nat.succ (odN o)\ndef odN : Od → Nat\n  | .s e => Nat.succ (evN e)\nend\ndef three : Nat := odN (Od.s (Ev.s (.s .z)))\ndef shown : String := Repr.repr (Ev.s (Od.s Ev.z))\n")]
        let ms ← Module.loadAll ["lib", dir]
        let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, loader := loaderOf ms }
        let cache ← IO.FS.createTempDir
        let paths (src : String) : IO (List (String × CommandState ZeroOneMany)) := do
          let cold := (← Cache.elaborateCached (some cache) [] src init 0).1
          let warm := (← Cache.elaborateCached (some cache) [] src init 0).1
          pure [("cold cache", cold), ("warm cache", warm), ("no cache", ← Cache.elaborateUncached src init),
                ("runFrontend", runFrontend src init)]
        let src := "import Q.M\n#eval three\n#eval shown\ndef x := Od.s\n"
        for (how, s) in ← paths src do
          checkEq (how, "[2:1: info: 3, 3:1: info: \"Ev.s (Od.s Ev.z)\", 4:10: error: 'Od.s' is private to module Q.M]")
            (how, toString (s.messages.toList.map (·.render src))) },
    { name := "trust is part of a module's cache key (22f)", run := fun _ => do
        -- the same Prelude, elaborated as untrusted and as trusted through one cache: the
        -- warnings and `#print axioms` of the one run are never replayed in the other
        let cache ← IO.FS.createTempDir
        let ms ← Module.loadAll ["lib"]
        let src := "import Prelude\ndef y : Nat := 2 + 2\n#print axioms y\n"
        let run (trusted : Name → Bool) : IO (CommandState ZeroOneMany) := do
          pure (← Cache.elaborateCached (some cache) [] src ({ trustedModule := trusted, loader := loaderOf ms } : CommandState ZeroOneMany) 0).1
        let unchecked (s : CommandState ZeroOneMany) : Nat :=
          (s.messages.filter fun m => (m.text.splitOn "is not checked").length > 1).size
        let axiomsOf (s : CommandState ZeroOneMany) : String :=
          ((s.messages.find? fun m => (m.text.splitOn "'y'").length > 1).map (·.text)).getD "?"
        for _ in [0:2] do
          let s ← run (fun _ => false)
          check (unchecked s > 10) s!"untrusted: {unchecked s} unchecked builtins reported"
          check (((axiomsOf s).splitOn "depends on axioms").length > 1) s!"untrusted: {axiomsOf s}"
          let s ← run Tests.libModule
          checkEq 0 (unchecked s)
          checkEq "'y' does not depend on any axioms" (axiomsOf s) },
    { name := "the toolchain's library is the first root, and nothing replaces its modules (22f)", run := fun _ => do
        let dir ← mkTree [("Prelude.wiz", "builtin nat.add := Nat.mul\n"), ("Fake.wiz", "import Prelude\ndef f : Nat := 1\n")]
        let roots : List System.FilePath := [← Module.toolchainLib, dir]
        checkEq (← IO.FS.realPath "lib") (← IO.FS.realPath roots.head!)
        let ms ← Module.loadClosure roots "import Fake\n"
        checkEq (some (roots.head! / "Prelude.wiz")) (ms["Prelude"]?.map (·.1))
        checkEq ["Prelude"] ((Module.fromFirstRoot roots ms).toArray.qsort (· < ·)).toList
        checkEq [("Prelude", dir / "Prelude.wiz")] (← Module.shadowed roots ms) },
    { name := "another checkout's lib/ in the current directory is not a root (22f)", run := fun _ => do
        -- run inside another checkout, every module of its `lib/` was reported as shadowed
        let dir ← mkTree [("lib/Prelude.wiz", "builtin nat.add := Nat.mul\n"), ("Extra/Mod.wiz", "import Prelude\ndef m : Nat := 1\n")]
        let roots ← Module.roots [dir / "Extra"]
        checkEq [← IO.FS.realPath "lib", dir / "Extra"] [← IO.FS.realPath roots.head!, roots[1]!]
        checkEq 2 roots.length
        let ms ← Module.loadClosure roots "import Mod\n"
        checkEq ([] : List (Name × System.FilePath)) (← Module.shadowed roots ms) },
    { name := "an import cycle is an error, not a hang", run := fun _ => do
        let dir ← mkTree [("A.wiz", "import B\n"), ("B.wiz", "import A\n")]
        let ms ← Module.loadAll [dir]
        let cache ← IO.FS.createTempDir
        let (s, _) ← Cache.elaborateCached (some cache) [] "import A\n" ({ trustedModule := Tests.libModule, loader := loaderOf ms } : CommandState ZeroOneMany) 0
        check (s.messages.any fun m => (m.text.splitOn "import cycle").length > 1)
          s!"messages: {s.messages.toList.map (·.text)}"
        let s := runFrontend (R := ZeroOneMany) "import A\n" { trustedModule := Tests.libModule, loader := loaderOf ms }
        check (s.messages.any fun m => (m.text.splitOn "import cycle").length > 1)
          s!"runFrontend: {s.messages.toList.map (·.text)}" },
    { name := "a module region round-trips (one artifact per module, tags checked)", run := fun _ => do
        -- (`--region-cache`: the module's effects as one mmap'able artifact)
        let dir ← mkTree [("M.wiz", "import Prelude\ndef x : Nat := 1 + 1\ndef y : Nat := x + x\n")]
        let ms ← Module.loadAll ["lib", dir]
        let cache ← IO.FS.createTempDir
        let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, loader := loaderOf ms }
        let rig := RigTag.tag (R := ZeroOneMany)
        let (s, _) ← Cache.elaborateCached (some cache) [] "import M\n#eval y\n" init 0 (region := some { rig })
        check (!s.messages.any (·.severity == .error)) s!"messages: {s.messages.toList.map (·.text)}"
        let binary ← Cache.binaryId (some cache)
        let k := Cache.moduleKey (loaderOf ms) (fun _ => none) 0 "M" (trusted := Tests.libModule)
        -- one region for the module, not one per command
        let regs ← regionFiles cache
        checkEq 1 (regs.filter (fun p => p.fileName == some (Cache.regionFileName binary k))).size
        let some a ← Cache.readModuleRegion (R := ZeroOneMany) cache binary rig k
          | throw (IO.userError "M has no region")
        checkEq "M" a.module
        checkEq k a.key
        checkEq Cache.regionFormat a.format
        checkEq Cache.salt a.textSalt
        checkEq Cache.regionMagic a.magic
        check (a.effects.size > 0) "the region holds no effects"
        check (!a.complete) "M imports Prelude, so it is not complete"
        check (a.rerun.size > 0) "M's import is not recorded for the rerun path"
        -- (a pure cache: write the effects back out and read them; every field survives)
        let dir2 ← IO.FS.createTempDir
        Cache.writeModuleRegion dir2 binary rig (k + 1) "M" a.effects a.keys a.complete a.rerun
        let some b ← Cache.readModuleRegion (R := ZeroOneMany) dir2 binary rig (k + 1)
          | throw (IO.userError "the region written for M does not read back")
        checkEq (effectSigs a.effects) (effectSigs b.effects)
        checkEq a.keys.toList b.keys.toList
        checkEq a.effects.size a.keys.size
        checkEq (k + 1) b.key
        -- (the tags are checked: another rig, format or key is not this module's artifact)
        check (b.fits binary (k + 1) rig) "a region does not fit itself"
        check (!(b.fits binary (k + 1) "nat")) "the rig is not checked"
        check (!(b.fits binary (k + 2) rig)) "the key is not checked"
        let badFormat : Cache.ModuleArtifact ZeroOneMany := { b with format := 999 }
        check (!(badFormat.fits binary (k + 1) rig)) "the format is not checked"
        let badBinary : Cache.ModuleArtifact ZeroOneMany := { b with binary := binary + 1 }
        check (!(badBinary.fits binary (k + 1) rig)) "the binary is not checked"
        let badSalt : Cache.ModuleArtifact ZeroOneMany := { b with textSalt := Cache.salt + 1 }
        check (!(badSalt.fits binary (k + 1) rig)) "the salt is not checked" },
    { name := "a corrupt or mismatched region is a miss (the text cache answers)", run := fun _ => do
        let dir ← mkTree [("M.wiz", "import Prelude\ndef x : Nat := 1\n")]
        let ms ← Module.loadAll ["lib", dir]
        let cache ← IO.FS.createTempDir
        let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, loader := loaderOf ms }
        let rig := RigTag.tag (R := ZeroOneMany)
        let stats ← IO.mkRef ({} : Cache.RegionCounts)
        let opts : Cache.RegionOptions := { rig, stats := some stats }
        let src := "import M\n#eval x\n"
        let (s0, _) ← Cache.elaborateCached (some cache) [] src init 0 (region := some opts)
        let good := s0.messages.toList.map (·.render src)
        check (!s0.messages.any (·.severity == .error)) s!"messages: {good}"
        let before ← stats.get
        let _ ← Cache.elaborateCached (some cache) [] src init 0 (region := some opts)
        check ((← stats.get).hits > before.hits) "the warm run did not come from a region"
        -- (a truncated region: a miss, not an error, and the run is rewritten)
        for f in ← regionFiles cache do IO.FS.writeFile f ""
        let after ← stats.get
        let (s1, _) ← Cache.elaborateCached (some cache) [] src init 0 (region := some opts)
        checkEq good (s1.messages.toList.map (·.render src))
        check ((← stats.get).misses > after.misses) "a truncated region was not a miss"
        for f in ← regionFiles cache do
          check ((← f.metadata).byteSize > 0) s!"{f} was not rewritten"
        -- (a region with the wrong format is rejected and rewritten, too)
        let binary ← Cache.binaryId (some cache)
        let k := Cache.moduleKey (loaderOf ms) (fun _ => none) 0 "M" (trusted := Tests.libModule)
        Cache.writeRegionFile (R := ZeroOneMany) (cache / Cache.regionFileName binary k)
          { magic := Cache.regionMagic, format := 999, binary, textSalt := Cache.salt, rig,
            module := "M", key := k }
        let after2 ← stats.get
        let (s2, _) ← Cache.elaborateCached (some cache) [] src init 0 (region := some opts)
        checkEq good (s2.messages.toList.map (·.render src))
        check ((← stats.get).misses > after2.misses) "a mismatched region was not a miss"
        let some a ← Cache.readModuleRegion (R := ZeroOneMany) cache binary rig k
          | throw (IO.userError "the mismatched region was not rewritten")
        checkEq Cache.regionFormat a.format
        check (a.effects.size > 0) "the rewritten region holds no effects" },
    { name := "a warm run is served from the module region, with the same state", run := fun _ => do
        let dir ← mkTree libFiles
        let ms ← Module.loadAll ["lib", dir]
        let cache ← IO.FS.createTempDir
        let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, loader := loaderOf ms }
        let rig := RigTag.tag (R := ZeroOneMany)
        let stats ← IO.mkRef ({} : Cache.RegionCounts)
        let opts : Cache.RegionOptions := { rig, stats := some stats }
        let src := "import Use\nimport Other\n#eval four + one\n"
        let (cold, _) ← Cache.elaborateCached (some cache) [] src init 0 (region := some opts)
        check (!cold.messages.any (·.severity == .error)) s!"messages: {cold.messages.toList.map (·.text)}"
        let before ← stats.get
        let (warm, hw) ← Cache.elaborateCached (some cache) [] src init 0 (region := some opts)
        let after ← stats.get
        check (after.hits > before.hits) s!"no module came from a region: {repr after}"
        check (after.commands > 0) s!"no command came from a region: {repr after}"
        -- (the text path, same directory: the same state and the same hit count)
        let (text, ht) ← Cache.elaborateCached (some cache) [] src init 0
        checkEq (warm.messages.toList.map (·.render src)) (text.messages.toList.map (·.render src))
        checkEq warm.globals.order.toList text.globals.order.toList
        checkEq hw ht },
    { name := "editing a module does not serve its stale region", run := fun _ => do
        let dir ← mkTree [("M.wiz", "import Prelude\ndef x : Nat := 1\n")]
        let cache ← IO.FS.createTempDir
        let rig := RigTag.tag (R := ZeroOneMany)
        let src := "import M\n#eval x\n"
        let recheck : IO (CommandState ZeroOneMany) := do
          let ms ← Module.loadAll ["lib", dir]
          let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, loader := loaderOf ms }
          pure (← Cache.elaborateCached (some cache) [] src init 0 (region := some { rig })).1
        let s1 ← recheck
        check (s1.messages.any fun m => (m.render src).endsWith "info: 1") s!"{s1.messages.toList.map (·.render src)}"
        IO.FS.writeFile (dir / "M.wiz") "import Prelude\ndef x : Nat := 2\n"
        let s2 ← recheck
        check (s2.messages.any fun m => (m.render src).endsWith "info: 2") s!"{s2.messages.toList.map (·.render src)}"
        check (!s2.messages.any fun m => (m.render src).endsWith "info: 1") s!"stale: {s2.messages.toList.map (·.render src)}"
        -- (the new key has its own region; the old one is stale, not served)
        let ms ← Module.loadAll ["lib", dir]
        let k2 := Cache.moduleKey (loaderOf ms) (fun _ => none) 0 "M" (trusted := Tests.libModule)
        let binary ← Cache.binaryId (some cache)
        check (← (cache / Cache.regionFileName binary k2).pathExists) "no region for the edited module"
        let some a ← Cache.readModuleRegion (R := ZeroOneMany) cache binary rig k2
          | throw (IO.userError "no readable region for the edited module")
        checkEq k2 a.key },
    { name := "regions layer over read-only caches (and never repair them)", run := fun _ => do
        -- (`--region-cache` + `--cache-ro`: regions live in the same directory layers)
        let dir ← mkTree libFiles
        let ms ← Module.loadAll ["lib", dir]
        let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, loader := loaderOf ms }
        let rig := RigTag.tag (R := ZeroOneMany)
        let stats ← IO.mkRef ({} : Cache.RegionCounts)
        let opts : Cache.RegionOptions := { rig, stats := some stats }
        let src := "import Use\nimport Other\n#eval four + one\n"
        -- (cold: the text entries and the regions in `ro`, as a Nix store would ship them)
        let ro ← IO.FS.createTempDir
        let (cold, _) ← Cache.elaborateCached (some ro) [] src init 0 (region := some opts)
        check (!cold.messages.any (·.severity == .error)) s!"messages: {cold.messages.toList.map (·.text)}"
        check ((← regionFiles ro).size > 0) "no region was written"
        let expected := cold.messages.toList.map (·.render src)
        let before ← snapshot ro
        -- (read caches only: a region is served from the read-only layer, nothing is written)
        let h0 ← stats.get
        let (s1, _) ← Cache.elaborateCached none [ro] src init 0 (region := some opts)
        check ((← stats.get).hits > h0.hits) "no module came from a region in the read-only layer"
        checkEq expected (s1.messages.toList.map (·.render src))
        checkEq before (← snapshot ro)
        -- (a write cache in front: the read-only region still answers, and stays untouched)
        let write ← IO.FS.createTempDir
        let h1 ← stats.get
        let (s2, _) ← Cache.elaborateCached (some write) [ro] src init 0 (region := some opts)
        check ((← stats.get).hits > h1.hits) "the read-only region did not answer through the write layer"
        checkEq expected (s2.messages.toList.map (·.render src))
        checkEq before (← snapshot ro)
        -- (a truncated region in a read-only layer is a miss, not an error: the text entry
        -- answers, the module is re-elaborated once into the write cache, and the bad file
        -- is left alone — a read-only cache is never repaired)
        let binary ← Cache.binaryId (some ro)
        let k := Cache.moduleKey (loaderOf ms) (fun _ => none) 0 "Use" (trusted := Tests.libModule)
        let bad := ro / Cache.regionFileName binary k
        IO.FS.writeFile bad ""
        let beforeBad ← snapshot ro
        let h2 ← stats.get
        let (s3, _) ← Cache.elaborateCached (some write) [ro] src init 0 (region := some opts)
        checkEq expected (s3.messages.toList.map (·.render src))
        check ((← stats.get).misses > h2.misses) "a truncated read-only region was not a miss"
        checkEq beforeBad (← snapshot ro)
        checkEq 0 (← bad.metadata).byteSize }
  ]

/-- A package: a library with two modules, and a file that checks against it. -/
def pkgFiles : List (String × String) :=
  [("grail.wiz", "import Grail\ndef package : Package := Package.new \"demo\"\n  |> Package.lib \"mylib\" \"src\"\n  |> Package.check \"app\" \"app.wiz\"\n"),
   ("src/Demo/Two.wiz", "import Prelude\ndef two : Nat := 2\n"),
   ("src/Demo/Three.wiz", "import Prelude\ndef three : Nat := 3\n"),
   ("app.wiz", "import Demo.Two\n#eval two + two\n")]

/-- The binary id of the grail the tests run: this test driver (its jobs run as
`<this test driver> --grail-job …`), by its hash, so a rebuilt driver doesn't reuse a
package's `.grail/build` from an older one. -/
def binId (tc : Toolchain) : IO UInt64 := Cache.binaryId tc.cacheDir

/-- A runner for a package directory; its jobs run as `<this test driver> --grail-job …`,
and its report goes to `log`. -/
def runner (dir : System.FilePath) (tc : Toolchain) (pkg : Grail.Package) (jobs : Nat := 1)
    (log : IO.Ref String) : IO Grail.Runner := do
  pure { ctx := { dir, std := "lib", tc, binId := ← binId tc, libRoots := Grail.libRootsOf dir pkg.targets },
         stats := ← IO.mkRef {}, memo := ← IO.mkRef {}, jobs, self := ← IO.appPath,
         out := fun s => log.modify (· ++ s), err := fun s => log.modify (· ++ s) }

/-- Run grail's build on a package directory; also returns the report. -/
def buildLog (dir : System.FilePath) (tc : Toolchain) (only : List String := []) (jobs : Nat := 1)
    (timeoutMs : Option Nat := none) : IO (Grail.Stats × Bool × String) := do
  match ← Grail.readConfig tc (← binId tc) "lib" dir with
  | .error e => throw (IO.userError e)
  | .ok (pkg, _) =>
    let log ← IO.mkRef ""
    let r ← runner dir tc pkg jobs log
    let r := { r with timeoutMs := timeoutMs.getD r.timeoutMs }
    let ok ← r.build pkg.targets (pkg.targets.filter fun t => only.isEmpty || only.contains t.name)
    pure (← r.stats.get, ok, ← log.get)

def build (dir : System.FilePath) (tc : Toolchain) (only : List String := []) (jobs : Nat := 1) : IO (Grail.Stats × Bool) := do
  let (s, ok, _) ← buildLog dir tc only jobs
  pure (s, ok)

/-- Every `.lean` file under a directory. -/
partial def leanFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out := #[]
  for e in ← dir.readDir do
    if ← e.path.isDir then out := out ++ (← leanFiles e.path)
    else if e.path.extension == some "lean" then out := out.push e.path
  pure out

def toolchainGroup : Group where
  name := "toolchain"
  exercise := "Stage 23a"
  cases := [
    { name := "wiz, grail and the test driver read no environment variables", run := fun _ => do
        let files := (← leanFiles "Wiz") ++ (← leanFiles "Grail") ++ #[System.FilePath.mk "Main.lean", "Tests/Main.lean"]
        for f in files do
          let text ← IO.FS.readFile f
          check ((text.splitOn "getEnv \"WIZ").length == 1) s!"{f} reads a WIZ_ variable" },
    { name := "wiz: an unknown flag or command is an error (exit 2), the usage alone is not", run := fun _ => do
        let wiz := ".lake/build/bin/wiz"
        let run (args : Array String) := IO.Process.output { cmd := wiz, args }
        let o ← run #["--impl=elab", "check", "x.wiz"]
        checkEq 2 o.exitCode
        check ((o.stderr.splitOn "unknown flag: --impl=elab").length > 1) s!"stderr: {o.stderr}"
        let o ← run #["frobnicate", "x.wiz"]
        checkEq 2 o.exitCode
        check ((o.stderr.splitOn "unknown command").length > 1) s!"stderr: {o.stderr}"
        checkEq 0 (← run #[]).exitCode
        checkEq 0 (← run #["--help"]).exitCode },
    { name := "flags fill the toolchain record", run := fun _ => do
        let (tc, rest) := ({} : Toolchain).parseFlags
          ["check", "--cc", "clang", "--cflags", "-I/a  -I/b", "-I", "src", "x.wiz", "--no-cache", "--llvm"]
        checkEq ["check", "x.wiz", "--llvm"] rest
        checkEq "clang" tc.cc
        checkEq ["-I/a", "-I/b"] tc.cflags
        checkEq ["src"] (tc.searchPath.map toString)
        check tc.cacheDir.isNone "the cache is on"
        -- and back to flags, for another process
        let tc := { tc with ldflags := ["-L/x"], cacheDir := some "/c" }
        let (tc', rest) := ({} : Toolchain).parseFlags tc.toFlags
        checkEq [] rest
        checkEq (repr tc).pretty (repr tc').pretty
        check (tc.id != ({ tc with cflags := [] } : Toolchain).id) "cflags are not in the id"
        checkEq tc.id ({ tc with cacheDir := none } : Toolchain).id },
    { name := "--cache-ro is repeatable and --no-cache clears both caches", run := fun _ => do
        let parse (args : List String) := ({} : Toolchain).parseFlags args
        -- left to right: reads keep their order, --cache sets the write cache
        let (tc, rest) := parse ["--cache-ro", "/a", "--cache", "/w", "--cache-ro", "/b", "check", "x.wiz"]
        checkEq ["/a", "/b"] (tc.readCaches.map toString)
        checkEq (some "/w") (tc.cacheDir.map toString)
        checkEq ["check", "x.wiz"] rest
        -- --no-cache clears both; a later --cache-ro (or --cache) adds again
        let (tc, _) := parse ["--cache-ro", "/a", "--cache", "/w", "--no-cache"]
        check tc.readCaches.isEmpty "a read cache survived --no-cache"
        check tc.cacheDir.isNone "the write cache survived --no-cache"
        let (tc, _) := parse ["--cache-ro", "/a", "--cache", "/w", "--no-cache", "--cache-ro", "/c"]
        checkEq ["/c"] (tc.readCaches.map toString)
        check tc.cacheDir.isNone "the write cache survived --no-cache"
        let (tc, _) := parse ["--no-cache", "--cache", "/w2"]
        checkEq (some "/w2") (tc.cacheDir.map toString)
        -- a grail build file's setting appends
        checkEq (some ["/a"]) ((({} : Toolchain).set "cache-ro" "/a").map fun t => t.readCaches.map toString)
        -- toFlags round-trips, with a write cache and read-only only
        let full : Toolchain := { cacheDir := some "/w", readCaches := ["/a", "/b"] }
        checkEq ["--cache-ro", "/a", "--cache-ro", "/b", "--cache", "/w"]
          ((full.toFlags).dropWhile (· != "--cache-ro") |>.take 6)
        let (back, rest) := parse full.toFlags
        checkEq [] rest
        checkEq (repr full).pretty (repr back).pretty
        let roOnly : Toolchain := { readCaches := ["/a", "/b"] }
        let (back, rest) := parse roOnly.toFlags
        checkEq [] rest
        checkEq (repr roOnly).pretty (repr back).pretty
        -- render: one line per read cache, in order, then the write cache
        check ((full.render.splitOn "cache-ro /a\ncache-ro /b\ncache /w\n").length > 1) full.render
        check ((roOnly.render.splitOn "cache-ro /a\ncache-ro /b\ncache (off)\n").length > 1) roOnly.render },
    { name := "-I DIR adds a module root", run := fun _ => do
        let dir ← mkTree [("Pkg/Three.wiz", "import Prelude\ndef three : Nat := 3\n")]
        let (tc, _) := ({} : Toolchain).parseFlags ["check", "main.wiz", "-I", dir.toString]
        let src := "import Pkg.Three\n#eval three\n"
        let ms ← Module.loadClosure ("lib" :: tc.searchPath) src
        let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := loaderOf ms }
        checkEq "[2:1: info: 3]" (toString (s.messages.toList.map (·.render src))) },
    { name := "#262: `wiz check -I src FILE` and `wiz check FILE -I src` both find the package's modules", run := fun _ => do
        let dir ← mkTree [("src/Crux/B.wiz", "import Prelude\ndef b : Nat := 1\n"),
                          ("src/Crux/A.wiz", "import Crux.B\n#eval b\n")]
        let wiz := (← IO.FS.realPath ".lake/build/bin/wiz").toString
        for args in [["check", "-I", "src", "src/Crux/A.wiz"], ["check", "src/Crux/A.wiz", "-I", "src"],
                     ["-I", "src", "check", "src/Crux/A.wiz"]] do
          let out ← IO.Process.output { cmd := wiz, args := (args ++ ["--no-cache"]).toArray, cwd := some dir }
          checkEq s!"{args}: 0 src/Crux/A.wiz:2:1: info: 1\n" s!"{args}: {out.exitCode} {out.stdout}{out.stderr}"
        -- the usage text names -I for check
        let out ← IO.Process.output { cmd := wiz, args := #["help"] }
        check ((out.stdout.splitOn "wiz check [-I DIR] FILE").length > 1) out.stdout },
    { name := "wiz check --region-cache: a warm run comes from regions, and corrupt ones are misses", run := fun _ => do
        let dir ← mkTree [("M.wiz", "import Prelude\ndef x : Nat := 2\n"), ("main.wiz", "import M\n#eval x\n")]
        let cache ← IO.FS.createTempDir
        let wiz := (← IO.FS.realPath ".lake/build/bin/wiz").toString
        let args := #["check", "main.wiz", "-I", dir.toString, "--cache", cache.toString,
                      "--region-cache", "--region-stats"]
        let run := IO.Process.output { cmd := wiz, args, cwd := some dir }
        let o1 ← run
        checkEq 0 o1.exitCode
        checkEq "main.wiz:2:1: info: 2\n" o1.stdout
        check ((o1.stderr.splitOn "region cache:").length > 1) s!"no stats: {o1.stderr}"
        let regions ← regionFiles cache
        check (regions.size > 0) "no region files were written"
        -- (a warm run: modules come from the regions, the answer is the same)
        let o2 ← run
        checkEq 0 o2.exitCode
        checkEq o1.stdout o2.stdout
        check ((o2.stderr.splitOn "region cache: 0 modules").length == 1)
          s!"nothing came from a region: {o2.stderr}"
        -- (corrupt every region: the next run falls back to the text entries and rewrites them)
        for f in regions do IO.FS.writeFile f ""
        let o3 ← run
        checkEq 0 o3.exitCode
        checkEq o1.stdout o3.stdout
        for f in ← regionFiles cache do
          check ((← f.metadata).byteSize > 0) s!"{f} was not rewritten" }
  ]

/-- (9f) An executable with a `link_c` file: editing the C file relinks it (only). -/
def linkCCase : Case :=
    { name := "an executable with link_c: a C edit reruns the link only", run := fun _ => do
        let tc : Toolchain := { (← toolchain) with cacheDir := some (← IO.FS.createTempDir) }
        let dir ← mkTree [("grail.wiz", "import Grail\ndef package : Package := Package.new \"p\" |> Package.exe \"hi\" \"app/hi.wiz\"\n"),
                          ("app/hi.wiz", "import IO\nlink_c \"hi.c\"\nextern \"hi_num\" hiNum : IO Nat\n" ++
                             "def main : IO Unit := do\n  n ← hiNum;\n  IO.println (Nat.toString n)\n"),
                          ("app/hi.c", "#include <stdint.h>\nuint64_t hi_num(void) { return 1; }\n")]
        let (s, ok) ← build dir tc
        if !ok then
          skip "no toolchain"
          return
        checkEq 3 s.ran
        let exe := (dir / ".grail" / "bin" / "hi").toString
        checkEq "1\n" (← IO.Process.output { cmd := exe }).stdout
        let (s, _) ← build dir tc
        checkEq 0 s.ran
        IO.FS.writeFile (dir / "app" / "hi.c") "#include <stdint.h>\nuint64_t hi_num(void) { return 2; }\n"
        let (s, _) ← build dir tc
        checkEq 1 s.ran
        checkEq "2\n" (← IO.Process.output { cmd := exe }).stdout
        -- a deleted file: the check reruns and says so
        IO.FS.removeFile (dir / "app" / "hi.c")
        let (_, ok, log) ← buildLog dir tc
        check (!ok) "built without its C file"
        check ((log.splitOn "link_c: no file hi.c").length > 1) s!"no error for the missing file:\n{log}" }

/-- `grail lsp` (this test driver's sibling `grail`) in `dir`: the diagnostics of `file`
after an initialize and a didOpen; `none` if there is no grail binary. -/
def grailLspDiagnostics (dir : System.FilePath) (file : String) : IO (Option (List String)) := do
  let grail := ((← IO.appPath).parent.getD ".") / "grail"
  unless ← grail.pathExists do return none
  let cache ← IO.FS.createTempDir
  let args := #["-C", dir.toString, "--cache", cache.toString, "lsp"]
  let child ← IO.Process.spawn { cmd := grail.toString, args, stdin := .piped, stdout := .piped, stderr := .piped }
  let (stdin, child) ← child.takeStdin
  let input := IO.FS.Stream.ofHandle stdin
  let output := IO.FS.Stream.ofHandle child.stdout
  -- a time limit that doesn't keep the test's process alive once the test is done
  let done ← IO.mkRef false
  let _ ← IO.asTask (prio := .dedicated) do
    for _ in [0:1200] do
      if ← done.get then return
      IO.sleep 100
    child.kill
  let path ← IO.FS.realPath (dir / file)
  let uri := s!"file://{path}"
  LSP.writeMessage input (Lean.Json.mkObj [("jsonrpc", "2.0"), ("id", (1 : Nat)), ("method", "initialize"),
    ("params", Lean.Json.mkObj [("capabilities", Lean.Json.mkObj [])])])
  LSP.writeMessage input (Lean.Json.mkObj [("jsonrpc", "2.0"), ("method", "textDocument/didOpen"),
    ("params", Lean.Json.mkObj [("textDocument", Lean.Json.mkObj [("uri", uri), ("languageId", "wiz"),
      ("version", (1 : Nat)), ("text", ← IO.FS.readFile path)])])])
  let mut diags := none
  repeat
    let some m ← LSP.readMessage output | break
    if LSP.getStr m ["method"] == "textDocument/publishDiagnostics" then
      let ds := match LSP.get? m ["params", "diagnostics"] with
        | some (.arr ds) => ds.toList.map (LSP.getStr · ["message"])
        | _ => []
      diags := some ds
      break
  done.set true
  child.kill
  let _ ← child.wait
  match diags with
  | some ds => pure (some ds)
  | none => throw (IO.userError s!"grail lsp ended without diagnostics: {← child.stderr.readToEnd}")

def grailLspCase : Case :=
    { name := "grail lsp: the server knows the package's modules", run := fun _ => do
        let dir ← mkTree (pkgFiles ++ [("main.wiz", "import Demo.Two
#eval two
")])
        let some ds ← grailLspDiagnostics dir "main.wiz"
          | skip "no grail beside the test driver; lake build grail"
        check (ds.any (· == "2")) s!"diagnostics: {ds}"
        check (!ds.any fun d => (d.splitOn "unknown module").length > 1) s!"diagnostics: {ds}"
        -- a broken grail.wiz: the server still starts, with the package directory as a root
        IO.FS.writeFile (dir / "grail.wiz") "import Grail\ndef package : Package := 3\n"
        IO.FS.writeFile (dir / "Root.wiz") "import Prelude\ndef r : Nat := 5\n"
        IO.FS.writeFile (dir / "main.wiz") "import Root\n#eval r\n"
        let some ds ← grailLspDiagnostics dir "main.wiz" | return
        check (ds.any (· == "5")) s!"diagnostics with a broken grail.wiz: {ds}" }

def grailGroup : Group where
  name := "grail"
  exercise := "Stage 23d"
  cases := [
    { name := "the build file is Wiz", run := fun _ => do
        let dir ← mkTree (pkgFiles ++ [("grail.local.wiz", "import Grail\ndef settings : Settings := Settings.empty |> Settings.set \"cflags\" \"-I \\\"x\\\"\"\n")])
        let cache ← IO.FS.createTempDir
        match ← Grail.readConfig { cacheDir := some cache } (← binId { cacheDir := some cache }) "lib" dir with
        | .error e => throw (IO.userError e)
        | .ok (pkg, localSettings) =>
          checkEq "demo" pkg.name
          check (pkg.targets == [Grail.Target.lib "mylib" "src", .check "app" "app.wiz"]) s!"targets: {repr pkg.targets}"
          checkEq [("cflags", "-I \"x\"")] localSettings },
    { name := "a second build runs no jobs", run := fun _ => do
        let dir ← mkTree pkgFiles
        let tc : Toolchain := { cacheDir := some (← IO.FS.createTempDir) }
        let (s1, ok1) ← build dir tc
        check ok1 "the first build failed"
        checkEq 3 s1.ran
        let (s2, ok2) ← build dir tc
        check ok2 "the second build failed"
        checkEq 0 s2.ran
        checkEq 3 s2.upToDate },
    { name := "--cache-ro is forwarded; a build replays from a read-only cache", run := fun _ => do
        let dir ← mkTree pkgFiles
        let self ← IO.appPath
        -- config: the read caches are rendered in order, then the write cache
        let ro1 ← IO.FS.createTempDir
        let ro2 ← IO.FS.createTempDir
        let w ← IO.FS.createTempDir
        let cfgArgs := #["--grail", "-C", dir.toString, "--cache-ro", ro1.toString,
                         "--cache-ro", ro2.toString, "--cache", w.toString, "config"]
        let cfg ← IO.Process.output { cmd := self.toString, args := cfgArgs }
        checkEq 0 cfg.exitCode
        check ((cfg.stdout.splitOn s!"cache-ro {ro1}\ncache-ro {ro2}\ncache {w}\n").length > 1) cfg.stdout
        -- a warm cache, written by a build through this binary
        let warm ← IO.FS.createTempDir
        let (_, ok) ← build dir ({ cacheDir := some warm } : Toolchain) ["app"]
        check ok "the warm build failed"
        -- a fresh package: only the read-only cache and an empty write cache
        let dir2 ← mkTree pkgFiles
        let write ← IO.FS.createTempDir
        let buildArgs := #["--grail", "-C", dir2.toString, "--cache-ro", warm.toString,
                           "--cache", write.toString, "build", "app"]
        let out ← IO.Process.output { cmd := self.toString, args := buildArgs }
        checkEq 0 out.exitCode
        check ((out.stdout.splitOn "jobs run").length > 1) s!"{out.stdout}{out.stderr}" },
    { name := "an edit reruns the checks that depend on it", run := fun _ => do
        let dir ← mkTree pkgFiles
        let tc : Toolchain := { cacheDir := some (← IO.FS.createTempDir) }
        let _ ← build dir tc
        IO.FS.writeFile (dir / "src/Demo/Two.wiz") "import Prelude\ndef two : Nat := 1 + 1\n"
        let (s, ok) ← build dir tc
        check ok "the build failed"
        -- Demo.Two and app.wiz; not Demo.Three
        checkEq 2 s.ran
        checkEq 1 s.upToDate },
    { name := "a failed check is reported and not recorded", run := fun _ => do
        let dir ← mkTree (pkgFiles.map fun (p, t) => if p == "app.wiz" then (p, "import Demo.Two\ndef bad : Nat := true\n") else (p, t))
        let tc : Toolchain := { cacheDir := some (← IO.FS.createTempDir) }
        let (s, ok) ← build dir tc ["app"]
        check (!ok) "the build succeeded"
        checkEq 1 s.failed
        let (s, _) ← build dir tc ["app"]
        checkEq 1 s.failed
        -- nothing half-written is left
        let tmp := dir / ".grail" / "tmp"
        if ← tmp.pathExists then checkEq 0 (← tmp.readDir).size },
    { name := "an executable: build (check, IR and C in one job), object, link", run := fun _ => do
        let tc : Toolchain := { (← toolchain) with cacheDir := some (← IO.FS.createTempDir) }
        let dir ← mkTree [("grail.wiz", "import Grail\ndef package : Package := Package.new \"p\" |> Package.exe \"hello\" \"hello.wiz\"\n"),
                          ("hello.wiz", "import IO\ndef main : IO Unit := IO.println \"hello from grail\"\n")]
        let (s, ok) ← build dir tc
        if !ok then
          skip "no toolchain"
          return
        checkEq 3 s.ran
        let out ← IO.Process.output { cmd := (dir / ".grail" / "bin" / "hello").toString }
        checkEq "hello from grail\n" out.stdout
        let (s, _) ← build dir tc
        checkEq 0 s.ran
        -- a change that doesn't change the program's code: only the one build job reruns
        IO.FS.writeFile (dir / "hello.wiz") "import IO\n-- a comment\ndef main : IO Unit := IO.println \"hello from grail\"\n"
        let (s, _) ← build dir tc
        checkEq 1 s.ran
        checkEq 2 s.upToDate },
    linkCCase,
    grailLspCase
  ]

/-- A diamond: `B` and `C` import `A`, `D` imports both, and `app.wiz` imports `D`. -/
def diamondFiles : List (String × String) :=
  [("grail.wiz", "import Grail\ndef package : Package := Package.new \"diamond\"\n  |> Package.lib \"lib\" \"src\"\n  |> Package.check \"app\" \"app.wiz\"\n"),
   ("src/A.wiz", "import Prelude\ndef a : Nat := 1\n"),
   ("src/B.wiz", "import A\ndef b : Nat := a + 1\n"),
   ("src/C.wiz", "import A\ndef c : Nat := a + 2\n"),
   ("src/D.wiz", "import B\nimport C\ndef d : Nat := b + c\n"),
   ("app.wiz", "import D\n#eval d\n")]

/-- The names in a package's `.grail/build`, sorted. -/
def buildDirs (dir : System.FilePath) : IO (List String) := do
  let entries ← (dir / ".grail" / "build").readDir
  pure (entries.map (·.fileName)).toList.mergeSort

def grailJobsGroup : Group where
  name := "grail-jobs"
  exercise := "Stage 23g"
  cases := [
    { name := "a diamond builds with -j 4 as with -j 1, and again runs nothing", run := fun _ => do
        let cache ← IO.FS.createTempDir
        let tc : Toolchain := { cacheDir := some cache }
        let d1 ← mkTree diamondFiles
        let (s1, ok1, log1) ← buildLog d1 tc (jobs := 1)
        check ok1 s!"-j 1 failed:\n{log1}"
        let d4 ← mkTree diamondFiles
        let (s4, ok4, log4) ← buildLog d4 tc (jobs := 4)
        check ok4 s!"-j 4 failed:\n{log4}"
        checkEq 5 s1.ran
        checkEq 5 s4.ran
        -- the same report, in the graph's order, and the same outputs
        checkEq log1 log4
        checkEq "[check src/A.wiz]\n[check src/B.wiz]\n[check src/C.wiz]\n[check src/D.wiz]\n[check app.wiz]\napp.wiz:2:1: info: 5\n" log4
        checkEq (← buildDirs d1) (← buildDirs d4)
        let (s, ok, _) ← buildLog d4 tc (jobs := 4)
        check ok "the second build failed"
        checkEq 0 s.ran
        checkEq 5 s.upToDate },
    { name := "a failed job stops what depends on it, only", run := fun _ => do
        let dir ← mkTree (diamondFiles.map fun (p, t) => if p == "src/B.wiz" then (p, "import A\ndef b : Nat := Nat.zero Nat.zero\n") else (p, t))
        let tc : Toolchain := { cacheDir := some (← IO.FS.createTempDir) }
        let (s, ok, log) ← buildLog dir tc (jobs := 4)
        check (!ok) "the build succeeded"
        -- A and C ran; B failed; D and app were skipped
        checkEq 2 s.ran
        checkEq 1 s.failed
        checkEq 2 s.skipped
        check ((log.splitOn "✗ check src/B.wiz\n  src/B.wiz:2:").length == 2) log
        check ((log.splitOn "- check src/D.wiz: skipped (check src/B.wiz failed)").length == 2) log
        check ((log.splitOn "- check app.wiz: skipped (check src/B.wiz failed)").length == 2) log
        -- nothing half-written is left
        let tmp := dir / ".grail" / "tmp"
        if ← tmp.pathExists then checkEq 0 (← tmp.readDir).size },
    { name := "a job has a time limit", run := fun _ => do
        let dir ← mkTree diamondFiles
        let tc : Toolchain := { cacheDir := some (← IO.FS.createTempDir) }
        let (s, ok, log) ← buildLog dir tc (jobs := 2) (timeoutMs := some 1)
        check (!ok) "the build succeeded"
        checkEq 0 s.ran
        check ((log.splitOn "timed out after 0.001 s").length > 1) log }
  ]

/-- Run git in `dir` (with an identity, for commits); fails the test if git fails. -/
def gitIn (dir : System.FilePath) (args : List String) : IO String := do
  let o ← IO.Process.output {
    cmd := "git", cwd := dir,
    args := #["-c", "user.name=grail", "-c", "user.email=grail@example.com", "-c", "init.defaultBranch=main",
              "-c", "commit.gpgsign=false", "-c", "tag.gpgsign=false"] ++ args.toArray }
  if o.exitCode != 0 then throw (IO.userError s!"git {args}: {o.stderr}")
  pure o.stdout.trimAscii.toString

/-- A dependency as a bare repository (no network): a package with a library, tagged
`v1`; returns the bare repository and the work tree it was pushed from. -/
def depRepo : IO (System.FilePath × System.FilePath) := do
  let work ← mkTree [("grail.wiz", "import Grail\ndef package : Package := Package.new \"greet\"\n  |> Package.lib \"greet\" \"src\"\n"),
                     ("src/Greet/Hello.wiz", "import Prelude\ndef hello : Nat := 1\n")]
  let bare ← IO.FS.createTempDir
  let _ ← gitIn bare ["init", "--quiet", "--bare"]
  let _ ← gitIn work ["init", "--quiet"]
  let _ ← gitIn work ["add", "."]
  let _ ← gitIn work ["commit", "--quiet", "-m", "v1"]
  let _ ← gitIn work ["tag", "v1"]
  let _ ← gitIn work ["push", "--quiet", bare.toString, "HEAD:refs/heads/main", "v1"]
  pure (bare, work)

/-- A package that depends on `greet` at `rev`. -/
def depPkg (url rev : String) : List (String × String) :=
  [("grail.wiz", s!"import Grail\ndef package : Package := Package.new \"app\"\n  |> Package.dep \"greet\" \"{url}\" \"{rev}\"\n  |> Package.check \"app\" \"app.wiz\"\n"),
   ("app.wiz", "import Greet.Hello\n#eval hello + 1\n")]

def setGrailWiz (dir : System.FilePath) (url rev : String) : IO Unit :=
  IO.FS.writeFile (dir / "grail.wiz") ((depPkg url rev).head!.2)

/-- `grail update`, in-process. -/
def updateDeps (dir : System.FilePath) (tc : Toolchain) : IO (Except String (List Grail.Locked)) := do
  match ← Grail.readConfig tc (← binId tc) "lib" dir with
  | .error e => pure (.error e)
  | .ok (pkg, _) => Grail.update (fun d => do pure ((← Grail.readConfig tc (← binId tc) "lib" d).map (·.1))) dir pkg

/-- `grail build`, with the dependencies' roots; also the notes. -/
def buildDeps (dir : System.FilePath) (tc : Toolchain) : IO (Except String (Grail.Stats × Bool × String)) := do
  match ← Grail.readConfig tc (← binId tc) "lib" dir with
  | .error e => pure (.error e)
  | .ok (pkg, _) =>
    let log ← IO.mkRef ""
    match ← Grail.lockedRoots (fun d => do pure ((← Grail.readConfig tc (← binId tc) "lib" d).map (·.1))) dir pkg
        (fun s => log.modify (· ++ s)) with
    | .error e => pure (.error e)
    | .ok roots =>
      let r ← runner dir tc pkg 2 log
      let r := { r with ctx := { r.ctx with libRoots := r.ctx.libRoots ++ roots } }
      let ok ← r.build pkg.targets pkg.targets
      pure (.ok (← r.stats.get, ok, ← log.get))

def grailDepsGroup : Group where
  name := "grail-deps"
  exercise := "Stage 23h"
  cases := [
    { name := "a git dependency: grail update writes the lock, builds use it", run := fun _ => do
        let (bare, work) ← depRepo
        let url := bare.toString
        let dir ← mkTree (depPkg url "v1")
        let tc : Toolchain := { cacheDir := some (← IO.FS.createTempDir) }
        -- no lock yet
        match ← buildDeps dir tc with
        | .error e => check ((e.splitOn "grail update").length > 1) e
        | .ok _ => throw (IO.userError "built without grail.lock")
        let .ok [l] ← updateDeps dir tc | throw (IO.userError "grail update failed")
        let v1 ← gitIn work ["rev-parse", "v1"]
        checkEq v1 l.commit
        let lock ← IO.FS.readFile (dir / "grail.lock")
        check ((Grail.parseLock lock |>.toOption) == some [l]) s!"grail.lock: {lock}"
        check ((lock.splitOn v1).length == 2) lock
        check (← (dir / ".grail/packages/greet/src/Greet/Hello.wiz").pathExists) "not fetched"
        let .ok (s, ok, log) ← buildDeps dir tc | throw (IO.userError "the build failed")
        check ok log
        checkEq 1 s.ran
        check ((log.splitOn "app.wiz:2:1: info: 2").length == 2) log
        -- again: nothing runs
        let .ok (s, _, _) ← buildDeps dir tc | throw (IO.userError "the second build failed")
        checkEq 0 s.ran
        -- a new tag upstream; grail.wiz asks for it, but the lock still has v1
        IO.FS.writeFile (work / "src/Greet/Hello.wiz") "import Prelude\ndef hello : Nat := 41\n"
        let _ ← gitIn work ["commit", "--quiet", "-am", "v2"]
        let _ ← gitIn work ["tag", "v2"]
        let _ ← gitIn work ["push", "--quiet", url, "HEAD:refs/heads/main", "v2"]
        setGrailWiz dir url "v2"
        let .ok (s, ok, log) ← buildDeps dir tc | throw (IO.userError "the build failed")
        check ok log
        checkEq 0 s.ran
        check ((log.splitOn "grail update").length > 1) s!"no note: {log}"
        checkEq v1 (← gitIn (dir / ".grail/packages/greet") ["rev-parse", "HEAD"])
        checkEq lock (← IO.FS.readFile (dir / "grail.lock"))
        -- grail update moves it
        let .ok [l2] ← updateDeps dir tc | throw (IO.userError "grail update failed")
        checkEq (← gitIn work ["rev-parse", "v2"]) l2.commit
        check (l2.content != l.content) "the content hash did not change"
        let .ok (s, ok, log) ← buildDeps dir tc | throw (IO.userError "the build failed")
        check ok log
        checkEq 1 s.ran
        check ((log.splitOn "app.wiz:2:1: info: 42").length == 2) log },
    { name := "a fresh checkout fetches the locked commit; edited files are refused", run := fun _ => do
        let (bare, _) ← depRepo
        let dir ← mkTree (depPkg bare.toString "main")
        let tc : Toolchain := { cacheDir := some (← IO.FS.createTempDir) }
        let .ok [l] ← updateDeps dir tc | throw (IO.userError "grail update failed")
        -- as if the package were cloned elsewhere: no .grail
        IO.FS.removeDirAll (dir / ".grail")
        let .ok (_, ok, log) ← buildDeps dir tc | throw (IO.userError "the build failed")
        check ok log
        checkEq l.commit (← gitIn (dir / ".grail/packages/greet") ["rev-parse", "HEAD"])
        IO.FS.writeFile (dir / ".grail/packages/greet/src/Greet/Hello.wiz") "import Prelude\ndef hello : Nat := 5\n"
        match ← buildDeps dir tc with
        | .error e => check ((e.splitOn "differs from").length > 1) e
        | .ok _ => throw (IO.userError "built with edited dependency files") },
    { name := "two commits of one dependency are refused", run := fun _ => do
        -- `mid` depends on greet at v1; the app on greet at main (a later commit) and on mid
        let (bare, work) ← depRepo
        IO.FS.writeFile (work / "src/Greet/Hello.wiz") "import Prelude\ndef hello : Nat := 2\n"
        let _ ← gitIn work ["commit", "--quiet", "-am", "later"]
        let _ ← gitIn work ["push", "--quiet", bare.toString, "HEAD:refs/heads/main"]
        let midWork ← mkTree [("grail.wiz", s!"import Grail\ndef package : Package := Package.new \"mid\"\n  |> Package.dep \"greet\" \"{bare}\" \"v1\"\n")]
        let midBare ← IO.FS.createTempDir
        let _ ← gitIn midBare ["init", "--quiet", "--bare"]
        let _ ← gitIn midWork ["init", "--quiet"]
        let _ ← gitIn midWork ["add", "."]
        let _ ← gitIn midWork ["commit", "--quiet", "-m", "mid"]
        let _ ← gitIn midWork ["push", "--quiet", midBare.toString, "HEAD:refs/heads/main"]
        let dir ← mkTree [("grail.wiz", s!"import Grail\ndef package : Package := Package.new \"app\"\n  |> Package.dep \"greet\" \"{bare}\" \"main\"\n  |> Package.dep \"mid\" \"{midBare}\" \"main\"\n")]
        let tc : Toolchain := { cacheDir := some (← IO.FS.createTempDir) }
        match ← updateDeps dir tc with
        | .error e => check ((e.splitOn "two commits of greet").length > 1) e
        | .ok ls => throw (IO.userError s!"resolved: {repr ls}") }
  ]

/-- Run `grail test` in-process on a package directory. -/
def runTests (dir : System.FilePath) (tc : Toolchain) (update : Bool := false) (testTimeoutMs : Option Nat := none) :
    IO (Array Grail.TestResult × Grail.Stats) := do
  let std : System.FilePath := "lib"
  match ← Grail.readConfig tc 7 std dir with
  | .error e => throw (IO.userError e)
  | .ok (pkg, _) =>
    let r ← runner dir tc pkg 2 (← IO.mkRef "")
    let r := { r with testTimeoutMs := testTimeoutMs.getD r.testTimeoutMs }
    let res ← r.tests pkg.targets [] update
    pure (res, ← r.stats.get)

def testPkg : List (String × String) :=
  [("grail.wiz", "import Grail\ndef package : Package := Package.new \"t\" |> Package.tests \"tests\" \"tests\"\n"),
   ("tests/two.wiz", "import Prelude\n#eval 1 + 1\n"),
   ("tests/sub/bad.wiz", "import Prelude\ndef b : Nat := true\n")]

def testRunnerGroup : Group where
  name := "testrunner"
  exercise := "Stage 23f"
  cases := [
    { name := "tests are files with expected output; --update writes it", run := fun _ => do
        let dir ← mkTree testPkg
        let tc : Toolchain := { cacheDir := some (← IO.FS.createTempDir) }
        let (res, _) ← runTests dir tc
        checkEq 2 res.size
        check (res.all (!·.ok)) "a test without .expected passed"
        let (res, _) ← runTests dir tc (update := true)
        check (res.all (·.ok)) "--update failed"
        checkEq "tests/two.wiz:2:1: info: 2\n" (← IO.FS.readFile (dir / "tests/two.expected"))
        let bad ← IO.FS.readFile (dir / "tests/sub/bad.expected")
        check ((bad.splitOn "tests/sub/bad.wiz:2:").length > 1 && (bad.splitOn "error").length > 1) s!"bad.expected: {bad}"
        let (res, _) ← runTests dir tc
        check (res.all (·.ok)) "the tests failed after --update"
        -- `--update` with nothing to update records its passes too (docs-tour: "0 recorded
        -- passes" on the run after it)
        let cache2 ← IO.FS.createTempDir
        let dir2 ← mkTree testPkg
        let tc2 : Toolchain := { cacheDir := some cache2 }
        let _ ← runTests dir2 tc2 (update := true)
        let (res, _) ← runTests dir2 tc2 (update := true)
        check (res.all (·.ok)) "the second --update failed"
        let (res, st) ← runTests dir2 tc2
        check (res.all (·.cached)) "an unchanged --update pass was not recorded"
        checkEq 0 st.ran
        -- passes are recorded: nothing runs again
        let (res, st) ← runTests dir tc
        check (res.all (·.cached)) "a pass was not recorded"
        checkEq 0 st.ran },
    { name := "a wrong output fails, with the first difference", run := fun _ => do
        let dir ← mkTree (testPkg ++ [("tests/two.expected", "tests/two.wiz:2:1: info: 3\n")])
        let tc : Toolchain := { cacheDir := some (← IO.FS.createTempDir) }
        let (res, _) ← runTests dir tc
        let some two := res.find? (·.file == "tests/two.wiz") | throw (IO.userError "no test two")
        check (!two.ok) "a wrong output passed"
        check ((two.message.splitOn "info: 3").length > 1 && (two.message.splitOn "info: 2").length > 1) two.message },
    { name := "a failing test without a `-- test:` line says it was a check (icestick-cpu C8)", run := fun _ => do
        -- the program's expected output, but no `-- test: run`: it was compared with the
        -- (empty) messages of checking the file, and nothing said why
        let dir ← mkTree [("grail.wiz", "import Grail\ndef package : Package := Package.new \"t\" |> Package.tests \"tests\" \"tests\"\n"),
          ("tests/hello.wiz", "import IO\ndef main : IO Unit := IO.println \"hi\"\n"),
          ("tests/hello.expected", "hi\n"),
          ("tests/two.wiz", "-- test: check\nimport Prelude\n#eval 1 + 1\n"),
          ("tests/two.expected", "tests/two.wiz:3:1: info: 3\n")]
        let tc : Toolchain := { cacheDir := some (← IO.FS.createTempDir) }
        let (res, _) ← runTests dir tc
        let some hello := res.find? (·.file == "tests/hello.wiz") | throw (IO.userError "no test hello")
        check (!hello.ok) "it passed"
        check ((hello.message.splitOn "-- test: run").length > 1) hello.message
        -- with the line, a failure is only the difference
        let some two := res.find? (·.file == "tests/two.wiz") | throw (IO.userError "no test two")
        check (!two.ok) "two passed"
        check ((two.message.splitOn "-- test:").length == 1) two.message },
    { name := "-- test: run compiles and runs main", run := fun _ => do
        let dir ← mkTree [("grail.wiz", "import Grail\ndef package : Package := Package.new \"t\" |> Package.tests \"tests\" \"tests\"\n"),
          ("tests/hello.wiz", "-- test: run\nimport IO\ndef main : IO Unit := IO.println \"hi\"\n"),
          ("tests/hello.expected", "hi\n"),
          ("tests/value.wiz", "-- test: run\nimport Prelude\ndef main : Nat := 6 * 7\n"),
          ("tests/value.expected", "42\n")]
        let tc : Toolchain := { (← toolchain) with cacheDir := some (← IO.FS.createTempDir) }
        let (res, _) ← runTests dir tc
        if res.any fun t => (t.message.splitOn "gmp.h").length > 1 then
          skip "no toolchain"; return
        for t in res do check t.ok s!"{t.file}: {t.message}" },
    { name := "--update never records a failure: a program that doesn't build, fails or times out", run := fun _ => do
        let tc : Toolchain := { (← toolchain) with cacheDir := some (← IO.FS.createTempDir) }
        let failed (res : Array Grail.TestResult) (file needle : String) : IO Unit := do
          match res.find? (·.file == file) with
          | none => throw (IO.userError s!"no result for {file}")
          | some t =>
            check (!t.ok) s!"{file} passed: {t.message}"
            check ((t.message.splitOn needle).length > 1) s!"{file}: {t.message}"
        -- its program doesn't check (the run test's check job fails)
        let dir ← mkTree [("grail.wiz", "import Grail\ndef package : Package := Package.new \"t\" |> Package.tests \"tests\" \"tests\"\n"),
          ("tests/broken.wiz", "-- test: run\nimport Prelude\ndef main : Nat := Nat.zero Nat.zero\n")]
        for update in [true, false] do
          let (res, _) ← runTests dir tc update
          failed res "tests/broken.wiz" "does not build"
          check (!(← (dir / "tests/broken.expected").pathExists)) "--update recorded the failure"
        -- a time limit
        let dir ← mkTree [("grail.wiz", "import Grail\ndef package : Package := Package.new \"t\" |> Package.tests \"tests\" \"tests\"\n"),
          ("tests/slow.wiz", "import Prelude\ndef n : Nat := 1\n")]
        let (res, _) ← runTests dir tc (update := true) (testTimeoutMs := some 1)
        failed res "tests/slow.wiz" "timed out"
        check (!(← (dir / "tests/slow.expected").pathExists)) "--update recorded the time-out"
        -- a program that fails when it runs
        let dir ← mkTree [("grail.wiz", "import Grail\ndef package : Package := Package.new \"t\" |> Package.tests \"tests\" \"tests\"\n"),
          ("tests/exit.wiz", "-- test: run\nimport Sys\ndef main : IO Unit := Process.exit 3\n")]
        let (res, _) ← runTests dir tc (update := true)
        if res.any fun t => (t.message.splitOn "gmp.h").length > 1 then
          skip "no toolchain"; return
        failed res "tests/exit.wiz" "exited with 3"
        check (!(← (dir / "tests/exit.expected").pathExists)) "--update recorded the failed run" },
    -- the suite's own driver (`Tests/Main.lean`): `tests --run GROUP INDEX` ran a case
    -- in-process and printed nothing for a pass, so a stale binary or a wrong index that
    -- ran another (passing) case looked like a pass; a selector that picked nothing
    -- passed with 0 cases. Run against the cases with known outcomes `driverFixtures`.
    { name := "tests --run: a failing case exits 1 with its output, a skipped one 3, a bad selector 2", run := fun _ => do
        let self ← IO.appPath
        let run (args : Array String) : IO (UInt32 × String) := do
          let o ← IO.Process.output { cmd := self.toString, args }
          pure (o.exitCode, o.stdout ++ o.stderr)
        let has (out s : String) : IO Unit := check ((out.splitOn s).length > 1) s!"no {s} in:\n{out}"
        let (code, out) ← run #["--run", "driver-fixtures", "0"]
        checkEq 0 code; has out "✓ fixture: passes"; has out "driver-fixtures #0: passed"
        let (code, out) ← run #["--run", "driver-fixtures", "1"]
        checkEq 1 code; has out "✗ fixture: fails"; has out "fixture failure"
        has out "fixture output before the failure"; has out "FAILED"
        let (code, out) ← run #["--run", "driver-fixtures#2"]
        checkEq 3 code; has out "⊘ fixture: skips"; has out "skipped (fixture reason)"; has out "SKIPPED"
        let (code, out) ← run #["--run", "=driver-fixtures", "3"]
        checkEq 3 code; has out "skipped (old fixture reason)"
        for bad in [#["--run", "driver-fixtures", "4"], #["--run", "driver-fixtures", "x"],
            #["--run", "no-such-group", "0"], #["--run", "driver-fixtures"],
            #["--run", "driver-fixtures", "0", "extra"], #["=no-such-group"], #["=testrunner#99"],
            #["testrunner", "--no-such-flag"], #["=rig", "--jobs", "0"], #["=rig", "--jobs", "x"]] do
          let (code, out) ← run bad
          check (code == 2) s!"tests {" ".intercalate bad.toList}: exit code {code}, not 2:\n{out}" },
    -- `--jobs N` runs an opted-in group's cases in a bounded pool; its log is the
    -- sequential log but for the times (the cases are printed in case order, whether
    -- they finished in that order or not)
    { name := "--jobs N: an opted-in group's log is the --jobs 1 log, in case order", run := fun _ => do
        let self ← IO.appPath
        let run (args : Array String) : IO (UInt32 × String) := do
          let o ← IO.Process.output { cmd := self.toString, args }
          pure (o.exitCode, o.stdout)
        let (c1, one) ← run #["--jobs", "1", "=rig"]
        let (c4, four) ← run #["--jobs", "4", "=rig"]
        checkEq 0 c1; checkEq 0 c4
        -- the case lines, without their times (`(0.032 s)`); the group total too
        let norm (out : String) : List String :=
          (out.splitOn "\n").filterMap fun l =>
            if l.startsWith "── " then some l
            else if l.startsWith "  ✓ " || l.startsWith "  ⊘ " || l.startsWith "  ✗ " then some (l.splitOn " (").head!
            else none
        check ((norm four).length > 4) "no cases in the --jobs 4 log"
        checkEq (norm one) (norm four)
        -- and the same result
        checkEq (one.splitOn "\n" |>.find? (·.endsWith " passed, 0 failed"))
          (four.splitOn "\n" |>.find? (·.endsWith " passed, 0 failed")) }
  ]

/-- The language tour's examples (docs/tour.md): every file in `examples/tour/`, run as
`grail test` runs it (its messages, or with `-- test: run` what `main` prints, against
its `.expected`), in a package of its own so that only that file runs. -/
def tourFiles : List String :=
  ["00-hello", "01-basics", "02-data", "03-structures", "04-classes", "05-vec", "06-proofs",
   "07-quantities", "08-codata", "09-ffi", "10-hdl", "11-mistakes"]

def tourCase (f : String) : Case :=
  { name := s!"examples/tour/{f}.wiz", run := fun _ => do
      let p := s!"examples/tour/{f}"
      let dir ← mkTree [
        ("grail.wiz", "import Grail\ndef package : Package := Package.new \"tour\" |> Package.tests \"tour\" \"examples/tour\"\n"),
        (p ++ ".wiz", ← IO.FS.readFile (p ++ ".wiz")),
        (p ++ ".expected", ← IO.FS.readFile (p ++ ".expected"))]
      let tc ← toolchain
      let tc : Toolchain := { tc with cacheDir := some (← tc.cacheDir.getDM IO.FS.createTempDir) }
      let (res, _) ← runTests dir tc
      checkEq 1 res.size
      for t in res do
        if !t.ok && (t.message.splitOn "gmp.h").length > 1 then
          skip "no toolchain"; return
        check t.ok s!"{t.file}: {t.message}" }

def tourGroup : Group where
  name := "tour"
  exercise := "docs/tour.md"
  cases :=
    { name := "examples/tour/ has exactly the files the group knows", run := fun _ => do
        let mut names : Array String := #[]
        for e in ← System.FilePath.readDir "examples/tour" do
          names := names.push e.fileName
        let want := tourFiles.flatMap fun f => [f ++ ".expected", f ++ ".wiz"]
        checkEq (want.toArray.qsort (· < ·)).toList (names.qsort (· < ·)).toList } ::
    tourFiles.map tourCase

def grailSelfhostGroup : Group where
  name := "grail-selfhost"
  exercise := "Stage 23e"
  cases := [
    { name := "grail builds the self-hosted checker, the same program as the tests'", run := fun _ => do
        -- the suite's elaboration cache (`lake test -- --cache DIR`, as CI does), else a fresh one
        let tc ← toolchain
        let tc : Toolchain := { tc with cacheDir := some (← tc.cacheDir.getDM IO.FS.createTempDir) }
        let dir ← IO.FS.realPath "."
        let log ← IO.mkRef ""
        let target := Grail.Target.selfhost "selfhost-checker" "checker"
        let r ← runner dir tc { name := "wiz", targets := [target], settings := [] } 4 log
        if !(← r.build [target] [target]) then
          if ((← log.get).splitOn "gmp.h").length > 1 then skip "no toolchain"; return
          throw (IO.userError (← log.get))
        let mine := dir / ".grail" / "bin" / "selfhost-checker"
        let .ok theirs ← Tests.Elab.selfhostChecker | throw (IO.userError "the tests' checker failed")
        let work ← IO.FS.createTempDir
        IO.FS.writeFile (work / "input.wiz") "import Prelude\ndef two : Nat := 1 + 1\n#check two\n"
        let a ← IO.Process.output { cmd := mine.toString, cwd := work }
        let b ← IO.Process.output { cmd := theirs.toString, cwd := work }
        checkEq b.stdout a.stdout
        check (!a.stdout.isEmpty) "no output"
        -- again: nothing runs
        let r : Grail.Runner := { r with stats := ← IO.mkRef ({} : Grail.Stats), memo := ← IO.mkRef ({} : Grail.Memo) }
        check (← r.build [target] [target]) "the second build failed"
        checkEq 0 (← r.stats.get).ran }
  ]

/-! ## Command targets (23i), `grail run` (23j), job hygiene (23k) -/

/-- A package of commands: `upper` makes `build/up.txt` from `src/in.txt` (through a
shell), `copy` copies it (an edge by path), `show` (phony) prints it. -/
def cmdGrail (extra : String := "") : String :=
  "import Grail\ndef package : Package := Package.new \"c\"\n" ++
  "  |> Package.command (Command.new \"upper\" (Tool.path \"sh\") |> Command.arg \"-c\" |> Command.arg \"tr a-z A-Z < \\\"$1\\\"\" |> Command.arg \"sh\" |> Command.input \"src/in.txt\" |> Command.stdout \"build/up.txt\")\n" ++
  "  |> Package.command (Command.new \"copy\" (Tool.path \"cp\") |> Command.input \"build/up.txt\" |> Command.output \"build/copy.txt\")\n" ++
  "  |> Package.phony (Command.new \"show\" (Tool.path \"cat\") |> Command.input \"build/copy.txt\")\n" ++ extra

def cmdFiles (extra : String := "") : List (String × String) :=
  [("grail.wiz", cmdGrail extra), ("src/in.txt", "hello\n")]

def cmdTc : IO Toolchain := do pure { cacheDir := some (← IO.FS.createTempDir) }

def has (log needle : String) : Bool := (log.splitOn needle).length > 1

/-- A process is gone (or a zombie) within `ms` milliseconds. -/
partial def goneWithin (pid : String) (ms : Nat) : IO Bool := do
  let stat := System.FilePath.mk "/proc" / pid / "stat"
  let alive ← try pure (((← IO.FS.readFile stat).splitOn ") ")[1]?.map (·.take 1 |>.toString) != some "Z") catch _ => pure false
  if !alive then return true
  if ms == 0 then return false
  IO.sleep 100
  goneWithin pid (ms - min ms 100)

/-- Wait for a file to appear (a job writes its pid there). -/
partial def waitFor (f : System.FilePath) (ms : Nat) : IO String := do
  if ← f.pathExists then
    let t := (← IO.FS.readFile f).trimAscii.toString
    if !t.isEmpty then return t
  if ms == 0 then throw (IO.userError s!"{f} did not appear")
  IO.sleep 100
  waitFor f (ms - min ms 100)

def grailCommandsGroup : Group where
  name := "grail-commands"
  exercise := "Stage 23i–j"
  cases := [
    { name := "commands chain through their outputs; a second build runs nothing", run := fun _ => do
        let dir ← mkTree (cmdFiles)
        let tc ← cmdTc
        let (s, ok, log) ← buildLog dir tc ["upper", "copy"]
        check ok log
        checkEq 2 s.ran
        checkEq "[command upper]\n[command copy]\n" log
        checkEq "HELLO\n" (← IO.FS.readFile (dir / "build/copy.txt"))
        let (s, ok, _) ← buildLog dir tc ["copy"]
        check ok "the second build failed"
        checkEq 0 s.ran
        checkEq 2 s.upToDate },
    { name := "an edit reruns; going back and deleting an output restore it from the store", run := fun _ => do
        let dir ← mkTree (cmdFiles)
        let tc ← cmdTc
        let _ ← buildLog dir tc ["copy"]
        IO.FS.writeFile (dir / "src/in.txt") "world\n"
        let (s, _, _) ← buildLog dir tc ["copy"]
        checkEq 2 s.ran
        checkEq "WORLD\n" (← IO.FS.readFile (dir / "build/copy.txt"))
        IO.FS.writeFile (dir / "src/in.txt") "hello\n"
        let (s, _, _) ← buildLog dir tc ["copy"]
        checkEq 0 s.ran
        checkEq "HELLO\n" (← IO.FS.readFile (dir / "build/copy.txt"))
        IO.FS.removeFile (dir / "build/copy.txt")
        IO.FS.writeFile (dir / "build/up.txt") "changed by hand\n"
        let (s, _, _) ← buildLog dir tc ["copy"]
        checkEq 0 s.ran
        checkEq "HELLO\n" (← IO.FS.readFile (dir / "build/copy.txt"))
        checkEq "HELLO\n" (← IO.FS.readFile (dir / "build/up.txt")) },
    { name := "the tool's identity and the command line are in the key", run := fun _ => do
        let script := "#!/bin/sh\necho one > \"$1\"\n"
        let g (arg : String) := "import Grail\ndef package : Package := Package.new \"c\"\n" ++
          s!"  |> Package.command (Command.new \"t\" (Tool.path \"./tool.sh\") |> Command.output \"out.txt\" |> Command.arg \"{arg}\")\n"
        let dir ← mkTree [("grail.wiz", g "a"), ("tool.sh", script)]
        IO.setAccessRights (dir / "tool.sh") { user := { read := true, write := true, execution := true } }
        let tc ← cmdTc
        let (s, ok, log) ← buildLog dir tc
        check ok log
        checkEq 1 s.ran
        checkEq "one\n" (← IO.FS.readFile (dir / "out.txt"))
        IO.FS.writeFile (dir / "tool.sh") "#!/bin/sh\necho two > \"$1\"\n"
        let (s, _, _) ← buildLog dir tc
        checkEq 1 s.ran
        checkEq "two\n" (← IO.FS.readFile (dir / "out.txt"))
        IO.FS.writeFile (dir / "grail.wiz") (g "b")
        let (s, _, _) ← buildLog dir tc
        checkEq 1 s.ran },
    { name := "outputs are checked: declared but not made, made but not declared, declared twice", run := fun _ => do
        let liar := "  |> Package.command (Command.new \"liar\" (Tool.path \"sh\") |> Command.arg \"-c\" |> Command.arg \"touch \\\"$1\\\"x\" |> Command.arg \"sh\" |> Command.output \"build/l.txt\")\n"
        let dir ← mkTree (cmdFiles liar)
        let (s, ok, log) ← buildLog dir (← cmdTc) ["liar"]
        check (!ok) "the build succeeded"
        checkEq 1 s.failed
        check (has log "the declared output build/l.txt was not made") log
        check (has log "build/l.txtx was made in the output directory but is not a declared output") log
        check (!(← (dir / "build/l.txtx").pathExists)) "the undeclared file was installed"
        let twice := "  |> Package.command (Command.new \"again\" (Tool.path \"cp\") |> Command.input \"src/in.txt\" |> Command.output \"build/up.txt\")\n"
        let dir ← mkTree (cmdFiles twice)
        let (_, ok, log) ← buildLog dir (← cmdTc) ["copy"]
        check (!ok) "the build succeeded"
        check (has log "commands upper and again both declare the output build/up.txt") log
        let missing := "  |> Package.command (Command.new \"m\" (Tool.path \"cp\") |> Command.input \"src/nope.txt\" |> Command.output \"o.txt\")\n"
        let dir ← mkTree (cmdFiles missing)
        let (_, ok, log) ← buildLog dir (← cmdTc) ["m"]
        check (!ok) "the build succeeded"
        check (has log "the input src/nope.txt does not exist, and no target makes it") log },
    { name := "a failed command says how it ended, with the end of its log", run := fun _ => do
        let bad := "  |> Package.command (Command.new \"bad\" (Tool.path \"sh\") |> Command.arg \"-c\" |> Command.arg \"echo working; echo oops >&2; kill -9 $$\")\n"
        let dir ← mkTree (cmdFiles bad)
        let (_, ok, log) ← buildLog dir (← cmdTc) ["bad"]
        check (!ok) "the build succeeded"
        check (has log "✗ command bad\n  killed by signal 9 (SIGKILL: out of memory, or killed by hand?); the end of its output:\n  working\n  oops\n") log
        check (has (← IO.FS.readFile (dir / ".grail/log/bad.txt")) "oops") "no log file"
        -- a job (a check) killed with nothing to say: no longer an empty message
        checkEq "killed by signal 9 (SIGKILL: out of memory, or killed by hand?), and printed nothing"
          (Grail.failureMessage { code := 137, stdout := "", stderr := "" } 1000)
        checkEq "exit code 3; the end of its output:\nx"
          (Grail.failureMessage { code := 3, stdout := "x\n", stderr := "" } 1000)
        -- a check's own error (exit 1) is its messages, as before
        checkEq "f.wiz:1:1: error: e\n" (Grail.failureMessage { code := 1, stdout := "", stderr := "f.wiz:1:1: error: e\n" } 1000) },
    { name := "a phony command always runs, is not recorded, and is not a default target", run := fun _ => do
        let dir ← mkTree (cmdFiles)
        let tc ← cmdTc
        let (s, ok, log) ← buildLog dir tc ["show"]
        check ok log
        checkEq 3 s.ran
        check (has log "[command show]\nHELLO\n") log
        let (s, _, _) ← buildLog dir tc ["show"]
        checkEq 1 s.ran
        checkEq 2 s.upToDate
        match ← Grail.readConfig tc (← binId tc) "lib" dir with
        | .error e => throw (IO.userError e)
        | .ok (pkg, _) => checkEq ["upper", "copy"] ((pkg.targets.filter (·.isDefault)).map (·.name)) },
    { name := "stale installed outputs are removed (changed ones kept); grail clean", run := fun _ => do
        let dir ← mkTree (cmdFiles)
        let tc ← cmdTc
        let _ ← buildLog dir tc ["copy"]
        IO.FS.writeFile (dir / "grail.wiz") ((cmdGrail).replace "build/copy.txt" "build/copy2.txt")
        let (_, ok, log) ← buildLog dir tc ["copy"]
        check ok log
        check (has log "removed build/copy.txt (installed by an earlier build; no target makes it any more)") log
        check (!(← (dir / "build/copy.txt").pathExists)) "the stale output is still there"
        IO.FS.writeFile (dir / "build/copy2.txt") "mine\n"
        let ctx : Grail.Ctx := { dir, std := "lib", tc, binId := 0 }
        let report ← Grail.cleanInstalled ctx
        check (has report "kept build/copy2.txt: changed since grail installed it") report
        check (has report "removed build/up.txt") report
        checkEq "mine\n" (← IO.FS.readFile (dir / "build/copy2.txt"))
        check (!(← (dir / "build/up.txt").pathExists)) "grail clean left an installed output" },
    { name := "grail run: a command's needs are built, its arguments appended, its exit code returned", run := fun _ => do
        let ex := "  |> Package.command (Command.new \"exit\" (Tool.path \"sh\") |> Command.arg \"-c\" |> Command.arg \"test -f build/copy.txt && exit $1\" |> Command.arg \"sh\" |> Command.needs \"build/copy.txt\")\n"
        let dir ← mkTree (cmdFiles ex)
        let tc ← cmdTc
        match ← Grail.readConfig tc (← binId tc) "lib" dir with
        | .error e => throw (IO.userError e)
        | .ok (pkg, _) =>
          let log ← IO.mkRef ""
          let r ← runner dir tc pkg 1 log
          let some t := pkg.targets.find? (·.name == "exit") | throw (IO.userError "no target")
          checkEq 7 (← r.runTarget pkg.targets t #["7"])
          checkEq "[command upper]\n[command copy]\n" (← log.get) },
    { name := "an exe of the package as a command's tool", run := fun _ => do
        let tc : Toolchain := { (← toolchain) with cacheDir := some (← IO.FS.createTempDir) }
        let dir ← mkTree [("grail.wiz", "import Grail\ndef package : Package := Package.new \"p\" |> Package.exe \"hello\" \"hello.wiz\"\n" ++
                            "  |> Package.command (Command.new \"say\" (Tool.exe \"hello\") |> Command.stdout \"said.txt\")\n"),
                          ("hello.wiz", "import IO\ndef main : IO Unit := IO.println \"hello from grail\"\n")]
        let (s, ok, log) ← buildLog dir tc ["say"]
        if !ok && (has log "obj") then
          skip "no toolchain"
          return
        check ok log
        checkEq 4 s.ran
        checkEq "hello from grail\n" (← IO.FS.readFile (dir / "said.txt"))
        -- a comment: the program is rebuilt as far as its C, which doesn't change
        IO.FS.writeFile (dir / "hello.wiz") "import IO\n-- c\ndef main : IO Unit := IO.println \"hello from grail\"\n"
        let (s, _, _) ← buildLog dir tc ["say"]
        checkEq 1 s.ran },
    { name := "an installed output keeps its executable bit", run := fun _ => do
        let mk := "  |> Package.command (Command.new \"script\" (Tool.path \"sh\") |> Command.arg \"-c\" |> Command.arg \"printf '#!/bin/sh\\\\necho ran\\\\n' > \\\"$1\\\"; chmod +x \\\"$1\\\"; echo data > \\\"$2\\\"\" |> Command.arg \"sh\" |> Command.output \"bin/run.sh\" |> Command.output \"bin/data.txt\")\n"
        let dir ← mkTree (cmdFiles mk)
        let (_, ok, log) ← buildLog dir (← cmdTc) ["script"]
        check ok log
        checkEq "ran\n" (← IO.Process.output { cmd := (dir / "bin/run.sh").toString }).stdout
        check (← Grail.isExecutable (dir / "bin/run.sh")) "the script is not executable"
        check (!(← Grail.isExecutable (dir / "bin/data.txt"))) "the data file is executable" },
    { name := "two targets with one name are refused", run := fun _ => do
        let dir ← mkTree [("grail.wiz", "import Grail\ndef package : Package := Package.new \"p\" |> Package.lib \"x\" \"src\" |> Package.check \"x\" \"a.wiz\"\n")]
        let tc ← cmdTc
        match ← Grail.readConfig tc (← binId tc) "lib" dir with
        | .ok _ => throw (IO.userError "accepted")
        | .error e => check (has e "two targets are called x") e }
  ]

/-- A command that starts a grandchild (`sleep`), writes its pid, and waits. -/
def slowFiles (secs : String) : List (String × String) :=
  [("grail.wiz", "import Grail\ndef package : Package := Package.new \"s\"\n" ++
     s!"  |> Package.command (Command.new \"slow\" (Tool.path \"sh\") |> Command.arg \"-c\" |> Command.arg \"sleep {secs} & echo $! > slow.pid; wait\")\n")]

/-- Start grail (this test driver, `--grail`) building `slow`, and kill it with `signal`
once the job has started: the job's grandchild must go too. -/
def killGrailCase (signal : String) : Case :=
    { name := s!"killing grail (SIG{signal}) kills its jobs", run := fun _ => do
        let dir ← mkTree (slowFiles (if signal == "KILL" then "298" else "297"))
        let cache ← IO.FS.createTempDir
        let self ← IO.appPath
        let args := #["--grail", "-C", dir.toString, "--cache", cache.toString, "build", "slow"]
        let child ← IO.Process.spawn { cmd := self.toString, args, stdout := .null, stderr := .null }
        let pid ← waitFor (dir / "slow.pid") 60000
        let o ← IO.Process.output { cmd := "kill", args := #[s!"-{signal}", toString child.pid] }
        checkEq 0 o.exitCode
        let _ ← child.wait
        check (← goneWithin pid 5000) s!"the job's process {pid} outlived grail" }

def grailHygieneGroup : Group where
  name := "grail-hygiene"
  exercise := "Stage 23k"
  cases := [
    killGrailCase "KILL",
    killGrailCase "TERM",
    { name := "a time limit kills the job's whole process group", run := fun _ => do
        let dir ← mkTree (slowFiles "296")
        let (_, ok, log) ← buildLog dir (← cmdTc) (timeoutMs := some 1500)
        check (!ok) "the build succeeded"
        check (has log "timed out after 1.500 s (its process group was killed)") log
        let pid ← waitFor (dir / "slow.pid") 1000
        check (← goneWithin pid 5000) s!"the job's process {pid} outlived its time limit" }
  ]

/-- This module's test groups, which `Tests/Main.lean` runs: one per line, in sorted
order, so that branches adding groups rarely touch the same lines. A new group also
needs a shard in `.github/test-shards.json` (CI checks). -/
def groups : List Group :=
  grailCommandsGroup ::
  grailDepsGroup ::
  grailGroup ::
  grailHygieneGroup ::
  grailJobsGroup ::
  grailSelfhostGroup ::
  modulesGroup ::
  testRunnerGroup ::
  toolchainGroup ::
  tourGroup ::
  []

end Tests.Grail
