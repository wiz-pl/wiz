import Tests.Grail

namespace Tests.Grail
open Wiz Tests

/-- A module's cache key: the fast half (old names) and the SHA-256 half (regions,
manifests). These tests use no toolchain/target namespace, as `elaborateCached`'s defaults
do. -/
def moduleCacheKey (m : Std.HashMap Name (System.FilePath × String)) (toolchain : UInt64)
    (n : Name) : Cache.Key :=
  let loader := loaderOf m
  let strongToolchain := Cache.toolchainOptionsTag "" false false NativeRun.defaultFuel none
  { fast := Cache.moduleKey loader (fun _ => none) toolchain n (trusted := Tests.libModule)
    strong := Cache.moduleKeyStrong loader (fun _ => none) toolchain n (trusted := Tests.libModule)
      (strongToolchain := strongToolchain)
    toolchain := strongToolchain }

/-- A digest of one cached effect, for comparing the text path with the region path
(the effect types have no `BEq`: terms are not compared structurally). -/
def effectSig (e : Cache.Effect ZeroOneMany) : String :=
  s!"{e.decls.toList.map (·.name)}|{e.messages.toList.map (·.text)}|{e.infos.size}|" ++
  s!"{e.sites.size}|{e.docs.size}|{e.instances.size}|{e.builtins.length}"

def effectSigs (es : Array (Cache.Effect ZeroOneMany)) : List String := es.toList.map effectSig

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
    { name := "cache keys: SHA-256 keys are domain-separated and length-framed", run := fun _ => do
        let digest := Smt.Sha256.hexFramed "wiz-cache-test-v1"
        checkEq 64 (digest ["ab", "c"]).length
        -- (without lengths, ["ab", "c"] and ["a", "bc"] would collide)
        check (digest ["ab", "c"] != digest ["a", "bc"]) "fields are concatenated without framing"
        check (digest ["ab", "c"] != Smt.Sha256.hexFramed "wiz-cache-test-v2" ["ab", "c"])
          "the domain does not separate keys"
        check (digest ["ab", "c"] != digest ["ab", "c", ""]) "an empty trailing field is free"
        let loader : Name → Option String := fun n => if n == "M" then some "def x : Nat := 1\n" else none
        let k := Cache.moduleKeyStrong loader (fun _ => none) 0 "M"
        checkEq 64 k.length
        checkEq k (Cache.moduleKeyStrong loader (fun _ => none) 0 "M")
        check (k != Cache.moduleKeyStrong loader (fun _ => none) 1 "M") "the toolchain is not in the strong key"
        check (k != Cache.moduleKeyStrong loader (fun _ => none) 0 "M" (strongToolchain := "tc-a"))
          "the strong toolchain is not in the module key"
        check (k != Cache.moduleKeyStrong loader (fun _ => none) 0 "M" (targetTag := "target-a"))
          "the target is not in the module key" },
    { name := "SHA-256: the NIST FIPS 180-4 known-answer vectors", run := fun _ => do
        -- Every padding case from FIPS 180-4 (and NIST's CAVP examples): the empty
        -- message, one short block, the 448-bit message (which still fits in one block but
        -- needs the length in a second word), the 896-bit two-block message, and the
        -- 1,000,000-'a' multi-block message. These are the trusted SMT cache's key
        -- function, so a wrong digest must fail here rather than only show up as a
        -- domain-separation inequality.
        checkEq "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
          (Smt.Sha256.hex "")
        checkEq "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
          (Smt.Sha256.hex "abc")
        checkEq "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
          (Smt.Sha256.hex "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")
        checkEq "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1"
          (Smt.Sha256.hex
            "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu")
        checkEq "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"
          (Smt.Sha256.hex (String.ofList (List.replicate 1000000 'a'))) },
    { name := "target and toolchain ids: separate SHA-256 namespaces, not the 64-bit build id", run := fun _ => do
        let tc : Toolchain := {}
        let other : Toolchain := { tc with cflags := ["-O2"] }
        checkEq 64 tc.tag.length
        checkEq 64 tc.targetTag.length
        check (tc.tag != other.tag) "cflags are not in the toolchain tag"
        check (tc.targetTag == other.targetTag) "the target tag depends on compiler flags"
        checkEq tc.tag ({ tc with cacheDir := some "/tmp/c" } : Toolchain).tag
        check (tc.tag != toString tc.id) "the strong tag is just the 64-bit id"
        -- (the elaboration cache's example namespaces the same inputs)
        let loader : Name → Option String := fun n => if n == "M" then some "def x : Nat := 1\n" else none
        check (Cache.moduleKeyStrong loader (fun _ => none) 0 "M" (strongToolchain := tc.tag)
          != Cache.moduleKeyStrong loader (fun _ => none) 0 "M" (strongToolchain := other.tag))
          "two toolchains share a module key"
        check (Cache.moduleKeyStrong loader (fun _ => none) 0 "M" (targetTag := tc.targetTag)
          != Cache.moduleKeyStrong loader (fun _ => none) 0 "M" (targetTag := "another-target"))
          "two targets share a module key" },
    { name := "cache keys: a manifest binds the SHA-256 key, so a 64-bit collision is a miss", run := fun _ => do
        let hex (c : Char) : String := String.ofList (List.replicate 64 c)
        let k1 : Cache.Key := { fast := 42, strong := hex 'a', toolchain := "tc", target := "target",
                                binary := "binary" }
        let k2 : Cache.Key := { k1 with strong := hex 'b' }
        let e : Cache.ManifestEntry :=
          { kind := "wizc", key := k1.fast, keySha := k1.strong,
            file := s!"{mixHash 1 k1.fast}.wizc", size := 1, sha256 := hex 'c',
            format := Cache.salt.toNat }
        check (e.valid 1) "the fixture entry is not self-consistent"
        let m0 : Cache.ModuleManifest :=
          { module := "M", key := k1.fast, keySha := k1.strong, binary := 1,
            toolchainTag := k1.toolchain, targetTag := k1.target, entries := #[e] }
        let m := { m0 with root := m0.rootOf }
        check (m.valid k1 1 "" "") "the manifest does not wake its own key"
        check (!(m.valid k2 1 "" "")) "the same fast key with another SHA-256 key was accepted"
        check (!(m.valid { k1 with toolchain := "other" } 1 "" "")) "the toolchain tag was not checked"
        check (!(m.valid { k1 with target := "other" } 1 "" "")) "the target tag was not checked"
        check (Cache.manifestFileName 1 k1 != Cache.manifestFileName 1 k2)
          "two strong keys share a manifest file"
        let dir ← IO.FS.createTempDir
        let ms ← Cache.ManifestStore.create (some dir) [] 1 "" "" .warn
        ms.writeManifest k1 "M" #[e] none
        ms.load k1
        check ((← ms.entryFor k1).isSome) "the written entry was not indexed under its SHA-256 key"
        ms.load k2
        check ((← ms.entryFor k2).isNone) "a colliding fast key found another key's entry" },
    { name := "cache keys: editing an include_str file changes the fast and SHA-256 keys", run := fun _ => do
        let dir ← mkTree [("M.wiz", "include_str \"data.txt\"\ndef x : Nat := 1\n"),
                          ("data.txt", "one\n")]
        let src ← IO.FS.readFile (dir / "M.wiz")
        let loader : Name → Option String := fun n => if n == "M" then some src else none
        let mods : Std.HashMap Name (System.FilePath × String) :=
          ({} : Std.HashMap Name (System.FilePath × String)).insert "M" (dir / "M.wiz", src)
        let keys : IO (UInt64 × String) := do
          let table ← Module.includeTable dir src mods
          let includes := Module.includeResolver table
          pure (Cache.moduleKey loader (fun _ => none) 0 "M" (includes := includes),
                Cache.moduleKeyStrong loader (fun _ => none) 0 "M" (includes := includes))
        let (fast1, strong1) ← keys
        IO.FS.writeFile (dir / "data.txt") "two\n"
        let (fast2, strong2) ← keys
        check (fast1 != fast2) "the include edit did not change the fast key"
        check (strong1 != strong2) "the include edit did not change the SHA-256 key"
        checkEq 64 strong2.length
        -- (going back to the old contents restores both halves)
        IO.FS.writeFile (dir / "data.txt") "one\n"
        let (fast3, strong3) ← keys
        checkEq fast1 fast3
        checkEq strong1 strong3 },
    { name := "cache keys: an old-format region and manifest are a miss and regenerate", run := fun _ => do
        let dir ← mkTree [("M.wiz", "import Prelude\ndef x : Nat := 1\n")]
        let ms ← Module.loadAll ["lib", dir]
        let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, loader := loaderOf ms }
        let cache ← IO.FS.createTempDir
        let rig := RigTag.tag (R := ZeroOneMany)
        let binary ← Cache.binaryId (some cache)
        let k := moduleCacheKey ms 0 "M"
        -- (a format-2 region under the new strong name: it has no SHA-256 fields, so it
        -- is a miss and the write cache replaces it)
        let _ ← Cache.writeRegionFile (R := ZeroOneMany) (cache / Cache.regionFileName binary k)
          { magic := Cache.regionMagic, format := 2, binary, textSalt := Cache.salt, rig,
            module := "M", key := k.fast, keySha := k.strong }
        let rstats ← IO.mkRef ({} : Cache.RegionCounts)
        let opts : Cache.RegionOptions := { rig, stats := some rstats }
        let src := "import M\n#eval x\n"
        let (s0, _) ← Cache.elaborateCached (some cache) [] src init 0 (region := some opts)
          (verify := .warn) (rig := rig)
        check (!s0.messages.any (·.severity == .error)) s!"messages: {s0.messages.toList.map (·.text)}"
        check ((← rstats.get).misses > 0) "the old-format region was not a miss"
        let some a ← Cache.readModuleRegion (R := ZeroOneMany) cache binary rig k
          | throw (IO.userError "the region was not regenerated")
        checkEq Cache.regionFormat a.format
        checkEq k.strong a.keySha
        -- (a format-1 manifest: the loader rejects it and the run writes format 2)
        let some mf ← manifestFor cache "M"
          | throw (IO.userError "no manifest for M")
        let old ← IO.FS.readFile mf
        IO.FS.writeFile mf (old.replace "(format 2)" "(format 1)")
        let (s1, _) ← Cache.elaborateCached (some cache) [] src init 0 (region := some opts) (verify := .warn) (rig := rig)
        checkEq (s0.messages.toList.map (·.render src)) (s1.messages.toList.map (·.render src))
        let some text := (String.fromUTF8? (← IO.FS.readBinFile mf))
          | throw (IO.userError "the manifest is not UTF-8")
        let some man := Cache.parseManifest text
          | throw (IO.userError "the manifest was not rewritten")
        checkEq Cache.manifestFormat man.format
        checkEq k.strong man.keySha },
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
        checkEq false (← store.seen (778 : UInt64))
        checkEq (repr before).pretty (repr (← snapshot r1)).pretty
        let memory ← Cache.Store.layered (R := ZeroOneMany) none [] binary
        checkEq false (← memory.seen (779 : UInt64))
        memory.markSeen (779 : UInt64) "M"
        checkEq true (← memory.seen (779 : UInt64)) },
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
        -- the fixed header (13u): a later import is the error, not a module the frontend loads
        let s := runFrontend (R := ZeroOneMany) "import Prelude\ndef two : Nat := 2\nimport Sneaky\n" { trustedModule := Tests.libModule, loader := loaderOf ms }
        check (s.messages.any fun m => m.code == "import-order") s!"runFrontend, after a definition: {s.messages.toList.map (·.text)}"
        let (s, _) := Query.elaborate (R := ZeroOneMany) {} src { trustedModule := Tests.libModule, loader := loaderOf ms, termInfo := true }
        check (sneaky s) s!"the language server's engine: {s.messages.toList.map (·.text)}"
        -- through the server: the diagnostic is at the import
        let srv : LSP.Server := { libs := ms.fold (fun m k (p, t) => m.insert k (p.toString, t)) {}, trusted := ["Prelude"] }
        let (_, out) ← LSP.handle srv (Lean.Json.mkObj [("jsonrpc", "2.0"), ("method", "textDocument/didOpen"),
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
                    "import M.C\nimport M.B\n" ++ boomA, "import M.Base\nimport M.A\ndef b : Bool := Bool.false\n" ++ boomA,
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
        let k := moduleCacheKey ms 0 "M"
        -- one region for the module, not one per command
        let regs ← regionFiles cache
        checkEq 1 (regs.filter (fun p => p.fileName == some (Cache.regionFileName binary k))).size
        let some a ← Cache.readModuleRegion (R := ZeroOneMany) cache binary rig k
          | throw (IO.userError "M has no region")
        checkEq "M" a.module
        checkEq k.fast a.key
        checkEq k.strong a.keySha
        checkEq Cache.regionFormat a.format
        checkEq Cache.salt a.textSalt
        checkEq Cache.regionMagic a.magic
        check (a.effects.size > 0) "the region holds no effects"
        check (!a.complete) "M imports Prelude, so it is not complete"
        check (a.rerun.size > 0) "M's import is not recorded for the rerun path"
        -- (a pure cache: write the effects back out and read them; every field survives)
        let dir2 ← IO.FS.createTempDir
        let k1 : Cache.Key := { k with fast := k.fast + 1 }
        let _ ← Cache.writeModuleRegion dir2 binary rig k1 "M" a.effects a.keys a.complete a.rerun
        let some b ← Cache.readModuleRegion (R := ZeroOneMany) dir2 binary rig k1
          | throw (IO.userError "the region written for M does not read back")
        checkEq (effectSigs a.effects) (effectSigs b.effects)
        checkEq a.keys.toList b.keys.toList
        checkEq a.effects.size a.keys.size
        checkEq k1.fast b.key
        -- (the tags are checked: another rig, format or key is not this module's artifact)
        check (b.fits binary k1 rig) "a region does not fit itself"
        check (!(b.fits binary k1 "nat")) "the rig is not checked"
        check (!(b.fits binary { k1 with fast := k1.fast + 1 } rig)) "the key is not checked"
        check (!(b.fits binary { k1 with strong := String.ofList (List.replicate 64 '0') } rig))
          "the SHA-256 key is not checked"
        check (!(b.fits binary { k1 with toolchain := "toolchain-2" } rig))
          "the toolchain namespace is not checked"
        check (!(b.fits binary { k1 with target := "target-2" } rig))
          "the target namespace is not checked"
        check (!(b.fits binary { k1 with binary := "binary-2" } rig))
          "the binary SHA-256 is not checked"
        let badFormat : Cache.ModuleArtifact ZeroOneMany := { b with format := 999 }
        check (!(badFormat.fits binary k1 rig)) "the format is not checked"
        let badBinary : Cache.ModuleArtifact ZeroOneMany := { b with binary := binary + 1 }
        check (!(badBinary.fits binary k1 rig)) "the binary is not checked"
        let badSalt : Cache.ModuleArtifact ZeroOneMany := { b with textSalt := Cache.salt + 1 }
        check (!(badSalt.fits binary k1 rig)) "the salt is not checked" },
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
        let k := moduleCacheKey ms 0 "M"
        let _ ← Cache.writeRegionFile (R := ZeroOneMany) (cache / Cache.regionFileName binary k)
          { magic := Cache.regionMagic, format := 999, binary, textSalt := Cache.salt, rig,
            module := "M", key := k.fast, keySha := k.strong }
        let after2 ← stats.get
        let (s2, _) ← Cache.elaborateCached (some cache) [] src init 0 (region := some opts)
        checkEq good (s2.messages.toList.map (·.render src))
        check ((← stats.get).misses > after2.misses) "a mismatched region was not a miss"
        let some a ← Cache.readModuleRegion (R := ZeroOneMany) cache binary rig k
          | throw (IO.userError "the mismatched region was not rewritten")
        checkEq Cache.regionFormat a.format
        check (a.effects.size > 0) "the rewritten region holds no effects" },
    { name := "a region checksum catches a bit flip and a truncation (miss, text fallback, repair)", run := fun _ => do
        -- (format 2: a `.wizs` sidecar holds the 8-byte hash of the image's bytes)
        let dir ← mkTree [("M.wiz", "import Prelude\ndef x : Nat := 1 + 1\n")]
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
        -- (the sidecar round-trips: a file's hash reads back as its checksum)
        let probe := cache / "checksum-probe.wizr"
        IO.FS.writeFile probe "abcdefgh"
        let sum ← Cache.checksumFile probe
        IO.FS.writeBinFile (Cache.regionSumFile probe) (Cache.u64Bytes sum)
        checkEq (some sum) (← Cache.regionFileChecksum probe)
        let _ ← flipByte probe 2
        checkEq (none : Option UInt64) (← Cache.regionFileChecksum probe)
        -- (a good region carries one)
        let binary ← Cache.binaryId (some cache)
        let k := moduleCacheKey ms 0 "M"
        let f := cache / Cache.regionFileName binary k
        check (← Cache.regionFileChecksum f).isSome "a fresh region has no checksum"
        -- (a same-size bit flip in the payload: a miss, not a load error or a wrong term)
        let _ ← flipByte f
        checkEq (none : Option UInt64) (← Cache.regionFileChecksum f)
        let m0 ← stats.get
        let (s1, _) ← Cache.elaborateCached (some cache) [] src init 0 (region := some opts)
        checkEq good (s1.messages.toList.map (·.render src))
        check ((← stats.get).misses > m0.misses) "a flipped byte was not a miss"
        check (← Cache.regionFileChecksum f).isSome "the write cache did not repair the region"
        -- (the repaired region is served again)
        let h0 ← stats.get
        let (s2, _) ← Cache.elaborateCached (some cache) [] src init 0 (region := some opts)
        check ((← stats.get).hits > h0.hits) "the repaired region was not served"
        checkEq good (s2.messages.toList.map (·.render src))
        -- (truncation: one byte short, then the payload cut in half)
        for (what, keep) in ([("one byte short", fun n => n - 1), ("half the payload", fun n => n / 2)] :
            List (String × (Nat → Nat))) do
          let b ← IO.FS.readBinFile f
          IO.FS.writeBinFile f (b.extract 0 (keep b.size))
          checkEq (none : Option UInt64) (← Cache.regionFileChecksum f)
          let m1 ← stats.get
          let (s3, _) ← Cache.elaborateCached (some cache) [] src init 0 (region := some opts)
          checkEq good (s3.messages.toList.map (·.render src))
          check ((← stats.get).misses > m1.misses) s!"a region {what} was not a miss"
          check (← Cache.regionFileChecksum f).isSome s!"a region {what} was not repaired" },
    { name := "a read-only region with a bad checksum is a miss, and the layer is left alone", run := fun _ => do
        let dir ← mkTree libFiles
        let ms ← Module.loadAll ["lib", dir]
        let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, loader := loaderOf ms }
        let rig := RigTag.tag (R := ZeroOneMany)
        let stats ← IO.mkRef ({} : Cache.RegionCounts)
        let opts : Cache.RegionOptions := { rig, stats := some stats }
        let src := "import Use\nimport Other\n#eval four + one\n"
        let ro ← IO.FS.createTempDir
        let (cold, _) ← Cache.elaborateCached (some ro) [] src init 0 (region := some opts)
        let expected := cold.messages.toList.map (·.render src)
        -- (corrupt one region's payload in the read-only layer)
        let binary ← Cache.binaryId (some ro)
        let k := moduleCacheKey ms 0 "Use"
        let bad := ro / Cache.regionFileName binary k
        let _ ← flipByte bad
        checkEq (none : Option UInt64) (← Cache.regionFileChecksum bad)
        let before ← snapshot ro
        -- (served with a write cache in front: the text entry answers, nothing is repaired)
        let write ← IO.FS.createTempDir
        let m0 ← stats.get
        let (s1, _) ← Cache.elaborateCached (some write) [ro] src init 0 (region := some opts)
        checkEq expected (s1.messages.toList.map (·.render src))
        check ((← stats.get).misses > m0.misses) "a bad read-only checksum was not a miss"
        checkEq before (← snapshot ro)
        check (!(← Cache.regionFileChecksum bad).isSome) "the read-only region was repaired" },
    { name := "cache prune: old keyed files go, fresh and unrelated ones stay, ro layers are untouched", run := fun _ => do
        let write ← IO.FS.createTempDir
        let ro ← IO.FS.createTempDir
        IO.FS.createDirAll (write / "bin")
        let old (dir : System.FilePath) (name : String) : IO System.FilePath := do
          let f := dir / name
          IO.FS.writeFile f "x"
          touchAgo f "40 days ago"
          pure f
        let oldEntry ← old write "a.wizc"
        let oldMarker ← old write "a.wizm"
        let oldRegion ← old write "a.wizr"
        let oldSum ← old write "a.wizs"
        let fresh ← old write "b.wizc"
        touchAgo fresh "1 day ago"
        let other ← old write "notes.txt"
        let binMemo ← old (write / "bin") "stamp"
        let roEntry ← old ro "a.wizc"
        let before ← snapshot ro
        let now := (← Std.Time.Timestamp.now).val.toSeconds.toInt
        -- (dry run: counted, nothing removed; `now` is explicit, so a clock cannot race the test)
        let d ← Cache.pruneCache write 7 (dryRun := true) (now := some now)
        checkEq 4 d.total
        checkEq 1 d.entries
        checkEq 1 d.markers
        checkEq 1 d.regions
        checkEq 1 d.sums
        for f in [oldEntry, oldMarker, oldRegion, oldSum] do
          check (← f.pathExists) s!"the dry run removed {f}"
        -- (the real run removes the old keyed files only)
        let c ← Cache.pruneCache write 7 (now := some now)
        checkEq 4 c.total
        check (!(← oldEntry.pathExists) && !(← oldMarker.pathExists) && !(← oldRegion.pathExists) &&
               !(← oldSum.pathExists)) "an old keyed file survived"
        check (← fresh.pathExists) "a fresh entry was pruned"
        check (← other.pathExists) "a non-cache file was pruned"
        check (← binMemo.pathExists) "the binary memo was pruned"
        check (← roEntry.pathExists) "a read-only layer's file was pruned"
        checkEq before (← snapshot ro)
        let summary := c.render 7 false write
        check ((summary.splitOn "removed 4 files (1 .wizc, 1 .wizm, 1 .wizr, 1 .wizs)").length > 1) summary
        -- (a pruned entry is just a miss: a warm cache still works, and is rewritten)
        let dir ← mkTree [("M.wiz", "import Prelude\ndef x : Nat := 1\n")]
        let ms ← Module.loadAll ["lib", dir]
        let cache ← IO.FS.createTempDir
        let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, loader := loaderOf ms }
        let rig := RigTag.tag (R := ZeroOneMany)
        let src := "import M\n#eval x\n"
        let (r0, _) ← Cache.elaborateCached (some cache) [] src init 0 (region := some { rig })
        let expected := r0.messages.toList.map (·.render src)
        let far := now + 400 * 86400
        let n ← Cache.pruneCache cache 7 (now := some far)
        check (n.total > 0) "a warm cache had nothing to prune"
        checkEq #[] (← regionFiles cache)
        let (r1, _) ← Cache.elaborateCached (some cache) [] src init 0 (region := some { rig })
        checkEq expected (r1.messages.toList.map (·.render src))
        check ((← regionFiles cache).size > 0) "the pruned region was not rewritten" },
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
        let k2 := moduleCacheKey ms 0 "M"
        let binary ← Cache.binaryId (some cache)
        check (← (cache / Cache.regionFileName binary k2).pathExists) "no region for the edited module"
        let some a ← Cache.readModuleRegion (R := ZeroOneMany) cache binary rig k2
          | throw (IO.userError "no readable region for the edited module")
        checkEq k2.fast a.key },
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
        let k := moduleCacheKey ms 0 "Use"
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

builtin_initialize registerGroup modulesGroup

end Tests.Grail
