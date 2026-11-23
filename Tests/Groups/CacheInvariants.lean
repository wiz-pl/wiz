import Tests.Grail

/-!
# Cache and region invariants

The spec is `wiz-notes/cache-invariants.md`. Each case pins one invariant of the
elaboration cache's containment boundary (commit `bd6a330df`):

* a fast-only key is an index, not an identity (I1/I2);
* a region is never served without a manifest entry (I3);
* a foreign `--cache-ro` layer is refused unless opted in (I5);
* a tampered manifest or region is a miss (I2/I3/I10);
* pruning and every read-only command leave a `--cache-ro` layer alone (I6/I9);
* `--cache-verify off` reads and writes no regions (I7);
* the generation index only expires a layer, it never selects an entry (I8);
* a manifest cannot name a file outside its layer (I4);
* the write cache is integrity, not authenticity (I11): a self-consistent rewrite is
  served, and that is the documented limit, not a bug to "fix" by weakening the default;
* region repair converges (K1): after a tamper, a further run hits, and two writes of one
  artifact give one SHA-256 (T4/T4b);
* poison is global per key (I12 option a, T11);
* per-layer `--cache-ro-unsigned` is the pending task 11 contract (T12, skipped until K3).

The cases are independent of `=toolchain`/`=modules`; those groups keep their own
end-to-end coverage. This group is the spec's executable form.
-/

namespace Tests.Grail
open Wiz Tests

/-- The module key `Cache.elaborateCached` uses for `n` with its default options. -/
def invModuleKey (m : Std.HashMap Name (System.FilePath × String)) (n : Name) : Cache.Key :=
  let loader := loaderOf m
  let strongToolchain := Cache.toolchainOptionsTag "" false false NativeRun.defaultFuel none
  { fast := Cache.moduleKey loader (fun _ => none) 0 n (trusted := Tests.libModule)
    strong := Cache.moduleKeyStrong loader (fun _ => none) 0 n (trusted := Tests.libModule)
      (strongToolchain := strongToolchain)
    toolchain := strongToolchain }

/-- An effect that declares `name : Nat := n` (or a `False` claim when `n` is none). -/
def invEffect (name : Name) (n : Option Nat) : Cache.Effect ZeroOneMany :=
  match n with
  | some k => { decls := #[{ name, type := .const "Nat" [], value := some (.natLit k) }] }
  | none => { decls := #[{ name, type := .const "False" [],
                           value := some (.const "Nat.zero" []) }] }

/-- The literal a declaration's value is, for checking a forged replay. -/
def invNatValue? (s : CommandState ZeroOneMany) (n : Name) : Option Nat :=
  match s.globals.find? n with
  | some d => match d.value with | some (.natLit k) => some k | _ => none
  | none => none

/-- Every file under `dir`, recursively. -/
partial def invEveryFile (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out := #[]
  for e in ← dir.readDir do
    if ← e.path.isDir then out := out ++ (← invEveryFile e.path)
    else out := out.push e.path
  pure out

/-- Change the first digit of a manifest's root, so its own root no longer matches. -/
def invTamperRoot (f : System.FilePath) : IO Unit := do
  let text ← IO.FS.readFile f
  match text.splitOn "(root " with
  | before :: after :: _ =>
    let after := after.drop 1
    let bad := if after.startsWith "0" then "1" else "0"
    IO.FS.writeFile f (before ++ "(root " ++ bad ++ after.drop 1)
  | _ => throw (IO.userError s!"{f}: no root field")

/-- A self-consistent manifest holding `entries` (and no region), with its root computed. -/
def invManifest (binary : UInt64) (key : Cache.Key) (entries : Array Cache.ManifestEntry) :
    Cache.ModuleManifest :=
  let m0 : Cache.ModuleManifest :=
    { module := "M", key := key.fast, keySha := key.strong, binary, entries }
  { m0 with root := m0.rootOf }

/-- The `wiz` binary the suite builds. -/
def invWiz : IO String := do pure (← IO.FS.realPath ".lake/build/bin/wiz").toString

/-- A cold `elaborateCached` run into `cache` (warn, region cache on). -/
def invCold (cache : System.FilePath) (src : String) (init : CommandState ZeroOneMany)
    (rig : String) (opts : Cache.RegionOptions := { rig := "" })
    (verify : Cache.VerifyMode := .warn) : IO (CommandState ZeroOneMany) := do
  let opts := if opts.rig.isEmpty then { opts with rig := rig } else opts
  pure (← Cache.elaborateCached (some cache) [] src init 0 (region := some opts)
    (verify := verify) (rig := rig)).1

/-- The number before `label` on the stats line that starts with `pfx` in `err`
(none: no such line). Exact field, so "10 modules" is not "0 modules". -/
def invStat (err pfx label : String) : Option Nat := do
  let line : String ← (err.splitOn "\n").find? (·.startsWith pfx)
  let parts : List String := (line.drop pfx.length).toString.splitOn ", "
  let field : String ← parts.find? (fun (p : String) =>
    let words := p.splitOn " "
    (" ".intercalate (words.drop 1)).startsWith label)
  (field.splitOn " ").head?.bind String.toNat?

def cacheInvariantsGroup : Group where
  name := "cache-invariants"
  exercise := "Stage 23a–c (cache containment)"
  shard := "library"
  cases := [
    /- I1/I2 — the fast half names a file, the strong half is the identity. -/
    { name := "a fast-only key is a miss: an index cannot select a manifested effect", run := fun _ => do
        let write ← IO.FS.createTempDir
        let binary : UInt64 := 4242
        let fast : UInt64 := 7
        let forged := invEffect "forgedFast" none
        IO.FS.writeFile (write / s!"{mixHash binary fast}.wizc") forged.toSx.render
        -- (an unmanifested fast-only entry is a miss in warn and strict; off is the
        -- explicit unverified mode)
        for mode in [Cache.VerifyMode.warn, .strict] do
          let store ← Cache.Store.layered (R := ZeroOneMany) (some write) [] binary mode
          check (← store.get fast).isNone s!"{repr mode}: a fast-only entry was served"
          check (← store.getEntry (Cache.Key.ofFast fast)).isNone
            s!"{repr mode}: a fast-only entry was served by getEntry"
        let off ← Cache.Store.layered (R := ZeroOneMany) (some write) [] binary .off
        check (← off.get fast).isSome "the explicit off mode lost the old lookup"
        -- (a manifested strong key is served under its strong id, and only that id:
        -- Key.ofFast and a colliding strong key select nothing)
        let strongA := String.ofList (List.replicate 64 'a')
        let strongB := String.ofList (List.replicate 64 'b')
        let keyA : Cache.Key := { fast, strong := strongA }
        let eA := invEffect "strongA" (some 1)
        IO.FS.writeFile (write / s!"{mixHash binary fast}.wizc") eA.toSx.render
        let ms ← Cache.ManifestStore.create (some write) [] binary "" "" .warn
        ms.writeManifest keyA "M" #[Cache.ManifestEntry.ofEffect binary keyA eA] none
        ms.load keyA
        check (← ms.entryFor keyA).isSome "the manifested strong key was not indexed"
        check (← ms.entryFor (Cache.Key.ofFast fast)).isNone
          "Key.ofFast found a strong-keyed entry"
        check (← ms.entryFor { keyA with strong := strongB }).isNone
          "a colliding strong key found another entry" },
    /- I3 — a region is a type-erased image; only a manifest entry binds it. -/
    { name := "a region with no manifest entry is never served (warn, strict, off)", run := fun _ => do
        let dir ← mkTree [("M.wiz", "import Prelude\ndef x : Nat := 1 + 1\n")]
        let ms ← Module.loadAll ["lib", dir]
        let cache ← IO.FS.createTempDir
        let binary ← Cache.binaryId (some cache)
        let k := invModuleKey ms "M"
        let rig := RigTag.tag (R := ZeroOneMany)
        let opts : Cache.RegionOptions := { rig }
        let forged := invEffect "forgedRegion" none
        -- (a valid, correctly tagged region: the file itself is intact)
        let _ ← Cache.writeModuleRegion (R := ZeroOneMany) cache binary rig k "M"
          #[forged] #[k.fast]
        check ((← regionFiles cache).size == 1) "no region was written"
        check (← Cache.readModuleRegion (R := ZeroOneMany) cache binary rig k).isSome
          "the region fixture is not readable"
        for mode in [Cache.VerifyMode.warn, .strict, .off] do
          let store ← Cache.Store.layeredRegion (R := ZeroOneMany) (some cache) [] binary opts
            mode rig
          check (← store.getRegion k).isNone
            s!"{repr mode}: an unmanifested region was served"
        -- (a read-only layer is not served by off either: no region, no manifest)
        let roStore ← Cache.Store.layeredRegion (R := ZeroOneMany) none [cache] binary opts
          .off rig
        check (← roStore.getRegion k).isNone
          "an unmanifested region was served from a read-only layer"
        -- (a manifest for the module that omits the region does not make it servable)
        let tag ← Cache.toolchainTag (some cache)
        let ms0 ← Cache.ManifestStore.create (some cache) [] binary tag rig .warn
        ms0.writeManifest k "M" #[] none
        let store0 ← Cache.Store.layeredRegion (R := ZeroOneMany) (some cache) [] binary opts
          .warn rig
        check (← store0.getRegion k).isNone "a region a manifest omits was served"
        -- (a manifest that lists the region and then fails its root poisons the key)
        let rf := cache / Cache.regionFileName binary k
        let bytes ← IO.FS.readBinFile rf
        let rent := Cache.ManifestEntry.ofBytes "wizr" k (rf.fileName.getD "") bytes
        let ms1 ← Cache.ManifestStore.create (some cache) [] binary tag rig .warn
        ms1.writeManifest k "M" #[] (some rent)
        let store1 ← Cache.Store.layeredRegion (R := ZeroOneMany) (some cache) [] binary opts
          .warn rig
        check (← store1.getRegion k).isSome "the listed region was not served"
        let some mf ← manifestFor cache "M"
          | throw (IO.userError "no manifest for M")
        invTamperRoot mf
        let store2 ← Cache.Store.layeredRegion (R := ZeroOneMany) (some cache) [] binary opts
          .warn rig
        check (← store2.getRegion k).isNone "a region named by a poisoned manifest was served" },
    /- I5/I12 — a foreign layer is default-deny; only an explicit opt-in serves it. -/
    { name := "a foreign --cache-ro layer is refused by default; the opt-ins serve it", run := fun _ => do
        let dir ← mkTree [("M.wiz", "import Prelude\ndef x : Nat := 2\n"),
                          ("main.wiz", "import M\n#eval x\n")]
        -- (the API path: cold write into a layer, then read it as a foreign layer)
        let ms ← Module.loadAll ["lib", dir]
        let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, loader := loaderOf ms }
        let rig := RigTag.tag (R := ZeroOneMany)
        let ro ← IO.FS.createTempDir
        let src := "import M\n#eval x\n"
        let cold ← invCold ro src init rig
        let expected := cold.messages.toList.map (·.render src)
        check (!cold.messages.any (·.severity == .error)) s!"cold: {expected}"
        let before ← snapshot ro
        -- (default: no manifest is loaded from the layer, so every command misses)
        let stats0 ← IO.mkRef ({} : Cache.VerifyCounts)
        let rstats0 ← IO.mkRef ({} : Cache.RegionCounts)
        let (s0, hits0) ← Cache.elaborateCached none [ro] src init 0
          (region := some { rig, stats := some rstats0 })
          (verify := .warn) (rig := rig) (stats := some stats0)
        checkEq expected (s0.messages.toList.map (·.render src))
        checkEq 0 hits0
        checkEq 0 (← stats0.get).regions
        checkEq before (← snapshot ro)
        -- (`--cache-verify off` is the other explicit opt-in: text only, no regions)
        let stats2 ← IO.mkRef ({} : Cache.VerifyCounts)
        let rstats2 ← IO.mkRef ({} : Cache.RegionCounts)
        let (s2, hits2) ← Cache.elaborateCached none [ro] src init 0
          (region := some { rig, stats := some rstats2 }) (verify := .off) (rig := rig)
          (stats := some stats2)
        checkEq expected (s2.messages.toList.map (·.render src))
        check (hits2 > 0) "off did not read the text entries"
        checkEq 0 (← stats2.get).regions
        checkEq 0 (← rstats2.get).hits
        checkEq before (← snapshot ro)
        -- (the CLI default: refused, with the opt-in named, and the layer unchanged)
        let wiz ← invWiz
        let run (args : Array String) := IO.Process.output { cmd := wiz, args, cwd := some dir }
        let coldCli ← run #["check", "main.wiz", "-I", dir.toString, "--cache", ro.toString,
                             "--region-cache"]
        checkEq 0 coldCli.exitCode
        checkEq "main.wiz:2:1: info: 2\n" coldCli.stdout
        let beforeCli ← snapshot ro
        let base : Array String := #["check", "main.wiz", "-I", dir.toString, "--no-cache",
                                     "--region-cache"]
        let refused ← run (base ++ #["--cache-ro", ro.toString, "--region-stats",
                                     "--cache-verify-stats"])
        checkEq 0 refused.exitCode
        checkEq coldCli.stdout refused.stdout
        check ((refused.stderr.splitOn "refusing an unauthenticated layer").length > 1)
          s!"the read-only layer was not refused: {refused.stderr}"
        check ((refused.stderr.splitOn "--cache-ro-unsigned").length > 1)
          s!"no opt-in named: {refused.stderr}"
        checkEq (some 0) (invStat refused.stderr "region cache: " "modules from a region")
        checkEq beforeCli (← snapshot ro)
        let served ← run (base ++ #["--cache-ro", ro.toString, "--cache-ro-unsigned",
                                    "--region-stats", "--cache-verify-stats"])
        checkEq 0 served.exitCode
        checkEq coldCli.stdout served.stdout
        let some sHits := invStat served.stderr "region cache: " "modules from a region"
          | throw (IO.userError s!"no region stats line: {served.stderr}")
        check (sHits > 0) s!"no region was served by the opt-in: {served.stderr}"
        let some sMan := invStat served.stderr "cache verify: " "manifests"
          | throw (IO.userError s!"no verify stats line: {served.stderr}")
        check (sMan > 0) s!"no manifest was loaded by the opt-in: {served.stderr}"
        checkEq beforeCli (← snapshot ro) },
    /- I2/I3/I10 — digest checks are at the file boundary. -/
    { name := "a tampered manifest or region is a miss (the text path answers)", run := fun _ => do
        let dir ← mkTree [("M.wiz", "import Prelude\ndef x : Nat := 1 + 1\n")]
        let ms ← Module.loadAll ["lib", dir]
        let cache ← IO.FS.createTempDir
        let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, loader := loaderOf ms }
        let rig := RigTag.tag (R := ZeroOneMany)
        let stats ← IO.mkRef ({} : Cache.RegionCounts)
        let opts : Cache.RegionOptions := { rig, stats := some stats }
        let src := "import M\n#eval x\n"
        let cold ← invCold cache src init rig opts
        let good := cold.messages.toList.map (·.render src)
        check (!cold.messages.any (·.severity == .error)) s!"cold: {good}"
        let binary ← Cache.binaryId (some cache)
        let k := invModuleKey ms "M"
        let f := cache / Cache.regionFileName binary k
        check (← Cache.regionFileChecksum f).isSome "a fresh region has no checksum"
        -- (a same-size bit flip: the sidecar is checked before the image is mapped)
        let _ ← flipByte f
        let m0 ← stats.get
        let s1 ← invCold cache src init rig opts
        checkEq good (s1.messages.toList.map (·.render src))
        check ((← stats.get).misses > m0.misses) "a flipped region byte was not a miss"
        -- (the repair must converge: one more run serves the region again)
        let r1 ← stats.get
        let s1b ← invCold cache src init rig opts
        checkEq good (s1b.messages.toList.map (·.render src))
        check ((← stats.get).hits > r1.hits)
          "the repaired region was not served on the next run (§6.5)"
        -- (the sidecar is not the manifest: recompute it after a flip, and the SHA-256
        -- in the module manifest must still reject the bytes. A fresh cache keeps this
        -- independent of the first tamper's dropped region.)
        let cache2 ← IO.FS.createTempDir
        let stats2 ← IO.mkRef ({} : Cache.RegionCounts)
        let opts2 : Cache.RegionOptions := { rig, stats := some stats2 }
        let cold2 ← invCold cache2 src init rig opts2
        check (!cold2.messages.any (·.severity == .error)) s!"cold2: {cold2.messages.toList.map (·.text)}"
        let binary2 ← Cache.binaryId (some cache2)
        let f2 := cache2 / Cache.regionFileName binary2 k
        check (← Cache.regionFileChecksum f2).isSome "the second fixture region has no checksum"
        let _ ← flipByte f2
        let sum ← Cache.checksumFile f2
        IO.FS.writeBinFile (Cache.regionSumFile f2) (Cache.u64Bytes sum)
        check (← Cache.regionFileChecksum f2).isSome "the forged sidecar does not match"
        let m1 ← stats2.get
        let s2 ← invCold cache2 src init rig opts2
        checkEq good (s2.messages.toList.map (·.render src))
        check ((← stats2.get).misses > m1.misses)
          "a region with a recomputed sidecar but a stale manifest digest was served"
        let r2 ← stats2.get
        let s2b ← invCold cache2 src init rig opts2
        checkEq good (s2b.messages.toList.map (·.render src))
        check ((← stats2.get).hits > r2.hits)
          "the repaired region was not served on the next run (§6.5)"
        -- (a tampered manifest root: its keys are poisoned, the text path answers)
        let some mf ← manifestFor cache2 "M"
          | throw (IO.userError "no manifest for M")
        invTamperRoot mf
        let h0 ← stats2.get
        let s3 ← invCold cache2 src init rig opts2
        checkEq good (s3.messages.toList.map (·.render src))
        check ((← stats2.get).misses > h0.misses) "a tampered manifest was trusted"
        let some man := Cache.parseManifest (← IO.FS.readFile mf)
          | throw (IO.userError "the manifest was not rewritten")
        check (man.valid { fast := man.key, strong := man.keySha,
                           toolchain := man.toolchainTag, target := man.targetTag }
          man.binary "" "") "the rewritten manifest is not valid"
        let r3 ← stats2.get
        let s3b ← invCold cache2 src init rig opts2
        checkEq good (s3b.messages.toList.map (·.render src))
        check ((← stats2.get).hits > r3.hits)
          "the manifest repair did not converge to a region hit" },
    /- I10 — the determinism question behind §6.5 (K1). -/
    { name := "a module region's bytes are deterministic (two writes, one SHA-256)", run := fun _ => do
        let dir ← mkTree [("M.wiz", "import Prelude\ndef x : Nat := 1 + 1\n")]
        let ms ← Module.loadAll ["lib", dir]
        let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, loader := loaderOf ms }
        let rig := RigTag.tag (R := ZeroOneMany)
        let c1 ← IO.FS.createTempDir
        let _ ← invCold c1 "import M\n" init rig
        let binary ← Cache.binaryId (some c1)
        let k := invModuleKey ms "M"
        let some a ← Cache.readModuleRegion (R := ZeroOneMany) c1 binary rig k
          | throw (IO.userError "M has no region")
        let c2 ← IO.FS.createTempDir
        let some e1 ← Cache.writeModuleRegion (R := ZeroOneMany) c2 binary rig k "M"
          a.effects a.keys a.complete a.rerun
          | throw (IO.userError "write 1 failed")
        let some e2 ← Cache.writeModuleRegion (R := ZeroOneMany) c2 binary rig k "M"
          a.effects a.keys a.complete a.rerun
          | throw (IO.userError "write 2 failed")
        checkEq e1.sha256 e2.sha256 },
    /- I6/I9 — pruning is write-cache-only. -/
    { name := "prune never rewrites or prunes a read-only layer (command and pre-run)", run := fun _ => do
        let wiz ← invWiz
        let run (args : Array String) := IO.Process.output { cmd := wiz, args }
        let write ← IO.FS.createTempDir
        let ro ← IO.FS.createTempDir
        let old (dir : System.FilePath) (name : String) : IO System.FilePath := do
          let f := dir / name
          IO.FS.writeFile f "x"
          touchAgo f "40 days ago"
          pure f
        let oldEntry ← old write "old.wizc"
        let oldRegion ← old write "old.wizr"
        let oldSum ← old write "old.wizs"
        let keep ← old write "notes.txt"
        let roEntry ← old ro "ro.wizc"
        let roRegion ← old ro "ro.wizr"
        let roSum ← old ro "ro.wizs"
        let before ← snapshot ro
        let o ← run #["cache", "prune", "--cache", write.toString, "--cache-ro", ro.toString,
                       "--days", "7"]
        checkEq 0 o.exitCode
        check ((o.stdout.splitOn "cache prune: removed 3 files").length > 1) s!"stdout: {o.stdout}"
        check ((o.stderr.splitOn "never pruned").length > 1) s!"stderr: {o.stderr}"
        check (!(← oldEntry.pathExists) && !(← oldRegion.pathExists) &&
          !(← oldSum.pathExists)) "an old keyed file survived"
        check ((← keep.pathExists)) "a non-keyed file was pruned"
        check (← roEntry.pathExists) "a read-only .wizc was pruned"
        check (← roRegion.pathExists) "a read-only .wizr was pruned"
        check (← roSum.pathExists) "a read-only .wizs was pruned"
        checkEq before (← snapshot ro)
        -- (no write cache: the command refuses and touches nothing)
        let o2 ← run #["cache", "prune", "--no-cache", "--cache-ro", ro.toString, "--days", "7"]
        checkEq 1 o2.exitCode
        check ((o2.stdout.splitOn "no write cache").length > 1 ||
          (o2.stderr.splitOn "no write cache").length > 1) s!"stdout: {o2.stdout}{o2.stderr}"
        checkEq before (← snapshot ro)
        -- (`--cache-prune DAYS` runs before the elaboration, on the write cache only)
        let dir ← mkTree [("M.wiz", "import Prelude\ndef x : Nat := 2\n"),
                          ("main.wiz", "import M\n#eval x\n")]
        let w2 ← IO.FS.createTempDir
        let ro2 ← IO.FS.createTempDir
        let cold ← IO.Process.output {
          cmd := wiz, cwd := some dir,
          args := #["check", "main.wiz", "-I", dir.toString, "--cache", ro2.toString,
                    "--region-cache"] }
        checkEq 0 cold.exitCode
        checkEq "main.wiz:2:1: info: 2\n" cold.stdout
        let old2 ← old w2 "stale.wizc"
        for f in ← invEveryFile ro2 do
          let name := f.fileName.getD ""
          if [".wizc", ".wizm", ".wizr", ".wizs"].any (fun e => name.endsWith e) then
            touchAgo f "40 days ago"
        let before2 ← snapshot ro2
        let o3 ← IO.Process.output {
          cmd := wiz, cwd := some dir,
          args := #["check", "main.wiz", "-I", dir.toString, "--cache", w2.toString,
                    "--cache-ro", ro2.toString, "--cache-ro-unsigned", "--region-cache",
                    "--cache-prune", "7"] }
        checkEq 0 o3.exitCode
        checkEq cold.stdout o3.stdout
        check ((o3.stderr.splitOn "cache prune: removed").length > 1) s!"stderr: {o3.stderr}"
        check ((o3.stderr.splitOn "removed 0 files").length == 1) s!"nothing was pruned: {o3.stderr}"
        check (!(← old2.pathExists)) "the stale write entry survived --cache-prune"
        checkEq before2 (← snapshot ro2) },
    /- I7 — off is the old unverified text store: no manifests, no regions. -/
    { name := "--cache-verify off reads and writes no regions (and writes no manifests)", run := fun _ => do
        let dir ← mkTree [("M.wiz", "import Prelude\ndef x : Nat := 1 + 1\n"),
                          ("main.wiz", "import M\n#eval x\n")]
        let ms ← Module.loadAll ["lib", dir]
        let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, loader := loaderOf ms }
        let rig := RigTag.tag (R := ZeroOneMany)
        let opts : Cache.RegionOptions := { rig }
        let src := "import M\n#eval x\n"
        let offCache ← IO.FS.createTempDir
        let off ← invCold offCache src init rig opts .off
        let expected := off.messages.toList.map (·.render src)
        check (!off.messages.any (·.severity == .error)) s!"off: {expected}"
        let offRegions := (← regionFiles offCache).size
        let offManifests := (← manifestFiles offCache).size
        check (offRegions == 0) s!"off wrote {offRegions} regions"
        check (offManifests == 0) s!"off wrote {offManifests} manifests"
        check (!(← (offCache / "manifest.sexpr").pathExists)) "off wrote a generation index"
        let offSums := ((← invEveryFile offCache).filter
          (fun f => (f.fileName.getD "").endsWith ".wizs")).size
        check (offSums == 0) s!"off wrote {offSums} sidecars"
        check (((← invEveryFile offCache).filter
          (fun f => (f.fileName.getD "").endsWith ".wizc")).size > 0)
          "off wrote no text entries at all"
        -- (a valid region in another cache is not served by an off store)
        let cache ← IO.FS.createTempDir
        let cold ← invCold cache src init rig opts
        check (!cold.messages.any (·.severity == .error)) s!"cold: {cold.messages.toList.map (·.text)}"
        let binary ← Cache.binaryId (some cache)
        let k := invModuleKey ms "M"
        check (← Cache.readModuleRegion (R := ZeroOneMany) cache binary rig k).isSome
          "the region fixture is not readable"
        let storeOff ← Cache.Store.layeredRegion (R := ZeroOneMany) (some cache) [] binary opts
          .off rig
        check (← storeOff.getRegion k).isNone "an off store served a valid region"
        -- (the CLI: the same answer, no regions written, no region hits)
        let wiz ← invWiz
        let cliCache ← IO.FS.createTempDir
        let base : Array String := #["check", "main.wiz", "-I", dir.toString, "--cache",
                                     cliCache.toString, "--region-cache", "--region-stats",
                                     "--cache-verify", "off"]
        let o1 ← IO.Process.output { cmd := wiz, args := base, cwd := some dir }
        check (o1.exitCode == 0) s!"off cli exit {o1.exitCode}: {o1.stdout}{o1.stderr}"
        checkEq "main.wiz:2:1: info: 2\n" o1.stdout
        check ((o1.stderr.splitOn "0 modules from a region").length > 1) s!"stderr: {o1.stderr}"
        let cliRegions := (← regionFiles cliCache).size
        let cliManifests := (← manifestFiles cliCache).size
        check (cliRegions == 0) s!"off (cli) wrote {cliRegions} regions"
        check (cliManifests == 0) s!"off (cli) wrote {cliManifests} manifests"
        check (!(← (cliCache / "manifest.sexpr").pathExists)) "off wrote a generation index"
        let o2 ← IO.Process.output { cmd := wiz, args := base, cwd := some dir }
        check (o2.exitCode == 0) s!"off cli (warm) exit {o2.exitCode}: {o2.stdout}{o2.stderr}"
        checkEq o1.stdout o2.stdout
        let cliRegions2 := (← regionFiles cliCache).size
        check (cliRegions2 == 0) s!"off (cli, warm) wrote {cliRegions2} regions" },
    /- I8 — the generation index only expires a layer; it is not a lookup table. -/
    { name := "an expired generation index misses the whole layer; the index cannot substitute for a manifest", run := fun _ => do
        let dir ← mkTree [("M.wiz", "import Prelude\ndef x : Nat := 1 + 1\n")]
        let ms ← Module.loadAll ["lib", dir]
        let cache ← IO.FS.createTempDir
        let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, loader := loaderOf ms }
        let rig := RigTag.tag (R := ZeroOneMany)
        let stats ← IO.mkRef ({} : Cache.RegionCounts)
        let opts : Cache.RegionOptions := { rig, stats := some stats }
        let src := "import M\n#eval x\n"
        let cold ← invCold cache src init rig opts
        let good := cold.messages.toList.map (·.render src)
        check (!cold.messages.any (·.severity == .error)) s!"cold: {good}"
        -- (a past `valid-until`: every manifest in the layer is a miss, text and region)
        let _ ← Cache.sealLayer cache true 1
        let h0 ← stats.get
        let s1 ← invCold cache src init rig opts
        checkEq good (s1.messages.toList.map (·.render src))
        check ((← stats.get).misses > h0.misses) "an expired generation did not miss the layer"
        checkEq h0.hits (← stats.get).hits
        -- (without an index there is no expiry: the manifests are usable again)
        let gen := cache / "manifest.sexpr"
        check (← gen.pathExists) "no generation index was written"
        IO.FS.removeFile gen
        let h1 ← stats.get
        let s2 ← invCold cache src init rig opts
        checkEq good (s2.messages.toList.map (·.render src))
        check ((← stats.get).hits > h1.hits) "removing the index did not restore the layer"
        -- (the index never supplies a manifest: list M, delete its manifest, still a miss)
        let some mf ← manifestFor cache "M"
          | throw (IO.userError "no manifest for M")
        IO.FS.removeFile mf
        let k := invModuleKey ms "M"
        let fake : Cache.Generation :=
          { generation := 1, prev := "", validUntil := 0,
            modules := #[(k.fast, k.strong, "M", "not-there.wizmf",
              String.ofList (List.replicate 64 'd'))] }
        let fake := { fake with root := fake.rootOf }
        IO.FS.writeFile gen (fake.toSx.render ++ "\n")
        -- (the index is not consulted for a lookup: M has no manifest, so its region
        -- is not served even though the index names it)
        let binary ← Cache.binaryId (some cache)
        let store ← Cache.Store.layeredRegion (R := ZeroOneMany) (some cache) [] binary opts
          .warn rig
        check (← store.getRegion k).isNone
          "a record in the generation index served a region without a manifest"
        let h2 ← stats.get
        let s3 ← invCold cache src init rig opts
        checkEq good (s3.messages.toList.map (·.render src))
        check ((← stats.get).misses > h2.misses)
          "the generation index hid the missing manifest" },
    /- I4 — a manifest is authoritative only inside its layer. -/
    { name := "a manifest cannot name a file outside its layer (path escape is invalid)", run := fun _ => do
        let cache ← IO.FS.createTempDir
        let binary : UInt64 := 4242
        let key : Cache.Key := { fast := 9, strong := String.ofList (List.replicate 64 'a') }
        let sha := String.ofList (List.replicate 64 'c')
        let expectedFile := s!"{mixHash binary key.fast}.wizc"
        let tag := cache.fileName.getD "cache"
        let outside := cache.parent.getD cache / s!"{tag}-escape.wizc"
        let outName := outside.fileName.getD "escape.wizc"
        let escapeFile := s!"../{outName}"
        let entry (file : String) (kind : String) : Cache.ManifestEntry :=
          { kind, key := key.fast, keySha := key.strong, file, size := 1, sha256 := sha,
            format := if kind == "wizr" then Cache.regionFormat else Cache.salt.toNat }
        -- (each is self-consistent except for the containment fields)
        let bad : List (String × Cache.ManifestEntry) :=
          [("a path escape", entry escapeFile "wizc"),
           ("an absolute path", entry "/tmp/escape.wizc" "wizc"),
           ("a non-expected name", entry "other.wizc" "wizc"),
           ("a region in the entry list", entry expectedFile "wizr"),
           ("a short digest", { (entry expectedFile "wizc") with sha256 := "abc" }),
           ("a short key-sha", { (entry expectedFile "wizc") with keySha := "abc" })]
        for (what, e) in bad do
          check (!e.valid binary) s!"{what}: the entry passed ManifestEntry.valid"
          let m := invManifest binary key #[e]
          check (!m.valid key binary "" "") s!"{what}: the manifest passed ModuleManifest.valid"
        -- (a loaded bad manifest poisons its key; nothing outside the layer is read)
        let m := invManifest binary key #[entry escapeFile "wizc"]
        IO.FS.createDirAll (cache / "manifest.d")
        IO.FS.writeFile (Cache.manifestFile cache binary key) (m.toSx.render ++ "\n")
        let ms ← Cache.ManifestStore.create (some cache) [] binary "" "" .warn
        ms.load key
        check (← ms.poisonedFor key) "a manifest naming a path escape did not poison its key"
        check (← ms.entryFor key).isNone "a manifest naming a path escape was indexed"
        check (!(← outside.pathExists)) "a path-escape file was created or read" },
    /- I6 — every read-only command is a scan, never a repair. -/
    { name := "cache verify/manifest and a warm run leave a read-only layer byte-identical", run := fun _ => do
        let dir ← mkTree [("M.wiz", "import Prelude\ndef x : Nat := 1 + 1\n"),
                          ("main.wiz", "import M\n#eval x\n")]
        let ms ← Module.loadAll ["lib", dir]
        let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, loader := loaderOf ms }
        let rig := RigTag.tag (R := ZeroOneMany)
        let ro ← IO.FS.createTempDir
        let cold ← invCold ro "import M\n#eval x\n" init rig
        let expected := cold.messages.toList.map (·.render "import M\n#eval x\n")
        check (!cold.messages.any (·.severity == .error)) s!"cold: {expected}"
        let wiz ← invWiz
        let before ← snapshot ro
        -- (verify: a full scan; read-only layers are reported as integrity, not authenticity)
        let v ← IO.Process.output { cmd := wiz, args := #["cache", "verify", "--no-cache",
          "--cache-ro", ro.toString, "--cache-verify", "strict"] }
        checkEq 0 v.exitCode
        check ((v.stdout.splitOn "read-only: a manifest is integrity, not authenticity").length > 1)
          s!"no integrity note: {v.stdout}"
        checkEq before (← snapshot ro)
        -- (manifest: report only, never writes the generation index)
        let gen := ro / "manifest.sexpr"
        check (!(← gen.pathExists)) "the cold run wrote a generation index"
        let m ← IO.Process.output { cmd := wiz, args := #["cache", "manifest", "--no-cache",
          "--cache-ro", ro.toString] }
        checkEq 0 m.exitCode
        check ((m.stdout.splitOn "(read-only)").length > 1) s!"not report-only: {m.stdout}"
        check (!(← gen.pathExists)) "cache manifest wrote a read-only layer"
        checkEq before (← snapshot ro)
        -- (a corrupt read-only region: verify fails, a warm run misses, neither repairs.
        -- Use a layer written by `wiz` itself, so its keys are the run's binary id.)
        let roCli ← IO.FS.createTempDir
        let coldCli ← IO.Process.output {
          cmd := wiz, cwd := some dir,
          args := #["check", "main.wiz", "-I", dir.toString, "--cache", roCli.toString,
                    "--region-cache"] }
        checkEq 0 coldCli.exitCode
        checkEq "main.wiz:2:1: info: 2\n" coldCli.stdout
        let regs ← regionFiles roCli
        check (regs.size > 0) "the CLI cold run wrote no region"
        for r in regs do
          let _ ← flipByte r
        let bad ← snapshot roCli
        let v2 ← IO.Process.output { cmd := wiz, args := #["cache", "verify", "--no-cache",
          "--cache-ro", roCli.toString] }
        checkEq 1 v2.exitCode
        checkEq bad (← snapshot roCli)
        let w ← IO.Process.output {
          cmd := wiz, cwd := some dir,
          args := #["check", "main.wiz", "-I", dir.toString, "--no-cache",
                    "--cache-ro", roCli.toString, "--cache-ro-unsigned", "--region-cache",
                    "--region-stats"] }
        checkEq 0 w.exitCode
        checkEq "main.wiz:2:1: info: 2\n" w.stdout
        let some without := invStat w.stderr "region cache: " "without"
          | throw (IO.userError s!"no region stats line: {w.stderr}")
        check (without > 0) s!"the corrupt read-only region was not a miss: {w.stderr}"
        checkEq (some 0) (invStat w.stderr "region cache: " "modules from a region")
        checkEq bad (← snapshot roCli) },
    /- I11 — the documented limit: a self-consistent rewrite in the write cache is served. -/
    { name := "a self-consistent rewrite is served: integrity is not authenticity (write cache)", run := fun _ => do
        let dir ← mkTree [("M.wiz", "import Prelude\ndef x : Nat := 2\n")]
        let ms ← Module.loadAll ["lib", dir]
        let cache ← IO.FS.createTempDir
        let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, loader := loaderOf ms }
        let rig := RigTag.tag (R := ZeroOneMany)
        let opts : Cache.RegionOptions := { rig }
        let src := "import M\n"
        let cold ← invCold cache src init rig opts
        checkEq (some 2) (invNatValue? cold "x")
        let binary ← Cache.binaryId (some cache)
        let k := invModuleKey ms "M"
        let some a ← Cache.readModuleRegion (R := ZeroOneMany) cache binary rig k
          | throw (IO.userError "M has no region")
        check (a.effects.size > 0) "M's region has no effects"
        checkEq k.fast a.key
        checkEq k.strong a.keySha
        -- (replace the module's effect with a different declaration, and make the
        -- manifest describe exactly the new bytes: the per-user write cache is trusted)
        let forged := invEffect "x" (some 3)
        let forgedArt : Cache.ModuleArtifact ZeroOneMany :=
          { a with effects := a.effects.set! 0 forged }
        let some ent ← Cache.writeModuleRegion (R := ZeroOneMany) cache binary rig k "M"
          forgedArt.effects forgedArt.keys forgedArt.complete forgedArt.rerun
          | throw (IO.userError "the forged region was not written")
        let some mf ← manifestFor cache "M"
          | throw (IO.userError "no manifest for M")
        let some man := Cache.parseManifest (← IO.FS.readFile mf)
          | throw (IO.userError "M's manifest does not parse")
        let man1 := { man with region := some ent }
        let man2 := { man1 with root := man1.rootOf }
        check (man2.valid k binary "" rig) "the forged manifest is not self-consistent"
        IO.FS.writeFile mf (man2.toSx.render ++ "\n")
        -- (a fresh store serves it: this is what a signature/key pin would have to stop)
        let warm ← invCold cache src init rig opts
        checkEq (some 3) (invNatValue? warm "x")
        let c ← Cache.verifyLayer cache
        checkEq 0 c.mismatches
        check (c.regions > 0) "the forged region was not scanned" },
    /- I12 (§1.4 option a) — poison is global per key. -/
    { name := "a poisoned read layer hides a valid write-cache region (global poison)", run := fun _ => do
        let dir ← mkTree [("M.wiz", "import Prelude\ndef x : Nat := 1 + 1\n"),
                          ("main.wiz", "import M\n#eval x\n")]
        let ms ← Module.loadAll ["lib", dir]
        let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, loader := loaderOf ms }
        let rig := RigTag.tag (R := ZeroOneMany)
        let opts : Cache.RegionOptions := { rig }
        let w ← IO.FS.createTempDir
        let ro ← IO.FS.createTempDir
        let src := "import M\n#eval x\n"
        let coldW ← invCold w src init rig opts
        let coldRo ← invCold ro src init rig opts
        check (!coldW.messages.any (·.severity == .error)) s!"write cold: {coldW.messages.toList.map (·.text)}"
        check (!coldRo.messages.any (·.severity == .error)) s!"read cold: {coldRo.messages.toList.map (·.text)}"
        let expected := coldW.messages.toList.map (·.render src)
        let some mf ← manifestFor ro "M"
          | throw (IO.userError "no manifest for M in the read layer")
        invTamperRoot mf
        let before ← snapshot ro
        let binary ← Cache.binaryId (some w)
        let k := invModuleKey ms "M"
        check (← Cache.readModuleRegion (R := ZeroOneMany) w binary rig k).isSome
          "the write layer's own region is not valid"
        let store ← Cache.Store.layeredRegion (R := ZeroOneMany) (some w) [ro] binary opts
          .warn rig (roUnsigned := true)
        check (← store.getRegion k).isNone
          "a poisoned read layer did not hide the write cache's valid region"
        let (s, _) ← Cache.elaborateCached (some w) [ro] src init 0 (region := some opts)
          (verify := .warn) (rig := rig) (roUnsigned := true)
        checkEq expected (s.messages.toList.map (·.render src))
        checkEq before (← snapshot ro) },
    /- K3 pending (task 11): the opt-in must cover only the layer before it. -/
    { name := "per-layer --cache-ro-unsigned: a later layer is still refused (pending task 11)", run := fun _ => do
        let dir ← mkTree [("A.wiz", "import Prelude\ndef a : Nat := 1\n"),
                          ("B.wiz", "import Prelude\ndef b : Nat := 2\n"),
                          ("mainA.wiz", "import A\n#eval a\n"),
                          ("mainB.wiz", "import B\n#eval b\n"),
                          ("main.wiz", "import A\nimport B\n#eval a + b\n")]
        let wiz ← invWiz
        let roA ← IO.FS.createTempDir
        let roB ← IO.FS.createTempDir
        let coldA ← IO.Process.output {
          cmd := wiz, cwd := some dir,
          args := #["check", "mainA.wiz", "-I", dir.toString, "--cache", roA.toString,
                    "--region-cache"] }
        checkEq 0 coldA.exitCode
        let coldB ← IO.Process.output {
          cmd := wiz, cwd := some dir,
          args := #["check", "mainB.wiz", "-I", dir.toString, "--cache", roB.toString,
                    "--region-cache"] }
        checkEq 0 coldB.exitCode
        let beforeA ← snapshot roA
        let beforeB ← snapshot roB
        let out ← IO.Process.output {
          cmd := wiz, cwd := some dir,
          args := #["check", "main.wiz", "-I", dir.toString, "--no-cache",
                    "--cache-ro", roA.toString, "--cache-ro-unsigned",
                    "--cache-ro", roB.toString, "--region-cache", "--region-stats"] }
        checkEq 0 out.exitCode
        checkEq "main.wiz:3:1: info: 3\n" out.stdout
        let warnedB := (out.stderr.splitOn "refusing an unauthenticated layer").length > 1 &&
                       (out.stderr.splitOn roB.toString).length > 1
        if warnedB then
          let some hits := invStat out.stderr "region cache: " "modules from a region"
            | throw (IO.userError s!"no region stats line: {out.stderr}")
          check (hits == 2) s!"expected roA's A+Prelude only, got {hits}: {out.stderr}"
          let some without := invStat out.stderr "region cache: " "without"
            | throw (IO.userError s!"no region stats line: {out.stderr}")
          check (without > 0) s!"roB's module was served: {out.stderr}"
        else
          skip "pending task 11: --cache-ro-unsigned is global; roB was served unsigned"
        checkEq beforeA (← snapshot roA)
        checkEq beforeB (← snapshot roB) }
  ]

builtin_initialize registerGroup cacheInvariantsGroup

end Tests.Grail
