import Tests.Elab
import Wiz.Ext.Resolve

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- A refusal with this stable code, or a failure: a success is not allowed to pass a
negative test. -/
def expectRefusal {α : Type} (code : String) (r : Except Wiz.Ext.Diagnostic α) : IO Unit :=
  match r with
  | .error d => checkEq code d.code
  | .ok _ => throw (IO.userError s!"expected the refusal '{code}', but the call succeeded")

/-- The `wiz` binary beside the test driver (or Lake's), for the three CLI refusals. -/
def extWizExe : IO System.FilePath := do
  let app ← IO.appPath
  for c in [(app.parent.getD ".") / "wiz", System.FilePath.mk ".lake/build/bin/wiz"] do
    if ← c.pathExists then return c
  throw (IO.userError "=ext: no wiz binary (build the suite with `lake build wiz tests`)")

/-- Run `wiz ARGS` in a fresh directory with `probe.wiz`, and return the exit code and
stderr. The file is never read by a refusal that happens before dispatch. -/
def extRunWiz (args : List String) : IO (UInt32 × String) := do
  let exe ← extWizExe
  let lib ← IO.FS.realPath "lib"
  let dir ← IO.FS.createTempDir
  IO.FS.writeFile (dir / "probe.wiz") "import Prelude\ndef main : Nat := 1\n"
  let out ← IO.Process.output
    { cmd := exe.toString, args := (["--no-cache", "-I", lib.toString] ++ args).toArray, cwd := dir }
  let wrote := (← (dir / "out").pathExists) || (← (dir / "out.c").pathExists) ||
    (← (dir / "out.mjs").pathExists) || (← (dir / "out.wasm").pathExists)
  IO.FS.removeDirAll dir
  if wrote then throw (IO.userError s!"wiz {args} wrote an artifact before refusing:\n{out.stderr}")
  pure (out.exitCode, out.stderr)

/-- One entry model, one resolver (`Wiz/Ext/{Basic,Resolve}.lean`), and `--target` as its
first user. The refusal cases are data: a stable code, before anything runs. -/
def extGroup : Group where
  name := "ext"
  exercise := "Wiz/Ext (the entry registry; --target is its first user)"
  parallel := true
  cases := [
    { name := "six target spellings resolve to five core entries; the key, ABI and capabilities are data", run := fun _ => do
        checkEq 6 Wiz.Ext.backendSpellings.length
        checkEq 5 Wiz.Ext.backendEntries.length
        checkEq "c, llvm, wasm, bpf, js or ebpf" Wiz.Ext.backendChoices
        for n in ["c", "llvm", "wasm", "bpf", "js", "ebpf"] do
          match Wiz.Ext.resolveBackend n with
          | .error d => throw (IO.userError s!"{n}: {d.code}: {d.message}")
          | .ok e => do
            check (e.kind == .backend) s!"{n} has kind {reprStr e.kind}"
            checkEq "wiz-backend/1" e.abi
            checkEq s!"target/{e.name}" (Wiz.Ext.Entry.key e)
            let arts := Wiz.Ext.artifactsOf e.name
            check (arts.any (fun (_, k) => k == .executable) ||
              arts.any (fun (_, k) => k == .module) ||
              arts.any (fun (_, k) => k == .src)) s!"{n} declares no artifact kind"
        let c ← match Wiz.Ext.resolveBackend "c" with
          | .ok e => pure e
          | .error d => throw (IO.userError d.message)
        for cap in [Wiz.Ext.Capability.emit, .link, .run, .attest, .library, .split, .repl] do
          check (c.caps.contains cap) s!"c lacks {cap.key}"
        let bpf ← match Wiz.Ext.resolveBackend "ebpf" with
          | .ok e => pure e
          | .error d => throw (IO.userError d.message)
        checkEq "bpf" bpf.name
        checkEq "bpf-core/1" bpf.schema
        check (bpf.caps.contains .check) "bpf must declare check"
        for cap in [Wiz.Ext.Capability.run, .attest, .library, .split, .repl] do
          check (!bpf.caps.contains cap) s!"bpf must not claim {cap.key}"
        check ((Wiz.Ext.artifactsOf "bpf").any (fun (_, k) => k == .descriptor)) "bpf has no descriptor artifact"
        let js ← match Wiz.Ext.resolveBackend "js" with
          | .ok e => pure e
          | .error d => throw (IO.userError d.message)
        check (js.caps.contains .run) "js runs a module"
        for cap in [Wiz.Ext.Capability.attest, .library, .split, .repl] do
          check (!js.caps.contains cap) s!"js must not claim {cap.key}" },
    { name := "an unknown target is refused with choices, never defaulted to c", run := fun _ => do
        expectRefusal "unknown-target" (Wiz.Ext.resolveBackend "bpf2")
        match Wiz.Ext.resolveBackend "bpf2" with
        | .error d =>
          check ((d.message.splitOn "choose c, llvm, wasm, bpf, js or ebpf").length > 1) d.message
        | .ok _ => throw (IO.userError "bpf2 resolved") },
    { name := "a duplicate (kind, name) is refused naming both providers; an alias occupies the same namespace", run := fun _ => do
        let a : Wiz.Ext.Entry :=
          { kind := .backend, name := "demo", provider := "wiz-a", abi := "wiz-backend/1",
            payload := .process "demo-backend" }
        let b : Wiz.Ext.Entry := { a with provider := "wiz-b" }
        match Wiz.Ext.Table.ofEntries [a, b] with
        | .error d => do
          checkEq "duplicate-target" d.code
          check (d.message.contains "wiz-a" && d.message.contains "wiz-b") s!"providers missing: {d.message}"
        | .ok _ => throw (IO.userError "a duplicate target was registered")
        let aliased : Wiz.Ext.Entry :=
          { kind := .backend, name := "demo", aliases := ["old-demo"], abi := "wiz-backend/1",
            payload := .process "demo-backend" }
        let t ← match Wiz.Ext.Table.ofEntries [aliased] with
          | .ok t => pure t
          | .error d => throw (IO.userError d.message)
        match Wiz.Ext.resolveBackendIn t "old-demo" with
        | .ok e => checkEq "demo" e.name
        | .error d => throw (IO.userError s!"the alias did not resolve: {d.code}: {d.message}")
        let clash : Wiz.Ext.Entry :=
          { kind := .backend, name := "old-demo", abi := "wiz-backend/1", payload := .process "demo-backend" }
        expectRefusal "duplicate-target" (Wiz.Ext.Table.ofEntries [aliased, clash]) },
    { name := "a package entry present but not enabled refuses target-not-enabled; the core rows are always enabled", run := fun _ => do
        let pkg : Wiz.Ext.Entry :=
          { kind := .backend, name := "demo", provider := "demo-pkg", set := "demo-set",
            abi := "wiz-backend/1", caps := [.emit], payload := .process "demo-backend" }
        let t ← match Wiz.Ext.Table.ofEntries (Wiz.Ext.backendEntries ++ [pkg]) with
          | .ok t => pure t
          | .error d => throw (IO.userError d.message)
        expectRefusal "target-not-enabled" (Wiz.Ext.resolveBackendIn t "demo")
        match Wiz.Ext.resolveBackendIn t "demo" (enabledSets := ["demo-set"]) with
        | .ok e => do
          checkEq "demo" e.name
          -- a package `.process` row resolves, but the core driver cannot run it: this
          -- is the manifest gap (a `.process`/`.data` driver is not wired)
          match e.coreDriver? with
          | .error d => checkEq "unsupported-target" d.code
          | .ok _ => throw (IO.userError "the core driver accepted a package process payload")
        | .error d => throw (IO.userError s!"the enabled entry did not resolve: {d.code}: {d.message}")
        -- core entries need no set, even when the package is present
        match Wiz.Ext.resolveBackendIn t "c" with
        | .ok e => checkEq "c" e.name
        | .error d => throw (IO.userError d.message) },
    { name := "a capability the entry does not declare is refused before dispatch", run := fun _ => do
        expectRefusal "target-capability" (Wiz.Ext.resolveBackendFor "js" [.link])
        expectRefusal "target-capability" (Wiz.Ext.resolveBackendFor "bpf" [.run])
        expectRefusal "target-capability" (Wiz.Ext.resolveBackendFor "wasm" [.library])
        match Wiz.Ext.resolveBackendFor "c" [.link, .attest] with
        | .ok e => checkEq "c" e.name
        | .error d => throw (IO.userError s!"c refused link+attest: {d.code}: {d.message}") },
    { name := "an unreadable ABI and an entry this toolchain cannot serve refuse with their own codes", run := fun _ => do
        let future : Wiz.Ext.Entry :=
          { kind := .backend, name := "future", abi := "wiz-backend/2", payload := .core .c }
        let tf ← match Wiz.Ext.Table.ofEntries [future] with
          | .ok t => pure t
          | .error d => throw (IO.userError d.message)
        expectRefusal "unsupported-target" (Wiz.Ext.resolveBackendIn tf "future")
        let u : Wiz.Ext.Entry :=
          { kind := .backend, name := "demo", abi := "wiz-backend/1",
            payload := .unsupported "the adapter is not installed (grail add demo)" }
        let tu ← match Wiz.Ext.Table.ofEntries [u] with
          | .ok t => pure t
          | .error d => throw (IO.userError d.message)
        expectRefusal "entry-unsupported" (Wiz.Ext.resolveBackendIn tu "demo") },
    { name := "override is doc-language-only, a core payload is core-only, and malformed entries are refused", run := fun _ => do
        let over : Wiz.Ext.Entry :=
          { kind := .backend, name := "x", abi := "wiz-backend/1", override := true, payload := .core .c }
        expectRefusal "invalid-target-override" (Wiz.Ext.Table.ofEntries [over])
        let empty : Wiz.Ext.Entry := { kind := .backend, name := "", abi := "wiz-backend/1", payload := .core .c }
        expectRefusal "invalid-target-name" (Wiz.Ext.Table.ofEntries [empty])
        let noAbi : Wiz.Ext.Entry := { kind := .backend, name := "y", payload := .core .c }
        expectRefusal "invalid-target-abi" (Wiz.Ext.Table.ofEntries [noAbi])
        let pkgCore : Wiz.Ext.Entry :=
          { kind := .backend, name := "z", provider := "demo-pkg", abi := "wiz-backend/1", payload := .core .c }
        expectRefusal "invalid-target-payload" (Wiz.Ext.Table.ofEntries [pkgCore]) },
    { name := "the enabled target enters the cache key: a bpf build cannot reuse c's cached module", run := fun _ => do
        let tcC : Toolchain := {}
        let tcB : Toolchain := { tcC with backend := "bpf" }
        check (tcC.targetTag != tcB.targetTag) "the target name is not in targetTag"
        check (tcC.tag != tcB.tag) "the target is not in the toolchain tag"
        check (tcC.id != tcB.id) "the target is not in the fast toolchain id"
        let lib ← preludeLoader
        let init : CommandState ZeroOneMany :=
          { trustedModule := Tests.libModule, loader := lib }
        let src := "import Prelude\ndef extCacheProbe : Nat := 1\n"
        let dir ← IO.FS.createTempDir
        let run (tc : Toolchain) : IO (CommandState ZeroOneMany × Nat) :=
          Cache.elaborateCached (some dir) [] src init 0
            (toolchain := tc.id) (strongToolchain := tc.tag) (targetTag := tc.targetTag)
        let (_, c1) ← run tcC
        let (_, c2) ← run tcC
        let (_, b1) ← run tcB
        let (_, b2) ← run tcB
        IO.FS.removeDirAll dir
        checkEq 0 c1
        check (c2 > 0) "the c build did not hit its own cache"
        check (b1 == 0) "a bpf build served a module cached under c"
        check (b2 > 0) "the bpf build did not hit its own cache" },
    { name := "CLI: --target bogus exits 1 with the old sentence and writes nothing", run := fun _ => do
        let (code, err) ← extRunWiz ["build", "probe.wiz", "-o", "out", "--target", "bogus"]
        checkEq (1 : UInt32) code
        check ((err.splitOn "unknown target bogus (choose c, llvm, wasm, bpf, js or ebpf)").length > 1) err },
    { name := "CLI: --target js --lib is a target-capability refusal (exit 2), before any build", run := fun _ => do
        let (code, err) ← extRunWiz ["build", "probe.wiz", "-o", "out", "--target", "js", "--lib"]
        checkEq (2 : UInt32) code
        check ((err.splitOn "target-capability: ").length > 1) err
        check ((err.splitOn "target js does not declare the capability 'library'").length > 1) err },
    { name := "CLI: --target bpf --attest is a target-capability refusal (exit 2), before the bpf driver", run := fun _ => do
        let (code, err) ← extRunWiz ["build", "probe.wiz", "-o", "out", "--target", "bpf", "--attest"]
        checkEq (2 : UInt32) code
        check ((err.splitOn "target-capability: ").length > 1) err
        check ((err.splitOn "target bpf does not declare the capability 'attest'").length > 1) err },
    { name := "CLI: --target ebpf is accepted through bpf's alias", run := fun _ => do
        let (code, err) ← extRunWiz ["check", "probe.wiz", "--target", "ebpf"]
        checkEq (0 : UInt32) code
        checkEq "" err },
    { name := "the fifth-target bug class is gone: Main.lean has no target name comparison or list", run := fun _ => do
        let src ← IO.FS.readFile "Main.lean"
        check ((src.splitOn "target == \"").length == 1) "Main.lean compares a target name"
        check ((src.splitOn "targets.contains").length == 1) "Main.lean still has the target list"
        check ((src.splitOn "def targets : List String").length == 1) "Main.lean still declares the target list" },
    { name := "capabilities are kind-scoped: a lint rule cannot emit, a backend cannot read a lint view", run := fun _ => do
        let refute (e : Wiz.Ext.Entry) (code : String) : IO Unit :=
          expectRefusal code (Wiz.Ext.Table.ofEntries [e])
        refute { kind := .backend, name := "demo", abi := "wiz-backend/1",
                 caps := [.emit, .decl], payload := .process "demo-backend" }
          "invalid-target-capability"
        refute { kind := .lintRule, name := "W101", abi := "wiz-lint/1",
                 caps := [.emit], payload := .data }
          "invalid-lint-rule-capability"
        refute { kind := .lintSet, name := "demo", abi := "wiz-lint/1",
                 caps := [.run], payload := .data }
          "invalid-lint-set-capability"
        refute { kind := .deriver, name := "BEq", abi := "wiz-meta/1",
                 caps := [.elabTactic], payload := .wizRule "deriveBEq" }
          "invalid-deriver-capability"
        refute { kind := .termElab, name := "term.tau", abi := "wiz-meta/1",
                 caps := [.elabTerm, .emit], payload := .wizRule "tauElab" }
          "invalid-term-elab-capability"
        refute { kind := .docLanguage, name := "demo", abi := "wiz.doc.languages/1",
                 caps := [.emit], payload := .data }
          "invalid-doc-language-capability"
        -- and the allowed lists are what the table accepts
        let allowed : List Wiz.Ext.Entry := [
          { kind := .lintRule, name := "W101", abi := "wiz-lint/1",
            caps := [.decl, .spans], payload := .data },
          { kind := .lintSet, name := "demo", abi := "wiz-lint/1",
            caps := [.facts, .elabLint], payload := .data },
          { kind := .termElab, name := "term.tau", abi := "wiz-meta/1",
            caps := [.elabTerm], payload := .wizRule "tauElab" },
          { kind := .tactic, name := "tac.tau", abi := "wiz-meta/1",
            caps := [.elabTactic], payload := .wizRule "tauTac" },
          { kind := .macro, name := "mac.tau", abi := "wiz-meta/1",
            caps := [.elabMacro], payload := .wizRule "tauMacro" },
          { kind := .backend, name := "demo", abi := "wiz-backend/1",
            caps := [.emit, .check], payload := .process "demo-backend" } ]
        match Wiz.Ext.Table.ofEntries allowed with
        | .ok t => checkEq 6 t.entries.length
        | .error d => throw (IO.userError s!"allowed capabilities refused: {d.code}: {d.message}") },
    { name := "an elaboration entry resolves through the same table: not-enabled, capability, ABI, duplicate", run := fun _ => do
        let tau : Wiz.Ext.Entry :=
          { kind := .termElab, name := "term.tau", provider := "demo-pkg", set := "demo-set",
            abi := "wiz-meta/1", caps := [.elabTerm], payload := .wizRule "tauElab" }
        let t ← match Wiz.Ext.Table.ofEntries [tau] with
          | .ok t => pure t
          | .error d => throw (IO.userError d.message)
        expectRefusal "term-elab-not-enabled" (t.resolve .termElab "term.tau" [.elabTerm])
        match t.resolve .termElab "term.tau" [.elabTerm] (enabledSets := ["demo-set"]) with
        | .ok e => checkEq "term.tau" e.name
        | .error d => throw (IO.userError s!"the enabled term elaborator did not resolve: {d.code}: {d.message}")
        expectRefusal "term-elab-capability"
          (t.resolve .termElab "term.tau" [.elabTactic] (enabledSets := ["demo-set"]))
        expectRefusal "unsupported-term-elab"
          (t.resolve .termElab "term.tau" (enabledSets := ["demo-set"]) (abi := "wiz-meta/2"))
        -- an entry declaring no elaboration capability cannot be run as one
        let noCap : Wiz.Ext.Entry :=
          { kind := .termElab, name := "term.none", provider := "demo-pkg", set := "demo-set",
            abi := "wiz-meta/1", payload := .wizRule "noElab" }
        let t2 ← match Wiz.Ext.Table.ofEntries [noCap] with
          | .ok t => pure t
          | .error d => throw (IO.userError d.message)
        expectRefusal "term-elab-capability"
          (t2.resolve .termElab "term.none" [.elabTerm] (enabledSets := ["demo-set"]))
        -- two providers for one elaboration kind name both
        let other : Wiz.Ext.Entry := { tau with provider := "demo-other" }
        match Wiz.Ext.Table.ofEntries [tau, other] with
        | .error d => do
          checkEq "duplicate-term-elab" d.code
          check (d.message.contains "demo-pkg" && d.message.contains "demo-other")
            s!"providers missing: {d.message}"
        | .ok _ => throw (IO.userError "two term elaborators for one kind were registered") }
  ]

builtin_initialize registerGroup extGroup

end Tests.Elab
