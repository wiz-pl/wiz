import Tests.Harness
import Wiz.Ext.Basic

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- A refusal with this stable code, or a failure: a success is not allowed to pass a
negative test. -/
def expectRefusal {α : Type} (code : String) (r : Except Wiz.Ext.Refusal α) : IO Unit :=
  match r with
  | .error e => checkEq code e.code
  | .ok _ => throw (IO.userError s!"expected the refusal '{code}', but the call succeeded")

/-- The shared entry registry (`Wiz/Ext/Basic.lean`): one declaration per core target,
resolution by `(kind, name)`, and refusals as data. These cases are pure: no compiler,
no process, no scratch directory. -/
def extGroup : Group where
  name := "ext"
  exercise := "Wiz/Ext/Basic.lean (the shared entry registry)"
  parallel := true
  cases := [
    { name := "the five core targets resolve by key and declare the capabilities they serve", run := fun _ => do
        for n in ["c", "llvm", "wasm", "bpf", "js"] do
          match Wiz.Ext.resolveBackend n with
          | .error r => throw (IO.userError s!"{n}: {r.code}: {r.message}")
          | .ok e => do
            check (e.kind == .backend) s!"{n} has kind {reprStr e.kind}, not backend"
            checkEq n e.name
            checkEq "wiz-backend/1" e.abi
            checkEq s!"target/{n}" (Wiz.Ext.Entry.key e)
        let c ← match Wiz.Ext.resolveBackend "c" with
          | .ok e => pure e | .error r => throw (IO.userError r.message)
        for cap in [Wiz.Ext.Cap.emit, .check, .link, .run, .attest, .library, .split, .repl] do
          check (c.caps.contains cap) s!"c lacks {cap.key}"
        let bpf ← match Wiz.Ext.resolveBackend "bpf" with
          | .ok e => pure e | .error r => throw (IO.userError r.message)
        check (bpf.caps.contains .check) "bpf must declare check"
        for cap in [Wiz.Ext.Cap.run, .attest, .library, .split, .repl] do
          check (!bpf.caps.contains cap) s!"bpf must not claim {cap.key}"
        let js ← match Wiz.Ext.resolveBackend "js" with
          | .ok e => pure e | .error r => throw (IO.userError r.message)
        check (js.caps.contains .run) "js runs a module"
        for cap in [Wiz.Ext.Cap.attest, .library, .split, .repl] do
          check (!js.caps.contains cap) s!"js must not claim {cap.key}" },
    { name := "an unknown target is refused, never defaulted to c", run := fun _ => do
        expectRefusal "unknown-target" (Wiz.Ext.resolveBackend "bpf2")
        match Wiz.Ext.resolveBackend "bpf2" with
        | .error e => check (e.message.contains "choose") s!"no choices in: {e.message}"
        | .ok _ => throw (IO.userError "bpf2 resolved") },
    { name := "a duplicate (kind, name) is refused naming both providers", run := fun _ => do
        let a : Wiz.Ext.Entry :=
          { kind := .backend, name := "demo", provider := "wiz-a", abi := "wiz-backend/1" }
        let b : Wiz.Ext.Entry := { a with provider := "wiz-b" }
        match Wiz.Ext.Table.ofEntries [a, b] with
        | .error e => do
          checkEq "duplicate-target" e.code
          check (e.message.contains "wiz-a" && e.message.contains "wiz-b") s!"provider names missing: {e.message}"
        | .ok _ => throw (IO.userError "a duplicate target was registered") },
    { name := "a capability the entry does not declare is refused before dispatch", run := fun _ => do
        expectRefusal "target-capability" (Wiz.Ext.resolveBackendFor "js" [.link])
        expectRefusal "target-capability" (Wiz.Ext.resolveBackendFor "bpf" [.run])
        match Wiz.Ext.resolveBackendFor "c" [.link, .attest] with
        | .ok _ => pure ()
        | .error r => throw (IO.userError s!"c refused link+attest: {r.code}: {r.message}") },
    { name := "an entry this toolchain cannot serve is refused with its reason", run := fun _ => do
        let u : Wiz.Ext.Entry :=
          { kind := .backend, name := "demo", abi := "wiz-backend/1",
            payload := .unsupported "this toolchain emits c-text/1, not bpf-core/1" }
        let t ← match Wiz.Ext.Table.ofEntries [u] with
          | .ok t => pure t
          | .error r => throw (IO.userError r.message)
        expectRefusal "entry-unsupported" (t.resolve .backend "demo") },
    { name := "override is a doc-language-only field, and a malformed entry is refused", run := fun _ => do
        let e : Wiz.Ext.Entry :=
          { kind := .backend, name := "x", abi := "wiz-backend/1", override := true }
        expectRefusal "invalid-target-override" (Wiz.Ext.Table.ofEntries [e])
        let empty : Wiz.Ext.Entry :=
          { kind := .backend, name := "", abi := "wiz-backend/1" }
        expectRefusal "invalid-target-name" (Wiz.Ext.Table.ofEntries [empty])
        let noAbi : Wiz.Ext.Entry := { kind := .backend, name := "y" }
        expectRefusal "invalid-target-abi" (Wiz.Ext.Table.ofEntries [noAbi]) }
  ]

builtin_initialize registerGroup extGroup

end Tests.Elab
