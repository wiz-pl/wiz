import Tests.Elab

open Wiz
open Wiz.Compiler.Bpf

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

/-!
# `bpf-trace`: the tracing program kind (tracepoint/uprobe)

This group covers the second program kind of the eBPF backend (`wiz-notes/ebpf-dynamic.md`
§1, §2, §6): a `tracepoint` (and a declared-layout `uprobe`) compiles to the C the loader
expects, the section name and numeric `bpf_attr.prog_type` are in the `wiz-probe/1`
descriptor, the event encoder writes the `scry-probe-event/1` JSON line, and the
unsupported/out-of-bounds/helper-misuse cases are positioned `bpf:` errors rather than
silent fallbacks.

Everything here is pure: no `clang`, no `bpf()`, no privileges. The attach/read/detach
half is a **local gate** (`docs/stages/08-backend/bpf.md`): it needs `CAP_BPF` and a
pinned kernel, and a tracepoint is not `BPF_PROG_TEST_RUN`-able in general. CI asserts the
bytes (C text + descriptor) and the refusal; it never loads a probe.
-/

namespace Tests.BpfTraceGroup

/-- Assert a rejection: the stable `bpf:` prefix, a message fragment, and (when `at` is
given) the positioned `(at file:line:col)` suffix. -/
def expectReject {α : Type} (r : Except String α) (fragment : String)
    (at? : Option String := none) : IO Unit :=
  match r with
  | .error e => do
    check (e.startsWith "bpf:") s!"not a `bpf:` diagnostic: {e}"
    check ((e.splitOn fragment).length > 1) s!"the message does not mention `{fragment}`: {e}"
    match at? with
    | some pos => check ((e.splitOn pos).length > 1) s!"the message is not positioned at `{pos}`: {e}"
    | none => pure ()
  | .ok _ => throw (IO.userError s!"accepted; expected a diagnostic mentioning `{fragment}`")

/-- A minimal XDP program: `flow : XdpContext → XdpAction`. -/
def xdpProgram (decls : Array SDecl) (maps : Array SMapDecl := #[]) : SProgram :=
  { entry := "flow", sectionName := "xdp", kind := .xdp, license := "GPL", version := 1,
    maps, decls, ret := .enum 5 }

/-- A minimal tracepoint program: `execve : TraceCtx → UIntN 32`. -/
def traceProgram (decls : Array SDecl) (maps : Array SMapDecl := #[])
    (sec : String := "tracepoint/syscalls/sys_enter_execve")
    (ret : STy := .uint 32) (transport : Transport := .perfEventArray)
    (kind : ProgKind := .tracepoint) : SProgram :=
  { entry := "execve", sectionName := sec, kind, license := "GPL",
    version := 1, maps, decls, ret, transport }

/-- A tracepoint body that reads one string and emits it once. The fixture
`Tests/fixtures/bpf/execve.bpfcore` is the serialised version of this shape; this helper
is the typed-surface neighbour used by the emitter tests. -/
def execveBody (slot : Nat := 0) : STm :=
  .ret <|
    .letE 1 (.option (.userStr 80))
      (.readUserStr 80 (.var 0) (.ctxArg 0 (.var 0)))
      (.switchOption (.var 1) (.uintLit 32 0) 2
        (.letE 3 .bool
          (.probeEmit "events" .execve slot (.var 0)
            (.ctxPid (.var 0)) (.ctxTgid (.var 0)) (.uintLit 32 0)
            (.ctxNow (.var 0)) (.var 2))
          (.uintLit 32 0)))

/-- The perf-array and lost-counter maps every tracing fixture declares. -/
def traceMaps : Array SMapDecl := #[
  { name := "events", kind := .perfEventArray, key := .uint 32, value := .uint 32,
    maxEntries := 64 },
  { name := "lost", kind := .percpuArray, key := .uint 32, value := .uint 64,
    maxEntries := 1 }]

/-- `str` occurs in `s`. -/
def has (s str : String) : Bool := (s.splitOn str).length > 1

def group : Group where
  name := "bpf-trace"
  exercise := "Exercise 8.7 (eBPF): the tracing sensor program kind"
  parallel := false
  shard := "library"
  cases := [
    -- The fixture is the whole pipeline: manifest + bpf-core/1 → check → C + descriptor.
    { name := "the execve fixture emits a tracepoint object shape", run := fun _ => do
        let manifestText ← IO.FS.readFile "Tests/fixtures/bpf/execve.toml"
        let coreText ← IO.FS.readFile "Tests/fixtures/bpf/execve.bpfcore"
        match parseManifest manifestText with
        | .error e => throw (IO.userError e)
        | .ok m => do
          check (m.program.kind == .tracepoint) "the manifest kind is not tracepoint"
          checkEq "tracepoint/syscalls/sys_enter_execve" m.program.sectionName
          check (m.program.transport == .perfEventArray) "the default transport is not perf"
          check (m.program.line > 0) "the manifest section has no line number"
          match Sexp.parseCore coreText with
          | .error e => throw (IO.userError e)
          | .ok core => do
            let prog : Program :=
              { entry := m.program.entry, sectionName := m.program.sectionName,
                kind := m.program.kind, license := m.program.license,
                version := m.program.version, maps := m.maps, decls := core.decls,
                ret := core.ret, transport := m.program.transport,
                span := { file := "Tests/fixtures/bpf/execve.toml",
                          line := m.program.line, col := 1 } }
            match emitProgram prog with
            | .error e => throw (IO.userError s!"the tracing fixture was rejected: {e}")
            | .ok c => do
              check (has c "#define BPF_TRACEPOINT 1") "the tracing define is missing"
              check (has c "SEC(\"tracepoint/syscalls/sys_enter_execve\")")
                "the section is not the tracepoint spelling the loader reads"
              check (has c "ctx_pid(") "no pid projection"
              check (has c "ctx_tgid(") "no tgid projection"
              check (has header "bpf_get_current_pid_tgid")
                "the header does not declare the pid/tgid helper"
              check (has c "bpf_probe_read_user_str") "no capped user read"
              check (has header "bpf_probe_read_user") "the header omits the pointer read"
              check (has c "read_user_ptr") "no bounded argv-slot accessor"
              check (has c "bpf_perf_event_output") "no perf-buffer output"
              check (has c "bpf_get_current_comm") "no comm fill"
              check (has c "read_user_str_80") "no literal-cap read helper"
              check (has c "return 0;") "a tracing entry must return int 0 for Unit"
              check (has c "__builtin_memcpy") "the event payload is not copied"
              match probeDescriptor prog with
              | .error e => throw (IO.userError e)
              | .ok d => do
                check (has d "\"schema\":\"wiz-probe/1\"") "not a wiz-probe/1 descriptor"
                check (has d "\"prog_type\":5") "the loader's program type is not TRACEPOINT=5"
                check (has d "\"prog_type_name\":\"BPF_PROG_TYPE_TRACEPOINT\"")
                  "the program type name is missing"
                check (has d "\"spec\":\"syscalls:sys_enter_execve\"")
                  "the attach spec is not category:event"
                check (has d "\"size\":64") "the tracepoint context size is not 64"
                check (has d "\"data_cap\":80") "the event data cap is not 80"
                check (has d "\"size\":128") "the event is not the 128-byte ABI"
                check (has d "\"truncated_flag\":1") "the truncation flag is not pinned"
                check (has d "\"transport\":\"perf_event_array\"")
                  "the transport is not the perf array"
                check (has d "\"bpf_probe_read_user_str\"") "the helper list omits the read"
                check (has d "\"id\":115") "the read helper's id is not 115"
                check (has d "\"bpf_probe_read_user\"") "the argv pointer helper is missing"
                check (has d "\"id\":112") "the pointer helper's id is not 112" },

    -- the CLI's own path: manifest + core → C + the descriptor beside it
    { name := "the manifest pipeline carries the descriptor", run := fun _ => do
        match ← compileManifest (System.FilePath.mk "Tests/fixtures/bpf/execve.toml") with
        | .error e => throw (IO.userError s!"compileManifest failed: {e}")
        | .ok compiled => do
          check (has compiled.c "SEC(\"tracepoint/syscalls/sys_enter_execve\")")
            "the compiled C has no tracepoint section"
          match compiled.probe with
          | some d => do
            check (has d "\"schema\":\"wiz-probe/1\"") "the pipeline wrote no wiz-probe/1"
            check (has d "\"prog_type\":5") "the pipeline lost the program type"
          | none => throw (IO.userError "the tracing pipeline wrote no descriptor") },

    -- §2.2: the userspace encoder, exact bytes.
    { name := "the event encoder writes the scry-probe-event/1 line", run := fun _ => do
        let e : ProbeEvent :=
          { probe := "execve", attach := "syscalls:sys_enter_execve", kind := "execve",
            ts := 123, pid := 4711, tid := 4711, tgid := 4711, ppid := 4700,
            comm := "sh", slot := 0, data := "/bin/sh", truncated := false,
            marker := some "scry-poc-f_edbaeb86bcfed108" }
        let expected :=
          "{\"schema\":\"scry-probe-event/1\",\"probe\":\"execve\"," ++
          "\"attach\":\"syscalls:sys_enter_execve\",\"ts\":123,\"pid\":4711," ++
          "\"tid\":4711,\"tgid\":4711,\"ppid\":4700,\"comm\":\"sh\"," ++
          "\"kind\":\"execve\",\"slot\":0,\"data\":\"/bin/sh\"," ++
          "\"truncated\":false,\"marker\":\"scry-poc-f_edbaeb86bcfed108\"}"
        checkEq expected e.toJson
        checkEq (expected ++ "\n") e.toLine
        -- escaping is not cosmetic: a probe payload is user bytes
        let q : ProbeEvent := { e with data := "a\"b\\c" , marker := none }
        check (has q.toJson "\"data\":\"a\\\"b\\\\c\"") "a quote/backslash was not escaped" },

    -- the fixture's OOB check: our check, not the kernel's `map_value_or_null`
    { name := "an out-of-bounds array index is a positioned compile error", run := fun _ => do
        let body : STm :=
          .ret <|
            .letE 1 (.option (.uint 32))
              (.withSpan { file := "probe.wiz", line := 12, col := 3 }
                (.mapLookup "arr" (.uintLit 32 4)))
              (.uintLit 32 0)
        let prog := traceProgram #[
          { name := "execve", params := #[.ctx .tracepoint], ret := .uint 32, body }]
          #[{ name := "arr", kind := .array, key := .uint 32, value := .uint 32,
              maxEntries := 4 }]
        expectReject (lowerProgram prog) "out of bounds" (some "(at probe.wiz:12:3)") },

    -- the neighbour: a runtime key is not statically bounded; the lookup's null test is
    -- the policy's job, and the kernel's `map_value_or_null` is the backstop
    { name := "a runtime array index is accepted", run := fun _ => do
        let body : STm :=
          .ret <|
            .letE 1 (.uint 32) (.uintLit 32 99) <|
            .letE 2 (.option (.uint 32)) (.mapLookup "arr" (.var 1)) (.uintLit 32 0)
        let prog := traceProgram #[
          { name := "execve", params := #[.ctx .tracepoint], ret := .uint 32, body }]
          #[{ name := "arr", kind := .array, key := .uint 32, value := .uint 32,
              maxEntries := 4 }]
        match lowerProgram prog with
        | .error e => throw (IO.userError s!"the runtime-key neighbour was rejected: {e}")
        | .ok _ => pure () },

    -- §2.1: the perf array is an output ring
    { name := "a perf_event_array cannot be looked up", run := fun _ => do
        let body : STm :=
          .ret <|
            .letE 1 (.option (.uint 32)) (.mapLookup "events" (.uintLit 32 0))
              (.uintLit 32 0)
        let prog := traceProgram #[
          { name := "execve", params := #[.ctx .tracepoint], ret := .uint 32, body }]
          #[{ name := "events", kind := .perfEventArray, key := .uint 32,
              value := .uint 32, maxEntries := 64 }]
        expectReject (lowerProgram prog) "output ring" },

    -- §2.1: the argv walk is a constant bound, not a runtime `argc`
    { name := "an argv slot past the constant bound is a positioned error", run := fun _ => do
        let body : STm :=
          .ret <|
            .letE 1 (.option (.userStr 80))
              (.withSpan { file := "probe.wiz", line := 40, col := 5 }
                (.argvSlot 80 (.var 0) (.ctxArg 1 (.var 0)) 4))
              (.uintLit 32 0)
        let prog := traceProgram #[
          { name := "execve", params := #[.ctx .tracepoint], ret := .uint 32, body }]
        expectReject (lowerProgram prog) "the argv slot 4 is outside 0..3"
          (some "(at probe.wiz:40:5)") },

    -- §2.3: a packet accessor has no meaning on a tracepoint context
    { name := "a packet projection in a tracepoint is rejected", run := fun _ => do
        let body : STm :=
          .ret <|
            .letE 1 .packet
              (.withSpan { file := "probe.wiz", line := 20, col := 7 }
                (.ctxPacket (.var 0)))
              (.uintLit 32 0)
        let prog := traceProgram #[
          { name := "execve", params := #[.ctx .tracepoint], ret := .uint 32, body }]
        expectReject (lowerProgram prog) "no `data`/`data_end`" (some "(at probe.wiz:20:7)") },

    -- §7.2: a helper's `kinds` is the gate, not the kernel's ENOTSUPP
    { name := "a tracing helper in an XDP program is rejected", run := fun _ => do
        let body : STm :=
          .ret <|
            .letE 1 (.uint 64)
              (.withSpan { file := "probe.wiz", line := 30, col := 9 }
                (.helper "Bpf.pidTgid" #[]))
              (.enumLit 5 2)
        let prog := xdpProgram #[
          { name := "flow", params := #[.ctx .xdp], ret := .enum 5, body }]
        expectReject (lowerProgram prog) "not available in a XDP program"
          (some "(at probe.wiz:30:9)") },

    { name := "the pid helper is accepted in a tracepoint", run := fun _ => do
        let body : STm :=
          .ret <|
            .letE 1 (.uint 64) (.helper "Bpf.pidTgid" #[]) (.uintLit 32 0)
        let prog := traceProgram #[
          { name := "execve", params := #[.ctx .tracepoint], ret := .uint 32, body }]
        match lowerProgram prog with
        | .error e => throw (IO.userError s!"the tracing helper neighbour was rejected: {e}")
        | .ok p => do
          match emitProgram p with
          | .error e => throw (IO.userError e)
          | .ok c =>
            check (has c "bpf_get_current_pid_tgid()") "the pid helper has no C spelling"
          match probeDescriptor p with
          | .error e => throw (IO.userError e)
          | .ok d => check (has d "\"id\":14") "the descriptor omits helper 14" },

    -- §5.1/§5.2: a manifest typo is positioned, not a silent C fallback
    { name := "an unsupported manifest program type is a positioned error", run := fun _ => do
        let text := "# a manifest
[program.bad]
entry = \"bad\"
section = \"xdp\"
type = \"kprobe\"
license = \"GPL\"
version = 1
"
        match parseManifest text with
        | .error e => do
          check (e.startsWith "bpf.toml:") s!"not a positioned manifest error: {e}"
          check (has e "is not a program kind") s!"the error does not name the type: {e}"
          check (has e "kprobe") s!"the error does not quote `kprobe`: {e}"
        | .ok _ => throw (IO.userError "the unsupported `type = \"kprobe\"` was accepted") },

    { name := "a section/type mismatch is a positioned error", run := fun _ => do
        let text := "# a manifest
[program.bad]
entry = \"bad\"
section = \"xdp\"
type = \"tracepoint\"
license = \"GPL\"
version = 1
"
        match parseManifest text with
        | .error e => do
          check (e.startsWith "bpf.toml:") s!"not a positioned manifest error: {e}"
          check (has e "but `type` is tracepoint") s!"the mismatch is not named: {e}"
        | .ok _ => throw (IO.userError "the section/type mismatch was accepted") },

    -- the ABI's section is program-specific, so the emitter uses the manifest's spelling
    { name := "a tracepoint section is preserved verbatim in SEC", run := fun _ => do
        let prog := traceProgram #[
          { name := "execve", params := #[.ctx .tracepoint], ret := .uint 32,
            body := .ret (.uintLit 32 0) }] #[] "tracepoint/sched/sched_process_fork"
        match lowerProgram prog with
        | .error e => throw (IO.userError e)
        | .ok p =>
          match emitProgram p with
          | .error e => throw (IO.userError e)
          | .ok c =>
            check (has c "SEC(\"tracepoint/sched/sched_process_fork\")")
              "the section was rewritten to the canonical spelling" },

    -- §2.1 fallback: the debug transport is a line on the trace pipe, not JSON
    { name := "the trace_printk fallback is emitted on request", run := fun _ => do
        let prog := traceProgram #[
          { name := "execve", params := #[.ctx .tracepoint], ret := .uint 32,
            body := execveBody }] traceMaps
          (sec := "tracepoint/syscalls/sys_enter_execve")
          (transport := .tracePrintk)
        match lowerProgram prog with
        | .error e => throw (IO.userError e)
        | .ok p =>
          match emitProgram p with
          | .error e => throw (IO.userError e)
          | .ok c => do
            check (has c "bpf_trace_printk") "the fallback transport is missing"
            check (!has c "bpf_perf_event_output") "the fallback still emits perf output"
            check (has c "#define BPF_TRACEPOINT 1") "the tracing define is missing"
            match probeDescriptor p with
            | .error e => throw (IO.userError e)
            | .ok d => do
              check (has d "\"transport\":\"trace_printk\"") "the descriptor hides the fallback"
              check (has d "\"bpf_trace_printk\"") "the helper list omits trace_printk" },

    -- §5.2 `uprobe`: the declared x86_64 `pt_regs` layout, program type KPROBE=2
    { name := "a uprobe program carries the declared pt_regs layout", run := fun _ => do
        let prog := traceProgram #[
          { name := "execve", params := #[.ctx .uprobe], ret := .uint 32,
            body := .ret (.uintLit 32 0) }] #[]
          (sec := "uprobe//bin/sh:readline")
          (ret := .uint 32) (kind := .uprobe)
        match lowerProgram prog with
        | .error e => throw (IO.userError e)
        | .ok p =>
          match emitProgram p with
          | .error e => throw (IO.userError e)
          | .ok c =>
            check (has c "#define BPF_UPROBE 1") "the uprobe define is missing"
            check (has c "SEC(\"uprobe//bin/sh:readline\")") "the uprobe section is missing"
            check (has c "_Static_assert(sizeof(struct bpf_pt_regs) == 168")
              "the pt_regs layout is not asserted"
            match probeDescriptor p with
            | .error e => throw (IO.userError e)
            | .ok d => do
              check (has d "\"prog_type\":2") "KPROBE is not program type 2"
              check (has d "\"arch\":\"x86_64\"") "the uprobe ABI is not pinned to x86_64"
              check (has d "\"size\":168") "the pt_regs size is not 168"
              check (has d "\"spec\":\"/bin/sh:readline\"") "the uprobe attach spec is wrong" },

    -- the control: adding a program kind must not change the packet path
    { name := "the existing xdp fixture is unchanged", run := fun _ => do
        let text ← IO.FS.readFile "Tests/fixtures/bpf/allow.bpfcore"
        match Sexp.parseCore text with
        | .error e => throw (IO.userError e)
        | .ok core => do
          let maps : Array MapDecl := #[
            { name := "allow", kind := .hash, key := .u32, value := .u8, maxEntries := 4096 },
            { name := "hits", kind := .percpuArray, key := .u32, value := .u64,
              maxEntries := 256 }]
          let prog : Program :=
            { entry := "flow", sectionName := "xdp", kind := .xdp, license := "GPL",
              version := 1, maps, decls := core.decls, ret := core.ret }
          match emitProgram prog with
          | .error e => throw (IO.userError s!"the xdp fixture was rejected: {e}")
          | .ok c => do
            check (has c "SEC(\"xdp\")") "the xdp section changed"
            check (!has c "BPF_TRACEPOINT") "an xdp object grew a tracing define"
            check (!has c "bpf_perf_event_output") "an xdp object grew a perf output"
            check (!has c "struct scry_probe_event") "an xdp object grew the event struct"
            check (has c "pkt_load32be") "the packet load disappeared"
            check (has c "__sync_fetch_and_add") "the atomic map add disappeared"
          match probeDescriptor prog with
          | .error _ => pure ()
          | .ok _ => throw (IO.userError "an xdp program grew a probe descriptor") },

    -- §5: the selfhost emits c-text/1 and serialises no program; it must refuse by name
    { name := "the selfhost refuses --target ebpf with the pinned sentence", run := fun _ => do
        -- the source-level half always runs: the pinned sentence is the contract
        let cli ← IO.FS.readFile "selfhost/Cli.wiz"
        check (has cli
          "unsupported-target: the backend 'ebpf' reads bpf-core/1. This toolchain emits c-text/1 and does not serialise its program (docs/selfhost-compiler.md:114). Build the probe with the host wiz.")
          "the pinned refusal is not in selfhost/Cli.wiz"
        check (has cli "def targetIsProbe") "the selfhost has no probe-target predicate"
        -- and, when the selfhost compiler builds, the driver's exit code and stderr
        match ← Tests.Elab.selfhostCompiler with
        | .error e => skip s!"selfhost compiler unavailable: {e}"
        | .ok exe => do
          let dir ← IO.FS.createTempDir
          IO.FS.writeFile (dir / "n.wiz") "import Prelude\ndef main : Nat := 1\n"
          let out ← IO.Process.output
            { cmd := "timeout", args := #["120", exe.toString, "check", "n.wiz",
                                          "--target", "ebpf"], cwd := dir }
          checkEq 1 out.exitCode
          check (has out.stderr
            "unsupported-target: the backend 'ebpf' reads bpf-core/1. This toolchain emits c-text/1 and does not serialise its program (docs/selfhost-compiler.md:114). Build the probe with the host wiz.")
            s!"the pinned refusal is not on stderr:\n{out.stderr}" }
  ]

builtin_initialize registerGroup group

end Tests.BpfTraceGroup
