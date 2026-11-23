/-
# `Bpf.Probe`: the tracing event ABI and the `wiz-probe/1` descriptor

This is the userspace half of the tracing program kind (`wiz-notes/ebpf-dynamic.md` §2).
The kernel program writes one fixed POD `struct scry_probe_event`; this module pins that
struct's offsets, the declared context layout, the helper set and the attach metadata in
a JSON descriptor, and provides the one pure encoder from a decoded event to the
`scry-probe-event/1` JSON Lines record.

The descriptor is what a loader reads instead of guessing from the C text: section name,
numeric `bpf_attr.prog_type`, attach spec, context layout, event offsets, data cap,
transport and helper ids. The C emitter and the descriptor share the constants in
`Bpf.Core`, so they cannot drift silently.

Nothing here calls `bpf()`, `clang` or the kernel: the encoder and the descriptor are
pure, so the CI test is compile-only. The attach/read/detach path is a documented local
gate (`docs/stages/08-backend/bpf.md`); it needs `CAP_BPF`.
-/
import Wiz.Compiler.Bpf.Core

namespace Wiz.Compiler.Bpf

/-! ## JSON fragments -/

/-- A hexadecimal digit (lower case). -/
def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- Escape a string for a JSON string literal. The probe's payload is user bytes; a
control character or a quote must not make the line unparsable. -/
def jsonEscape (s : String) : String :=
  let rec go (cs : List Char) (acc : String) : String :=
    match cs with
    | [] => acc
    | c :: rest =>
      let acc :=
        if c == '"' then acc ++ "\\\""
        else if c == '\\' then acc ++ "\\\\"
        else if c == '\n' then acc ++ "\\n"
        else if c == '\r' then acc ++ "\\r"
        else if c == '\t' then acc ++ "\\t"
        else if c.toNat < 0x20 then
          acc ++ "\\u00" ++ s!"{hexDigit (c.toNat / 16)}" ++ s!"{hexDigit (c.toNat % 16)}"
        else acc.push c
      go rest acc
  go s.toList ""

def jsonStr (s : String) : String := "\"" ++ jsonEscape s ++ "\""

def jsonNum (n : Nat) : String := toString n

def jsonBool (b : Bool) : String := if b then "true" else "false"

/-- An object from already-encoded values; the key order is the list's order, so the
descriptor and the event line are stable and diffable. -/
def jsonObj (fields : List (String × String)) : String :=
  "{" ++ String.intercalate "," (fields.map fun (k, v) => jsonStr k ++ ":" ++ v) ++ "}"

def jsonArr (xs : List String) : String :=
  "[" ++ String.intercalate "," xs ++ "]"

/-! ## The `scry-probe-event/1` record -/

/-- One decoded probe event. `pid` is the process id (`tgid` in kernel terms), `tid` is
the thread id (`pid` in kernel terms); both are present because a syscall tracepoint runs
on the thread, while the join wants the process. `slot` says which capture slot the
payload came from (0 = filename/path, 1.. = argv/other). `marker` is a host-side
convenience; the authoritative match is over `data` (`§2.2`). -/
structure ProbeEvent where
  probe : String
  attach : String
  kind : String
  ts : Nat
  pid : Nat
  tid : Nat
  tgid : Nat
  ppid : Nat
  comm : String
  slot : Nat
  data : String
  truncated : Bool := false
  marker : Option String := none
  deriving Repr, BEq, Inhabited

/-- The JSON Lines record of `wiz-notes/ebpf-dynamic.md` §2.2, one line, no trailing
newline. The field set is a superset of the note's example: `tid`/`tgid`/`slot` make the
thread/process distinction and the payload slot explicit instead of implicit in the
host's prose. -/
def ProbeEvent.toJson (e : ProbeEvent) : String :=
  jsonObj <|
    [ ("schema", jsonStr "scry-probe-event/1"),
      ("probe", jsonStr e.probe),
      ("attach", jsonStr e.attach),
      ("ts", jsonNum e.ts),
      ("pid", jsonNum e.pid),
      ("tid", jsonNum e.tid),
      ("tgid", jsonNum e.tgid),
      ("ppid", jsonNum e.ppid),
      ("comm", jsonStr e.comm),
      ("kind", jsonStr e.kind),
      ("slot", jsonNum e.slot),
      ("data", jsonStr e.data),
      ("truncated", jsonBool e.truncated) ] ++
    (match e.marker with
     | some m => [("marker", jsonStr m)]
     | none => [])

/-- The JSON line plus the newline the file format requires. -/
def ProbeEvent.toLine (e : ProbeEvent) : String := e.toJson ++ "\n"

/-! ## Layouts -/

/-- One field of a declared C layout. The offsets are the ABI, not a hint: a loader copies
`size` bytes at `offset`. -/
structure LayoutField where
  name : String
  offset : Nat
  size : Nat
  deriving Repr, BEq, Inhabited

def LayoutField.toJson (f : LayoutField) : String :=
  jsonObj [("name", jsonStr f.name), ("offset", jsonNum f.offset), ("size", jsonNum f.size)]

/-- `struct bpf_trace_event`, the `sys_enter_*` context declared from the tracepoint's
format file: the 8-byte `trace_entry`, the syscall id, then six arguments. No
`vmlinux.h`, no BTF, no CO-RE. The per-tracepoint field offsets are the format file's:
`common_type:0/2 common_flags:2/1 common_preempt_count:3/1 common_pid:4/4 id:8/8
filename:16/8 argv:24/8 envp:32/8` for `sys_enter_execve`. -/
def traceCtxFields : Array LayoutField := #[
  { name := "common", offset := 0, size := 8 },
  { name := "id", offset := 8, size := 8 },
  { name := "args", offset := 16, size := 48 }
]

def traceCtxSize : Nat := 64

/-- `struct bpf_pt_regs`, the x86_64 uapi `struct pt_regs` (21 words, 168 B). The layout
is declared for x86_64 only; the descriptor pins `"arch":"x86_64"` because
`clang -target bpfel` cannot see the host architecture. The first six C argument
registers are rdi, rsi, rdx, rcx, r8, r9. -/
def uprobeCtxFields : Array LayoutField := #[
  { name := "r15", offset := 0, size := 8 },
  { name := "r14", offset := 8, size := 8 },
  { name := "r13", offset := 16, size := 8 },
  { name := "r12", offset := 24, size := 8 },
  { name := "bp", offset := 32, size := 8 },
  { name := "bx", offset := 40, size := 8 },
  { name := "r11", offset := 48, size := 8 },
  { name := "r10", offset := 56, size := 8 },
  { name := "r9", offset := 64, size := 8 },
  { name := "r8", offset := 72, size := 8 },
  { name := "ax", offset := 80, size := 8 },
  { name := "cx", offset := 88, size := 8 },
  { name := "dx", offset := 96, size := 8 },
  { name := "si", offset := 104, size := 8 },
  { name := "di", offset := 112, size := 8 },
  { name := "orig_ax", offset := 120, size := 8 },
  { name := "ip", offset := 128, size := 8 },
  { name := "cs", offset := 136, size := 8 },
  { name := "flags", offset := 144, size := 8 },
  { name := "sp", offset := 152, size := 8 },
  { name := "ss", offset := 160, size := 8 }
]

def uprobeCtxSize : Nat := 168

/-- `struct scry_probe_event`, the kernel → userspace POD event (§2.1). `data` is the
captured prefix (the literal cap is `eventDataCap`), `len` is the valid prefix, and
`meta` packs the slot (low 16) and `truncated` (bit 16). `comm` is
`bpf_get_current_comm`'s NUL-terminated buffer. -/
def eventFields : Array LayoutField := #[
  { name := "kind", offset := 0, size := 4 },
  { name := "pid", offset := 4, size := 4 },
  { name := "tgid", offset := 8, size := 4 },
  { name := "ppid", offset := 12, size := 4 },
  { name := "ts", offset := 16, size := 8 },
  { name := "len", offset := 24, size := 4 },
  { name := "meta", offset := 28, size := 4 },
  { name := "data", offset := 32, size := eventDataCap },
  { name := "comm", offset := 112, size := eventCommCap }
]

/-- The mask a decoder applies to `meta` for the slot. -/
def eventSlotMask : Nat := 0xffff

/-- The `meta` flag a decoder reads: the payload hit the cap. -/
def eventTruncatedFlag : Nat := 1

/-! ## The helper set -/

/-- One kernel helper an object calls. `gplOnly` is why a tracepoint probe's licence must
be `GPL`; the loader checks the kernel's `bpftool feature probe` against this list. -/
structure KernelHelper where
  name : String
  id : Nat
  gplOnly : Bool
  since : Nat
  deriving Repr, BEq, Inhabited

def KernelHelper.toJson (h : KernelHelper) : String :=
  jsonObj <|
    [ ("name", jsonStr h.name),
      ("id", jsonNum h.id),
      ("gpl_only", jsonBool h.gplOnly),
      ("since", jsonNum h.since) ]

def pidTgidHelper : KernelHelper :=
  { name := "bpf_get_current_pid_tgid", id := 14, gplOnly := false, since := 4 }

def ktimeHelper : KernelHelper :=
  { name := "bpf_ktime_get_ns", id := 5, gplOnly := false, since := 4 }

def randomHelper : KernelHelper :=
  { name := "bpf_get_prandom_u32", id := 7, gplOnly := false, since := 4 }

def readUserHelper : KernelHelper :=
  { name := "bpf_probe_read_user", id := 112, gplOnly := true, since := 5 }

def readUserStrHelper : KernelHelper :=
  { name := "bpf_probe_read_user_str", id := 115, gplOnly := true, since := 5 }

def perfOutputHelper : KernelHelper :=
  { name := "bpf_perf_event_output", id := 25, gplOnly := false, since := 4 }

def currentCommHelper : KernelHelper :=
  { name := "bpf_get_current_comm", id := 16, gplOnly := false, since := 4 }

def tracePrintkHelper : KernelHelper :=
  { name := "bpf_trace_printk", id := 6, gplOnly := true, since := 4 }

/-- Every helper named by a term, collected by walking the inlined call graph's terms.
The result is de-duplicated and sorted by id so the descriptor is stable. -/
partial def usedHelperNames (transport : Transport) (t : Tm) (acc : List String) : List String :=
  let add (n : String) (acc : List String) : List String :=
    if acc.contains n then acc else n :: acc
  let acc : List String :=
    match t.node with
    | .ctxPid _ | .ctxTgid _ => add "bpf_get_current_pid_tgid" acc
    | .ctxNow _ => add "bpf_ktime_get_ns" acc
    | .readUserStr _ _ _ => add "bpf_probe_read_user_str" acc
    | .argvSlot _ _ _ _ =>
      add "bpf_probe_read_user_str" (add "bpf_probe_read_user" acc)
    | .probeEmit _ _ _ _ _ _ _ _ _ _ =>
      add "bpf_get_current_comm" <|
        match transport with
        | .perfEventArray => add "bpf_perf_event_output" acc
        | .tracePrintk => add "bpf_trace_printk" acc
    | .helper _ h _ =>
      match h.name with
      | "Bpf.now" => add "bpf_ktime_get_ns" acc
      | "Bpf.random" => add "bpf_get_prandom_u32" acc
      | "Bpf.pidTgid" => add "bpf_get_current_pid_tgid" acc
      | _ => acc
    | _ => acc
  t.node.children.foldl (fun a c => usedHelperNames transport c a) acc

def kernelHelpersOf (p : Program) : Array KernelHelper :=
  let names := p.decls.foldl (fun acc d => usedHelperNames p.transport d.body acc) []
  let all : Array KernelHelper := #[
    pidTgidHelper, ktimeHelper, randomHelper, readUserHelper, readUserStrHelper,
    perfOutputHelper, currentCommHelper, tracePrintkHelper
  ]
  (all.filter fun h => names.contains h.name).qsort fun a b => a.id < b.id

/-! ## The descriptor -/

/-- A map's wire type spelling (`u32`, not `UIntN 32`): a loader reads this, so keep it
machine-shaped. -/
def Ty.jsonName : Ty → String
  | .unit => "unit"
  | .bool => "bool"
  | .u8 => "u8"
  | .u16 => "u16"
  | .u32 => "u32"
  | .u64 => "u64"
  | .i8 => "i8"
  | .i16 => "i16"
  | .i32 => "i32"
  | .i64 => "i64"
  | .enum n => s!"enum:{n}"
  | .struct _ => "struct"
  | .option t => s!"option:{t.jsonName}"
  | .packet => "packet"
  | .ctx k => s!"ctx:{k.typeName}"
  | .userStr cap => s!"userstr:{cap}"
  | .userPtr => "userptr"
  | .map k v kind => s!"map:{k.jsonName}:{v.jsonName}:{kind.describe}"

def mapJson (m : MapDecl) : String :=
  jsonObj <|
    [ ("name", jsonStr m.name),
      ("kind", jsonStr m.kind.describe),
      ("key", jsonStr m.key.jsonName),
      ("value", jsonStr m.value.jsonName),
      ("max_entries", jsonNum m.maxEntries) ]

/-- The `wiz-probe/1` descriptor. The caller must have run `Bpf.Check` (`emitProgram` does);
this function only formats the metadata the loader needs, and refuses a packet program
because a packet program has no probe attach. -/
def probeDescriptor (p : Program) : Except String String := do
  unless p.kind.isTracing do
    throw s!"bpf: a probe descriptor is for a tracepoint or uprobe program, not {p.kind.describe}"
  let some attach := p.attach? |
    throw s!"bpf: the section `{p.sectionName}` has no {p.kind.describe} attach metadata"
  let ctxFields := if p.kind == .tracepoint then traceCtxFields else uprobeCtxFields
  let ctxSize := if p.kind == .tracepoint then traceCtxSize else uprobeCtxSize
  let helperJson := (kernelHelpersOf p).toList.map KernelHelper.toJson
  let mapJsonList := p.maps.toList.map mapJson
  pure <| jsonObj <|
    [ ("schema", jsonStr "wiz-probe/1"),
      ("program", jsonStr p.entry),
      ("entry", jsonStr p.entry),
      ("section", jsonStr p.sectionName),
      ("kind", jsonStr p.kind.describe),
      ("prog_type", jsonNum p.kind.progType),
      ("prog_type_name", jsonStr p.kind.progTypeName),
      ("license", jsonStr p.license),
      ("transport", jsonStr p.transport.describe),
      ("attach", jsonObj [
        ("kind", jsonStr attach.kind),
        ("target", jsonStr attach.target),
        ("event", jsonStr attach.event),
        ("spec", jsonStr attach.spec)]),
      ("context", jsonObj [
        ("struct", jsonStr p.kind.contextName),
        ("arch", jsonStr (if p.kind == .uprobe then "x86_64" else "any")),
        ("size", jsonNum ctxSize),
        ("fields", jsonArr (ctxFields.toList.map LayoutField.toJson))]),
      ("event", jsonObj [
        ("schema", jsonStr "scry-probe-event/1"),
        ("struct", jsonStr "scry_probe_event"),
        ("size", jsonNum eventSize),
        ("data_cap", jsonNum eventDataCap),
        ("comm_cap", jsonNum eventCommCap),
        ("meta", jsonObj [
          ("slot_shift", jsonNum eventMetaSlotShift),
          ("slot_mask", jsonNum eventSlotMask),
          ("flags_shift", jsonNum eventMetaFlagsShift),
          ("truncated_flag", jsonNum eventTruncatedFlag)]),
        ("fields", jsonArr (eventFields.toList.map LayoutField.toJson))]),
      ("maps", jsonArr mapJsonList),
      ("helpers", jsonArr helperJson),
      ("json_fields", jsonArr [
        "probe", "attach", "ts", "pid", "tid", "tgid", "ppid", "comm", "kind",
        "slot", "data", "truncated", "marker"]) ]

end Wiz.Compiler.Bpf
