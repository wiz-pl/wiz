/-
# `BpfCore`: the typed, flat core behind `--target bpf`

This is the IR slice of `wiz-notes/ebpf-target.md` §4.1-§4.2. It is **not** the compiler's
`Wiz.Compiler.IR`: that IR is untyped (`IR.Expr` carries no types, and `match` on a
recursive type has already become the generic `wiz.ind` interpreter), so it cannot tell
the eBPF emitter that `ctor 1 #[x]` is `some x` rather than `List.cons x xs` — tag 1 in
both. `BpfCore` therefore carries a `Ty` on every term. The annotations are produced by
the restriction pass (`Bpf.Lower`, from the elaborated types) or by a `bpf-core/1`
fixture; `Bpf.Check` enforces them.

The design rules that the type is shaped by:

* values are `uN`/`iN` for `N ∈ {8,16,32,64}`, `Bool`, nullary enums, flat structs,
  `Option` of those, and the opaque `packet`/`ctx`; there is no pointer, closure, array,
  string, `Nat` or heap object;
* a `struct` is a flat C struct (field order, natural alignment), not the erased nested Σ
  of the C backend — this backend lays it out itself, and BTF reports the same layout;
* a `map` is a handle, not a value: it cannot be stored, returned or put in a struct;
* `Bpf.repeat` is the only loop former, and P0 rejects it (loops are P1);
* every term has a `Span`, so a rejection can name Wiz source (§9.4).
-/
namespace Wiz.Compiler.Bpf

/-! ## Program kind and context layout -/

/-- The context a program is compiled against.

`xdp`/`tc` are the packet kinds. `tracepoint` and `uprobe` are the two **tracing** kinds:
their context is a fixed, declared layout (the tracepoint's own format file, or the
platform's `struct pt_regs`), so they need no `vmlinux.h`, no BTF and no CO-RE
(`wiz-notes/ebpf-dynamic.md` §1). A tracing program is a sensor: it reads the syscall's
arguments through the bounded accessors and writes one POD event.
-/
inductive ProgKind where
  | xdp
  | tc
  | tracepoint
  | uprobe
  deriving Repr, BEq, Inhabited

/-- The canonical ELF section name. A `tracepoint`/`uprobe` section is program-specific
(`tracepoint/<category>/<event>`, `uprobe/<binary>:<symbol>`); the emitter uses
`Program.sectionName`, and this is the loader's fallback spelling. -/
def ProgKind.elfSection : ProgKind → String
  | .xdp => "xdp"
  | .tc => "classifier"
  | .tracepoint => "tracepoint"
  | .uprobe => "uprobe"

/-- The loader's attach metadata. For a tracepoint the spec is `category:event` (the
`perf_event_open` name); for a uprobe it is `binary:symbol`. The packet kinds have no
argument. -/
structure Attach where
  /-- `"xdp"`, `"tc"`, `"tracepoint"` or `"uprobe"` -/
  kind : String
  /-- tracepoint: the category (`syscalls`); uprobe: the binary; otherwise `""` -/
  target : String
  /-- tracepoint: the event (`sys_enter_execve`); uprobe: the symbol; otherwise `""` -/
  event : String
  /-- the exact spec: `syscalls:sys_enter_execve`, `binary:symbol`, `xdp`, `classifier` -/
  spec : String
  deriving Repr, BEq, Inhabited

/-- Split a tracepoint section `tracepoint/<category>/<event>`. Exactly two non-empty
parts are required; a typo is a `none`, never a guessed category. -/
def tracepointParts? (sec : String) : Option (String × String) :=
  if sec.startsWith "tracepoint/" then
    match (sec.drop "tracepoint/".length).toString.splitOn "/" with
    | [category, event] =>
      if category.isEmpty || event.isEmpty then none else some (category, event)
    | _ => none
  else none

/-- Split a uprobe section `uprobe/<binary>:<symbol>`. The binary may be an absolute
path (`uprobe//bin/sh:readline` leaves `/bin/sh`), and the symbol is the last non-empty
part. A binary path containing `:` is not supported (the loader's section grammar is
ambiguous there); use a symlink without a colon. -/
def uprobeParts? (sec : String) : Option (String × String) :=
  if sec.startsWith "uprobe/" then
    match (sec.drop "uprobe/".length).toString.splitOn ":" with
    | [binary, symbol] =>
      if binary.isEmpty || symbol.isEmpty then none else some (binary, symbol)
    | _ => none
  else none

/-- The attach metadata for a kind and a section spelling, if the spelling has the shape
that kind needs. -/
def ProgKind.attach? (k : ProgKind) (sec : String) : Option Attach :=
  match k with
  | .xdp =>
    if sec == "xdp" then some { kind := "xdp", target := "", event := "", spec := "xdp" }
    else none
  | .tc =>
    if sec == "tc" || sec == "classifier" || sec == "sched_cls" then
      some { kind := "tc", target := "", event := "", spec := "classifier" }
    else none
  | .tracepoint =>
    (tracepointParts? sec).map fun (category, event) =>
      { kind := "tracepoint", target := category, event, spec := s!"{category}:{event}" }
  | .uprobe =>
    (uprobeParts? sec).map fun (binary, symbol) =>
      { kind := "uprobe", target := binary, event := symbol, spec := s!"{binary}:{symbol}" }

/-- Accept the section spellings of §5.2 (and libbpf's `sched_cls` alias), plus the two
declared tracing shapes. -/
def ProgKind.ofSection? (sec : String) : Option ProgKind :=
  match sec with
  | "xdp" => some .xdp
  | "tc" | "classifier" | "sched_cls" => some .tc
  | _ =>
    if (tracepointParts? sec).isSome then some .tracepoint
    else if (uprobeParts? sec).isSome then some .uprobe
    else none

/-- `true` for the two tracing kinds (the sensor half). -/
def ProgKind.isTracing : ProgKind → Bool
  | .tracepoint | .uprobe => true
  | .xdp | .tc => false

/-- The eBPF program type libbpf derives from the section. -/
def ProgKind.typeName : ProgKind → String
  | .xdp => "xdp"
  | .tc => "sched_cls"
  | .tracepoint => "tracepoint"
  | .uprobe => "kprobe"

/-- `bpf_attr.prog_type`'s numeric value (`include/uapi/linux/bpf.h`): XDP = 6,
SCHED_CLS = 3, TRACEPOINT = 5, KPROBE = 2. The loader reads this, not a string. -/
def ProgKind.progType : ProgKind → Nat
  | .xdp => 6
  | .tc => 3
  | .tracepoint => 5
  | .uprobe => 2

/-- The `enum bpf_prog_type` spelling, for a descriptor and a diagnostic. -/
def ProgKind.progTypeName : ProgKind → String
  | .xdp => "BPF_PROG_TYPE_XDP"
  | .tc => "BPF_PROG_TYPE_SCHED_CLS"
  | .tracepoint => "BPF_PROG_TYPE_TRACEPOINT"
  | .uprobe => "BPF_PROG_TYPE_KPROBE"

/-- The declared context C struct in `bpf_rt.h`. -/
def ProgKind.contextName : ProgKind → String
  | .xdp => "xdp_md"
  | .tc => "__sk_buff"
  | .tracepoint => "bpf_trace_event"
  | .uprobe => "bpf_pt_regs"

/-- For diagnostics: the Wiz-level name of the context/program kind. -/
def ProgKind.describe : ProgKind → String
  | .xdp => "XDP"
  | .tc => "TC"
  | .tracepoint => "tracepoint"
  | .uprobe => "uprobe"

/-! ## Maps -/

inductive MapKind where
  | hash
  | array
  | percpuArray
  | lruHash
  /-- `BPF_MAP_TYPE_PERF_EVENT_ARRAY`: the tracing event transport (§2.1). It is an
  output ring, not a key/value store: it has no lookup/update/delete in this subset. -/
  | perfEventArray
  deriving Repr, BEq, Inhabited

def MapKind.cName : MapKind → String
  | .hash => "BPF_MAP_TYPE_HASH"
  | .array => "BPF_MAP_TYPE_ARRAY"
  | .percpuArray => "BPF_MAP_TYPE_PERCPU_ARRAY"
  | .lruHash => "BPF_MAP_TYPE_LRU_HASH"
  | .perfEventArray => "BPF_MAP_TYPE_PERF_EVENT_ARRAY"

def MapKind.describe : MapKind → String
  | .hash => "hash"
  | .array => "array"
  | .percpuArray => "percpu_array"
  | .lruHash => "lru_hash"
  | .perfEventArray => "perf_event_array"

/-- The limits of §2.7/§6.1: a key is at most 64 B, a value at most 512 B, and an
`array`'s key is the entry index. -/
def MapKind.arrayLike : MapKind → Bool
  | .array | .percpuArray => true
  | _ => false

/-- `true` for the one map kind that is an output, not a key/value store. -/
def MapKind.isPerfEventArray : MapKind → Bool
  | .perfEventArray => true
  | _ => false

/-! ## Event transport and kinds -/

/-- How a probe's events leave the kernel. `perfEventArray` is the first transport
(§2.1); `tracePrintk` is the debug-only fallback (GPL; a line on the trace pipe, not
JSON). A descriptor records which one the object uses. -/
inductive Transport where
  | perfEventArray
  | tracePrintk
  deriving Repr, BEq, Inhabited

def Transport.describe : Transport → String
  | .perfEventArray => "perf_event_array"
  | .tracePrintk => "trace_printk"

def Transport.parse? : String → Option Transport
  | "perf" | "perf_event_array" => some .perfEventArray
  | "trace_printk" | "printk" => some .tracePrintk
  | _ => none

/-- The event kinds of `scry-probe-event/1` (§2.1/§2.2). The number is the wire value in
`struct scry_probe_event.kind`; the name is what the JSON and the descriptor use. -/
inductive EventKind where
  | execve
  | openat
  | write
  | connect
  | heartbeat
  deriving Repr, BEq, Inhabited

def EventKind.code : EventKind → Nat
  | .execve => 1
  | .openat => 2
  | .write => 3
  | .connect => 4
  | .heartbeat => 5

def EventKind.name : EventKind → String
  | .execve => "execve"
  | .openat => "openat"
  | .write => "write"
  | .connect => "connect"
  | .heartbeat => "heartbeat"

def EventKind.ofName? : String → Option EventKind
  | "execve" => some .execve
  | "openat" => some .openat
  | "write" => some .write
  | "connect" => some .connect
  | "heartbeat" => some .heartbeat
  | _ => none

/-- The number of syscall arguments a tracepoint context exposes (`args[6]`), and the
number of registers a uprobe's `pt_regs` exposes as arguments (rdi, rsi, rdx, rcx, r8,
r9). A projection past this is a compile error, not a zero. -/
def traceArgCount : Nat := 6

/-- The constant bound on the argv-slot walk (`wiz-notes/ebpf-dynamic.md` §2.1: scan
slots 0..3, never a runtime `argc`). A slot past this is a compile error. -/
def argvSlotMax : Nat := 4

/-- The event's payload cap. It is a literal in the descriptor and in the emitted C; a
runtime length never selects the copy size (§2.1). -/
def eventDataCap : Nat := 80

/-- `struct scry_probe_event.comm`'s size (`TASK_COMM_LEN`). -/
def eventCommCap : Nat := 16

/-- `sizeof(struct scry_probe_event)` with natural alignment: 4+4+4+4 + 8 + 4+4 +
80 + 16 = 128. `meta` packs the slot (low 16) and the flags (bit 16 = truncated), so the
event is the note's 128 B. The descriptor pins the offsets and the shifts. -/
def eventSize : Nat := 128

/-- `meta`'s low 16 bits are the capture slot. -/
def eventMetaSlotShift : Nat := 0

/-- `meta`'s bit 16 is `truncated` (the payload hit the literal cap). -/
def eventMetaFlagsShift : Nat := 16

/-! ## Types -/

/-- The subset's types (§4.1). A width is a *literal*: the backend specialises every
`UIntN`/`IntN` operation at its inlined call site, so there is no runtime width. -/
inductive Ty where
  | unit
  | bool
  | u8 | u16 | u32 | u64
  | i8 | i16 | i32 | i64
  /-- a nullary inductive with `n` constructors; the tag is one byte -/
  | enum (n : Nat)
  /-- a Wiz `structure`, as a flat C struct of POD fields -/
  | struct (fields : Array Ty)
  /-- `Option t`: `(tag : u8, payload : t)`; the tag *is* the map-null test -/
  | option (t : Ty)
  /-- opaque: the packet is an offset and a checked load, never a pointer -/
  | packet
  /-- opaque: the only exposed fields are projections the emitter knows -/
  | ctx (kind : ProgKind)
  /-- A captured user string: a fixed literal cap and a length. It is plain bytes, not
  `String`; `len` is the valid prefix and `trunc` says the kernel read hit the cap.
  This is the one value a probe reads out of user memory (§2.1). -/
  | userStr (cap : Nat)
  /-- An opaque user-pointer token: a syscall argument, never dereferenced. The only
  consumer is `TraceCtx.readUserStr`'s capped accessor. -/
  | userPtr
  /-- a handle, not a value; it cannot be stored, passed or returned -/
  | map (k v : Ty) (kind : MapKind)
  deriving Repr, BEq, Inhabited

/-- The bit width of a register type, `none` for everything else. -/
def Ty.width : Ty → Option Nat
  | .u8 | .i8 => some 8
  | .u16 | .i16 => some 16
  | .u32 | .i32 => some 32
  | .u64 | .i64 => some 64
  | _ => none

/-- `true` for `IntN`; `false` for `UIntN` and every non-word type. -/
def Ty.isSigned : Ty → Bool
  | .i8 | .i16 | .i32 | .i64 => true
  | _ => false

/-- The unsigned register type of width `w`, if `w` is one the ISA has. -/
def Ty.unsignedOf? : Nat → Option Ty
  | 8 => some .u8
  | 16 => some .u16
  | 32 => some .u32
  | 64 => some .u64
  | _ => none

/-- The signed register type of width `w`, if the ISA has it. -/
def Ty.signedOf? : Nat → Option Ty
  | 8 => some .i8
  | 16 => some .i16
  | 32 => some .i32
  | 64 => some .i64
  | _ => none

/-- Natural alignment of a C struct field / value. Opaque types are not storable and
have no layout (the caller checks with `Ty.byteSize`). -/
partial def Ty.align : Ty → Nat
  | .u64 | .i64 => 8
  | .u32 | .i32 | .userStr _ => 4
  | .u16 | .i16 => 2
  | .option t => t.align
  | .struct fs => fs.foldl (fun a f => max a f.align) 1
  | _ => 1

/-- Join with `", "` (used in diagnostics and C type spellings). -/
def commaSep (xs : List String) : String := String.intercalate ", " xs

/-- Round `n` up to a multiple of `a` (`a ≥ 1`). -/
def alignUp (n a : Nat) : Nat :=
  if a <= 1 then n else ((n + a - 1) / a) * a

/-- The size of a value in bytes, with the emitter's layout: field order, natural
alignment, and `Option t` as `{ tag : u8; pad; value : t }` (so `Option u8` is 2 bytes,
never read as a 4-byte word). `none` for a type with no value representation. -/
partial def Ty.byteSize : Ty → Option Nat
  | .unit => some 0
  | .bool | .u8 | .i8 | .enum _ => some 1
  | .u16 | .i16 => some 2
  | .u32 | .i32 => some 4
  | .u64 | .i64 => some 8
  | .userStr cap => some (alignUp (8 + cap) 4)
  | .packet | .ctx _ | .userPtr | .map _ _ _ => none
  | .option t => t.byteSize.map fun s => alignUp (t.align + s) t.align
  | .struct fs =>
    let step : Option (Nat × Nat) → Ty → Option (Nat × Nat)
      | some (off, maxA), f =>
        f.byteSize.map fun s =>
          let a := f.align
          (alignUp off a + s, max maxA a)
      | none, _ => none
    (fs.foldl step (some (0, 1))).map fun (off, maxA) => alignUp off maxA

/-- Plain old data: a map key/value, a struct field, or a value the kernel can copy.
Pointers, closures and heap objects are not POD, and neither are the opaque context
types (`ctx` is a pointer the verifier tracks; `packet` is not storable either). -/
partial def Ty.isPod : Ty → Bool
  | .unit | .bool | .u8 | .u16 | .u32 | .u64 | .i8 | .i16 | .i32 | .i64 | .enum _ => true
  | .userStr _ => true
  | .option t => t.isPod
  | .struct fs => fs.toList.all fun f => f.isPod
  | _ => false

/-- Number of constructor tags of an enum, `none` for other types. -/
def Ty.enumArity : Ty → Option Nat
  | .enum n => some n
  | _ => none

/-- The payload of an `Option`, `none` for other types. -/
def Ty.optionInner : Ty → Option Ty
  | .option t => some t
  | _ => none

/-- A short name for diagnostics and for C type spellings. -/
partial def Ty.describe : Ty → String
  | .unit => "Unit"
  | .bool => "Bool"
  | .u8 => "UIntN 8"
  | .u16 => "UIntN 16"
  | .u32 => "UIntN 32"
  | .u64 => "UIntN 64"
  | .i8 => "IntN 8"
  | .i16 => "IntN 16"
  | .i32 => "IntN 32"
  | .i64 => "IntN 64"
  | .enum n => s!"enum {n}"
  | .struct fs => s!"struct \{ {commaSep (fs.toList.map Ty.describe)} }"
  | .option t => s!"Option ({t.describe})"
  | .packet => "Packet"
  | .ctx k => s!"{k.describe}Context"
  | .userStr cap => s!"UserStr {cap}"
  | .userPtr => "UserPtr"
  | .map k v kind => s!"Map ({k.describe}) ({v.describe}) ({kind.describe})"

/-! ## Spans -/

/-- Where a term came from. The P0 fixtures are `.bpfcore` text, so the span is carried
in the file (`(at "flow.wiz" 12 3 …)`); the restriction pass will take it from the
elaborated syntax tree. A line of `0` means "generated, no source position". -/
structure Span where
  file : String := "<generated>"
  line : Nat := 0
  col : Nat := 0
  deriving Repr, BEq, Inhabited

def Span.describe (s : Span) : String :=
  let file := if s.file.isEmpty then "<generated>" else s.file
  if s.line == 0 then file else s!"{file}:{s.line}:{s.col}"

/-! ## Terms -/

/-- Width-preserving arithmetic. `div`/`mod` are **unsigned only** here; the signed forms
are rejected by the restriction pass (SDIV/SMOD are ISA v4 and have the
`INT_MIN / -1` edge). `shl`/`shr`'s right operand is a literal byte count `< width`
(checked by `Bpf.Check`); the ISA masks a shift count by 63/31, which is not Wiz's rule,
so a non-literal amount is not in the subset. -/
inductive BinOp where
  | add | sub | mul | div | mod | land | lor | xor | shl | shr
  deriving Repr, BEq, Inhabited

/-- Unsigned comparisons; signed `lt`/`le` lower to the same operator after the sign-bit
flip (the operand type says which). -/
inductive CmpOp where
  | eq | ne | lt | le
  deriving Repr, BEq, Inhabited

/-- What a helper call may do. `pure` is absent deliberately: a helper is a kernel
effect, and the surface's `BpfM` linearity is what orders it. -/
inductive Effect where
  | readsMap | writesMap | time | random | trace
  deriving Repr, BEq, Inhabited

/-- The helper table entry (§7.2). A helper is a table entry, not a string: the emitter
emits by `id`, and the surface declaration is type-checked against `args`/`res`. -/
structure Helper where
  name : String
  id : Nat
  args : Array Ty
  res : Ty
  eff : Effect
  since : Nat
  /-- The program kinds that may call it. Empty means every kind. This is the
  "unverifiable helper use" gate: a packet-only or tracing-only helper in the wrong
  program kind is a positioned compile error, never a silent `wiz_unknown_prim`. -/
  kinds : Array ProgKind := #[]
  deriving Repr, Inhabited

namespace Helpers

/-- P0's non-map helpers. Map helpers are not here: `Map.lookup` and friends are
operations with map types, and the copy/null-test shape is the emitter's.

The tracing helper is the one a sensor needs to identify the process; the other tracing
helpers (`bpf_probe_read_user` 112, `bpf_probe_read_user_str` 115,
`bpf_perf_event_output` 25, `bpf_get_current_comm` 16, `bpf_trace_printk` 6) are emitted
by the `readUserStr`/`argvSlot`/`probeEmit` nodes rather than
called from the typed surface, because their argument is a fixed stack buffer or a
variadic format. They are still recorded in the probe descriptor. -/
def table : Array Helper := #[
  { name := "Bpf.now", id := 5, args := #[], res := .u64, eff := .time, since := 5 },
  { name := "Bpf.random", id := 7, args := #[], res := .u32, eff := .random, since := 4 },
  { name := "Bpf.pidTgid", id := 14, args := #[], res := .u64, eff := .trace, since := 4,
    kinds := #[.tracepoint, .uprobe] }
]

def find? (n : String) : Option Helper := table.find? fun h => h.name == n

end Helpers

mutual

/-- A typed term. Every constructor that produces a value carries its `Ty`; the
`Bpf.Check` pass verifies that the carried type is the type the construct actually
produces, so a malformed fixture is a diagnostic, not a miscompile. -/
inductive TmNode where
  | var (ty : Ty) (x : Nat)
  | lit (ty : Ty) (v : Nat)
  | bin (ty : Ty) (op : BinOp) (a b : Tm)
  | cmp (op : CmpOp) (a b : Tm)
  | ite (ty : Ty) (c t e : Tm)
  /-- `let x : ty := v; body`; `ty` is the *binder's* type and `x` is a fresh slot
  (`x == ctx.size`), so the core is A-normal and variables are unique — the same
  numeric-variable convention as the IR. -/
  | letE (ty : Ty) (x : Nat) (v : Tm) (body : Tm)
  | proj (ty : Ty) (i : Nat) (s : Tm)
  | mkStruct (ty : Ty) (fields : Array Tm)
  | mkSome (ty : Ty) (v : Tm)
  | mkNone (ty : Ty)
  /-- `match s with | none => none | some x => some` -/
  | switchOption (ty : Ty) (s : Tm) (onNone : Tm) (x : Nat) (onSome : Tm)
  /-- an exhaustive switch on an enum tag -/
  | switchTag (ty : Ty) (s : Tm) (alts : Array Tm)
  /-- `Bpf.repeat`: `step` is the name of a function `S → UIntN 32 → S`. P0 rejects it;
  the node is in the grammar so P1 changes the checker, not the core. -/
  | repeat (ty : Ty) (bound : Nat) (init : Tm) (step : String)
  /-- a checked packet load; `width ∈ {8,16,32,64}`, the offset is `u32` -/
  | pktLoad (ty : Ty) (width : Nat) (be : Bool) (p : Tm) (off : Tm)
  /-- `XdpContext.packet`/`TcContext.packet`: the only way to get a `Packet` -/
  | ctxPacket (c : Tm)
  | ctxIfindex (c : Tm)
  | ctxRxQueue (c : Tm)
  /-- `TraceCtx.pid`: the thread id, `bpf_get_current_pid_tgid() & 0xffffffff` -/
  | ctxPid (c : Tm)
  /-- `TraceCtx.tgid`: the process id, `bpf_get_current_pid_tgid() >> 32` -/
  | ctxTgid (c : Tm)
  /-- `TraceCtx.now`: `bpf_ktime_get_ns()` (monotonic, unordered; sort host-side) -/
  | ctxNow (c : Tm)
  /-- `TraceCtx.arg c i`: the i-th syscall argument as an opaque user-pointer token. -/
  | ctxArg (i : Nat) (c : Tm)
  /-- `TraceCtx.argWord c i`: the same argument as a scalar (a fd, a flags word). -/
  | ctxArgWord (i : Nat) (c : Tm)
  /-- `TraceCtx.readUserStr c ptr`: one `bpf_probe_read_user_str` with the literal cap
  from the result type; `none` is `-EFAULT`, never a partial success. -/
  | readUserStr (ty : Ty) (c : Tm) (ptr : Tm)
  /-- `TraceCtx.argvSlot c argv slot`: read the pointer at `argv + 8*slot` with
  `bpf_probe_read_user`, reject a null slot, then read its string with the capped
  accessor. `slot` is a literal below `argvSlotMax`; the walk never reads `argc`. -/
  | argvSlot (ty : Ty) (c : Tm) (argv : Tm) (slot : Nat)
  /-- `Probe.emit events kind slot c pid tgid ppid ts data`: fill one POD
  `scry_probe_event` on the stack and send it to the perf event array (or the
  `trace_printk` fallback). The result is `Bool`: `false` means the output helper failed;
  the policy may count it in a `lost` map, and it must never retry unbounded. -/
  | probeEmit (ty : Ty) (events : String) (kind : EventKind) (slot : Nat)
      (c pid tgid ppid ts data : Tm)
  | mapLookup (ty : Ty) (m : String) (k : Tm)
  | mapUpdate (ty : Ty) (m : String) (k v : Tm)
  | mapDelete (ty : Ty) (m : String) (k : Tm)
  | mapAdd (ty : Ty) (m : String) (k n : Tm)
  /-- zero-extend/truncate between accepted widths (`UIntN.resize`) -/
  | cast (ty : Ty) (src : Ty) (v : Tm)
  | call (ty : Ty) (f : String) (args : Array Tm)
  | helper (ty : Ty) (h : Helper) (args : Array Tm)
  | ret (t : Tm)

/-- A term and its source position. -/
inductive Tm where
  | mk (span : Span) (node : TmNode)

end

/-- The source position of a term. (`Tm` is an `inductive`, not a `structure`, so the
projections are explicit; the dot notation `t.span` still works.) -/
def Tm.span (t : Tm) : Span := match t with | .mk s _ => s

/-- The node of a term (the constructor payload). -/
def Tm.node (t : Tm) : TmNode := match t with | .mk _ n => n

instance : Inhabited Tm := ⟨.mk {} (.lit .unit 0)⟩

/-- The type a term produces. `cmp` is `Bool`; `ret` is `Unit`. -/
partial def Tm.ty (t : Tm) : Ty :=
  match t.node with
  | .var ty _ => ty
  | .lit ty _ => ty
  | .bin ty _ _ _ => ty
  | .cmp _ _ _ => .bool
  | .ite ty _ _ _ => ty
  | .letE _ _ _ body => body.ty
  | .proj ty _ _ => ty
  | .mkStruct ty _ => ty
  | .mkSome ty _ => ty
  | .mkNone ty => ty
  | .switchOption ty _ _ _ _ => ty
  | .switchTag ty _ _ => ty
  | .repeat ty _ _ _ => ty
  | .pktLoad ty _ _ _ _ => ty
  | .ctxPacket _ => .packet
  | .ctxIfindex _ => .u32
  | .ctxRxQueue _ => .u32
  | .ctxPid _ | .ctxTgid _ => .u32
  | .ctxNow _ => .u64
  | .ctxArg _ _ => .userPtr
  | .ctxArgWord _ _ => .u64
  | .readUserStr ty _ _ => ty
  | .argvSlot ty _ _ _ => ty
  | .probeEmit ty _ _ _ _ _ _ _ _ _ => ty
  | .mapLookup ty _ _ => ty
  | .mapUpdate ty _ _ _ => ty
  | .mapDelete ty _ _ => ty
  | .mapAdd ty _ _ _ => ty
  | .cast ty _ _ => ty
  | .call ty _ _ => ty
  | .helper ty _ _ => ty
  | .ret _ => .unit

/-- Direct subterms, in evaluation order. -/
def TmNode.children : TmNode → Array Tm
  | .var _ _ | .lit _ _ => #[]
  | .bin _ _ a b => #[a, b]
  | .cmp _ a b => #[a, b]
  | .ite _ c t e => #[c, t, e]
  | .letE _ _ v body => #[v, body]
  | .proj _ _ s => #[s]
  | .mkStruct _ fs => fs
  | .mkSome _ v => #[v]
  | .mkNone _ => #[]
  | .switchOption _ s onNone _ onSome => #[s, onNone, onSome]
  | .switchTag _ s alts => #[s] ++ alts
  | .repeat _ _ init _ => #[init]
  | .pktLoad _ _ _ p off => #[p, off]
  | .ctxPacket c | .ctxIfindex c | .ctxRxQueue c => #[c]
  | .ctxPid c | .ctxTgid c | .ctxNow c => #[c]
  | .ctxArg _ c | .ctxArgWord _ c => #[c]
  | .readUserStr _ c ptr => #[c, ptr]
  | .argvSlot _ c argv _ => #[c, argv]
  | .probeEmit _ _ _ _ c pid tgid ppid ts data => #[c, pid, tgid, ppid, ts, data]
  | .mapLookup _ _ k => #[k]
  | .mapUpdate _ _ k v => #[k, v]
  | .mapDelete _ _ k => #[k]
  | .mapAdd _ _ k n => #[k, n]
  | .cast _ _ v => #[v]
  | .call _ _ args => args
  | .helper _ _ args => args
  | .ret t => #[t]

/-- A structural size, used only for the P0 static-budget *estimate* (the real number is
`clang`'s object; §2.5). -/
partial def Tm.size (t : Tm) : Nat :=
  1 + (t.node.children.foldl (fun n c => n + c.size) 0)

/-- Every direct callee named in a term. -/
partial def Tm.calls (t : Tm) : Array String :=
  let here : Array String := match t.node with
    | .call _ f _ => #[f]
    | _ => #[]
  t.node.children.foldl (fun acc c => acc ++ c.calls) here

/-- Wrap a node with a source position. -/
def Tm.withSpan (s : Span) (n : TmNode) : Tm := .mk s n

/-- The nearest explicit source position, if any (fixtures often omit them). -/
def Tm.spanOf (t : Tm) : Option Span :=
  if t.span.line != 0 || t.span.file != "<generated>" then some t.span else none

/-! ## Declarations and a program -/

/-- A top-level definition. Calls are inlined (`static __always_inline`); `params` are
slots `0 … params.size-1`, and `body` continues the same slot numbering in its `let`s. -/
structure Decl where
  name : String
  params : Array Ty
  ret : Ty
  body : Tm

/-- A map, declared statically (§5.1, §6). The key and value are POD; the size is fixed
at load time. -/
structure MapDecl where
  name : String
  kind : MapKind
  key : Ty
  value : Ty
  maxEntries : Nat
  deriving Repr, Inhabited

/-- A whole program: one entry, the maps it names, and the definitions to inline. The
type at the kernel boundary is `ret` (an action enum: `XdpAction` or `TcAction`). -/
structure Program where
  /-- the Wiz definition and the C function name -/
  entry : String
  /-- `"xdp"` / `"classifier"` -/
  sectionName : String
  kind : ProgKind
  license : String
  /-- a `UIntN 32` literal (`bpf_attr.prog_version`) -/
  version : Nat
  maps : Array MapDecl
  decls : Array Decl
  /-- the program's result type: an action enum for XDP/TC, `Unit` or `UIntN 32` for a
  tracing program -/
  ret : Ty
  /-- how a tracing program's events leave the kernel; ignored by XDP/TC -/
  transport : Transport := .perfEventArray
  /-- the manifest/source position, for a positioned whole-program diagnostic -/
  span : Span := {}

def Program.decl? (p : Program) (n : String) : Option Decl :=
  p.decls.find? fun d => d.name == n

def Program.map? (p : Program) (n : String) : Option MapDecl :=
  p.maps.find? fun m => m.name == n

/-- The entry declaration, if the name resolves. -/
def Program.entryDecl? (p : Program) : Option Decl := p.decl? p.entry

/-- The loader's attach metadata, or `none` when the section does not have the shape the
program kind needs. -/
def Program.attach? (p : Program) : Option Attach := p.kind.attach? p.sectionName

/-! ## The action enums (§5.2) -/

/-- XDP: `aborted = 0, drop = 1, pass = 2, tx = 3, redirect = 4`; P0-P2 allows the first
three. TC: `ok = 0, shot = 2, redirect = 7`. The core only sees the arity (the tag is a
number); the loader sees the values through `XdpAction`/`TcAction` in `bpf_rt.h`. -/
def xdpActionArity : Nat := 5
def tcActionArity : Nat := 8

end Wiz.Compiler.Bpf
