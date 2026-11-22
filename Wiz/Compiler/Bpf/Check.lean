/-
# `Bpf.Check`: the subset's gate

The eBPF target's contract is that a program outside the subset is rejected **here**, in
Wiz terms, before `clang` or the kernel sees it (eBPF design note §2, §4.4). The kernel
verifier is a backstop, not the compiler's error message.

`checkProgram` is pure and cheap on purpose (it runs in `wiz check`): no `clang`, no
privileges, no file system. The checks are:

* every type is representable (widths, flat structs, POD maps, no heap);
* every term is well typed and A-normal (the carried `Ty` is the type the construct
  produces);
* the program's result is an action enum, not a `Nat`/`Bool`/struct;
* the call graph is acyclic (calls are inlined; a cycle cannot be removed by inlining);
* `Bpf.repeat` is rejected in P0 (loops are P1);
* map keys/values are POD and within the kernel's sizes;
* a static instruction budget and a per-function frame estimate (both are *estimates*;
  §2.2/§2.5 says the object and the verifier log are the authority).

The messages keep the stable prefix `bpf:` (§4.4). A source position, when the fixture
carries one, follows the message as `(at file:line:col)`.
-/
import Wiz.Compiler.Bpf.Core

namespace Wiz.Compiler.Bpf

/-! ## Diagnostics -/

/-- A rejection at a source position. The literal prefix is `bpf:` — the negative corpus
asserts it (§8.6). -/
def reject {α : Type} (span : Span) (msg : String) : Except String α :=
  .error s!"bpf: {msg} (at {span.describe})"

/-- A rejection about the program as a whole (no single term). -/
def rejectTop {α : Type} (msg : String) : Except String α :=
  .error s!"bpf: {msg}"

/-- A whole-program rejection with a position when the manifest/core carries one. A
generated program has no position, and the message stays `bpf: …`; a manifest's
`[program.NAME]` line becomes `bpf: … (at bpf.toml:3:1)`, so a typo in `type` or
`section` is a positioned compile error, not a fall-through. -/
def rejectAt {α : Type} (span : Span) (msg : String) : Except String α :=
  if span.line == 0 && span.file == "<generated>" then rejectTop msg else reject span msg

def typeMismatch {α : Type} (span : Span) (what : String) (expected actual : Ty) :
    Except String α :=
  reject span s!"{what}: expected {expected.describe}, got {actual.describe}"

/-! ## The stable messages of §4.4 -/

def natMessage : String :=
  "`Nat` is not representable: it is unbounded (a GMP object above 2^62) and the kernel \
has 64-bit registers and no allocator. Use `UIntN 64`, or a width that fits the field. A \
`Nat` is accepted only where it folds to a literal at compile time."

def listMessage : String :=
  "`List` is a recursive heap object; the kernel has no allocator, and structural \
recursion has no bounded form. Rewrite the loop as `Bpf.repeat (bound := N)` over \
`UIntN 32`, or keep the data in a fixed-size struct or a map."

def stringMessage : String :=
  "`String` is a heap object; a packet is a `Packet` (an offset and a checked load), not \
a `String`."

def bytesMessage : String :=
  "`Bytes` is a heap object and a pointer into it has no eBPF type. Read the packet with \
`Packet.load8/16/32/64`, which checks bounds."

def arrayMessage : String :=
  "`Array` allocates; the kernel has no allocator. Declare a `bpf_map` and update it, or \
use a fixed-size struct."

def refMessage : String :=
  "`Ref` is mutable heap state (a cell); the kernel has no heap. A map is the only \
mutable store."

def floatMessage : String :=
  "`Float64` — the eBPF ISA has no floating-point instructions."

def closureMessage : String :=
  "a closure has no eBPF representation (the ISA has no indirect call). Pass a named \
function or a capture-free lambda to `Bpf.repeat`, which is inlined."

def ioMessage : String :=
  "`IO` — a kernel program has no world. Use `BpfM`, whose world is erased and whose \
effects are kernel helpers."

def partialMessage (f : String) : String :=
  s!"`partial` definition `{f}` has a witness, not a termination measure; the verifier \
has no bound to check. A kernel program may not call it."

def uint128Message : String :=
  "`UIntN 128` — a word wider than 64 bits is not a register. Split it into two \
`UIntN 64` fields (and implement the carry yourself)."

def widthMessage (w : Nat) : String :=
  s!"`UIntN {w}` is not a register width. The eBPF ISA has 8, 16, 32 and 64-bit \
registers; use one of those (or two 64-bit halves)."

def bitvecMessage (n : Nat) : String :=
  s!"`BitVec {n}` is outside the subset: only 8, 16, 32 and 64 are register widths. A \
{n}-bit value is not a machine register, and a lowering that keeps it in one would need \
a mask after every operation. Use `UIntN {n}` only if {n} is one of those widths."

def signedDivMessage : String :=
  "signed division is not in the subset: `IntN.div`/`IntN.mod` need SDIV/SMOD (ISA v4) \
and have an `INT_MIN / -1` special case. Use `UIntN` arithmetic, or split the sign off \
explicitly."

def shiftMessage (w : Nat) (k : Nat) : String :=
  s!"the shift amount must be a literal below the width (got {k} for a {w}-bit word). \
The eBPF ISA masks the shift count by 63/31, which is not Wiz's rule (`k >= w` is 0); a \
bare `<<` would silently disagree at the boundary. Write a literal `k < {w}`."

def loopMessage : String :=
  "`Bpf.repeat` is not in the P0 subset (bounded loops are P1). Emit a straight-line \
program; P1 lifts this check."

def literalMessage (ty : Ty) (v : Nat) : String :=
  s!"the literal {v} does not fit {ty.describe}; write a value below 2^{ty.width.getD 0} \
(the backend does not silently wrap, unlike `UIntN.ofNat`)."

def mapPodMessage (what : String) (ty : Ty) : String :=
  s!"the map {what} type `{ty.describe}` contains a pointer, a closure or a heap object. \
A map key/value is plain old data: no pointers, no RC. Use scalars, structs of scalars, \
enums and `Option` of those."

def actionMessage (ty : Ty) : String :=
  s!"the program's result must be an action enum (`XdpAction` or `TcAction`), not \
`{ty.describe}`. A `Nat`, `Bool` or struct return has no defined kernel meaning."

def traceResultMessage (ty : Ty) : String :=
  s!"a tracing program's result must be `Unit` or `UIntN 32` (the tracepoint return \
code), not `{ty.describe}`. There is no packet action to return."

def traceCtxMessage (what : String) (ty : Ty) : String :=
  s!"`{what}` needs a tracepoint or uprobe context, not `{ty.describe}`. A tracing \
program has no packet; read the syscall arguments with `TraceCtx.arg` and the capped \
`TraceCtx.readUserStr`."

def packetCtxMessage (what : String) (ty : Ty) : String :=
  s!"`{what}` needs an XDP or TC context, not `{ty.describe}`. A tracepoint/uprobe \
context has no `data`/`data_end`, so there is no checked packet load on this path."

def packetTraceMessage : String :=
  "a `Packet` has no representation in a tracepoint/uprobe program: the tracing context \
has no `data`/`data_end`. Use `TraceCtx.readUserStr` or `TraceCtx.argvSlot`."

def traceArgMessage (i : Nat) : String :=
  s!"the syscall argument index {i} is outside 0..{traceArgCount - 1}. A tracepoint \
context has six arguments (`args[6]`); a uprobe's `pt_regs` ABI exposes six in the \
declared layout. A probe never walks a runtime argument count."

def userStrMessage (cap : Nat) : String :=
  s!"the captured string cap {cap} is outside 1..256. The cap is a literal in the \
descriptor and in the emitted C; a runtime length never selects the copy size."

def argvSlotMessage (slot : Nat) : String :=
  s!"the argv slot {slot} is outside 0..{argvSlotMax - 1}. A probe scans a constant set \
of argv slots, never a runtime `argc`; `bpf_probe_read_user` reads one pointer at \
`argv + 8*slot`, and a null/failed slot is `none`, not an unbounded walk."

def perfMapMessage (m : String) : String :=
  s!"`{m}` is a `perf_event_array`, an output ring, not a key/value map: it has no \
lookup/update/delete in this subset. Write to it with `Probe.emit`."

def mapIndexMessage (m : String) (kind : MapKind) (i : Nat) (n : Nat) : String :=
  s!"the `{kind.describe}` map `{m}` has {n} entries; the literal index {i} is out of \
bounds. The kernel would return NULL at run time; this is a compile-time error, not a \
runtime check."

def helperKindMessage (h : String) (k : ProgKind) : String :=
  s!"the helper `{h}` is not available in a {k.describe} program. It is a tracing \
helper; a packet program has no syscall context. The helper table's `kinds` is the \
gate, not the kernel's `ENOTSUPP`."

def traceLicenseMessage (lic : String) : String :=
  s!"a tracing probe needs `license = \"GPL\"` (got `{lic}`): \
`bpf_probe_read_user_str` and `bpf_trace_printk` are GPL-only. A non-GPL object would \
load-fail with `EINVAL`/`ENOTSUPP` on the helper."

def frameMessage (f : String) (n : Nat) : String :=
  s!"the frame budget is 256 bytes but `{f}` needs about {n} (locals plus estimated \
spills). Shrink the struct or split the program."

def budgetMessage (n : Nat) : String :=
  s!"the program emits about {n} instructions (budget 100000). Reduce an unrolled loop \
bound or the number of inlined helpers."

def cycleMessage (f : String) : String :=
  s!"the call graph is cyclic (`{f}` reaches itself). The kernel rejects recursion, and \
`always_inline` cannot remove a cycle. Rewrite the recursion as `Bpf.repeat` (P1) or a \
map."

/-! ## Types -/

/-- Verify that a type is representable: widths are the ISA's, structs are flat and at
most 64 bytes, and `Option` payloads are POD. (Whether a type may be *stored* is
`Ty.isPod`, checked at the map and struct boundaries.) -/
partial def checkTy (t : Ty) : Except String Unit := do
  match t with
  | .struct fs =>
    for f in fs.toList do
      checkTy f
    if fs.toList.any (fun f => f == .unit) then
      rejectTop s!"the struct `{t.describe}` has a `Unit` field, which has no C \
representation (P0 does not erase a field in the middle of a struct)"
    match t.byteSize with
    | none => rejectTop s!"the struct `{t.describe}` has no C layout"
    | some n => do
      if n > 64 then
        rejectTop s!"a value is at most 64 bytes, but `{t.describe}` is {n}. Split the \
struct or keep the large data in a map."
      unless t.isPod do
        rejectTop s!"the struct `{t.describe}` is not plain old data"
  | .option inner =>
    checkTy inner
    if inner == .unit then
      rejectTop "an `Option Unit` has no payload representation (P0); use a `Bool` or an enum"
    match t.byteSize with
    | none => rejectTop s!"`{t.describe}` has no C layout"
    | some n => do
      -- A captured string is the one value allowed past the 64-byte struct limit: its cap
      -- is a literal chosen by the probe policy, and the frame budget below still applies.
      let limit := match inner with | .userStr _ => 256 | _ => 64
      if n > limit then
        rejectTop s!"`{t.describe}` is {n} bytes; a value is at most {limit}"
      unless inner.isPod do
        rejectTop s!"`{t.describe}` wraps a non-POD payload; an `Option` is a value, not a \
pointer"
  | .userStr cap =>
    if cap == 0 || cap > 256 then rejectTop (userStrMessage cap)
  | .userPtr => pure ()
  | .map k v _ =>
    checkTy k
    checkTy v
  | .packet | .ctx _ => pure ()
  | .unit => pure ()
  | _ => pure ()

/-! ## Literals -/

/-- A literal has to fit its type. This is stricter than `UIntN.ofNat`, which silently
wraps (`lib/Word.wiz:250`); §4.2 requires the rejection. -/
def checkLit (ty : Ty) (v : Nat) (span : Span) : Except String Unit :=
  let fits (w : Nat) := v < Nat.pow 2 w
  match ty with
  | .u8 | .i8 => if fits 8 then pure () else reject span (literalMessage ty v)
  | .u16 | .i16 => if fits 16 then pure () else reject span (literalMessage ty v)
  | .u32 | .i32 => if fits 32 then pure () else reject span (literalMessage ty v)
  | .u64 | .i64 => if fits 64 then pure () else reject span (literalMessage ty v)
  | .bool => if v <= 1 then pure () else reject span s!"a `Bool` literal is 0 or 1, not {v}"
  | .enum n =>
    if v < n then pure () else reject span s!"the tag {v} is outside the enum's {n} constructors"
  | .unit => if v == 0 then pure () else reject span s!"a `Unit` has no literal {v}"
  | _ => reject span s!"a literal of type `{ty.describe}` is not representable"

/-! ## Terms -/

/-- The canonical types for map operations. Map handles are not values; a `Tm` can only
name one, and `checkTm` resolves the name and checks the key/value types. -/
def lookupMap (p : Program) (span : Span) (m : String) : Except String MapDecl :=
  match p.map? m with
  | some d => pure d
  | none => reject span s!"the map `{m}` is not declared in the manifest"

def checkVar (ctx : Array Ty) (span : Span) (ty : Ty) (x : Nat) : Except String Unit :=
  match ctx[x]? with
  | none => reject span s!"variable x{x} is not in scope (the context has {ctx.size} slots)"
  | some actual =>
    if actual == ty then pure () else typeMismatch span s!"variable x{x}" ty actual

/-- A word type's width, or a rejection. -/
def wordWidth (span : Span) (ty : Ty) : Except String Nat :=
  match ty.width with
  | some w => pure w
  | none => reject span s!"this operation needs a word (`UIntN`/`IntN`), not `{ty.describe}`"

/-- The context a tracing projection needs. A packet context is rejected here, not left to
the emitter: the C would not compile, and the diagnostic must name the Wiz term. -/
def checkTraceCtx (span : Span) (what : String) (c : Tm) : Except String Unit :=
  match c.ty with
  | .ctx k =>
    if k.isTracing then pure ()
    else reject span (traceCtxMessage what c.ty)
  | _ => reject span (traceCtxMessage what c.ty)

/-- The context a packet projection needs. -/
def checkPacketCtx (span : Span) (what : String) (c : Tm) : Except String Unit :=
  match c.ty with
  | .ctx .xdp | .ctx .tc => pure ()
  | other => reject span (packetCtxMessage what other)

/-- A `perf_event_array` is an output ring; it has no key/value operations. -/
def checkNotPerfMap (span : Span) (d : MapDecl) : Except String Unit :=
  if d.kind.isPerfEventArray then reject span (perfMapMessage d.name) else pure ()

/-- A literal index into an `array`/`percpu_array` must be inside `max_entries`. This is
the check the kernel's `map_value_or_null` would otherwise turn into a run-time NULL (or,
worse, a silently dead branch); it is deliberately a compile error. A non-literal key is
runtime data and is not bounded here (the map lookup's null test is the policy's job). -/
def checkMapIndex (span : Span) (d : MapDecl) (k : Tm) : Except String Unit :=
  if d.kind.arrayLike then
    match k.node with
    | .lit .u32 i =>
      if i >= d.maxEntries then reject span (mapIndexMessage d.name d.kind i d.maxEntries)
      else pure ()
    | _ => pure ()
  else pure ()

/-- Check one term against the type it must have. -/
partial def checkTm (p : Program) (ctx : Array Ty) (expected : Ty) (t : Tm) :
    Except String Unit := do
  if t.ty != expected then typeMismatch t.span "type mismatch" expected t.ty
  match t.node with
  | .var ty x => checkVar ctx t.span ty x
  | .lit ty v => checkLit ty v t.span
  | .bin ty op a b =>
    let _ ← wordWidth t.span ty
    checkTm p ctx ty a
    checkTm p ctx ty b
    let w ← wordWidth t.span ty
    match op with
    | .shl | .shr =>
      match b.node with
      | .lit _ k =>
        if k >= w then reject t.span (shiftMessage w k) else pure ()
      | _ => reject t.span (shiftMessage w 0)
    | .div | .mod =>
      if ty.isSigned then reject t.span signedDivMessage else pure ()
    | _ => pure ()
  | .cmp op a b =>
    if a.ty != b.ty then typeMismatch t.span "a comparison's operands" a.ty b.ty
    match op with
    | .eq | .ne =>
      match a.ty with
      | .u8 | .u16 | .u32 | .u64 | .i8 | .i16 | .i32 | .i64 | .bool | .enum _ => pure ()
      | _ => reject t.span s!"`==`/`!=` are not defined for `{a.ty.describe}`"
    | .lt | .le =>
      match a.ty.width with
      | some _ => pure ()
      | none => reject t.span s!"`<`/`<=` need a word, not `{a.ty.describe}`"
    checkTm p ctx a.ty a
    checkTm p ctx a.ty b
  | .ite _ c a b =>
    checkTm p ctx .bool c
    checkTm p ctx expected a
    checkTm p ctx expected b
  | .letE ty x v body =>
    if ty == .unit then
      reject t.span "a `Unit` binding has no C representation"
    unless x == ctx.size do
      reject t.span s!"the binder x{x} is not the next slot (the context has {ctx.size}); \
`BpfCore` is A-normal and variables are unique"
    checkTm p ctx ty v
    checkTm p (ctx.push ty) expected body
  | .proj ty i s =>
    match s.ty with
    | .struct fs =>
      match fs[i]? with
      | none => reject t.span s!"field {i} of `{s.ty.describe}` (it has {fs.size})"
      | some ft =>
        if ft != ty then typeMismatch t.span s!"field {i}" ty ft
    | other => reject t.span s!"`.{i}` needs a struct, not `{other.describe}`"
    checkTm p ctx s.ty s
  | .mkStruct ty fs =>
    match ty with
    | .struct fields =>
      if fields.size != fs.size then
        reject t.span s!"`{ty.describe}` has {fields.size} fields, not {fs.size}"
      for i in [0:fields.size] do
        checkTm p ctx fields[i]! fs[i]!
    | _ => reject t.span s!"a struct value has a non-struct type `{ty.describe}`"
  | .mkSome ty v =>
    match ty.optionInner with
    | some inner => checkTm p ctx inner v
    | none => reject t.span s!"`some` needs an `Option`, not `{ty.describe}`"
  | .mkNone ty =>
    match ty.optionInner with
    | some _ => pure ()
    | none => reject t.span s!"`none` needs an `Option`, not `{ty.describe}`"
  | .switchOption ty s onNone x onSome =>
    match s.ty.optionInner with
    | none => reject t.span s!"`match` on an `Option` needs an `Option`, not `{s.ty.describe}`"
    | some inner =>
      checkTm p ctx s.ty s
      checkTm p ctx expected onNone
      unless x == ctx.size do
        reject t.span s!"the `some` binder x{x} is not the next slot"
      checkTm p (ctx.push inner) expected onSome
      checkTy ty
  | .switchTag ty s alts =>
    match s.ty.enumArity with
    | none => reject t.span s!"a tag switch needs a nullary enum, not `{s.ty.describe}`"
    | some n =>
      if alts.size != n then
        reject t.span s!"the switch is not exhaustive: {alts.size} arms for {n} constructors"
      checkTm p ctx s.ty s
      for a in alts.toList do checkTm p ctx expected a
      checkTy ty
  | .repeat _ bound _ _ =>
    if bound == 0 then reject t.span "`Bpf.repeat`'s bound must be positive"
    else reject t.span loopMessage
  | .pktLoad ty width be pkt off =>
    if p.kind.isTracing then reject t.span packetTraceMessage
    match Ty.unsignedOf? width with
    | none => reject t.span s!"a packet load is 8, 16, 32 or 64 bits, not {width}"
    | some word =>
      if ty != .option word then
        typeMismatch t.span "a packet load's result" (.option word) ty
      checkTm p ctx .packet pkt
      checkTm p ctx .u32 off
      let _ := be
      pure ()
  | .ctxPacket c =>
    if p.kind.isTracing then reject t.span packetTraceMessage
    checkPacketCtx t.span "XdpContext.packet" c
    checkTm p ctx c.ty c
  | .ctxIfindex c | .ctxRxQueue c =>
    if p.kind.isTracing then reject t.span packetTraceMessage
    checkPacketCtx t.span "a context projection" c
    checkTm p ctx c.ty c
  | .ctxPid c | .ctxTgid c =>
    checkTraceCtx t.span "TraceCtx.pid/tgid" c
    checkTm p ctx c.ty c
  | .ctxNow c =>
    checkTraceCtx t.span "TraceCtx.now" c
    checkTm p ctx c.ty c
  | .ctxArg i c | .ctxArgWord i c =>
    if i >= traceArgCount then reject t.span (traceArgMessage i)
    checkTraceCtx t.span "TraceCtx.arg" c
    checkTm p ctx c.ty c
  | .readUserStr ty c ptr =>
    match ty.optionInner with
    | some (.userStr cap) =>
      unless (1 <= cap && cap <= 256) do reject t.span (userStrMessage cap)
    | _ =>
      reject t.span s!"`TraceCtx.readUserStr` produces `Option (UserStr N)`, not \
`{ty.describe}`"
    checkTraceCtx t.span "TraceCtx.readUserStr" c
    checkTm p ctx c.ty c
    if ptr.ty != .userPtr then
      typeMismatch t.span s!"`TraceCtx.readUserStr`'s pointer" .userPtr ptr.ty
    checkTm p ctx .userPtr ptr
  | .argvSlot ty c argv slot =>
    match ty.optionInner with
    | some (.userStr cap) =>
      unless (1 <= cap && cap <= 256) do reject t.span (userStrMessage cap)
    | _ =>
      reject t.span s!"`TraceCtx.argvSlot` produces `Option (UserStr N)`, not `{ty.describe}`"
    if slot >= argvSlotMax then reject t.span (argvSlotMessage slot)
    checkTraceCtx t.span "TraceCtx.argvSlot" c
    checkTm p ctx c.ty c
    if argv.ty != .userPtr then
      typeMismatch t.span s!"`TraceCtx.argvSlot`'s argv" .userPtr argv.ty
    checkTm p ctx .userPtr argv
  | .probeEmit ty events kind slot c pid tgid ppid ts data =>
    if ty != .bool then typeMismatch t.span "`Probe.emit`" .bool ty
    if slot >= 8 then
      reject t.span s!"the capture slot {slot} is outside 0..7; a probe emits a bounded \
set of slots, not a runtime index"
    checkTraceCtx t.span "Probe.emit" c
    checkTm p ctx c.ty c
    for (what, tm, want) in [("pid", pid, Ty.u32), ("tgid", tgid, Ty.u32),
                             ("ppid", ppid, Ty.u32), ("ts", ts, Ty.u64)] do
      if tm.ty != want then typeMismatch t.span s!"`Probe.emit`'s {what}" want tm.ty
      checkTm p ctx want tm
    match data.ty with
    | .userStr cap =>
      if cap == 0 || cap > 256 then reject t.span (userStrMessage cap)
    | other => reject t.span s!"`Probe.emit`'s payload is a captured `UserStr`, not \
`{other.describe}`. Read it with `TraceCtx.readUserStr`; never pass a pointer."
    checkTm p ctx data.ty data
    match p.transport with
    | .perfEventArray =>
      let d ← lookupMap p t.span events
      unless d.kind.isPerfEventArray do
        reject t.span s!"`Probe.emit` writes a `perf_event_array`, but `{events}` is a \
`{d.kind.describe}` map. Declare `[map.{events}]` with `kind = \"perf_event_array\"`."
    | .tracePrintk => pure ()
  | .mapLookup ty m k =>
    let d ← lookupMap p t.span m
    checkNotPerfMap t.span d
    checkMapIndex t.span d k
    if ty != .option d.value then
      typeMismatch t.span s!"`Map.lookup {m}`" (.option d.value) ty
    checkTm p ctx d.key k
  | .mapUpdate ty m k v =>
    let d ← lookupMap p t.span m
    checkNotPerfMap t.span d
    checkMapIndex t.span d k
    if ty != .bool then typeMismatch t.span s!"`Map.update {m}`" .bool ty
    checkTm p ctx d.key k
    checkTm p ctx d.value v
  | .mapDelete ty m k =>
    let d ← lookupMap p t.span m
    checkNotPerfMap t.span d
    checkMapIndex t.span d k
    if ty != .bool then typeMismatch t.span s!"`Map.delete {m}`" .bool ty
    checkTm p ctx d.key k
  | .mapAdd ty m k n =>
    let d ← lookupMap p t.span m
    checkNotPerfMap t.span d
    checkMapIndex t.span d k
    if ty != .u64 then typeMismatch t.span s!"`Map.add {m}`" .u64 ty
    if d.value != .u64 then
      reject t.span s!"`Map.add {m}` needs a `UIntN 64` value, but `{m}` stores \
`{d.value.describe}`"
    checkTm p ctx d.key k
    checkTm p ctx .u64 n
  | .cast ty src v =>
    let _ ← wordWidth t.span ty
    let _ ← wordWidth t.span src
    checkTm p ctx src v
  | .call ty f args =>
    match p.decl? f with
    | none => reject t.span s!"the call to `{f}` has no definition in this program"
    | some d =>
      if ty != d.ret then typeMismatch t.span s!"`{f}`'s result" d.ret ty
      if args.size != d.params.size then
        reject t.span s!"`{f}` takes {d.params.size} arguments, not {args.size}"
      for i in [0:d.params.size] do
        checkTm p ctx d.params[i]! args[i]!
  | .helper ty h args =>
    match Helpers.find? h.name with
    | none => reject t.span s!"`{h.name}` is not in the helper table"
    | some d =>
      if ty != d.res then typeMismatch t.span s!"`{h.name}`'s result" d.res ty
      if !d.kinds.isEmpty && !d.kinds.contains p.kind then
        reject t.span (helperKindMessage h.name p.kind)
      if args.size != d.args.size then
        reject t.span s!"`{h.name}` takes {d.args.size} arguments, not {args.size}"
      for i in [0:d.args.size] do
        checkTm p ctx d.args[i]! args[i]!
  | .ret _ =>
    reject t.span "`return` is only allowed in a tail position, not as a value"

/-- A declaration body: `ret` and the arms of a tail `if`/`match` are continuations, so
they are checked against the function's result type rather than `Unit`. -/
partial def checkTail (p : Program) (ctx : Array Ty) (ret : Ty) (t : Tm) :
    Except String Unit := do
  match t.node with
  | .ret v => checkTm p ctx ret v
  | .letE ty x v body =>
    if ty == .unit then
      reject t.span "a `Unit` binding has no C representation"
    unless x == ctx.size do
      reject t.span s!"the binder x{x} is not the next slot (the context has {ctx.size})"
    checkTm p ctx ty v
    checkTail p (ctx.push ty) ret body
  | .ite _ c a b =>
    checkTm p ctx .bool c
    checkTail p ctx ret a
    checkTail p ctx ret b
  | .switchOption _ s onNone x onSome =>
    match s.ty.optionInner with
    | none => reject t.span s!"`match` on an `Option` needs an `Option`, not `{s.ty.describe}`"
    | some inner =>
      checkTm p ctx s.ty s
      checkTail p ctx ret onNone
      unless x == ctx.size do
        reject t.span s!"the `some` binder x{x} is not the next slot"
      checkTail p (ctx.push inner) ret onSome
  | .switchTag _ s alts =>
    match s.ty.enumArity with
    | none => reject t.span s!"a tag switch needs a nullary enum, not `{s.ty.describe}`"
    | some n =>
      if alts.size != n then
        reject t.span s!"the switch is not exhaustive: {alts.size} arms for {n} constructors"
      checkTm p ctx s.ty s
      for a in alts.toList do checkTail p ctx ret a
  | _ =>
    if t.ty != ret then
      typeMismatch t.span "the body does not produce the declared result" ret t.ty

/-! ## Declarations, the call graph, and the budgets -/

def checkDecl (p : Program) (d : Decl) : Except String Unit := do
  for ty in d.params.toList do
    match ty with
    | .map _ _ _ =>
      reject d.body.span s!"`{d.name}` takes a map as a parameter. A map is a handle, not a \
value: it cannot be passed, stored or returned; name it in the program's map table instead"
    | .unit =>
      reject d.body.span s!"`{d.name}` has a `Unit` parameter, which has no C representation"
    | .packet =>
      if p.kind.isTracing then reject d.body.span packetTraceMessage else checkTy ty
    | .ctx k =>
      if k != p.kind then
        reject d.body.span s!"`{d.name}` takes a {k.describe} context, but the program is \
{p.kind.describe}"
      else checkTy ty
    | _ => checkTy ty
  if p.kind.isTracing && d.ret == .packet then reject d.body.span packetTraceMessage
  checkTy d.ret
  checkTail p d.params d.ret d.body

/-- Does `from` reach `target` through calls? `seen` breaks cycles in the *query*; the
answer is still `true` for a cycle, which is the point. -/
partial def reaches (p : Program) (target : String) (seen : List String) (src : String) : Bool :=
  match p.decl? src with
  | none => false
  | some d =>
    d.body.calls.toList.any fun c =>
      c == target || (!seen.contains c && reaches p target (c :: seen) c)

/-- The call graph must be acyclic: the emitter inlines every call, and the kernel rejects
a call to a function on the current stack (§2.1). -/
def checkAcyclic (p : Program) : Except String Unit := do
  for d in p.decls.toList do
    let cyclic := d.body.calls.toList.any fun c =>
      c == d.name || reaches p d.name [d.name] c
    if cyclic then rejectTop (cycleMessage d.name)

/-- A rough stack estimate for one declaration: every `let` costs its value (at least
8 bytes, as a register spill), and the parameters are already in the frame. The real
number is `clang`'s; §2.2 says the post-`clang` `r10 - N` check is authoritative. -/
partial def localBytes (t : Tm) : Nat :=
  let here : Nat := match t.node with
    | .letE ty _ _ _ => (ty.byteSize.getD 8).max 8
    -- the argv-slot accessor holds one pointer while the string is read
    | .argvSlot _ _ _ _ => 8
    -- the event is a stack local in the emitted block; the number is the ABI's size
    | .probeEmit _ _ _ _ _ _ _ _ _ _ => eventSize
    | _ => 0
  here + t.node.children.foldl (fun n c => n + localBytes c) 0

def declFrame (d : Decl) : Nat :=
  d.params.foldl (fun n ty => n + (ty.byteSize.getD 8).max 8) 0 + localBytes d.body

/-- The size after inlining, with a fuel so a malformed cyclic program cannot hang the
checker (cycles are rejected first). -/
partial def expandedSize (p : Program) (fuel : Nat) (d : Decl) : Nat :=
  let here := d.body.size
  d.body.calls.foldl (fun n f =>
    n + match p.decl? f with
      | none => 0
      | some c => if fuel == 0 then c.body.size else expandedSize p (fuel - 1) c) 0
  + here

def checkBudgets (p : Program) : Except String Unit := do
  for d in p.decls.toList do
    let frame := declFrame d
    if frame > 256 then rejectTop (frameMessage d.name frame)
  let total := p.decls.foldl (fun n d => n + expandedSize p (p.decls.size + 1) d) 0
  if total > 100000 then rejectTop (budgetMessage total)

/-! ## Maps and the program boundary -/

def checkMaps (p : Program) : Except String Unit := do
  let names := p.maps.foldl (fun (s : List String) m =>
    if s.contains m.name then s else m.name :: s) []
  if names.length != p.maps.size then
    rejectTop "two maps have the same name"
  for m in p.maps.toList do
    checkTy m.key
    checkTy m.value
    unless m.key.isPod do rejectTop (mapPodMessage "key" m.key)
    unless m.value.isPod do rejectTop (mapPodMessage "value" m.value)
    match m.key.byteSize with
    | none => rejectTop (mapPodMessage "key" m.key)
    | some n => do
      if n == 0 then rejectTop s!"the key of `{m.name}` is empty"
      if n > 64 then
        rejectTop s!"the key of `{m.name}` is {n} bytes; the limit is 64"
    match m.value.byteSize with
    | none => rejectTop (mapPodMessage "value" m.value)
    | some n => do
      if n == 0 then rejectTop s!"the value of `{m.name}` is empty"
      if n > 512 then
        rejectTop s!"the value of `{m.name}` is {n} bytes; the limit is 512"
    if m.kind.arrayLike && m.key != .u32 then
      rejectTop s!"the `{m.kind.describe}` map `{m.name}` is indexed by `UIntN 32`, not \
`{m.key.describe}`"
    if m.kind.isPerfEventArray then
      if m.key != .u32 || m.value != .u32 then
        rejectTop s!"the `perf_event_array` map `{m.name}` has a `UIntN 32` key and value \
(a CPU index and a perf fd), not `{m.key.describe}`/`{m.value.describe}`"
    if m.maxEntries == 0 then rejectTop s!"the map `{m.name}` has `max_entries = 0`"

/-- The whole-program checks. -/
def checkProgram (p : Program) : Except String Unit := do
  let some entry := p.entryDecl? |
    rejectAt p.span s!"the entry `{p.entry}` has no definition"
  match p.attach? with
  | none =>
    rejectAt p.span s!"unknown section `{p.sectionName}` for a {p.kind.describe} program \
(choose xdp; tc, classifier or sched_cls; tracepoint/<category>/<event>; or \
uprobe/<binary>:<symbol>)"
  | some _ => pure ()
  if p.license.isEmpty then
    rejectAt p.span "a program needs a licence (`\"GPL\"` for GPL-only helpers)"
  if p.kind.isTracing then do
    if p.license != "GPL" then rejectAt p.span (traceLicenseMessage p.license)
    else pure ()
    match p.ret with
    | .unit | .u32 => pure ()
    | other => rejectAt p.span (traceResultMessage other)
  else
    match p.ret with
    | .enum n =>
      let need := if p.kind == .xdp then xdpActionArity else tcActionArity
      if n < need then
        rejectAt p.span s!"`{p.ret.describe}` has {n} constructors; the {p.kind.describe} \
action has at least {need}"
      else pure ()
    | other => rejectAt p.span (actionMessage other)
  if entry.ret != p.ret then
    typeMismatch entry.body.span s!"`{p.entry}`'s result" p.ret entry.ret
  match entry.params.toList with
  | [ty] =>
    match ty with
    | .ctx k =>
      if k != p.kind then
        rejectAt entry.body.span s!"`{p.entry}` takes a {k.describe} context, but the \
program is {p.kind.describe}"
    | other =>
      rejectAt entry.body.span s!"`{p.entry}`'s parameter must be the context, not \
`{other.describe}`"
  | _ => rejectAt entry.body.span s!"`{p.entry}` takes {entry.params.size} parameters; an \
entry takes one context"
  let names := p.decls.foldl (fun (s : List String) d =>
    if s.contains d.name then s else d.name :: s) []
  if names.length != p.decls.size then rejectTop "two definitions have the same name"
  checkMaps p
  for d in p.decls.toList do checkDecl p d
  checkAcyclic p
  checkBudgets p

end Wiz.Compiler.Bpf
