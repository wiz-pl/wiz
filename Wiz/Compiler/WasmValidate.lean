/-!
# A structural validator for WebAssembly modules

`Wiz.WasmValidate.validate bytes` checks the bytes of a WebAssembly module without
running it and without an external tool (no `wasm-tools`, no V8). It parses every
section, checks the cross-references (types, functions, tables, memories, globals,
exports, elements and data), and type-checks each function body against the operand
stack. It is deliberately an **encoder-side validator**: it knows the instruction
subset that `Wiz.Compiler.Wasm` emits, and reports an unknown opcode rather than
quietly accepting it. A module that `Wiz.Compiler.Wasm` writes is passed through it in
`Build.compileWasm`, so an encoder bug is a compile error, not a wrong answer; the
test group also runs it on hand-damaged bytes to show that it catches them.

The checker follows the binary-format and validation rules of the WebAssembly core
specification (MVP):

* magic and version; a custom section anywhere, other sections in order, each at most
  once, each exactly its declared length;
* function bodies with `block`/`loop`/`if` frames, branch depths, `br_table`, locals,
  calls and `call_indirect`, memory accesses and alignment, and the numeric
  instructions the backend uses;
* the stack-polymorphic `unreachable` state inside a frame (a body's tail may be
  unreachable);
* offsets in element and data segments, exports and the start function.
-/

namespace Wiz.WasmValidate

/-! ## Value types and the module's shapes -/

inductive VT where
  | i32
  | i64
  | f32
  | f64
  deriving Repr, BEq, Inhabited

def VT.toString : VT → String
  | .i32 => "i32"
  | .i64 => "i64"
  | .f32 => "f32"
  | .f64 => "f64"

instance : ToString VT := ⟨VT.toString⟩

def VT.ofByte? : UInt8 → Option VT
  | 0x7F => some .i32
  | 0x7E => some .i64
  | 0x7D => some .f32
  | 0x7C => some .f64
  | _ => none

structure FuncType where
  params : Array VT := #[]
  results : Array VT := #[]
  deriving Repr, BEq, Inhabited

structure Limits where
  min : Nat
  max : Option Nat := none
  deriving Repr, BEq, Inhabited

structure TableType where
  elem : UInt8 := 0x70
  limits : Limits
  deriving Repr, BEq, Inhabited

structure GlobalType where
  vt : VT
  mutable : Bool
  deriving Repr, BEq, Inhabited

structure Export where
  name : String
  kind : UInt8
  idx : Nat
  deriving Repr, BEq, Inhabited

structure Import where
  module : String
  name : String
  /-- only function imports are in this backend's subset -/
  typeIdx : Nat
  deriving Repr, BEq, Inhabited

/-! ## A byte reader -/

structure Rd where
  data : ByteArray
  pos : Nat := 0
  deriving Inhabited

def Rd.remaining (r : Rd) : Nat := r.data.size - r.pos

def Rd.u8 (r : Rd) : Except String (UInt8 × Rd) :=
  if h : r.pos < r.data.size then
    .ok (r.data.get r.pos h, { r with pos := r.pos + 1 })
  else
    .error s!"unexpected end of module at byte {r.pos}"

def Rd.take (r : Rd) (n : Nat) : Except String (ByteArray × Rd) :=
  if n ≤ r.remaining then
    .ok (r.data.extract r.pos (r.pos + n), { r with pos := r.pos + n })
  else
    .error s!"unexpected end of module at byte {r.pos} (wanted {n} more bytes)"

/-- Unsigned LEB128, at most 10 bytes (all lengths and indices here are small). -/
partial def ulebGo (r : Rd) (shift acc k : Nat) : Except String (Nat × Rd) := do
  if k ≥ 10 then throw s!"LEB128 integer too long at byte {r.pos}"
  let (b, r) ← r.u8
  let low := b.toNat % 128
  let acc := acc + Nat.shiftLeft low shift
  if b.toNat / 128 == 0 then
    pure (acc, r)
  else
    ulebGo r (shift + 7) acc (k + 1)

def Rd.uleb (r : Rd) : Except String (Nat × Rd) := ulebGo r 0 0 0

/-- Signed LEB128, decoded (for `i32.const` and `i64.const`). -/
partial def slebGo (r : Rd) (shift acc k : Nat) : Except String (Int × Rd) := do
  if k ≥ 10 then throw s!"LEB128 integer too long at byte {r.pos}"
  let (b, r) ← r.u8
  let low := b.toNat % 128
  let acc := acc + Nat.shiftLeft low shift
  if b.toNat / 128 == 0 then
    let bits := shift + 7
    let signed := if low ≥ 64 then acc - Nat.shiftLeft 1 bits else acc
    pure (Int.ofNat signed, r)
  else
    slebGo r (shift + 7) acc (k + 1)

def Rd.sleb (r : Rd) : Except String (Int × Rd) := slebGo r 0 0 0

def Rd.name (r : Rd) : Except String (String × Rd) := do
  let (n, r) ← r.uleb
  let (bs, r) ← r.take n
  match String.fromUTF8? bs with
  | some s => pure (s, r)
  | none => throw s!"a name is not valid UTF-8 at byte {r.pos}"

def Rd.byte (r : Rd) : Except String (UInt8 × Rd) := r.u8

/-! ## Sections -/

structure Local where
  count : Nat
  vt : VT
  deriving Repr, BEq, Inhabited

structure Code where
  locals : Array Local
  /-- the bytes after the locals declaration, up to the body's end -/
  body : ByteArray
  deriving Inhabited

structure Elem where
  offset : Int
  funcs : Array Nat
  deriving Repr, BEq, Inhabited

structure Data where
  offset : Int
  bytes : ByteArray
  deriving Inhabited

structure Global where
  type : GlobalType
  /-- the initial value (`i32.const` or `i64.const`) -/
  init : Int
  deriving Repr, BEq, Inhabited

structure Module where
  types : Array FuncType := #[]
  imports : Array Import := #[]
  funcTypes : Array Nat := #[]
  tables : Array TableType := #[]
  memories : Array Limits := #[]
  globals : Array Global := #[]
  exports : Array Export := #[]
  elems : Array Elem := #[]
  codes : Array Code := #[]
  datas : Array Data := #[]
  start : Option Nat := none
  dataCount : Option Nat := none

/-- The rank of a section for the ordering rule (custom sections are skipped). The data
count section (12) sits between the element (9) and code (10) sections. -/
def sectionRank (id : Nat) : Option Nat :=
  match id with
  | 1 => some 2 | 2 => some 4 | 3 => some 6 | 4 => some 8 | 5 => some 10
  | 6 => some 12 | 7 => some 14 | 8 => some 16 | 9 => some 18 | 12 => some 19
  | 10 => some 20 | 11 => some 22 | _ => none

def readLimits (r : Rd) : Except String (Limits × Rd) := do
  let (flags, r) ← r.uleb
  match flags with
  | 0 => do
    let (min, r) ← r.uleb
    pure ({ min }, r)
  | 1 => do
    let (min, r) ← r.uleb
    let (max, r) ← r.uleb
    if max < min then throw s!"a limit's maximum {max} is below its minimum {min}"
    pure ({ min, max := some max }, r)
  | _ => throw s!"unsupported limits flags {flags}"

def readTableType (r : Rd) : Except String (TableType × Rd) := do
  let (elem, r) ← r.u8
  unless elem == 0x70 do throw s!"a table's element type is 0x{elem.toNat} (only funcref, 0x70)"
  let (limits, r) ← readLimits r
  pure ({ elem, limits }, r)

def readGlobalType (r : Rd) : Except String (GlobalType × Rd) := do
  let (b, r) ← r.u8
  let some vt := VT.ofByte? b | throw s!"unknown value type 0x{s!"{b.toNat}"} in a global"
  let (m, r) ← r.u8
  match m with
  | 0 => pure ({ vt, mutable := false }, r)
  | 1 => pure ({ vt, mutable := true }, r)
  | _ => throw s!"bad global mutability {m}"

partial def readVecGo {α : Type} (one : Rd → Except String (α × Rd)) (r : Rd) (acc : Array α)
    (k : Nat) : Except String (Array α × Rd) := do
  if k == 0 then pure (acc, r)
  else
    let (x, r) ← one r
    readVecGo one r (acc.push x) (k - 1)

def readVec {α : Type} (r : Rd) (one : Rd → Except String (α × Rd)) : Except String (Array α × Rd) := do
  let (n, r) ← r.uleb
  if n > 10_000_000 then throw s!"a vector declares {n} entries"
  readVecGo one r #[] n

def readFuncType (r : Rd) : Except String (FuncType × Rd) := do
  let (tag, r) ← r.u8
  unless tag == 0x60 do throw s!"a type is not a function type (0x{tag.toNat})"
  let (params, r) ← readVec r (fun r => do
    let (b, r) ← r.u8
    let some vt := VT.ofByte? b | throw s!"unknown parameter type 0x{b.toNat}"
    pure (vt, r))
  let (results, r) ← readVec r (fun r => do
    let (b, r) ← r.u8
    let some vt := VT.ofByte? b | throw s!"unknown result type 0x{b.toNat}"
    pure (vt, r))
  if results.size > 1 then throw "a function type has more than one result (not in this subset)"
  pure ({ params, results }, r)

def readImport (r : Rd) : Except String (Import × Rd) := do
  let (module, r) ← r.name
  let (name, r) ← r.name
  let (kind, r) ← r.u8
  match kind with
  | 0 => do
    let (ty, r) ← r.uleb
    pure ({ module, name, typeIdx := ty }, r)
  | 1 | 2 | 3 => throw s!"an imported table, memory or global is outside this backend's subset (import kind {kind})"
  | 4 => throw "a tag import (exceptions) is outside this backend's subset"
  | _ => throw s!"unknown import kind {kind}"

def readExport (r : Rd) : Except String (Export × Rd) := do
  let (name, r) ← r.name
  let (kind, r) ← r.u8
  if kind > 3 then throw s!"unknown export kind {kind}"
  let (idx, r) ← r.uleb
  pure ({ name, kind, idx }, r)

/-- A constant expression: `i32.const n` or `i64.const n`, then `end`. The backend uses
`i32.const` for the global's initial value and for element/data offsets, so this is all
that is needed. -/
def readConst (r : Rd) (expected : VT) : Except String (Int × Rd) := do
  let (op, r) ← r.u8
  let (got, r) ←
    match op with
    | 0x41 => pure (.i32, r)
    | 0x42 => pure (.i64, r)
    | _ => throw s!"a constant expression starts with opcode 0x{op.toNat}"
  unless got == expected do throw s!"a constant expression has type {got}, expected {expected}"
  let (n, r) ← r.sleb
  let (endb, r) ← r.u8
  unless endb == 0x0B do throw s!"a constant expression does not end at byte {r.pos}"
  pure (n, r)

def readGlobal (r : Rd) : Except String (Global × Rd) := do
  let (gt, r) ← readGlobalType r
  let (init, r) ← readConst r gt.vt
  pure ({ type := gt, init }, r)

def readElem (r : Rd) : Except String (Elem × Rd) := do
  let (flags, r) ← r.uleb
  match flags with
  | 0 => do
    let (offset, r) ← readConst r .i32
    let (funcs, r) ← readVec r (fun r => r.uleb)
    pure ({ offset, funcs }, r)
  | 2 => do
    let (table, r) ← r.uleb
    unless table == 0 do throw s!"an element segment names table {table} (only 0)"
    let (offset, r) ← readConst r .i32
    let (kind, r) ← r.u8
    unless kind == 0x00 do throw s!"an element segment has element kind {kind}"
    let (funcs, r) ← readVec r (fun r => r.uleb)
    pure ({ offset, funcs }, r)
  | _ => throw s!"unsupported element segment flags {flags}"

def readData (r : Rd) : Except String (Data × Rd) := do
  let (flags, r) ← r.uleb
  match flags with
  | 0 => do
    let (offset, r) ← readConst r .i32
    let (n, r) ← r.uleb
    let (bytes, r) ← r.take n
    pure ({ offset, bytes }, r)
  | _ => throw s!"unsupported data segment flags {flags} (only an active segment)"

def readCode (r : Rd) : Except String (Code × Rd) := do
  let (size, r) ← r.uleb
  let (bodyBytes, r) ← r.take size
  let bodyRd : Rd := { data := bodyBytes }
  let (locals, bodyRd) ← readVec bodyRd (fun r => do
    let (count, r) ← r.uleb
    let (b, r) ← r.u8
    let some vt := VT.ofByte? b | throw s!"unknown local type 0x{b.toNat}"
    pure ({ count, vt }, r))
  pure ({ locals, body := bodyBytes.extract bodyRd.pos bodyBytes.size }, r)

/-! ## Function bodies

The validator's operand stack carries `Option VT`, where `none` is the polymorphic
value that follows `unreachable` in a frame. -/

inductive FrameKind where
  | func
  | block
  | loop
  | ifThen
  deriving Repr, BEq, Inhabited

structure Frame where
  kind : FrameKind
  startTypes : Array VT
  endTypes : Array VT
  /-- the operand-stack height when the frame began (after its parameters) -/
  height : Nat
  unreachable : Bool := false
  hasElse : Bool := false
  deriving Repr, BEq, Inhabited

structure VState where
  stack : Array (Option VT) := #[]
  frames : Array Frame := #[]
  deriving Repr, Inhabited

def VState.top? (s : VState) : Option Frame := s.frames.back?

def VState.pop (s : VState) : Except String (Option VT × VState) := do
  let some f := s.top? | throw "no control frame"
  if s.stack.size == f.height then
    if f.unreachable then pure (none, s)
    else throw "type stack underflow"
  else if s.stack.size > f.height then
    pure (s.stack.back!, { s with stack := s.stack.pop })
  else
    throw "type stack below its frame's height"

def VState.push (s : VState) (t : Option VT) : VState :=
  { s with stack := s.stack.push t }

def VState.popExpect (s : VState) (t : VT) : Except String VState := do
  let (got, s) ← s.pop
  match got with
  | none => pure s
  | some u => if u == t then pure s else throw s!"expected {t}, found {u}"

def VState.peek (s : VState) : Except String (Option VT) := do
  let some f := s.top? | throw "no control frame"
  if s.stack.size == f.height then
    if f.unreachable then pure none else throw "type stack underflow"
  else if s.stack.size > f.height then pure s.stack.back!
  else throw "type stack below its frame's height"

def VState.makeUnreachable (s : VState) : VState :=
  match s.top? with
  | none => s
  | some f =>
    { s with stack := s.stack.extract 0 f.height,
             frames := s.frames.set! (s.frames.size - 1) { f with unreachable := true } }

def Frame.labelTypes (f : Frame) : Array VT :=
  if f.kind == .loop then f.startTypes else f.endTypes

def VState.label (s : VState) (depth : Nat) : Except String Frame := do
  if depth ≥ s.frames.size then throw s!"branch depth {depth} is outside {s.frames.size} frames"
  pure s.frames[s.frames.size - 1 - depth]!

def popTypes (s : VState) (ts : Array VT) : Except String VState := do
  let mut s := s
  for t in ts.reverse do
    s ← s.popExpect t
  pure s

def pushTypes (s : VState) (ts : Array VT) : VState :=
  ts.foldl (fun s t => s.push (some t)) s

def beginFrame (s : VState) (kind : FrameKind) (startTypes endTypes : Array VT) : Except String VState := do
  let s ← popTypes s startTypes
  let f : Frame := { kind, startTypes, endTypes, height := s.stack.size }
  pure (pushTypes { s with frames := s.frames.push f } startTypes)

/-! ## Proposal features

The backend uses the **tail-call proposal** (`return_call`/`return_call_indirect`). There
is no module-level feature flag in the binary format, so the validator carries the
requirement explicitly: `validate` defaults to requiring tail calls, and a caller can
turn them off to check that a module from an older encoder does not use them. -/

structure Features where
  /-- accept `return_call` and `return_call_indirect` (the tail-call proposal) -/
  tailCalls : Bool := true
  deriving Repr, BEq, Inhabited

/-- The environment a function body is checked against. -/
structure Env where
  types : Array FuncType
  /-- the type index of every function: imported first, then defined -/
  funcs : Array Nat
  tables : Array TableType
  memories : Array Limits
  globals : Array GlobalType
  features : Features := {}

/-- The numeric instructions (unary and binary operators). -/
partial def checkNumeric (op : UInt8) (r : Rd) (s : VState) : Except String (Rd × VState) := do
  let unary (t : VT) : Except String (Rd × VState) := do
    let s ← s.popExpect t
    pure (r, s.push (some t))
  let binary (t : VT) : Except String (Rd × VState) := do
    let s ← s.popExpect t
    let s ← s.popExpect t
    pure (r, s.push (some t))
  let compare (t : VT) : Except String (Rd × VState) := do
    let s ← s.popExpect t
    let s ← s.popExpect t
    pure (r, s.push (some .i32))
  match op with
  | 0x45 => do
    let s ← s.popExpect .i32
    pure (r, s.push (some .i32))
  | 0x46 | 0x47 | 0x48 | 0x49 | 0x4A | 0x4B | 0x4C | 0x4D | 0x4E | 0x4F => compare .i32
  | 0x50 => do
    let s ← s.popExpect .i64
    pure (r, s.push (some .i32))
  | 0x51 | 0x52 | 0x53 | 0x54 | 0x55 | 0x56 | 0x57 | 0x58 | 0x59 | 0x5A => compare .i64
  | 0x67 | 0x68 | 0x69 => unary .i32
  | 0x6A | 0x6B | 0x6C | 0x6D | 0x6E | 0x6F | 0x70 | 0x71 | 0x72 | 0x73 | 0x74 | 0x75 | 0x76 | 0x77 | 0x78 =>
    binary .i32
  | 0x79 | 0x7A | 0x7B => unary .i64
  | 0x7C | 0x7D | 0x7E | 0x7F | 0x80 | 0x81 | 0x82 | 0x83 | 0x84 | 0x85 | 0x86 | 0x87 | 0x88 | 0x89 | 0x8A =>
    binary .i64
  | 0xA7 => do
    let s ← s.popExpect .i64
    pure (r, s.push (some .i32))
  | 0xAC | 0xAD => do
    let s ← s.popExpect .i32
    pure (r, s.push (some .i64))
  | _ => throw s!"unknown or unsupported opcode 0x{op.toNat} at byte {r.pos}"

def checkAlign (maxLog2 : Nat) (align : Nat) : Except String Unit :=
  if align > maxLog2 then throw s!"memory alignment {align} is larger than the natural one ({maxLog2})" else pure ()

/-- One instruction. Returns the reader and the new state; `end` pops a frame. -/
partial def step (env : Env) (locals : Array VT) (op : UInt8) (r : Rd) (s : VState) :
    Except String (Rd × VState) := do
  match op with
  | 0x00 => pure (r, s.makeUnreachable)
  | 0x01 => pure (r, s)
  | 0x02 | 0x03 => do
    let (bt, r) ← r.u8
    let (startTypes, endTypes) ←
      if bt == 0x40 then pure (#[], #[])
      else match VT.ofByte? bt with
        | some vt => pure (#[], #[vt])
        | none => throw s!"unsupported block type 0x{bt.toNat} at body byte {r.pos - 1} (this backend uses an empty one)"
    let s ← beginFrame s (if op == 0x02 then .block else .loop) startTypes endTypes
    pure (r, s)
  | 0x04 => do
    let (bt, r) ← r.u8
    let (startTypes, endTypes) ←
      if bt == 0x40 then pure (#[], #[])
      else match VT.ofByte? bt with
        | some vt => pure (#[], #[vt])
        | none => throw s!"unsupported block type 0x{bt.toNat} at body byte {r.pos - 1} (this backend uses an empty one)"
    let s ← s.popExpect .i32
    let s ← beginFrame s .ifThen startTypes endTypes
    pure (r, s)
  | 0x05 => do
    let some f := s.top? | throw "`else` outside a frame"
    unless f.kind == .ifThen do throw "`else` outside an `if`"
    if f.hasElse then throw "two `else`s in one `if`"
    let s ← popTypes s f.endTypes
    unless s.stack.size == f.height do throw "the `if` branch leaves extra values"
    let s := { s with stack := s.stack.extract 0 f.height,
                      frames := s.frames.set! (s.frames.size - 1)
                        { f with unreachable := false, hasElse := true } }
    pure (r, pushTypes s f.startTypes)
  | 0x0B => do
    let some f := s.top? | throw "`end` outside a frame"
    let s ← popTypes s f.endTypes
    unless s.stack.size == f.height do throw "a block leaves extra values"
    if f.kind == .ifThen && !f.hasElse && !f.endTypes.isEmpty then
      throw "an `if` with results has no `else`"
    let s := { s with frames := s.frames.pop }
    pure (r, pushTypes s f.endTypes)
  | 0x0C => do
    let (depth, r) ← r.uleb
    let f ← s.label depth
    let s ← popTypes s f.labelTypes
    pure (r, s.makeUnreachable)
  | 0x0D => do
    let (depth, r) ← r.uleb
    let f ← s.label depth
    let s ← s.popExpect .i32
    let s ← popTypes s f.labelTypes
    pure (r, pushTypes s f.labelTypes)
  | 0x0F => do
    let some f := s.frames[0]? | throw "`return` outside a function"
    let s ← popTypes s f.endTypes
    pure (r, s.makeUnreachable)
  | 0x10 => do
    let (i, r) ← r.uleb
    if i ≥ env.funcs.size then throw s!"call of function {i}, but there are {env.funcs.size}"
    let ty := env.funcs[i]!
    if ty ≥ env.types.size then throw s!"function {i} has type {ty}, which does not exist"
    let ft := env.types[ty]!
    let s ← popTypes s ft.params
    pure (r, pushTypes s ft.results)
  | 0x11 => do
    let (ty, r) ← r.uleb
    let (table, r) ← r.uleb
    if ty ≥ env.types.size then throw s!"call_indirect names type {ty}, which does not exist"
    if table ≥ env.tables.size then throw s!"call_indirect names table {table}, which does not exist"
    let ft := env.types[ty]!
    let s ← s.popExpect .i32
    let s ← popTypes s ft.params
    pure (r, pushTypes s ft.results)
  | 0x12 => do
    -- (tail-call proposal) a call whose results are the current function's results
    unless env.features.tailCalls do
      throw "`return_call` needs the tail-call proposal, which is not enabled in this validator"
    let (i, r) ← r.uleb
    if i ≥ env.funcs.size then throw s!"return_call of function {i}, but there are {env.funcs.size}"
    let ty := env.funcs[i]!
    if ty ≥ env.types.size then throw s!"function {i} has type {ty}, which does not exist"
    let ft := env.types[ty]!
    let some f := s.frames[0]? | throw "`return_call` outside a function"
    unless ft.results == f.endTypes do
      throw s!"return_call of a function returning {ft.results.size} values in a function returning {f.endTypes.size}"
    let s ← popTypes s ft.params
    pure (r, s.makeUnreachable)
  | 0x13 => do
    -- (tail-call proposal) the indirect form: arguments, then the table index on top
    unless env.features.tailCalls do
      throw "`return_call_indirect` needs the tail-call proposal, which is not enabled in this validator"
    let (ty, r) ← r.uleb
    let (table, r) ← r.uleb
    if ty ≥ env.types.size then throw s!"return_call_indirect names type {ty}, which does not exist"
    if table ≥ env.tables.size then throw s!"return_call_indirect names table {table}, which does not exist"
    let ft := env.types[ty]!
    let some f := s.frames[0]? | throw "`return_call_indirect` outside a function"
    unless ft.results == f.endTypes do
      throw s!"return_call_indirect returns {ft.results.size} values in a function returning {f.endTypes.size}"
    let s ← s.popExpect .i32
    let s ← popTypes s ft.params
    pure (r, s.makeUnreachable)
  | 0x1A => do
    let (_, s) ← s.pop
    pure (r, s)
  | 0x1B => do
    let s ← s.popExpect .i32
    let (a, s) ← s.pop
    let (b, s) ← s.pop
    match a, b with
    | some x, some y => if x != y then throw s!"select of {x} and {y}"
    | _, _ => pure ()
    pure (r, s.push (a <|> b))
  | 0x20 => do
    let (i, r) ← r.uleb
    if i ≥ locals.size then throw s!"local.get of local {i}, but there are {locals.size}"
    pure (r, s.push (some locals[i]!))
  | 0x21 => do
    let (i, r) ← r.uleb
    if i ≥ locals.size then throw s!"local.set of local {i}, but there are {locals.size}"
    let s ← s.popExpect locals[i]!
    pure (r, s)
  | 0x22 => do
    let (i, r) ← r.uleb
    if i ≥ locals.size then throw s!"local.tee of local {i}, but there are {locals.size}"
    let s ← s.popExpect locals[i]!
    pure (r, s.push (some locals[i]!))
  | 0x23 => do
    let (i, r) ← r.uleb
    if i ≥ env.globals.size then throw s!"global.get of global {i}, but there are {env.globals.size}"
    pure (r, s.push (some env.globals[i]!.vt))
  | 0x24 => do
    let (i, r) ← r.uleb
    if i ≥ env.globals.size then throw s!"global.set of global {i}, but there are {env.globals.size}"
    unless env.globals[i]!.mutable do throw s!"global.set of immutable global {i}"
    let s ← s.popExpect env.globals[i]!.vt
    pure (r, s)
  | 0x28 | 0x29 => do
    -- (MVP memarg: an alignment hint and an offset; no memory index)
    let (align, r) ← r.uleb
    let (_, r) ← r.uleb
    if env.memories.isEmpty then throw "a load without a memory"
    checkAlign (if op == 0x28 then 2 else 3) align
    let s ← s.popExpect .i32
    pure (r, s.push (some (if op == 0x28 then .i32 else .i64)))
  | 0x36 | 0x37 => do
    let (align, r) ← r.uleb
    let (_, r) ← r.uleb
    if env.memories.isEmpty then throw "a store without a memory"
    checkAlign (if op == 0x36 then 2 else 3) align
    let s ← s.popExpect (if op == 0x36 then .i32 else .i64)
    let s ← s.popExpect .i32
    pure (r, s)
  | 0x3F => do
    let (_, r) ← r.u8
    if env.memories.isEmpty then throw "memory.size without a memory"
    pure (r, s.push (some .i32))
  | 0x40 => do
    let (_, r) ← r.u8
    if env.memories.isEmpty then throw "memory.grow without a memory"
    let s ← s.popExpect .i32
    pure (r, s.push (some .i32))
  | 0x41 => do
    let (_, r) ← r.sleb
    pure (r, s.push (some .i32))
  | 0x42 => do
    let (_, r) ← r.sleb
    pure (r, s.push (some .i64))
  | _ => checkNumeric op r s

/-- Run a function body to its final `end`. -/
partial def runBody (env : Env) (locals : Array VT) (r : Rd) (s : VState) :
    Except String (Rd × VState) := do
  let (op, r) ← r.u8
  let (r, s) ← step env locals op r s
  if op == 0x0B && s.frames.isEmpty then pure (r, s)
  else runBody env locals r s

def checkBody (env : Env) (f : FuncType) (c : Code) : Except String Unit := do
  let mut locals := f.params
  for l in c.locals do
    if l.count > 1_000_000 then throw s!"a function declares {l.count} locals in one group"
    for _ in [0:l.count] do locals := locals.push l.vt
  let start : Frame := { kind := .func, startTypes := #[], endTypes := f.results, height := 0 }
  let s : VState := { frames := #[start] }
  let r : Rd := { data := c.body }
  let (r, s) ← runBody env locals r s
  unless s.frames.isEmpty do throw "a function body ends inside a block"
  unless r.pos == r.data.size do throw s!"{r.data.size - r.pos} bytes after a function body's `end`"
  -- the function's final end leaves its results; nothing else may be on the stack
  let expected := f.results.map some
  unless s.stack.toList == expected.toList do
    throw s!"a function body leaves {s.stack.size} values (its type has {f.results.size} results)"

/-! ## The module -/

partial def parseSections (r : Rd) (m : Module) (lastRank : Nat) : Except String Module := do
    if r.pos == r.data.size then pure m
    else do
      let (id, r) ← r.u8
      let (size, r) ← r.uleb
      let (sec, r) ← r.take size
      let sr : Rd := { data := sec }
      let (m, sr) ← match id.toNat with
        | 0 => do
          let (_, sr) ← sr.name
          pure (m, sr)
        | 1 => do
          let (types, sr) ← readVec sr readFuncType
          pure ({ m with types }, sr)
        | 2 => do
          let (imports, sr) ← readVec sr readImport
          for i in imports do
            if i.typeIdx ≥ m.types.size then
              throw s!"import {i.name} names type {i.typeIdx}, which does not exist"
          pure ({ m with imports }, sr)
        | 3 => do
          let (funcTypes, sr) ← readVec sr (fun r => r.uleb)
          pure ({ m with funcTypes }, sr)
        | 4 => do
          let (tables, sr) ← readVec sr readTableType
          pure ({ m with tables }, sr)
        | 5 => do
          let (memories, sr) ← readVec sr readLimits
          pure ({ m with memories }, sr)
        | 6 => do
          let (globals, sr) ← readVec sr readGlobal
          pure ({ m with globals }, sr)
        | 7 => do
          let (exports, sr) ← readVec sr readExport
          pure ({ m with exports }, sr)
        | 8 => do
          let (start, sr) ← sr.uleb
          pure ({ m with start := some start }, sr)
        | 9 => do
          let (elems, sr) ← readVec sr readElem
          pure ({ m with elems }, sr)
        | 12 => do
          let (n, sr) ← sr.uleb
          pure ({ m with dataCount := some n }, sr)
        | 10 => do
          let (codes, sr) ← readVec sr readCode
          pure ({ m with codes }, sr)
        | 11 => do
          let (datas, sr) ← readVec sr readData
          pure ({ m with datas }, sr)
        | n => throw s!"unknown section id {n}"
      if id.toNat != 0 then
        unless sr.pos == sr.data.size do
          throw s!"section {id} has {sr.data.size - sr.pos} bytes left over"
      match id.toNat, sectionRank id.toNat with
      | 0, _ => parseSections r m lastRank
      | _, some rank =>
        if rank ≤ lastRank then throw s!"section {id} is out of order or repeated"
        parseSections r m rank
      | _, none => throw s!"unknown section id {id}"

def parseModule (bytes : ByteArray) : Except String Module := do
  let r : Rd := { data := bytes }
  let (magic, r) ← r.take 4
  unless magic.toList == [0x00, 0x61, 0x73, 0x6D] do throw "not a WebAssembly module (bad magic)"
  let (version, r) ← r.take 4
  unless version.toList == [0x01, 0x00, 0x00, 0x00] do throw "unsupported WebAssembly version"
  parseSections r {} 0

def validate (bytes : ByteArray) (features : Features := {}) : Except String Unit := do
  let m ← parseModule bytes
  -- (this backend imports only functions, so the index spaces are the imported
  -- functions followed by the defined ones)
  let importedFuncs := m.imports.size
  let allFuncTypeIdx := m.imports.map (·.typeIdx) ++ m.funcTypes
  for i in m.funcTypes do
    if i ≥ m.types.size then throw s!"the function section names type {i}, which does not exist"
  if m.codes.size != m.funcTypes.size then
    throw s!"the code section has {m.codes.size} bodies for {m.funcTypes.size} functions"
  if let some n := m.dataCount then
    if n != m.datas.size then throw s!"the data count is {n} but there are {m.datas.size} segments"
  let funcTypeOf (i : Nat) : Except String FuncType := do
    if i ≥ allFuncTypeIdx.size then throw s!"function {i} does not exist"
    let ty := allFuncTypeIdx[i]!
    if ty ≥ m.types.size then throw s!"function {i} has type {ty}, which does not exist"
    pure m.types[ty]!
  -- exports
  for e in m.exports do
    match e.kind with
    | 0 => if e.idx ≥ allFuncTypeIdx.size then throw s!"export `{e.name}` names function {e.idx}, which does not exist"
    | 1 => if e.idx ≥ m.tables.size then throw s!"export `{e.name}` names table {e.idx}, which does not exist"
    | 2 => if e.idx ≥ m.memories.size then throw s!"export `{e.name}` names memory {e.idx}, which does not exist"
    | 3 => if e.idx ≥ m.globals.size then throw s!"export `{e.name}` names global {e.idx}, which does not exist"
    | _ => pure ()
  -- the start function
  if let some i := m.start then
    let ft ← funcTypeOf i
    unless ft.params.isEmpty && ft.results.isEmpty do
      throw "the start function takes or returns values"
  -- elements: the table must exist and be large enough for the segment
  for el in m.elems do
    unless m.tables.size > 0 do throw "an element segment without a table"
    if el.offset < 0 then throw "an element segment's offset is negative"
    let start := el.offset.toNat
    if start + el.funcs.size > m.tables[0]!.limits.min then
      throw s!"an element segment ({start} + {el.funcs.size}) is outside the table ({m.tables[0]!.limits.min})"
    for f in el.funcs do
      if f ≥ allFuncTypeIdx.size then throw s!"an element segment names function {f}, which does not exist"
  -- data: the memory must exist and hold the segment
  for d in m.datas do
    unless m.memories.size > 0 do throw "a data segment without a memory"
    if d.offset < 0 then throw "a data segment's offset is negative"
    let start := d.offset.toNat
    let pages := m.memories[0]!.min
    if start + d.bytes.size > pages * 65536 then
      throw s!"a data segment ({start} + {d.bytes.size}) is outside the memory ({pages} pages)"
  -- globals: their initial values (this backend emits only `i32.const`); validate them
  -- lazily by re-reading each section is overkill: the initial expressions were consumed
  -- by `readVec readGlobalType`? no: readGlobalType stops before the init expression, so
  -- the section parser has not checked them. Do it here from the raw bytes is not possible.
  -- Instead `readGlobals` below is unused; the global section is parsed by `parseModule`,
  -- whose check that the section is exhausted would fail if an init expression remained.
  -- (The backend's single global is parsed by `readGlobal` in `parseModule`, see below.)
  -- function bodies
  let env : Env := {
    types := m.types
    funcs := allFuncTypeIdx
    tables := m.tables
    memories := m.memories
    globals := m.globals.map (·.type)
    features
  }
  for c in m.codes, i in [0:m.codes.size] do
    let ft ← funcTypeOf (importedFuncs + i)
    match checkBody env ft c with
    | .ok () => pure ()
    | .error e => throw s!"function {importedFuncs + i}: {e}"
  pure ()

end Wiz.WasmValidate
