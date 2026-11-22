/-
# `Bpf.Lower`: the restriction pass, typed surface → `BpfCore`

`Wiz.Compiler.IR` has thrown the types away, and `match` on a recursive type is already the
generic `wiz.ind` interpreter (design note §1.2). The eBPF backend therefore cannot read
the IR: it needs the *elaborated* types. `BpfCore` is the typed slice; this module is the
type-directed erasure from the Wiz fragment into it.

P0 boundary, stated honestly: the surface below is the **shape** the restriction pass will
consume (a typed term: every `let` carries its type, every operation carries its width),
and `lowerProgram` is the real erasure. What is missing is the adapter from the
elaborator's `Term R` to `STm`: that needs the elaborator's types and spans and a build to
iterate on, so it is recorded as a P0 roadblock rather than guessed. A `bpf-core/1`
fixture bypasses the adapter for now (`Bpf.Sexp`).

The two rules that make the lowering total:

* **widths are literals** — `UIntN w`/`IntN w`/`BitVec n` are specialised here; a width
  outside `{8,16,32,64}` is a rejection, not a runtime value;
* **`Nat` is compile-time only** — a `Nat` term is accepted only where it folds to a
  literal (a packet offset, a loop bound); elsewhere it is the §4.4 rejection.

The edge cases of §2.6 are rejected here with the stable messages:
`BitVec n` outside `{8,16,32,64}`, signed `/`/`%` (including `INT_MIN / -1`), and a shift
whose count is not a literal below the width (the ISA's 63/31 mask is not Wiz's rule).
-/
import Wiz.Compiler.Bpf.Check

namespace Wiz.Compiler.Bpf

/-! ## The typed surface -/

/-- A surface type: the Wiz types in §4.1, plus enough markers for the constructs that are
rejected (a `List`, a closure, `IO`, …) to name themselves in the diagnostic. -/
inductive STy where
  | unit | bool
  | uint (w : Nat)
  | int (w : Nat)
  | bitvec (n : Nat)
  | enum (n : Nat)
  | struct (fields : Array STy)
  | option (t : STy)
  | packet
  | ctx (kind : ProgKind)
  | map (k v : STy) (kind : MapKind)
  /-- markers for the rejected Wiz types -/
  | nat | string | bytes
  | list (t : STy) | array (t : STy) | ref (t : STy) | task (t : STy)
  | float64
  | io (t : STy)
  | closure
  deriving Repr, BEq, Inhabited

partial def STy.describe : STy → String
  | .unit => "Unit"
  | .bool => "Bool"
  | .uint w => s!"UIntN {w}"
  | .int w => s!"IntN {w}"
  | .bitvec n => s!"BitVec {n}"
  | .enum n => s!"enum {n}"
  | .struct fs => s!"structure ({commaSep (fs.toList.map STy.describe)})"
  | .option t => s!"Option ({t.describe})"
  | .packet => "Packet"
  | .ctx k => s!"{k.describe}Context"
  | .map k v kind => s!"Map ({k.describe}) ({v.describe}) ({kind.describe})"
  | .nat => "Nat"
  | .string => "String"
  | .bytes => "Bytes"
  | .list t => s!"List ({t.describe})"
  | .array t => s!"Array ({t.describe})"
  | .ref t => s!"Ref ({t.describe})"
  | .task t => s!"Task ({t.describe})"
  | .float64 => "Float64"
  | .io t => s!"IO ({t.describe})"
  | .closure => "a function value"

/-- Width-preserving operations on a word. `/` and `%` are the *unsigned* forms; the signed
ones are `IOp` and rejected. -/
inductive UOp where
  | add | sub | mul | div | mod | land | lor | xor
  deriving Repr, BEq, Inhabited

/-- `IntN` operations. `div`/`mod` are present only so the lowering can reject them with
the `INT_MIN / -1` message. -/
inductive IOp where
  | add | sub | mul | div | mod | land | lor | xor
  deriving Repr, BEq, Inhabited

/-- A typed surface term. `at` carries the source position; a nested `at` replaces it for
its subtree. `letE` carries its annotation because that annotation is what makes the core
typed (§4.2: "the type annotation is required"). -/
inductive STm where
  | withSpan (span : Span) (t : STm)
  | var (x : Nat)
  | uintLit (w : Nat) (v : Nat)
  /-- `v` is the two's-complement bit pattern, as `IntN` stores it -/
  | intLit (w : Nat) (v : Nat)
  | bitvecLit (n : Nat) (v : Nat)
  | boolLit (b : Bool)
  /-- a nullary constructor's tag (`XdpAction.pass` is `.enumLit 5 2`) -/
  | enumLit (n : Nat) (tag : Nat)
  | natLit (v : Nat)
  /-- a closed `Nat` operation, accepted only where it folds to a literal -/
  | natOp (op : UOp) (a b : STm)
  | uintOp (w : Nat) (op : UOp) (a b : STm)
  | intOp (w : Nat) (op : IOp) (a b : STm)
  | bitvecOp (n : Nat) (op : UOp) (a b : STm)
  | shift (w : Nat) (left : Bool) (a : STm) (k : Nat)
  | resize (srcW dstW : Nat) (a : STm)
  | eq (a b : STm)
  | lt (signed : Bool) (a b : STm)
  | le (signed : Bool) (a b : STm)
  | ite (c t e : STm)
  | letE (x : Nat) (ty : STy) (v : STm) (body : STm)
  | proj (i : Nat) (s : STm)
  | mkStruct (fs : Array STm)
  | mkSome (t : STm)
  | mkNone (ty : STy)
  | switchOption (s : STm) (onNone : STm) (x : Nat) (onSome : STm)
  | pktLoad (w : Nat) (be : Bool) (p off : STm)
  | ctxPacket (c : STm)
  | ctxIfindex (c : STm)
  | ctxRxQueue (c : STm)
  | mapLookup (m : String) (k : STm)
  | mapUpdate (m : String) (k v : STm)
  | mapDelete (m : String) (k : STm)
  | mapAdd (m : String) (k n : STm)
  | call (f : String) (args : Array STm)
  | helper (h : String) (args : Array STm)
  | ret (t : STm)

def STm.span (t : STm) : Span := match t with | .withSpan s _ => s | _ => {}

/-- Strip the source-position wrapper (only the outermost one is needed by `lowerConst`). -/
def STm.strip : STm → STm
  | .withSpan _ t => t
  | t => t

structure SDecl where
  /-- the Wiz definition name -/
  name : String
  params : Array STy
  ret : STy
  body : STm
  /-- `partial`: rejected outright (§2.1) -/
  isPartial : Bool := false
  span : Span := {}

structure SMapDecl where
  name : String
  kind : MapKind
  key : STy
  value : STy
  maxEntries : Nat
  span : Span := {}

/-- The whole surface program (§5.1's manifest supplies the metadata; the typed terms are
the restriction pass's output). -/
structure SProgram where
  entry : String
  sectionName : String
  kind : ProgKind
  license : String
  version : Nat
  maps : Array SMapDecl
  decls : Array SDecl
  ret : STy
  span : Span := {}

/-! ## Widths and types -/

def lowerUnsigned (span : Span) (w : Nat) : Except String Ty :=
  match Ty.unsignedOf? w with
  | some t => pure t
  | none =>
    if w == 128 then reject span uint128Message
    else reject span (widthMessage w)

def lowerSigned (span : Span) (w : Nat) : Except String Ty :=
  match Ty.signedOf? w with
  | some t => pure t
  | none =>
    if w == 128 then reject span uint128Message
    else reject span s!"`IntN {w}` is not a register width. The eBPF ISA has 8, 16, 32 \
and 64-bit registers; use one of those."

/-- `BitVec n` is a `UIntN n` (lib/BitVec.wiz), but only at a register width: a `u5` is
`u8 & 0x1f` after every operation, which is exactly the lowering that goes quietly wrong
(§4.1). -/
def lowerBitVec (span : Span) (n : Nat) : Except String Ty :=
  match Ty.unsignedOf? n with
  | some t => pure t
  | none => reject span (bitvecMessage n)

partial def lowerTy (span : Span) (t : STy) : Except String Ty := do
  match t with
  | .unit => pure .unit
  | .bool => pure .bool
  | .uint w => lowerUnsigned span w
  | .int w => lowerSigned span w
  | .bitvec n => lowerBitVec span n
  | .enum n =>
    if n == 0 then reject span "an empty enum has no tag" else pure (.enum n)
  | .struct fs =>
    let fields ← fs.toList.mapM (lowerTy span)
    if fields.any (fun f => f == .unit) then
      reject span "a `Unit` struct field has no C representation; remove the field (P0 does \
not erase a field in the middle of a struct)"
    let ty : Ty := .struct fields.toArray
    unless ty.isPod do
      reject span s!"the struct `{ty.describe}` is not plain old data: a value is scalars, \
enums, structs of those, or `Option` of those (no pointer, closure or heap object)"
    match ty.byteSize with
    | none => reject span s!"the struct `{ty.describe}` has no C layout"
    | some n =>
      if n > 64 then
        reject span s!"a value is at most 64 bytes, but `{ty.describe}` is {n}. Split the \
struct or keep the large data in a map."
      else pure ty
  | .option inner =>
    let i ← lowerTy span inner
    if i == .unit then
      reject span "an `Option Unit` has no payload representation; use a `Bool` or a \
nullary enum instead"
    let ty : Ty := .option i
    unless i.isPod do
      reject span s!"`{ty.describe}` wraps a non-POD payload"
    match ty.byteSize with
    | none => reject span s!"`{ty.describe}` has no C layout"
    | some n =>
      if n > 64 then reject span s!"`{ty.describe}` is {n} bytes; a value is at most 64"
      else pure ty
  | .packet => pure .packet
  | .ctx k => pure (.ctx k)
  | .map k v kind => do
    let k ← lowerTy span k
    let v ← lowerTy span v
    pure (.map k v kind)
  | .nat => reject span natMessage
  | .string => reject span stringMessage
  | .bytes => reject span bytesMessage
  | .list _ => reject span listMessage
  | .array _ => reject span arrayMessage
  | .ref _ => reject span refMessage
  | .task _ =>
    reject span "`Task` — a kernel program has no threads or scheduler; the kernel runs \
the program to completion on one packet"
  | .float64 => reject span floatMessage
  | .io _ => reject span ioMessage
  | .closure => reject span closureMessage

/-! ## Closed `Nat` constants -/

/-- Fold a closed `Nat` expression. Only literals and the arithmetic that the header
offsets use (`12 + 2`) are accepted; this is §4.3's "`Nat` is a compile-time type only". -/
partial def lowerConst (span : Span) (t : STm) : Except String Nat := do
  match t.strip with
  | .withSpan s inner => lowerConst s inner
  | .natLit v => pure v
  | .natOp op a b =>
    let x ← lowerConst span a
    let y ← lowerConst span b
    match op with
    | .add => pure (x + y)
    | .sub => pure (x - y)
    | .mul => pure (x * y)
    | _ => reject span "a `Nat` offset is folded with `+`, `-` or `*` only"
  | _ =>
    reject span natMessage

/-! ## Signatures -/

structure Sig where
  params : Array Ty
  ret : Ty

def lowerSig (d : SDecl) : Except String Sig := do
  let params ← d.params.toList.mapM (lowerTy d.span)
  if params.any (fun p => p == .unit) then
    reject d.span s!"`{d.name}` has a `Unit` parameter, which has no C representation"
  let ret ← lowerTy d.span d.ret
  pure { params := params.toArray, ret }

def findSig (sigs : Array (String × Sig)) (f : String) : Option Sig :=
  (sigs.find? fun (n, _) => n == f).map (·.2)

def findMap (maps : Array MapDecl) (span : Span) (m : String) : Except String MapDecl :=
  match maps.find? fun d => d.name == m with
  | some d => pure d
  | none => reject span s!"the map `{m}` is not declared in the manifest"

/-! ## Terms -/

/-- Lower one surface term in the given slot context (`ctx[x]` is the type of `x`). The
`span` is the current source position; an `at` subtree replaces it. -/
partial def lowerTm (maps : Array MapDecl) (sigs : Array (String × Sig))
    (ctx : Array Ty) (span : Span) (t : STm) : Except String Tm := do
  let mk (node : TmNode) : Tm := .mk span node
  match t with
  | .withSpan s inner => lowerTm maps sigs ctx s inner
  | .var x =>
    match ctx[x]? with
    | some ty => pure (mk (.var ty x))
    | none => reject span s!"variable x{x} is not in scope (the context has {ctx.size} slots)"
  | .uintLit w v =>
    let ty ← lowerUnsigned span w
    checkLit ty v span
    pure (mk (.lit ty v))
  | .intLit w v =>
    let ty ← lowerSigned span w
    checkLit ty v span
    pure (mk (.lit ty v))
  | .bitvecLit n v =>
    let ty ← lowerBitVec span n
    checkLit ty v span
    pure (mk (.lit ty v))
  | .boolLit b =>
    pure (mk (.lit .bool (if b then 1 else 0)))
  | .enumLit n tag =>
    let ty ← lowerTy span (.enum n)
    checkLit ty tag span
    pure (mk (.lit ty tag))
  | .natLit _ => reject span natMessage
  | .natOp _ _ _ => reject span natMessage
  | .uintOp w op a b =>
    let ty ← lowerUnsigned span w
    let a ← lowerTm maps sigs ctx span a
    let b ← lowerTm maps sigs ctx span b
    unless a.ty == ty do
      reject span s!"the left operand of `UIntN {w}` is `{a.ty.describe}`"
    unless b.ty == ty do
      reject span s!"the right operand of `UIntN {w}` is `{b.ty.describe}`"
    let bop ← match op with
      | .add => pure .add | .sub => pure .sub | .mul => pure .mul
      | .div => pure .div | .mod => pure .mod
      | .land => pure .land | .lor => pure .lor | .xor => pure .xor
    pure (mk (.bin ty bop a b))
  | .intOp w op a b =>
    match op with
    | .div | .mod => reject span signedDivMessage
    | _ =>
      let ty ← lowerSigned span w
      let a ← lowerTm maps sigs ctx span a
      let b ← lowerTm maps sigs ctx span b
      unless a.ty == ty do
        reject span s!"the left operand of `IntN {w}` is `{a.ty.describe}`"
      unless b.ty == ty do
        reject span s!"the right operand of `IntN {w}` is `{b.ty.describe}`"
      let bop ← match op with
        | .add => pure .add | .sub => pure .sub | .mul => pure .mul
        | .land => pure .land | .lor => pure .lor | .xor => pure .xor
        | .div | .mod => pure .add -- unreachable: rejected above
      pure (mk (.bin ty bop a b))
  | .bitvecOp n op a b =>
    let ty ← lowerBitVec span n
    let a ← lowerTm maps sigs ctx span a
    let b ← lowerTm maps sigs ctx span b
    unless a.ty == ty do reject span s!"the left operand of `BitVec {n}` is `{a.ty.describe}`"
    unless b.ty == ty do reject span s!"the right operand of `BitVec {n}` is `{b.ty.describe}`"
    let bop ← match op with
      | .add => pure .add | .sub => pure .sub | .mul => pure .mul
      | .div => pure .div | .mod => pure .mod
      | .land => pure .land | .lor => pure .lor | .xor => pure .xor
    pure (mk (.bin ty bop a b))
  | .shift w left a k =>
    let ty ← lowerUnsigned span w
    if k >= w then reject span (shiftMessage w k)
    let a ← lowerTm maps sigs ctx span a
    unless a.ty == ty do reject span s!"the operand of a `UIntN {w}` shift is `{a.ty.describe}`"
    let amount : Tm := .mk span (.lit ty k)
    pure (mk (.bin ty (if left then .shl else .shr) a amount))
  | .resize srcW dstW a =>
    let fty ← lowerUnsigned span srcW
    let tty ← lowerUnsigned span dstW
    let a ← lowerTm maps sigs ctx span a
    unless a.ty == fty do
      reject span s!"`UIntN.resize {srcW} {dstW}` of a `{a.ty.describe}`"
    pure (mk (.cast tty fty a))
  | .eq a b =>
    let a ← lowerTm maps sigs ctx span a
    let b ← lowerTm maps sigs ctx span b
    unless a.ty == b.ty do
      reject span s!"the operands of `==` are `{a.ty.describe}` and `{b.ty.describe}`"
    pure (mk (.cmp .eq a b))
  | .lt signed a b =>
    let a ← lowerTm maps sigs ctx span a
    let b ← lowerTm maps sigs ctx span b
    unless a.ty == b.ty do
      reject span s!"the operands of a comparison are `{a.ty.describe}` and `{b.ty.describe}`"
    match a.ty.width with
    | none => reject span s!"`<`/`<=` need a word, not `{a.ty.describe}`"
    | some _ =>
      if signed != a.ty.isSigned then
        reject span s!"the comparison's signedness does not match `{a.ty.describe}`"
      pure (mk (.cmp .lt a b))
  | .le signed a b =>
    let a ← lowerTm maps sigs ctx span a
    let b ← lowerTm maps sigs ctx span b
    unless a.ty == b.ty do
      reject span s!"the operands of a comparison are `{a.ty.describe}` and `{b.ty.describe}`"
    match a.ty.width with
    | none => reject span s!"`<`/`<=` need a word, not `{a.ty.describe}`"
    | some _ =>
      if signed != a.ty.isSigned then
        reject span s!"the comparison's signedness does not match `{a.ty.describe}`"
      pure (mk (.cmp .le a b))
  | .ite c a b =>
    let c ← lowerTm maps sigs ctx span c
    unless c.ty == .bool do reject span s!"an `if` condition is `Bool`, not `{c.ty.describe}`"
    let a ← lowerTm maps sigs ctx span a
    let b ← lowerTm maps sigs ctx span b
    unless a.ty == b.ty do
      reject span s!"the branches of an `if` are `{a.ty.describe}` and `{b.ty.describe}`"
    pure (mk (.ite a.ty c a b))
  | .letE x sty v body =>
    let ty ← lowerTy span sty
    if ty == .unit then
      reject span "a `Unit` binding has no C representation; bind the value the program uses"
    match ty with
    | .map _ _ _ =>
      reject span "a map is a handle, not a value: it cannot be bound, stored or returned"
    | _ => pure ()
    let v ← lowerTm maps sigs ctx span v
    unless v.ty == ty do
      reject span s!"`let x{x} : {sty.describe}` is bound a `{v.ty.describe}`"
    unless x == ctx.size do
      reject span s!"the binder x{x} is not the next slot (the context has {ctx.size})"
    let body ← lowerTm maps sigs (ctx.push ty) span body
    pure (mk (.letE ty x v body))
  | .proj i s =>
    let s ← lowerTm maps sigs ctx span s
    match s.ty with
    | .struct fs =>
      match fs[i]? with
      | none => reject span s!"field {i} of `{s.ty.describe}` (it has {fs.size})"
      | some ty => pure (mk (.proj ty i s))
    | other => reject span s!"`.{i}` needs a struct, not `{other.describe}`"
  | .mkStruct fs =>
    let fields ← fs.toList.mapM (lowerTm maps sigs ctx span)
    let ty : Ty := .struct (fields.toArray.map (·.ty))
    unless ty.isPod do reject span "a struct value is plain old data"
    match ty.byteSize with
    | none => reject span s!"`{ty.describe}` has no layout"
    | some n =>
      if n > 64 then reject span s!"`{ty.describe}` is {n} bytes; a value is at most 64"
      else pure (mk (.mkStruct ty fields.toArray))
  | .mkSome v =>
    let v ← lowerTm maps sigs ctx span v
    let ty : Ty := .option v.ty
    match ty.byteSize with
    | none => reject span s!"`{ty.describe}` has no layout"
    | some n =>
      if n > 64 then reject span s!"`{ty.describe}` is {n} bytes; a value is at most 64"
      else pure (mk (.mkSome ty v))
  | .mkNone sty =>
    let ty ← lowerTy span sty
    match ty.optionInner with
    | some _ => pure (mk (.mkNone ty))
    | none => reject span s!"`none` needs an `Option`, not `{sty.describe}`"
  | .switchOption s onNone x onSome =>
    let s ← lowerTm maps sigs ctx span s
    match s.ty.optionInner with
    | none => reject span s!"`match` on an `Option` needs an `Option`, not `{s.ty.describe}`"
    | some inner =>
      let onNone ← lowerTm maps sigs ctx span onNone
      unless x == ctx.size do
        reject span s!"the `some` binder x{x} is not the next slot (the context has {ctx.size})"
      let onSome ← lowerTm maps sigs (ctx.push inner) span onSome
      unless onNone.ty == onSome.ty do
        reject span s!"the arms of a `match` are `{onNone.ty.describe}` and `{onSome.ty.describe}`"
      pure (mk (.switchOption onNone.ty s onNone x onSome))
  | .pktLoad w be p off =>
    let ty ← match Ty.unsignedOf? w with
      | some u => pure (.option u)
      | none => reject span s!"a packet load is 8, 16, 32 or 64 bits, not {w}"
    let p ← lowerTm maps sigs ctx span p
    unless p.ty == .packet do
      reject span s!"a packet load's scrutinee is `Packet`, not `{p.ty.describe}`"
    let off ← match off.strip with
      | .natLit _ | .natOp _ _ _ =>
        let v ← lowerConst span off
        if v < Nat.pow 2 32 then pure (.mk span (.lit .u32 v))
        else reject span s!"the packet offset {v} does not fit `UIntN 32`"
      | _ =>
        let tm ← lowerTm maps sigs ctx span off
        if tm.ty == .u32 then pure tm
        else reject span s!"a packet offset is `UIntN 32`, not `{tm.ty.describe}`"
    pure (mk (.pktLoad ty w be p off))
  | .ctxPacket c =>
    let c ← lowerTm maps sigs ctx span c
    match c.ty with
    | .ctx _ => pure (mk (.ctxPacket c))
    | other => reject span s!"`XdpContext.packet` needs a context, not `{other.describe}`"
  | .ctxIfindex c =>
    let c ← lowerTm maps sigs ctx span c
    match c.ty with
    | .ctx _ => pure (mk (.ctxIfindex c))
    | other => reject span s!"a context projection needs a context, not `{other.describe}`"
  | .ctxRxQueue c =>
    let c ← lowerTm maps sigs ctx span c
    match c.ty with
    | .ctx _ => pure (mk (.ctxRxQueue c))
    | other => reject span s!"a context projection needs a context, not `{other.describe}`"
  | .mapLookup m k =>
    let d ← findMap maps span m
    let k ← lowerTm maps sigs ctx span k
    unless k.ty == d.key do
      reject span s!"`{m}`'s key is `{d.key.describe}`, not `{k.ty.describe}`"
    pure (mk (.mapLookup (.option d.value) m k))
  | .mapUpdate m k v =>
    let d ← findMap maps span m
    let k ← lowerTm maps sigs ctx span k
    let v ← lowerTm maps sigs ctx span v
    unless k.ty == d.key do
      reject span s!"`{m}`'s key is `{d.key.describe}`, not `{k.ty.describe}`"
    unless v.ty == d.value do
      reject span s!"`{m}`'s value is `{d.value.describe}`, not `{v.ty.describe}`"
    pure (mk (.mapUpdate .bool m k v))
  | .mapDelete m k =>
    let d ← findMap maps span m
    let k ← lowerTm maps sigs ctx span k
    unless k.ty == d.key do
      reject span s!"`{m}`'s key is `{d.key.describe}`, not `{k.ty.describe}`"
    pure (mk (.mapDelete .bool m k))
  | .mapAdd m k n =>
    let d ← findMap maps span m
    let k ← lowerTm maps sigs ctx span k
    let n ← lowerTm maps sigs ctx span n
    unless k.ty == d.key do
      reject span s!"`{m}`'s key is `{d.key.describe}`, not `{k.ty.describe}`"
    unless d.value == .u64 do
      reject span s!"`Map.add {m}` needs a `UIntN 64` value, but `{m}` stores \
`{d.value.describe}`"
    unless n.ty == .u64 do
      reject span s!"`Map.add`'s count is `UIntN 64`, not `{n.ty.describe}`"
    pure (mk (.mapAdd .u64 m k n))
  | .call f args =>
    let some sig := findSig sigs f |
      reject span s!"the call to `{f}` has no definition in this program"
    if args.size != sig.params.size then
      reject span s!"`{f}` takes {sig.params.size} arguments, not {args.size}"
    let args ← args.toList.mapM (lowerTm maps sigs ctx span)
    for i in [0:sig.params.size] do
      unless args[i]!.ty == sig.params[i]! do
        reject span s!"argument {i + 1} of `{f}` is `{args[i]!.ty.describe}`, not \
`{sig.params[i]!.describe}`"
    pure (mk (.call sig.ret f args.toArray))
  | .helper h args =>
    let some d := Helpers.find? h |
      reject span s!"`{h}` is not in the P0 helper table"
    if args.size != d.args.size then
      reject span s!"`{h}` takes {d.args.size} arguments, not {args.size}"
    let args ← args.toList.mapM (lowerTm maps sigs ctx span)
    for i in [0:d.args.size] do
      unless args[i]!.ty == d.args[i]! do
        reject span s!"argument {i + 1} of `{h}` is `{args[i]!.ty.describe}`, not \
`{d.args[i]!.describe}`"
    pure (mk (.helper d.res d args.toArray))
  | .ret v =>
    let v ← lowerTm maps sigs ctx span v
    pure (mk (.ret v))

/-! ## Declarations and the program -/

def lowerDecl (maps : Array MapDecl) (sigs : Array (String × Sig)) (d : SDecl) :
    Except String Decl := do
  if d.isPartial then reject d.span (partialMessage d.name)
  let params ← d.params.toList.mapM (lowerTy d.span)
  let ret ← lowerTy d.span d.ret
  let body ← lowerTm maps sigs params.toArray d.span d.body
  pure { name := d.name, params := params.toArray, ret, body }

/-- Lower the whole surface program, then run the checker. The checker is the gate even
for a program that came through this function: the lowering is not assumed correct. -/
def lowerProgram (p : SProgram) : Except String Program := do
  for d in p.decls.toList do
    if d.isPartial then reject d.span (partialMessage d.name)
  let sigs ← p.decls.toList.mapM fun d => do
    let s ← lowerSig d
    pure ((d.name, s) : String × Sig)
  let maps ← p.maps.toList.mapM fun m => do
    let key ← lowerTy m.span m.key
    let value ← lowerTy m.span m.value
    pure ({ name := m.name, kind := m.kind, key, value, maxEntries := m.maxEntries } : MapDecl)
  let ret ← lowerTy p.span p.ret
  let decls ← p.decls.toList.mapM (lowerDecl maps.toArray sigs.toArray)
  let prog : Program :=
    { entry := p.entry
      sectionName := p.sectionName
      kind := p.kind
      license := p.license
      version := p.version
      maps := maps.toArray
      decls := decls.toArray
      ret }
  checkProgram prog
  pure prog

end Wiz.Compiler.Bpf
