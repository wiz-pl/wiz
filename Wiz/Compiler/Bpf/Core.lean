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

/-- The context a program is compiled against. Only XDP and TC in P0-P2 (tracing needs
CO-RE, which this path deliberately avoids). -/
inductive ProgKind where
  | xdp
  | tc
  deriving Repr, BEq, Inhabited

/-- The ELF section name libbpf expects. -/
def ProgKind.elfSection : ProgKind → String
  | .xdp => "xdp"
  | .tc => "classifier"

/-- Accept the section spellings of §5.2 (and libbpf's `sched_cls` alias). -/
def ProgKind.ofSection? : String → Option ProgKind
  | "xdp" => some .xdp
  | "tc" | "classifier" | "sched_cls" => some .tc
  | _ => none

/-- The eBPF program type libbpf derives from the section. -/
def ProgKind.typeName : ProgKind → String
  | .xdp => "xdp"
  | .tc => "sched_cls"

/-- For diagnostics: the Wiz-level name of the context/program kind. -/
def ProgKind.describe : ProgKind → String
  | .xdp => "XDP"
  | .tc => "TC"

/-! ## Maps -/

inductive MapKind where
  | hash
  | array
  | percpuArray
  | lruHash
  deriving Repr, BEq, Inhabited

def MapKind.cName : MapKind → String
  | .hash => "BPF_MAP_TYPE_HASH"
  | .array => "BPF_MAP_TYPE_ARRAY"
  | .percpuArray => "BPF_MAP_TYPE_PERCPU_ARRAY"
  | .lruHash => "BPF_MAP_TYPE_LRU_HASH"

def MapKind.describe : MapKind → String
  | .hash => "hash"
  | .array => "array"
  | .percpuArray => "percpu_array"
  | .lruHash => "lru_hash"

/-- The limits of §2.7/§6.1: a key is at most 64 B, a value at most 512 B, and an
`array`'s key is the entry index. -/
def MapKind.arrayLike : MapKind → Bool
  | .array | .percpuArray => true
  | _ => false

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
  | .u32 | .i32 => 4
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
  | .packet | .ctx _ | .map _ _ _ => none
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
  deriving Repr, Inhabited

namespace Helpers

/-- P0's non-map helpers. Map helpers are not here: `Map.lookup` and friends are
operations with map types, and the copy/null-test shape is the emitter's. -/
def table : Array Helper := #[
  { name := "Bpf.now", id := 5, args := #[], res := .u64, eff := .time, since := 5 },
  { name := "Bpf.random", id := 7, args := #[], res := .u32, eff := .random, since := 4 }
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
  /-- the program's result type; must be an enum (the action) -/
  ret : Ty

def Program.decl? (p : Program) (n : String) : Option Decl :=
  p.decls.find? fun d => d.name == n

def Program.map? (p : Program) (n : String) : Option MapDecl :=
  p.maps.find? fun m => m.name == n

/-- The entry declaration, if the name resolves. -/
def Program.entryDecl? (p : Program) : Option Decl := p.decl? p.entry

/-! ## The action enums (§5.2) -/

/-- XDP: `aborted = 0, drop = 1, pass = 2, tx = 3, redirect = 4`; P0-P2 allows the first
three. TC: `ok = 0, shot = 2, redirect = 7`. The core only sees the arity (the tag is a
number); the loader sees the values through `XdpAction`/`TcAction` in `bpf_rt.h`. -/
def xdpActionArity : Nat := 5
def tcActionArity : Nat := 8

end Wiz.Compiler.Bpf
