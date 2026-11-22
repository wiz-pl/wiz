import Wiz.Compiler.Erase

/-!
# The IR

A first-order language in A-normal form, the input of the backends (stage 8). Every
intermediate value has a name, functions are top level (lambdas are lifted, so closures
are explicit: `pap f xs` is `f` partially applied), and control flow is `case` on a
tag, join points and tail jumps.

Values are **objects** (a tag and fields, reference counted) or **scalars**: numbers,
`◾`, and constructors without fields (`ctor t #[]` is the scalar `t`, so tags cost no
allocation). Following Perceus (Reinking, Xie, de Moura & Leijen, *Perceus: Garbage
Free Reference Counting with Reuse*, PLDI 2021), reference counts are explicit:
`dup x` and `drop x`, inserted by `RC.lean`. A variable is **owned** (using it as an
argument transfers that reference) or **borrowed** (stage 8e: a parameter marked `@&`,
whose reference the caller keeps, or a field of a borrowed object). `proj` reads a
field without a new reference.
-/

namespace Wiz.IR

abbrev Var := Nat
abbrev JoinId := Nat

/-- The typed key of an IR primitive. `extern` carries the whole foreign-function key
(`extern:cname:kinds:result:io:header:finalizer`), because a program registers its own
foreign functions. Every other operation is a constructor, so a backend's dispatch is an
exhaustive match rather than a string comparison. -/
inductive PrimOp where
  | natZero | natSucc | natPred | natAdd | natSub | natMul | natBeq | natBlt
  | natDiv | natMod | natPow | natLand | natLor | natXor | natShiftLeft | natShiftRight
  | natLog2
  | memo
  | lazyTag | lazySet
  | tag | natTag | fieldAt | mkObj
  | dropMoved
  /-- a registered foreign function: the key is the `extern:` key itself -/
  | extern (key : Name)
  deriving Repr, BEq, Inhabited

/-- Which code generator a primitive table belongs to. -/
inductive Backend where
  | c
  | llvm
  | wasm
  deriving Repr, BEq, Inhabited

/-- One entry of a backend's primitive table: the typed key, the backend, the number of
run-time arguments and whether the operation borrows them, and the runtime function that
lowers it. The table is the single source of truth for the backend's dispatch; an
operation absent from it is a compile-time error, not a `wiz_unknown_prim` call. -/
structure PrimEntry where
  /-- the external key (what the IR prints and the caches used to see) -/
  key : Name
  prim : PrimOp
  backend : Backend
  arity : Nat
  borrows : Bool
  symbol : String
  deriving Repr, Inhabited

namespace PrimOp

/-- The external name of a primitive (the same text the IR used to carry). -/
def key : PrimOp → Name
  | .natZero => "nat.zero"
  | .natSucc => "nat.succ"
  | .natPred => "nat.pred"
  | .natAdd => "nat.add"
  | .natSub => "nat.sub"
  | .natMul => "nat.mul"
  | .natBeq => "nat.beq"
  | .natBlt => "nat.blt"
  | .natDiv => "nat.div"
  | .natMod => "nat.mod"
  | .natPow => "nat.pow"
  | .natLand => "nat.land"
  | .natLor => "nat.lor"
  | .natXor => "nat.xor"
  | .natShiftLeft => "nat.shiftLeft"
  | .natShiftRight => "nat.shiftRight"
  | .natLog2 => "nat.log2"
  | .memo => "memo"
  | .lazyTag => "lazyTag"
  | .lazySet => "lazySet"
  | .tag => "tag"
  | .natTag => "natTag"
  | .fieldAt => "fieldAt"
  | .mkObj => "mkObj"
  | .dropMoved => "dropMoved"
  | .extern k => k

/-- The closed primitives, by their external name. Foreign functions are not here: the
caller parses the `extern:` key (it needs the signature) and builds `.extern`. -/
def ofKey? : Name → Option PrimOp
  | "nat.zero" => some .natZero
  | "nat.succ" => some .natSucc
  | "nat.pred" => some .natPred
  | "nat.add" => some .natAdd
  | "nat.sub" => some .natSub
  | "nat.mul" => some .natMul
  | "nat.beq" => some .natBeq
  | "nat.blt" => some .natBlt
  | "nat.div" => some .natDiv
  | "nat.mod" => some .natMod
  | "nat.pow" => some .natPow
  | "nat.land" => some .natLand
  | "nat.lor" => some .natLor
  | "nat.xor" => some .natXor
  | "nat.shiftLeft" => some .natShiftLeft
  | "nat.shiftRight" => some .natShiftRight
  | "nat.log2" => some .natLog2
  | "memo" => some .memo
  | "lazyTag" => some .lazyTag
  | "lazySet" => some .lazySet
  | "tag" => some .tag
  | "natTag" => some .natTag
  | "fieldAt" => some .fieldAt
  | "mkObj" => some .mkObj
  | "dropMoved" => some .dropMoved
  | _ => none

/-- Is this one of the native number operations (`nat.…`)? -/
def isNat : PrimOp → Bool
  | .natZero | .natSucc | .natPred | .natAdd | .natSub | .natMul | .natBeq | .natBlt
  | .natDiv | .natMod | .natPow | .natLand | .natLor | .natXor | .natShiftLeft
  | .natShiftRight | .natLog2 => true
  | _ => false

/-- The number of run-time arguments of a closed primitive. (An `extern`'s arity comes
from its signature: `RVal.nativeArity`, which also counts the `IO` world.) -/
def arity : PrimOp → Nat
  | .natZero => 0
  | .natSucc | .natPred | .natLog2 | .lazyTag | .tag | .natTag => 1
  | .extern _ => 2
  | _ => 2

/-- Operations that only inspect their arguments: they borrow, so the caller keeps its
references. This used to be a name list in `IR.lean`; it is now metadata of the table. -/
def borrows : PrimOp → Bool
  | .natBeq | .natBlt | .tag | .natTag => true
  | _ => false

/-- A C identifier for a Wiz name: letters and digits stay, anything else is `_xx`. -/
def mangle (n : Name) : String :=
  "w_" ++ String.join (n.toList.map fun c =>
    if c.isAlphanum then c.toString
    else "_" ++ (Nat.toDigits 16 c.toNat).asString ++ "_")

/-- The C wrapper of a foreign function. -/
def externWrapper (key : Name) : String := "wiz_ext" ++ (mangle key).drop 1

/-- The runtime symbols of the closed primitives (all backends call the same runtime).
`nat.zero` is absent: it lowers to the literal `0`, never to a call. -/
def runtimeSymbols : List (PrimOp × String) :=
  [ (.natSucc, "wiz_nat_succ"), (.natPred, "wiz_nat_pred"),
    (.natAdd, "wiz_nat_add"), (.natSub, "wiz_nat_sub"), (.natMul, "wiz_nat_mul"),
    (.natBeq, "wiz_nat_beq"), (.natBlt, "wiz_nat_blt"),
    (.natDiv, "wiz_nat_div"), (.natMod, "wiz_nat_mod"), (.natPow, "wiz_nat_pow"),
    (.natLand, "wiz_nat_land"), (.natLor, "wiz_nat_lor"), (.natXor, "wiz_nat_xor"),
    (.natShiftLeft, "wiz_nat_shiftLeft"), (.natShiftRight, "wiz_nat_shiftRight"),
    (.natLog2, "wiz_nat_log2"),
    (.memo, "wiz_memo"), (.lazyTag, "wiz_lazy_tag"), (.lazySet, "wiz_lazy_set"),
    (.tag, "wiz_tag_of"), (.natTag, "wiz_nat_tag"), (.fieldAt, "wiz_field_at"),
    (.mkObj, "wiz_mk_obj"), (.dropMoved, "wiz_drop_moved") ]

/-- A backend's table: one entry per closed primitive, stamped with the backend. -/
def table (backend : Backend) : List PrimEntry :=
  runtimeSymbols.map fun (p, symbol) =>
    { key := p.key, prim := p, backend, arity := p.arity, borrows := p.borrows, symbol }

/-- The lowering of `p` in `backend`, from that backend's checked table. `none` means
the backend must report an error: it never emits a `wiz_unknown_prim` call. -/
def symbol? (backend : Backend) (p : PrimOp) : Option String :=
  match p with
  | .extern key => some (externWrapper key)
  | _ => (table backend).find? (fun e => e.prim == p) |>.map (·.symbol)

end PrimOp

inductive Expr where
  /-- `◾`, a scalar -/
  | erased
  /-- a number (a scalar, or a big number object) -/
  | lit (n : Nat)
  /-- an object with a tag and fields; with no fields, the scalar `tag` -/
  | ctor (tag : Nat) (args : Array Var)
  /-- field `i` of `x` (borrowed from `x`: no new reference) -/
  | proj (i : Nat) (x : Var)
  /-- full application of a top-level function -/
  | fap (f : Name) (args : Array Var)
  /-- partial application: a closure -/
  | pap (f : Name) (args : Array Var)
  /-- apply a closure -/
  | ap (f : Var) (args : Array Var)
  /-- a runtime operation, a checked key of the backend's primitive table -/
  | prim (op : PrimOp) (args : Array Var)
  /-- (8c) drop `x`, but if it was unique keep its memory as a *reuse token* -/
  | reset (x : Var)
  /-- (8c) `ctor tag args`, in the token's memory if it has the right size -/
  | reuse (tok : Var) (tag : Nat) (args : Array Var)
  deriving Repr, Inhabited, BEq

inductive Body where
  | vdecl (x : Var) (e : Expr) (b : Body)
  /-- branch on the tag of `x` (an object's tag, or a scalar's value) -/
  | case (x : Var) (alts : Array Body)
  | ret (x : Var)
  /-- `join j(params) := body; k`: `body` may only use its parameters -/
  | jdecl (j : JoinId) (params : Array Var) (body : Body) (k : Body)
  | jmp (j : JoinId) (args : Array Var)
  | dup (x : Var) (b : Body)
  | drop (x : Var) (b : Body)
  | unreachable
  deriving Repr, Inhabited

structure Decl where
  name : Name
  params : Array Var
  body : Body
  /-- which parameters are borrowed (stage 8e; empty: all owned) -/
  borrow : Array Bool := #[]
  deriving Repr, Inhabited

namespace Expr

/-- Native operations that only look at their arguments: the **comparisons** and the
**tag inspections** (`tag`, `natTag`). They borrow their arguments, like a borrowed
parameter, so the caller keeps its references (a key compared during a lookup, or the
scrutinee of a `match`, is neither incremented nor decremented). Every other native
operation consumes its arguments. -/
def primBorrows (op : PrimOp) : Bool :=
  op.borrows

def args : Expr → Array Var
  | ctor _ as | fap _ as | pap _ as | prim _ as => as
  | ap f as => #[f] ++ as
  | proj _ x | reset x => #[x]
  | reuse tok _ as => #[tok] ++ as
  | _ => #[]

def toString : Expr → String
  | erased => "◾"
  | lit n => s!"{n}"
  | ctor t as => if as.isEmpty then s!"{t}" else s!"ctor {t} {vs as}"
  | proj i x => s!"proj {i} x{x}"
  | fap f as => s!"{f} {vs as}"
  | pap f as => s!"pap {f} {vs as}"
  | ap f as => s!"ap x{f} {vs as}"
  | prim op as => s!"prim {op.key} {vs as}"
  | reset x => s!"reset x{x}"
  | reuse tok t as => s!"reuse x{tok} in ctor {t} {vs as}"
where
  vs (as : Array Var) : String := " ".intercalate (as.toList.map (s!"x{·}"))

end Expr

namespace Body

/-- The free variables of a body. -/
partial def freeVars (b : Body) : Std.HashSet Var :=
  go b {}
where
  go : Body → Std.HashSet Var → Std.HashSet Var
    | vdecl x e b, acc => (e.args.foldl (·.insert ·) ((go b acc).erase x))
    | case x alts, acc => alts.foldl (fun acc a => go a acc) (acc.insert x)
    | ret x, acc => acc.insert x
    | jdecl _ ps body k, acc =>
      let accB := ps.foldl (·.erase ·) (go body {})
      accB.fold (·.insert ·) (go k acc)
    | jmp _ as, acc => as.foldl (·.insert ·) acc
    | dup x b, acc | drop x b, acc => (go b acc).insert x
    | unreachable, acc => acc

partial def toString (b : Body) (ind : String := "  ") : String :=
  match b with
  | vdecl x e b => s!"{ind}let x{x} := {e.toString}\n{b.toString ind}"
  | case x alts =>
    let as := alts.toList.zipIdx.map fun (a, i) => s!"{ind}| {i} =>\n{a.toString (ind ++ "    ")}"
    s!"{ind}case x{x} of\n{"\n".intercalate as}"
  | ret x => s!"{ind}ret x{x}"
  | jdecl j ps body k =>
    s!"{ind}join j{j}({Expr.toString.vs ps}) :=\n{body.toString (ind ++ "    ")}\n{k.toString ind}"
  | jmp j as => s!"{ind}jmp j{j} {Expr.toString.vs as}"
  | dup x b => s!"{ind}dup x{x}\n{b.toString ind}"
  | drop x b => s!"{ind}drop x{x}\n{b.toString ind}"
  | unreachable => s!"{ind}unreachable"

end Body

def Decl.toString (d : Decl) : String :=
  let ps := d.params.zipIdx.toList.map fun (p, i) => if d.borrow[i]?.getD false then s!"@&x{p}" else s!"x{p}"
  s!"def {d.name} {" ".intercalate ps} :=\n{d.body.toString}"

/-! ### Closed definitions (CAFs)

A top-level function without parameters (after erasure) is a *constant applicative form*,
as in GHC and Lean: its body is the same value at every use. The native backends compute
it on its first use and keep it for the rest of the run (immortal, never freed: see
`wiz_caf_init` in `runtime/`). Lazily, never at startup, so a definition that is never
used is never computed, even one that diverges or is huge. A value of type `IO A` is a
function of the world: its body builds a closure (or is a function with a parameter), so
caching it does not run it.

Not cached: `wiz.entry` (run once, by `main`), the exported functions' closures, the
wrappers of foreign functions (a foreign function without arguments is called each time,
as written), and bodies that do no work, whose value is cheaper to rebuild than to look
up: scalars, and calls of other constants (which are cached themselves). -/

/-- Is `e` work worth caching? (Allocations and calls; `zeroParam` are the functions
without parameters, whose calls are lookups or cheap themselves.) -/
def Expr.isWork (zeroParam : Name → Bool) : Expr → Bool
  | .erased | .proj .. => false
  | .lit n => n ≥ 2 ^ 62
  | .ctor _ as => !as.isEmpty
  | .fap f _ => !zeroParam f
  | .pap .. | .ap .. | .prim .. | .reset _ | .reuse .. => true

/-- Does a body do work worth caching? -/
partial def Body.isWork (zeroParam : Name → Bool) : Body → Bool
  | .vdecl _ e b => e.isWork zeroParam || b.isWork zeroParam
  | .case _ alts => alts.any (·.isWork zeroParam)
  | .jdecl _ _ jb k => jb.isWork zeroParam || k.isWork zeroParam
  | .dup _ b | .drop _ b => b.isWork zeroParam
  | .ret _ | .jmp .. | .unreachable => false

/-- Excluded from caching whatever their body: run once, or called for their effect. -/
def cafExcluded (n : Name) : Bool :=
  n == "wiz.entry" || n.startsWith "wiz.export." || n.startsWith "wiz.native."

/-- The closed definitions whose values the native backends cache. -/
def cafs (decls : Array Decl) : Std.HashSet Name :=
  let zero : Std.HashSet Name := decls.foldl (fun s d =>
    if d.params.isEmpty && !cafExcluded d.name then s.insert d.name else s) {}
  decls.foldl (fun s d =>
    if zero.contains d.name && d.body.isWork zero.contains then s.insert d.name else s) {}

end Wiz.IR
