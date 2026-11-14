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
  /-- a runtime operation: `nat.add` …, `lazyTag` -/
  | prim (op : Name) (args : Array Var)
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

/-- Native operations that only look at their arguments (comparisons): they **borrow**
them, like a borrowed parameter, so the caller keeps its references (a key compared
during a lookup is neither incremented nor decremented). Every other native operation
consumes its arguments. -/
def primBorrows (op : Name) : Bool :=
  op == "nat.beq" || op == "nat.blt"

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
  | prim op as => s!"prim {op} {vs as}"
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
