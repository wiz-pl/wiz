import Wiz.Compiler.IR
import Wiz.Compiler.Run
import Std.Data.TreeMap

/-!
# Simplification of the IR (stage 15c)

Run on every function right after lowering, before constants are hoisted and before
reference counting (so variables can still be renamed freely):

* **Constant folding.** A native operation on numbers whose arguments are known
  literals is computed at compile time, with the kernel's own semantics
  (`natNative?`: truncated subtraction, `n / 0 = 0`, …); `nat.beq`/`nat.blt` give the
  `Bool` tag. A test of a variable against itself is known too. (`nat.pow` and
  `nat.shiftLeft` are folded only while the result stays small.)
* **Case of a known constructor.** `case x` where `x` is known — bound to `ctor t …`,
  to a literal, or already tested by an enclosing `case x` — is replaced by branch `t`.
  A projection of a known constructor is its field (the variable is renamed).
* **What a branch learns.** In branch `0` of `case (natTag y)`, `y` is `0`; in branch
  `1` (`true`) of `case (nat.beq y z)`, `y` and `z` are equal, so a literal one makes the
  other a literal too. Later folds use that.

The results that become unused are removed by `elimDead` (`Reuse.lean`), which counts
these operations as pure.

* **Self tail calls as loops** (stage 15f). A function `f ps` whose body calls `f`
  in tail position (`let r := f as; ret r`) becomes a join point
  `join J(ps') := body[ps ↦ ps', f as ↦ jmp J as]; jmp J ps` (with fresh parameters `ps'`): the
  backends emit join points as labels and jumps (C `goto`, LLVM `br`), so the
  recursion is a loop and uses constant stack, whatever the C compiler does.
-/

namespace Wiz.IR

/-- The order of the keys of `SimpEnv.projs`. -/
def compareProj (a b : Nat × Var) : Ordering :=
  (compare a.2 b.2).then (compare a.1 b.1)

/-- What is known about the variables in scope. Persistent trees, not hash maps: the
branches of a `case` each extend the same environment, and a shared hash map is copied
whole on insertion (quadratic memory in the nesting depth). -/

structure SimpEnv where
  /-- renamings (a projection of a known constructor is its field) -/
  σ : Std.TreeMap Var Var := ∅
  /-- the (simplified) bindings -/
  defs : Std.TreeMap Var Expr := ∅
  /-- variables known to be these numbers -/
  lits : Std.TreeMap Var Nat := ∅
  /-- variables already tested by an enclosing `case`: the branch taken -/
  tags : Std.TreeMap Var Nat := ∅
  /-- the projections already bound (field, object) ↦ variable, on the path from the
  function's start: a projection computed again is renamed to the first one -/
  projs : Std.TreeMap (Nat × Var) Var compareProj := ∅
  deriving Inhabited

/-- Lazy objects (`coit`, `scofix`: tags from 1000) are overwritten when observed
(`lazySet`), so their fields are not known. -/
def lazyTagBase : Nat := 1000

namespace SimpEnv

def r (env : SimpEnv) (x : Var) : Var := env.σ.getD x x

def renameE (env : SimpEnv) : Expr → Expr
  | .ctor t as => .ctor t (as.map env.r)
  | .proj i x => .proj i (env.r x)
  | .fap f as => .fap f (as.map env.r)
  | .pap f as => .pap f (as.map env.r)
  | .ap f as => .ap (env.r f) (as.map env.r)
  | .prim op as => .prim op (as.map env.r)
  | .reset x => .reset (env.r x)
  | .reuse tok t as => .reuse (env.r tok) t (as.map env.r)
  | e => e

/-- The tag `case x` would take, if known. -/
def knownTag (env : SimpEnv) (x : Var) : Option Nat :=
  match env.defs.get? x with
  | some (.ctor t _) => if t < lazyTagBase then some t else none
  | _ => match env.lits.get? x with
    | some n => some n
    | none => env.tags.get? x

end SimpEnv

/-- A `Bool` (the prelude's tags: `false`, `true`). -/
def boolExpr (b : Bool) : Expr := .ctor (if b then 1 else 0) #[]

/-- Fold an operation on known numbers (the kernel's semantics), unless the result
could be huge. -/
def foldNat (op : PrimOp) (ns : Array Nat) : Option Expr :=
  match op, ns with
  | .natBeq, #[a, b] => some (boolExpr (a == b))
  | .natBlt, #[a, b] => some (boolExpr (a < b))
  | .natPow, #[a, b] => if a ≤ 1 || a.log2 * b ≤ 4096 then (natNative? op.key ns).map .lit else none
  | .natShiftLeft, #[a, b] => if b ≤ 4096 || a == 0 then (natNative? op.key ns).map .lit else none
  | _, _ => if op.isNat then (natNative? op.key ns).map .lit else none

/-- The simplified expression, or the variable it is equal to. -/
def foldExpr (env : SimpEnv) : Expr → Expr ⊕ Var
  | .proj i y => match env.defs.get? y with
    | some (.ctor t as) =>
      if h : i < as.size ∧ t < lazyTagBase then .inr (as[i]'h.1) else .inl (.proj i y)
    | _ => .inl (.proj i y)
  | .prim .tag #[y] => match env.defs.get? y with
    | some (.ctor t _) => if t < lazyTagBase then .inl (.ctor t #[]) else .inl (.prim .tag #[y])
    | _ => .inl (.prim .tag #[y])
  | .prim .natTag #[y] => match env.lits.get? y with
    | some n => .inl (.ctor (if n == 0 then 0 else 1) #[])
    | none => .inl (.prim .natTag #[y])
  | .prim op as =>
    if op == .natBeq && as.size == 2 && as[0]! == as[1]! then .inl (boolExpr true)
    else if op == .natBlt && as.size == 2 && as[0]! == as[1]! then .inl (boolExpr false)
    else match as.mapM env.lits.get? with
      | some ns => match foldNat op ns with
        | some e => .inl e
        | none => .inl (.prim op as)
      | none => .inl (.prim op as)
  | e => .inl e

/-- What branch `i` of `case x` learns. -/
def learn (env : SimpEnv) (x i : Var) : SimpEnv :=
  let env := { env with tags := env.tags.insert x i }
  match env.defs.get? x, i with
  | some (.prim .natTag #[y]), 0 => { env with lits := env.lits.insert y 0 }
  | some (.prim .natBeq #[a, b]), 1 =>
    match env.lits.get? a, env.lits.get? b with
    | some n, none => { env with lits := env.lits.insert b n }
    | none, some n => { env with lits := env.lits.insert a n }
    | _, _ => env
  | _, _ => env

/-- Constant folding and case of known constructors (see the module docstring). -/
partial def Body.simp (env : SimpEnv) : Body → Body
  | .vdecl x e rest =>
    match foldExpr env (env.renameE e) with
    | .inr y => Body.simp { env with σ := env.σ.insert x y } rest
    | .inl e =>
      match e with
      -- a projection already bound on the way here: the same field (stage 15j)
      | .proj i y => match env.projs.get? (i, y) with
        | some z => Body.simp { env with σ := env.σ.insert x z } rest
        | none =>
          .vdecl x e (Body.simp { env with defs := env.defs.insert x e, projs := env.projs.insert (i, y) x } rest)
      | _ =>
      let lits := match e with
        | .lit n => env.lits.insert x n
        | _ => env.lits
      -- (a lazy cell observed is overwritten: its fields read before are stale)
      let projs := match e with
        | .prim .lazySet _ => ∅
        | _ => env.projs
      .vdecl x e (Body.simp { env with defs := env.defs.insert x e, lits, projs } rest)
  | .case x alts =>
    let x := env.r x
    match env.knownTag x with
    | some t => if h : t < alts.size then Body.simp env alts[t] else .case x (alts.map (Body.simp env))
    | none => .case x (alts.mapIdx fun i a => Body.simp (learn env x i) a)
  | .ret x => .ret (env.r x)
  -- a join body only uses its parameters
  | .jdecl j ps body k => .jdecl j ps (Body.simp {} body) (Body.simp env k)
  | .jmp j as => .jmp j (as.map env.r)
  | .dup x b => .dup (env.r x) (Body.simp env b)
  | .drop x b => .drop (env.r x) (Body.simp env b)
  | .unreachable => .unreachable

/-- The largest variable and join point bound or used in a body. -/
partial def Body.maxIds : Body → Nat × Nat
  | .vdecl x e b => let (v, j) := b.maxIds; (e.args.foldl max (max v x), j)
  | .case x alts => alts.foldl (fun (v, j) a => let (v', j') := a.maxIds; (max v v', max j j')) (x, 0)
  | .ret x => (x, 0)
  | .jdecl j ps body k =>
    let (v1, j1) := body.maxIds
    let (v2, j2) := k.maxIds
    (ps.foldl max (max v1 v2), max j (max j1 j2))
  | .jmp j as => (as.foldl max 0, j)
  | .dup x b | .drop x b => let (v, j) := b.maxIds; (max v x, j)
  | .unreachable => (0, 0)

/-- Replace the self tail calls of `f` (with `n` arguments) by jumps to `J`. -/
partial def Body.selfTail (f : Name) (n : Nat) (J : JoinId) : Body → Body × Bool
  | .vdecl r (.fap g as) (.ret r') =>
    if g == f && r == r' && as.size == n then (.jmp J as, true) else (.vdecl r (.fap g as) (.ret r'), false)
  | .vdecl x e b => let (b, c) := b.selfTail f n J; (.vdecl x e b, c)
  | .case x alts =>
    let rs := alts.map (Body.selfTail f n J)
    (.case x (rs.map (·.1)), rs.any (·.2))
  -- a join body's `ret` returns from the function: its tail calls are tail calls too
  | .jdecl j ps body k =>
    let (body, c1) := body.selfTail f n J
    let (k, c2) := k.selfTail f n J
    (.jdecl j ps body k, c1 || c2)
  | .dup x b => let (b, c) := b.selfTail f n J; (.dup x b, c)
  | .drop x b => let (b, c) := b.selfTail f n J; (.drop x b, c)
  | b => (b, false)

/-- A function calling itself in tail position becomes a loop (see the module docstring). -/
def Decl.loopify (d : Decl) : Decl :=
  let (v, j) := d.body.maxIds
  let v := d.params.foldl max v
  let J := j + 1
  match d.body.selfTail d.name d.params.size J with
  | (body, true) =>
    -- the join point gets fresh parameters (the body renamed; join bodies are closed),
    -- so the function keeps its own (borrow annotations, `#ir`)
    let fresh := (List.range d.params.size).toArray.map (v + 1 + ·)
    let σ := (d.params.zip fresh).foldl (fun m (a, b) => m.insert a b) (∅ : Std.TreeMap Var Var)
    { d with body := .jdecl J fresh (Body.simp { σ } body) (.jmp J d.params) }
  | _ => d

def Decl.simplify (d : Decl) : Decl :=
  ({ d with body := Body.simp {} d.body } : Decl).loopify

end Wiz.IR
