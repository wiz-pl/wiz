import Wiz.Compiler.IR

/-!
# Reference counting (Perceus)

Insert `dup` and `drop` so that every reference is consumed exactly once
(Reinking et al., *Perceus*, PLDI 2021). A variable is **owned** when it is bound
(it holds a reference), and must be either passed on (as an argument, a returned value,
or a jump argument) or dropped:

* an argument that is still needed afterwards (or appears again in the same call) is
  `dup`ed first; otherwise the call takes over the reference;
* a variable is dropped **as soon as it is dead**: right after the binding that last
  used it, at the start of each `case` branch that doesn't use it, or at the start of
  the function if it is never used. This is what makes Perceus garbage free: no
  object is kept alive longer than its last use;
* `proj` doesn't consume the object, and reads the field without a new reference: the
  field of an owned object is `dup`ed at once (it may outlive the object), the field of
  a borrowed one is borrowed too.

**Borrowed parameters** (stage 8e, as in Lean 4): a parameter the function never
consumes is *borrowed*: the caller keeps its reference and lends it for the call, so
neither side counts. `Borrow.lean` decides which parameters are borrowed; here a
borrowed variable is simply one that is not owned: it is `dup`ed when it is consumed and
never dropped. At a call, an argument in a borrowed position is lent (not consumed); a
variable lent to a call and also passed to an owned position of the same call is
`dup`ed for the owned one (the callee might free it while the borrow is still used).
Join points have borrowed parameters too. The comparisons `nat.beq` and `nat.blt`, and
the tag inspections `tag` and `natTag`, borrow their arguments the same way
(`Expr.primBorrows`).

Join point bodies only use their parameters (see `Lower.lean`), so they start from
their own parameters.
-/

namespace Wiz.IR

/-- Which parameters are borrowed: of the functions of the program and of the join
points of the current function (absent: all owned). -/
structure BorrowSigs where
  fns : Std.HashMap Name (Array Bool) := {}
  jps : Std.HashMap JoinId (Array Bool) := {}
  deriving Inhabited

/-- Is parameter `i` of `f` borrowed? -/
def BorrowSigs.fn (σ : BorrowSigs) (f : Name) (i : Nat) : Bool :=
  ((σ.fns.get? f).bind (·[i]?)).getD false

/-- Is parameter `i` of join point `j` borrowed? -/
def BorrowSigs.jp (σ : BorrowSigs) (j : JoinId) (i : Nat) : Bool :=
  ((σ.jps.get? j).bind (·[i]?)).getD false

/-- Prefix `b` with drops of the owned variables not used in it. -/
def dropDead (owned : Std.HashSet Var) (live : Std.HashSet Var) (b : Body) : Body × Std.HashSet Var :=
  let dead := (owned.toArray.filter (!live.contains ·)).qsort (· < ·)
  (dead.foldr (fun x acc => .drop x acc) b, dead.foldl (·.erase ·) owned)

/-- The arguments of an expression in owned positions (consumed), and those lent to
borrowed positions. -/
def splitArgs (σ : BorrowSigs) : Expr → Array Var × Array Var
  | .proj _ _ => (#[], #[])
  | .fap f as =>
    (as.zipIdx.filterMap fun (a, i) => if σ.fn f i then none else some a,
     as.zipIdx.filterMap fun (a, i) => if σ.fn f i then some a else none)
  | .prim op as => if Expr.primBorrows op then (#[], as) else (as, #[])
  | e => (e.args, #[])

/-- **Exercise 8.1.** Insert reference counting operations into `b`, where `owned` are
the variables currently holding a reference (see the module docstring). For a call
with arguments `as`, walk them left to right: an argument that is not owned, still live
in the rest of the body, or used again later in `as`, gets a `dup`; otherwise its
reference moves into the call. `σ` says which arguments are only lent (stage 8e; with
the empty `σ`, none are). -/
partial def insertRC (σ : BorrowSigs) (owned : Std.HashSet Var) (b : Body) : Body :=
  --<sol
  match b with
  | .vdecl x (.proj i y) rest =>
    let live := rest.freeVars
    -- the field of an owned object becomes ours (`dup`ed before the object may be
    -- dropped); the field of a borrowed one is borrowed
    let mine := owned.contains y && live.contains x
    let owned := if mine then owned.insert x else owned
    let (rest', _) := dropDead owned live (insertRC σ (owned.filter live.contains) rest)
    .vdecl x (.proj i y) (if mine then .dup x rest' else rest')
  | .vdecl x e rest =>
    let live := rest.freeVars
    -- the arguments the expression consumes, and those it borrows
    let (consumed, lent) := splitArgs σ e
    let (dups, owned) := consume owned (lent.foldl (·.insert ·) live) consumed
    let owned := owned.insert x
    let (rest', _) := dropDead owned live (insertRC σ (owned.filter live.contains) rest)
    dups.foldr (fun y acc => .dup y acc) (.vdecl x e rest')
  | .case x alts =>
    .case x (alts.map fun alt =>
      let (alt', _) := dropDead owned alt.freeVars (insertRC σ (owned.filter alt.freeVars.contains) alt)
      alt')
  | .ret x =>
    let (dups, owned) := consume owned {} #[x]
    let (b', _) := dropDead owned {} (.ret x)
    dups.foldr (fun y acc => .dup y acc) b'
  | .jdecl j ps body k =>
    let ownedB : Std.HashSet Var := ps.zipIdx.foldl (fun s (p, i) => if σ.jp j i then s else s.insert p) {}
    let (body', _) := dropDead ownedB body.freeVars (insertRC σ (ownedB.filter body.freeVars.contains) body)
    .jdecl j ps body' (insertRC σ owned k)
  | .jmp j as =>
    let consumed := as.zipIdx.filterMap fun (a, i) => if σ.jp j i then none else some a
    let lent : Std.HashSet Var := as.zipIdx.foldl (fun s (a, i) => if σ.jp j i then s.insert a else s) {}
    let (dups, owned) := consume owned lent consumed
    let (b', _) := dropDead owned lent (.jmp j as)
    dups.foldr (fun y acc => .dup y acc) b'
  | b => b
where
  /-- Consume `as` in order: returns the variables to `dup` first, and what stays owned. -/
  consume (owned : Std.HashSet Var) (live : Std.HashSet Var) (as : Array Var) : Array Var × Std.HashSet Var :=
    Id.run do
      let mut owned := owned
      let mut dups := #[]
      for a in as, i in [0:as.size] do
        let usedLater := live.contains a || (as.extract (i + 1) as.size).contains a
        if owned.contains a && !usedLater then owned := owned.erase a
        else dups := dups.push a
      pure (dups, owned)
  --|ex
  --| sorry
  --sol>

--<sol
/-! ### Reference counting in one pass

`insertRC` asks for the free variables of the rest of the body at every binding, and
keeps them alive while it handles the rest: quadratic in time and space along a chain
of `n` bindings (a 15 000-binding constant took 9 s and 4 GB). The same result in one
pass, bottom-up, from two observations:

* the set `owned` that `insertRC` passes to a node is always the node's free variables
  that hold a reference, and whether a variable holds one is fixed where it is bound
  (a reference only moves at a variable's last use, so a variable still live hasn't
  lost it): bound by `vdecl`, or an owned parameter, or the field of an owned object
  (`proj`; an owned field that is never used is not owned, but then it is not live
  either);
* so each node's `dup`s and `drop`s only need the free variables of its continuation,
  which the bottom-up pass returns (threaded through, so each set is updated in place).
-/

namespace RCFast

/-- The variables that hold a reference where they are bound (see above). -/
partial def ownedVars (σ : BorrowSigs) (b : Body) (acc : Std.HashSet Var) : Std.HashSet Var :=
  match b with
  | .vdecl x (.proj _ y) rest => ownedVars σ rest (if acc.contains y then acc.insert x else acc)
  | .vdecl x _ rest => ownedVars σ rest (acc.insert x)
  | .case _ alts => alts.foldl (fun acc a => ownedVars σ a acc) acc
  | .jdecl j ps body k =>
    let acc := ps.zipIdx.foldl (fun s (p, i) => if σ.jp j i then s else s.insert p) acc
    ownedVars σ k (ownedVars σ body acc)
  | .dup _ b | .drop _ b => ownedVars σ b acc
  | _ => acc

/-- Prefix `b` with drops of `xs` (sorted, as `dropDead` orders them). -/
def drops (xs : Array Var) (b : Body) : Body :=
  (xs.qsort (· < ·)).foldr (fun x acc => .drop x acc) b

/-- `insertRC.consume` with `owned` = the owned variables among `as` (all of them free at
the node): the variables to `dup` first, and which of `as` moved into the call. -/
def consume (own : Std.HashSet Var) (live : Var → Bool) (as : Array Var) : Array Var × Std.HashSet Var :=
  Id.run do
    let mut moved : Std.HashSet Var := {}
    let mut dups := #[]
    for a in as, i in [0:as.size] do
      let usedLater := live a || (as.extract (i + 1) as.size).contains a
      if own.contains a && !moved.contains a && !usedLater then moved := moved.insert a
      else dups := dups.push a
    pure (dups, moved)

/-- `insertRC σ (owned vars free in b) b`, and the free variables of `b`. -/
partial def go (σ : BorrowSigs) (own : Std.HashSet Var) (b : Body) : Body × Std.HashSet Var :=
  match b with
  | .vdecl x (.proj i y) rest =>
    let (rest', fv) := go σ own rest
    let mine := own.contains y && fv.contains x
    let rest' := if own.contains y && !fv.contains y then .drop y rest' else rest'
    let fv := (fv.erase x).insert y
    (.vdecl x (.proj i y) (if mine then .dup x rest' else rest'), fv)
  | .vdecl x e rest =>
    let (rest', fv) := go σ own rest
    let (consumed, lent) := splitArgs σ e
    let (dups, moved) := consume own (fun v => fv.contains v || lent.contains v) consumed
    -- dead after this binding: `x` and the owned arguments that didn't move
    let dead := ((e.args.push x).filter fun v => own.contains v && !fv.contains v && !moved.contains v)
    let dead := dead.foldl (fun (acc : Array Var) v => if acc.contains v then acc else acc.push v) #[]
    let rest' := drops dead rest'
    let fv := e.args.foldl (·.insert ·) (fv.erase x)
    (dups.foldr (fun y acc => .dup y acc) (.vdecl x e rest'), fv)
  | .case x alts =>
    let rs := alts.map (go σ own)
    -- the free variables of the whole `case` (merged into the largest set)
    let big := (rs.zipIdx.foldl (fun (best : Nat × Nat) (r, i) => if r.2.size > best.1 then (r.2.size, i) else best) (0, 0)).2
    let fv := rs.zipIdx.foldl (fun acc (r, i) => if i == big then acc else r.2.fold (·.insert ·) acc)
      ((rs[big]?.map (·.2)).getD {})
    let fv := fv.insert x
    let ownedHere := fv.toArray.filter own.contains
    (.case x (rs.map fun (alt', fvA) => drops (ownedHere.filter (!fvA.contains ·)) alt'), fv)
  | .ret x =>
    (if own.contains x then .ret x else .dup x (.ret x), ({} : Std.HashSet Var).insert x)
  | .jdecl j ps body k =>
    let (body', fvB) := go σ own body
    let ownedPs := ps.zipIdx.filterMap fun (p, i) => if σ.jp j i then none else some p
    let body' := drops (ownedPs.filter (!fvB.contains ·)) body'
    let (k', fv) := go σ own k
    -- (`body` only uses its parameters)
    let fv := fvB.fold (fun acc v => if ps.contains v then acc else acc.insert v) fv
    (.jdecl j ps body' k', fv)
  | .jmp j as =>
    let consumed := as.zipIdx.filterMap fun (a, i) => if σ.jp j i then none else some a
    let lent : Std.HashSet Var := as.zipIdx.foldl (fun s (a, i) => if σ.jp j i then s.insert a else s) {}
    let (dups, moved) := consume own lent.contains consumed
    -- owned arguments that stay owned and aren't lent are dropped before the jump
    let dead := as.filter fun v => own.contains v && !moved.contains v && !lent.contains v
    let dead := dead.foldl (fun (acc : Array Var) v => if acc.contains v then acc else acc.push v) #[]
    (dups.foldr (fun y acc => .dup y acc) (drops dead (.jmp j as)), as.foldl (·.insert ·) {})
  | b => (b, b.freeVars)

end RCFast
--|ex
--sol>

/-- Reference counting for a function: its parameters are owned, except those `σ` says
are borrowed. -/
def Decl.insertRC (d : Decl) (σ : BorrowSigs := {}) : Decl :=
  let owned : Std.HashSet Var :=
    d.params.zipIdx.foldl (fun s (p, i) => if σ.fn d.name i then s else s.insert p) {}
  --<sol
  -- (`RCFast`: the same as `insertRC`, in linear time)
  let (body, fv) := RCFast.go σ (RCFast.ownedVars σ d.body owned) d.body
  let body := RCFast.drops (d.params.filter fun p => owned.contains p && !fv.contains p) body
  --|ex
  --| let live := d.body.freeVars
  --| let (body, _) := dropDead owned live (Wiz.IR.insertRC σ (owned.filter live.contains) d.body)
  --sol>
  { d with body, borrow := d.params.zipIdx.map fun (_, i) => σ.fn d.name i }

/-- `Decl.insertRC` by the specification `insertRC` (quadratic; for differential tests). -/
def Decl.insertRCSpec (d : Decl) (σ : BorrowSigs := {}) : Decl :=
  let owned : Std.HashSet Var :=
    d.params.zipIdx.foldl (fun s (p, i) => if σ.fn d.name i then s else s.insert p) {}
  let live := d.body.freeVars
  let (body, _) := dropDead owned live (Wiz.IR.insertRC σ (owned.filter live.contains) d.body)
  { d with body, borrow := d.params.zipIdx.map fun (_, i) => σ.fn d.name i }

end Wiz.IR
