import Wiz.Compiler.Reuse

/-!
# Drop specialisation (stage 8e)

Taking an owned object apart reads its fields and `dup`s them (they may outlive it),
then drops the object; if it was unique, freeing it decrements those same fields again:

    let a := proj 0 x; dup a; let b := proj 1 x; dup b; drop x

Perceus specialises the drop for the two cases (Reinking et al., §2.3): if `x` is unique,
its fields move out (no `dup`, no decrement) and only its cell is freed; otherwise the
`dup`s happen and `x` is decremented as before. Here both cases are one runtime
operation, `dropMoved x m`, where the mask `m` says which fields moved out:

    let a := proj 0 x; let b := proj 1 x; let m := 3; let _ := prim dropMoved x m

(unique: drop the other fields, free the cell; shared: `dup` the moved fields, decrement
`x`). A pair returned by a call and taken apart then costs no reference counting when it
is unique (the usual case). Runs last, after reuse (drops paired with allocations are
already `reset`s).
-/

namespace Wiz.IR

inductive Stmt where
  | v (x : Var) (e : Expr)
  | dup (x : Var)
  | drop (x : Var)
  deriving Inhabited

/-- A straight-line block: its statements and how it ends. -/
partial def flattenBlock : Body → Array Stmt → Array Stmt × Body
  | .vdecl x e b, acc => flattenBlock b (acc.push (.v x e))
  | .dup x b, acc => flattenBlock b (acc.push (.dup x))
  | .drop x b, acc => flattenBlock b (acc.push (.drop x))
  | b, acc => (acc, b)

def Stmt.wrap (b : Body) : Stmt → Body
  | .v x e => .vdecl x e b
  | .dup x => .dup x b
  | .drop x => .drop x b

/-- Fresh variables and join points. -/
abbrev SpecM := StateM (Var × JoinId)

def specVar : SpecM Var := modifyGet fun (v, j) => (v, (v + 1, j))
def specJoin : SpecM JoinId := modifyGet fun (v, j) => (j, (v, j + 1))

/-- The `dup`s right before `drop x` (`ss[k]`) of fields read from `x`, that can move
into the specialised drop: their positions and the fields' indices. Only reads of `x`'s
fields and such `dup`s may come between. -/
def movableDups (ss : Array Stmt) (k : Nat) (x : Var) (parents : Std.HashMap Var (Var × Nat)) :
    Array Nat × Array Nat := Id.run do
  let mut pos : Array Nat := #[]
  let mut fields : Array Nat := #[]
  let mut vars : Array Var := #[]
  let mut j := k
  while j > 0 do
    j := j - 1
    match (ss[j]! : Stmt) with
    | .v _ (.proj _ y) => if y != x then break
    | .dup a =>
      match parents.get? a with
      | some (y, i) =>
        if y != x then break
        -- one move per field (and per variable); i < 62 fits in the mask
        if i < 62 && !fields.contains i && !vars.contains a then
          pos := pos.push j; fields := fields.push i; vars := vars.push a
      | none => break
    | _ => break
  return (pos, fields)

mutual

partial def specBody (parents : Std.HashMap Var (Var × Nat)) (b : Body) : SpecM Body := do
  let (ss, term) := flattenBlock b #[]
  specStmts parents ss 0 term #[]

/-- Specialise the drops of `ss` from position `k` on; `done` are the statements already
kept (in order). -/
partial def specStmts (parents : Std.HashMap Var (Var × Nat)) (ss : Array Stmt) (k : Nat) (term : Body)
    (done : Array (Nat × Stmt)) : SpecM Body := do
  if h : k < ss.size then
    match ss[k] with
    | .v x (.proj i y) => specStmts (parents.insert x (y, i)) ss (k + 1) term (done.push (k, ss[k]))
    | .drop x =>
      let (pos, fields) := movableDups ss k x parents
      if pos.isEmpty then specStmts parents ss (k + 1) term (done.push (k, ss[k])) else
      let m ← specVar
      let z ← specVar
      let mask := fields.foldl (fun acc i => acc + 2 ^ i) 0
      let done := (done.filter fun (i, _) => !pos.contains i)
        |>.push (k, .v m (.lit mask)) |>.push (k, .v z (.prim .dropMoved #[x, m]))
      specStmts parents ss (k + 1) term done
    | s => specStmts parents ss (k + 1) term (done.push (k, s))
  else
    let term ← match term with
      | .case x alts => pure (.case x (← alts.mapM (specBody parents)))
      | .jdecl j ps body k => pure (.jdecl j ps (← specBody {} body) (← specBody parents k))
      | t => pure t
    pure (done.foldr (fun (_, s) acc => s.wrap acc) term)

end

/-- The largest variable and join point of a body. -/
partial def maxIds : Body → Var × JoinId → Var × JoinId
  | .vdecl x e b, (v, j) => maxIds b (e.args.foldl max (max v x), j)
  | .dup x b, (v, j) | .drop x b, (v, j) => maxIds b (max v x, j)
  | .case x alts, (v, j) => alts.foldl (fun acc a => maxIds a acc) (max v x, j)
  | .jdecl j' ps body k, (v, j) => maxIds k (maxIds body (ps.foldl max v, max j j'))
  | .jmp j' as, (v, j) => (as.foldl max v, max j j')
  | .ret x, (v, j) => (max v x, j)
  | .unreachable, acc => acc

def Decl.specializeDrops (d : Decl) : Decl :=
  let (v, j) := maxIds d.body (d.params.foldl max 0, 0)
  { d with body := ((specBody {} d.body).run (v + 1, j + 1)).1 }

end Wiz.IR
