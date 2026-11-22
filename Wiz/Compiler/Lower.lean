import Wiz.Compiler.IR
import Wiz.Compiler.Simp
import Wiz.Compiler.PrimCode
import Wiz.Compiler.Run

/-!
# Lowering erased terms to the IR

* **Lambda lifting.** A `lam` (with the lambdas directly under it) becomes a new
  top-level function taking its free variables first; in place, a closure
  `pap f fvs`. A `fix` is lifted the same way, and its own name is the closure again.
* **Calls.** A top-level function applied to as many arguments as it has parameters
  is a direct call (`fap`); fewer make a closure (`pap`); more call it and then apply
  the result (`ap`). Registered native operations become `prim`s.
* **A-normal form.** Every intermediate result gets a variable. The continuation of a
  `case` that isn't in tail position becomes a **join point**, whose parameters are
  the result and every variable the continuation uses (so join bodies are closed,
  which keeps reference counting simple).
* The generic eliminators call the definitions of `PrimCode.lean`; `coit`/`scofix`
  build lazy objects (tags 1000 and 1001).
-/

namespace Wiz.IR

/-- How a variable of the erased term is represented. -/
inductive Binding where
  | var (x : Var)
  /-- the name of a lifted `fix`: the function applied to its captured variables -/
  | self (f : Name) (fvs : Array Var)
  deriving Inhabited

structure Ctx where
  /-- parameters of top-level functions -/
  arities : Std.HashMap Name Nat
  /-- registered native operations: global ↦ typed primitive -/
  natives : Std.HashMap Name PrimOp
  /-- the function being lowered, for naming lifted lambdas -/
  owner : Name
  /-- functions inlined when fully applied: constructors (bodies that only build objects) -/
  inlines : Std.HashMap Name ETerm := {}

abbrev LowerM := ReaderT Ctx (StateT (Nat × Nat × Array Decl) (Except String))

/-- What to do with a value: return it (tail position), or continue. -/
inductive Cont where
  | ret
  | fn (k : Var → LowerM Body)

/-- The wrapper function for a native operation, for partial applications. -/
def nativeWrapper (op : PrimOp) : Name := "wiz.native." ++ op.key

/-- A primitive's arity. A closed primitive's is table metadata; a foreign function's
comes from its signature (the `IO` world counts as an argument). -/
def primArity (op : PrimOp) : Nat :=
  match op with
  | .extern key => RVal.nativeArity key
  | _ => op.arity

/-- Resolve a registered native key to a typed primitive. An unknown key is an error
here, at lowering, rather than a `wiz_unknown_prim` call at run time. -/
def resolvePrim (key : Name) : Except String PrimOp :=
  match PrimOp.ofKey? key with
  | some p => pure p
  | none =>
    if (RVal.ExternSig.ofKey? key).isSome then pure (.extern key)
    else throw s!"unknown primitive `{key}` (register it with `builtin` or a matching `extern`)"

def freshVar : LowerM Var := modifyGet fun (v, j, ds) => (v, (v + 1, j, ds))
def freshJoin : LowerM JoinId := modifyGet fun (v, j, ds) => (j, (v, j + 1, ds))
def addDecl (d : Decl) : LowerM Unit := modify fun (v, j, ds) => (v, j, ds.push d)
def freshName (base : String) : LowerM Name := do
  -- the variable counter is unique (lifted lambdas nest, so counting decls is not)
  pure s!"{(← read).owner}.{base}{← freshVar}"

/-- Rename free variables of a body. -/
partial def Body.rename (σ : Std.HashMap Var Var) : Body → Body
  | .vdecl x e b => .vdecl x (renE e) (Body.rename σ b)
  | .case x alts => .case (r x) (alts.map (Body.rename σ))
  | .ret x => .ret (r x)
  | .jdecl j ps body k => .jdecl j ps body (Body.rename σ k)
  | .jmp j as => .jmp j (as.map r)
  | .dup x b => .dup (r x) (Body.rename σ b)
  | .drop x b => .drop (r x) (Body.rename σ b)
  | .unreachable => .unreachable
where
  r (x : Var) : Var := σ.getD x x
  renE : Expr → Expr
    | .ctor t as => .ctor t (as.map r)
    | .proj i x => .proj i (r x)
    | .fap f as => .fap f (as.map r)
    | .pap f as => .pap f (as.map r)
    | .ap f as => .ap (r f) (as.map r)
    | .prim op as => .prim op (as.map r)
    | .reset x => .reset (r x)
    | .reuse tok t as => .reuse (r tok) t (as.map r)
    -- no wildcard: a new expression form must say how it renames
    | .erased => .erased
    | .lit n => .lit n

/-- The free de Bruijn indices of a term under `depth` binders (as outer indices). -/
partial def freeIdx (e : ETerm) (depth : Nat := 0) (acc : Std.HashSet Nat := {}) : Std.HashSet Nat :=
  match e with
  | .var i => if i ≥ depth then acc.insert (i - depth) else acc
  | .lam _ b | .fix _ b => freeIdx b (depth + 1) acc
  | .app f a => freeIdx a depth (freeIdx f depth acc)
  | .letE _ v b => freeIdx b (depth + 1) (freeIdx v depth acc)
  | .obj _ fs | .prim _ fs => fs.foldl (fun acc f => freeIdx f depth acc) acc
  | .proj _ t => freeIdx t depth acc
  | .case s bs => bs.foldl (fun acc b => freeIdx b depth acc) (freeIdx s depth acc)
  | _ => acc

/-- Peel the lambdas at the top of a term. -/
def peelLams : ETerm → List Name × ETerm
  | .lam x b => let (xs, b) := peelLams b; (x :: xs, b)
  | t => ([], t)

mutual

/-- Lower `e` (variables per `env`, innermost first) and pass its value to `k`. -/
partial def lower (env : List Binding) (e : ETerm) (k : Cont) : LowerM Body := do
  match e with
  | .var i => match env[i]? with
    | some (.var x) => finish k x
    | some (.self f fvs) => bind (.pap f fvs) k
    | none => throw s!"lower: unbound variable {i}"
  | .global n => do
    match (← read).natives.get? n with
    | some op =>
      -- `nat.zero` is a number; a foreign constant is a call
      bind (if op == .natZero then .lit 0 else if primArity op == 0 then .prim op #[]
        else .pap (nativeWrapper op) #[]) k
    | none =>
      let a := ((← read).arities.get? n).getD 0
      bind (if a == 0 then .fap n #[] else .pap n #[]) k
  | .natLit n => bind (.lit n) k
  | .erased => bind .erased k
  | .lam .. | .fix .. => liftLambda env e k
  | .app .. => lowerApp env e k
  | .letE _ v b => lower env v (.fn fun x => lower (.var x :: env) b k)
  | .obj t fs => lowerArgs env fs.toList fun xs => bind (.ctor t xs.toArray) k
  | .proj i t => lower env t (.fn fun x => bind (.proj i x) k)
  | .case s bs => lower env s (.fn fun x => lowerCase env x bs k)
  | .prim op args =>
    match op with
    | .unreachable => pure .unreachable
    | .coit => lowerArgs env args.toList fun xs => bind (.ctor 1000 xs.toArray) k
    | .scofix => lowerArgs env args.toList fun xs => bind (.ctor 1001 xs.toArray) k
    | .lazyTag => lowerArgs env args.toList fun xs => bind (.prim .lazyTag xs.toArray) k
    | .lazySet => lowerArgs env args.toList fun xs => bind (.prim .lazySet xs.toArray) k
    | .ind => lowerArgs env args.toList fun xs => bind (.fap "wiz.ind" xs.toArray) k
    | .delim => lowerArgs env args.toList fun xs => bind (.fap "wiz.delim" xs.toArray) k
    | .out => lowerArgs env args.toList fun xs => bind (.fap "wiz.out" xs.toArray) k
    | .pack => lowerArgs env args.toList fun xs => bind (.fap "wiz.pack" xs.toArray) k
    | .unpack | .view .. => lowerArgs env args.toList fun xs => bind (.fap "wiz.unpack" xs.toArray) k
    | .tag => lowerArgs env args.toList fun xs => bind (.prim .tag xs.toArray) k
    | .natTag => lowerArgs env args.toList fun xs => bind (.prim .natTag xs.toArray) k
    | .natPred => lowerArgs env args.toList fun xs => bind (.prim .natPred xs.toArray) k
    | .natSucc => lowerArgs env args.toList fun xs => bind (.prim .natSucc xs.toArray) k
    | .fieldAt => lowerArgs env args.toList fun xs => bind (.prim .fieldAt xs.toArray) k
    | .mkObj => lowerArgs env args.toList fun xs => bind (.prim .mkObj xs.toArray) k

partial def lowerArgs (env : List Binding) (es : List ETerm) (k : List Var → LowerM Body) : LowerM Body :=
  match es with
  | [] => k []
  | e :: es => lower env e (.fn fun x => lowerArgs env es fun xs => k (x :: xs))

/-- `let x := e` and continue. -/
partial def bind (e : Expr) (k : Cont) : LowerM Body := do
  let x ← freshVar
  pure (.vdecl x e (← finish k x))

partial def finish (k : Cont) (x : Var) : LowerM Body :=
  match k with
  | .ret => pure (.ret x)
  | .fn f => f x

/-- `case` in tail position, or else with a join point for the continuation. -/
partial def lowerCase (env : List Binding) (x : Var) (bs : Array ETerm) (k : Cont) : LowerM Body := do
  match k with
  | .ret => pure (.case x (← bs.mapM fun b => lower env b .ret))
  | .fn _ =>
    let r ← freshVar
    let kb ← finish k r
    -- the join body may only use its parameters: pass what it uses
    let captured := ((kb.freeVars.erase r).toArray.qsort (· < ·))
    let params ← captured.mapM fun _ => freshVar
    let σ : Std.HashMap Var Var := (captured.zip params).foldl (fun m (a, b) => m.insert a b) {}
    let j ← freshJoin
    let alts ← bs.mapM fun b => lower env b (.fn fun v => pure (.jmp j (#[v] ++ captured)))
    pure (.jdecl j (#[r] ++ params) (Body.rename σ kb) (.case x alts))

/-- Lift a lambda (or `fix`) to a top-level function; in place, a closure. -/
partial def liftLambda (env : List Binding) (e : ETerm) (k : Cont) : LowerM Body := do
  let (isFix, inner) := match e with
    | .fix _ b => (true, b)
    | b => (false, b)
  let (xs, body) := peelLams inner
  let depth := xs.length + (if isFix then 1 else 0)
  let free := (freeIdx body depth).toArray.qsort (· < ·)
  let name ← freshName (if isFix then "fix" else "lam")
  -- materialise captured `fix` names as closures first
  let rec capture (is : List Nat) (acc : Array Var) (k' : Array Var → LowerM Body) : LowerM Body :=
    match is with
    | [] => k' acc
    | i :: is => match env[i]? with
      | some (.var x) => capture is (acc.push x) k'
      | some (.self f fvs) => do
        let y ← freshVar
        pure (.vdecl y (.pap f fvs) (← capture is (acc.push y) k'))
      | none => throw s!"lower: unbound variable {i}"
  capture free.toList #[] fun outer => do
    let capParams ← outer.mapM fun _ => freshVar
    let lamParams ← xs.toArray.mapM fun _ => freshVar
    -- the body's environment: its lambdas, the `fix` name, then the captured variables
    let outerEnv : List Binding := (List.range (free.foldl max 0 + 1)).map fun i =>
      match free.idxOf? i with
      | some j => .var capParams[j]!
      | none => .var 0  -- not used by the body
    let selfEnv : List Binding := if isFix then [.self name capParams] else []
    let bodyEnv := lamParams.toList.reverse.map Binding.var ++ selfEnv ++ outerEnv
    let arities := (← read).arities.insert name (capParams.size + lamParams.size)
    let b ← withReader (fun c => { c with arities }) (lower bodyEnv body .ret)
    addDecl { name, params := capParams ++ lamParams, body := b }
    withReader (fun c => { c with arities }) (bind (.pap name outer) k)

/-- An application: direct calls to known functions, natives, closures otherwise. -/
partial def lowerApp (env : List Binding) (e : ETerm) (k : Cont) : LowerM Body := do
  let rec spine : ETerm → ETerm × List ETerm
    | .app f a => let (h, as) := spine f; (h, as ++ [a])
    | t => (t, [])
  let (h, args) := spine e
  let known : Option (Name × Array Var × Nat) ← match h with
    | .global n => do
      match (← read).natives.get? n with
      | some _ => pure none
      | none => pure (some (n, #[], ((← read).arities.get? n).getD 0))
    | .var i => match env[i]? with
      | some (.self f fvs) => do pure (some (f, fvs, ((← read).arities.get? f).getD 0))
      | _ => pure none
    | _ => pure none
  lowerArgs env args fun xs => do
    let xs := xs.toArray
    match h, known with
    | .global n, none =>
      -- a native operation
      let op := ((← read).natives.get? n).getD (.extern n)
      let a := primArity op
      if xs.size ≥ a then
        let x ← freshVar
        let rest := xs.extract a xs.size
        if rest.isEmpty then pure (.vdecl x (.prim op (xs.extract 0 a)) (← finish k x))
        else pure (.vdecl x (.prim op (xs.extract 0 a)) (← bind (.ap x rest) k))
      else bind (.pap (nativeWrapper op) xs) k
    | _, some (f, pre, arity) =>
      let all := pre ++ xs
      if let some body := (← read).inlines.get? f then
        if pre.isEmpty && all.size == arity then
          return ← lower (all.toList.reverse.map Binding.var) body k
      if all.size == arity then bind (.fap f all) k
      else if all.size < arity then bind (.pap f all) k
      else
        let x ← freshVar
        pure (.vdecl x (.fap f (all.extract 0 arity)) (← bind (.ap x (all.extract arity all.size)) k))
    | _, none =>
      lower env h (.fn fun f => bind (.ap f xs) k)

end

/-- A body that only builds objects (a constructor's). -/
partial def ctorShaped : ETerm → Bool
  | .obj _ fs => fs.all ctorShaped
  | .var _ | .erased | .natLit _ => true
  | _ => false

/-- Lower a whole program: the reachable definitions, the eliminators of `PrimCode`,
wrappers for native operations, and `main`. The result is sorted by name, so the
output doesn't depend on hash order (deterministic builds). -/
def lowerProgram (code : Code) (main : ETerm) (extra : Array (Name × ETerm) := #[]) : Except String (Array Decl) := do
  let mut defs : Array (Name × ETerm) := #[]
  let mut natives : Std.HashMap Name PrimOp := {}
  for (n, e) in code.toList do
    match e with
    | .prim .unreachable #[.global key] => natives := natives.insert n (← resolvePrim key)
    | e => defs := defs.push (n, e)
  defs := (defs.qsort (·.1 < ·.1)) ++ PrimCode.all.toArray ++ #[("wiz.entry", main)] ++ extra
  let arities : Std.HashMap Name Nat := defs.foldl (fun m (n, e) => m.insert n (peelLams e).1.length) {}
  -- constructors: inline them, so allocations can meet drops (and reuse)
  let inlines : Std.HashMap Name ETerm := defs.foldl (fun m (n, e) =>
    let (xs, b) := peelLams e
    if !xs.isEmpty && ctorShaped b then m.insert n b else m) {}
  let mut out : Array Decl := #[]
  -- wrappers for partially applied native operations
  let keys := (natives.toList.map (·.2)).eraseDups.toArray.qsort (fun a b => a.key < b.key)   -- complexity: ok (one pass over the native primitive map)
  for key in keys do
    let ps := (List.range (primArity key)).toArray
    -- (`nat.zero` is a number, not an operation)
    let e : Expr := if key == .natZero then .lit 0 else .prim key ps
    out := out.push { name := nativeWrapper key, params := ps, body := .vdecl ps.size e (.ret ps.size) }
  for (n, e) in defs do
    let (xs, body) := peelLams e
    let ctx : Ctx := { arities, natives, owner := n, inlines }
    let params := (List.range xs.length).toArray
    let env := params.toList.reverse.map Binding.var
    let (b, (_, _, lifted)) ← (lower env body .ret).run ctx |>.run (xs.length, 0, #[])
    out := out ++ lifted.push { name := n, params, body := b }
  -- constant folding, known constructors, self tail calls as loops (`Simp.lean`)
  pure (out.map (·.simplify))

end Wiz.IR
