import Wiz.Compiler.Run

/-!
# The interpreter of `native_refl`: `#eval`'s, with fuel and errors

`native_refl` (stage 27a) decides a closed equation by running both sides. It runs them
here: the same evaluation as `run` (Run.lean, `#eval`'s interpreter), on the same erased
code, but

* every step costs fuel (a function application, a global's code, a primitive), and
  running out is an error ("native evaluation did not finish within N steps"), so a
  long computation in the language server ends with a message instead of hanging it;
* everything `run` answers with `panic!` and a default value (a case on a non-object,
  a missing definition, an impossible case, a foreign function, a malformed
  description) is an error here, and so is a number operation on something that is not
  a number (`run` reads it as `0`). A `native_refl` result is never built from a
  default value, also in the language server, which does not exit on a panic.

It is trusted code (as `run` is): `native_refl`'s axioms rest on it.
-/

namespace Wiz.NativeRun

open Wiz

/-- The state: fuel left. -/
abbrev M := EStateM String Nat

/-- The default limit (`--native-fuel N`). -/
def defaultFuel : Nat := 20000000000

@[inline] def tick : M Unit := do
  let n ← get
  if n == 0 then throw "out of fuel"
  set (n - 1)

def num (v : RVal) : M Nat :=
  match v.toNat? with
  | some n => pure n
  | none => throw "a number operation on a value that is not a number"

/-- The number of bits beyond which `nat.pow` and `nat.shiftLeft` are refused: Lean's
`Nat.pow` panics (ending the process, the language server too) on exponents from 2^24. -/
def maxBits : Nat := 16777216

mutual

partial def run (code : Code) (env : List RVal) : ETerm → M RVal
  | .erased => pure .erased
  | .var i => match env[i]? with
    | some v => pure v
    | none => throw s!"unbound variable {i}"
  | .global n => do
    tick
    match code[n]? with
    | some (.prim .unreachable #[.global op]) =>
      -- (only `nat.zero` is a constant the interpreter knows; a foreign constant's value
      -- is whatever C returns, which only compiled code sees)
      if op == "nat.zero" then pure (.nat 0)
      else if RVal.nativeArity op == 0 then throw s!"{n} is a foreign constant ({op}): only compiled code has its value"
      else pure (.native op #[])
    | some t => run code [] t
    | none => throw s!"no code for {n}"
  | .lam _ b => pure (.clo env b)
  | .app f a => do apply code (← run code env f) (← run code env a)
  | .letE _ v b => do run code ((← run code env v) :: env) b
  | .obj t fs => do pure (.obj t (← fs.mapM (run code env)))
  | .proj i t => do pure ((← run code env t).field i)
  | .case s bs => do
    match ← run code env s with
    | .obj t _ => match bs[t]? with
      | some b => run code env b
      | none => throw s!"case: no branch for tag {t}"
    | _ => throw "case on a value that is not an object"
  | .fix _ b => pure (.fixv env b)
  | .prim op as => do runPrim code op (← as.mapM (run code env))
  | .natLit n => pure (.nat n)

partial def apply (code : Code) (f a : RVal) : M RVal := do
  tick
  match f with
  | .clo env b => run code (a :: env) b
  | .fixv env b => do apply code (← run code (.fixv env b :: env) b) a
  | .pap op args =>
    let args := args.push a
    if args.size < RVal.arity op then pure (.pap op args) else firePap code op args
  | .native op args =>
    let args := args.push a
    if args.size < RVal.nativeArity op then pure (.native op args) else fireNative op args
  | _ => throw "application of a value that is not a function"

partial def fireNative (op : Name) (args : Array RVal) : M RVal := do
  if op.startsWith "nat." then
    let ns ← args.mapM num
    match op, ns with
    | "nat.pow", #[a, b] =>
      if a > 1 && a.log2 * b ≥ maxBits || a > 1 && b ≥ maxBits then
        throw s!"nat.pow: the result would have more than {maxBits} bits"
    | "nat.shiftLeft", #[a, b] =>
      if a > 0 && b ≥ maxBits then throw s!"nat.shiftLeft: the result would have more than {maxBits} bits"
    | _, _ => pure ()
    if let some r := natNative? op ns then return .nat r
  match op with
  | "nat.beq" => do let a ← num args[0]!; let b ← num args[1]!; pure (.obj (if a == b then 1 else 0) #[])
  | "nat.blt" => do let a ← num args[0]!; let b ← num args[1]!; pure (.obj (if a < b then 1 else 0) #[])
  | "memo" => match args[1]? with
    | some v => pure v
    | none => throw "memo: no argument"
  | "extern:wiz_nat_show:n:s:pure::" => do
    let n ← num args[0]!
    let chars := (toString n).toList.foldr (fun c t => RVal.obj 1 #[.obj 0 #[.nat c.toNat], t]) (.obj 0 #[])
    pure (.obj 0 #[chars])
  | _ => throw s!"{op}: a foreign function (only compiled code runs it)"

partial def applyN (code : Code) (f : RVal) : List RVal → M RVal
  | [] => pure f
  | a :: as => do applyN code (← apply code f a) as

partial def firePap (code : Code) : PapOp → Array RVal → M RVal
  | .delimRec, #[mret, marg, mrec, mhrec, F, s] => do delim code mret marg mrec mhrec (← apply code F s)
  | .indK, #[D, m, j, k, h] => do ind code D m (← apply code j h) (← apply code k h)
  | .mapK, #[f, j, k, h] => do applyN code f [← apply code j h, ← apply code k h]
  | .coitK, #[D, step, j, s] => pure (.coit D step j s)
  | .scofixK, #[f, _, i, a] => pure (.scofix f i a)
  | _, _ => throw "bad partial application of a primitive"

partial def unpack (code : Code) (D v : RVal) : M RVal :=
  match D with
  | .obj 5 _ => match v with
    | .nat n => pure (RVal.natView n)
    | .obj 0 _ => pure (RVal.natView 0)
    | _ => match v.field 0 with
      | .nat n => pure (RVal.natView (n + 1))
      | _ => throw "unpack: not a number"
  | .obj 4 #[_, F] => do
    let t := RVal.obj (RVal.tagOf v) #[]
    pure (.obj 0 #[t, ← unpackRest code v (← apply code F t) 0])
  | d => unpackRest code v d 0

partial def unpackRest (code : Code) (v d : RVal) (n : Nat) : M RVal :=
  match d with
  | .obj 1 #[_, F] | .obj 4 #[_, F] => do
    let f := v.field n
    pure (.obj 0 #[f, ← unpackRest code v (← apply code F f) (n + 1)])
  | .obj 2 #[_, D'] | .obj 3 #[_, _, D'] => do pure (.obj 0 #[v.field n, ← unpackRest code v D' (n + 1)])
  | .obj 0 _ => pure (.obj 0 #[.erased, .erased])
  | _ => throw "unpack: not a description"

partial def pack (code : Code) (D x : RVal) : M RVal :=
  match D with
  | .obj 5 _ => match RVal.tagOf (x.field 0) with
    | 0 => pure (.nat 0)
    | _ => match (x.field 1).field 0 |>.toNat? with
      | some n => pure (.nat (n + 1))
      | none => throw "pack: not a number"
  | .obj 4 #[_, F] => do
    pure (.obj (RVal.tagOf (x.field 0)) (← packFields code (← apply code F (x.field 0)) (x.field 1) #[]))
  | d => do pure (.obj 0 (← packFields code d x #[]))

partial def packFields (code : Code) (d x : RVal) (acc : Array RVal) : M (Array RVal) :=
  match d with
  | .obj 1 #[_, F] | .obj 4 #[_, F] => do packFields code (← apply code F (x.field 0)) (x.field 1) (acc.push (x.field 0))
  | .obj 2 #[_, D'] | .obj 3 #[_, _, D'] => packFields code D' (x.field 1) (acc.push (x.field 0))
  | .obj 0 _ => pure acc
  | _ => throw "pack: not a description"

partial def ind (code : Code) (D m i x : RVal) : M RVal := do
  let u ← unpack code D x
  let d := match D with
    | .obj 5 #[D'] => D'
    | D => D
  applyN code m [i, u, ← hyps code D m d u]

partial def hyps (code : Code) (D m d xs : RVal) : M RVal :=
  match d with
  | .obj 0 _ => pure .erased
  | .obj 1 #[_, F] | .obj 4 #[_, F] => do hyps code D m (← apply code F (xs.field 0)) (xs.field 1)
  | .obj 2 #[j, D'] => do pure (.obj 0 #[← ind code D m j (xs.field 0), ← hyps code D m D' (xs.field 1)])
  | .obj 3 #[_, j, D'] => do pure (.obj 0 #[.pap .indK #[D, m, j, xs.field 0], ← hyps code D m D' (xs.field 1)])
  | _ => throw "ind: not a description"

partial def delim (code : Code) (mret marg mrec mhrec D : RVal) : M RVal :=
  match D with
  | .obj 0 #[i] => apply code mret i
  | .obj 1 #[_, F] | .obj 4 #[_, F] => applyN code marg [.erased, .erased, F, .pap .delimRec #[mret, marg, mrec, mhrec, F]]
  | .obj 2 #[j, D'] => do applyN code mrec [.erased, j, D', ← delim code mret marg mrec mhrec D']
  | .obj 3 #[_, j, D'] => do applyN code mhrec [.erased, .erased, j, D', ← delim code mret marg mrec mhrec D']
  | _ => throw "Desc.elim: not a description"

partial def out (code : Code) (x : RVal) : M RVal :=
  match x with
  | .coit D step i s => do outMap code D (.pap .coitK #[D, step]) (← applyN code step [i, s])
  | .scofix f i a => do out code (← applyN code f [.erased, .pap .scofixK #[f], i, a])
  | v => pure v

partial def outMap (code : Code) (d f xs : RVal) : M RVal :=
  match d with
  | .obj 0 _ => pure xs
  | .obj 1 #[_, F] | .obj 4 #[_, F] => do pure (.obj 0 #[xs.field 0, ← outMap code (← apply code F (xs.field 0)) f (xs.field 1)])
  | .obj 2 #[j, D'] => do pure (.obj 0 #[← applyN code f [j, xs.field 0], ← outMap code D' f (xs.field 1)])
  | .obj 3 #[_, j, D'] => do pure (.obj 0 #[.pap .mapK #[f, j, xs.field 0], ← outMap code D' f (xs.field 1)])
  | _ => throw "out: not a description"

partial def runPrim (code : Code) : Prim → Array RVal → M RVal
  | .ind, #[D, m, i, x] => ind code D m i x
  | .delim, #[a, b, c, h, D] => delim code a b c h D
  | .coit, #[D, st, i, s] => pure (.coit D st i s)
  | .scofix, #[f, i, a] => pure (.scofix f i a)
  | .out, #[x] => out code x
  | .unreachable, _ => throw "reached an impossible case (or a definition that could not be erased)"
  | .lazyTag, #[x] => pure <| match x with
    | .coit .. => .obj 1 #[]
    | .scofix .. => .obj 2 #[]
    | _ => .obj 0 #[]
  | .lazySet, #[_, p] => pure p
  | .pack, #[D, x] => pack code D x
  | .unpack, #[D, x] | .view .., #[D, x] => unpack code D x
  | .tag, #[x] => pure (.obj (RVal.tagOf x) #[])
  | .natTag, #[x] => pure (.obj (RVal.tagOf x) #[])
  | .natPred, #[x] => do pure (.nat ((← num x) - 1))
  | .natSucc, #[x] => do pure (.nat ((← num x) + 1))
  | .fieldAt, #[x, n] => do pure (x.field (← num n))
  | .mkObj, #[t, fs] =>
    let rec collect (l : RVal) (acc : Array RVal) (fuel : Nat) : Array RVal :=
      match fuel, l with
      | f + 1, .obj 0 #[a, rest] => collect rest (acc.push a) f
      | _, _ => acc
    pure (.obj (RVal.tagOf t) (collect fs #[] 100000))
  | op, _ => throw s!"bad application of the primitive {repr op}"

end

/-- Run `f` applied to `args` with `fuel` steps. -/
def applyWith (code : Code) (f : RVal) (args : List RVal) (fuel : Nat) : Except String (RVal × Nat) :=
  match (args.foldlM (apply code) f).run fuel with
  | .ok v rest => .ok (v, rest)
  | .error "out of fuel" _ => .error s!"evaluation did not finish within {fuel} steps"
  | .error e _ => .error s!"evaluation failed: {e}"

/-- Run `e` with `fuel` steps. -/
def runWith (code : Code) (e : ETerm) (fuel : Nat) : Except String (RVal × Nat) :=
  match (run code [] e).run fuel with
  | .ok v rest => .ok (v, fuel - rest)
  | .error "out of fuel" _ => .error s!"native evaluation did not finish within {fuel} steps (raise the limit with --native-fuel N)"
  | .error e _ => .error s!"native evaluation failed: {e}"

end Wiz.NativeRun
