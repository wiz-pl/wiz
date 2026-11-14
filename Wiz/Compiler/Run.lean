import Wiz.Compiler.Inline

/-!
# Running erased programs

An environment-based interpreter for `ETerm`. Strict (call-by-value), except that
coinductive values (`coit`, `scofix`) are lazy and unfold only under `out`.

The generic eliminators are **primitives that walk the description** at runtime. A
description is an ordinary runtime value: `⟨0 i⟩` (ret), `⟨1 ◾ F⟩` (arg), `⟨2 j D⟩`
(rec), `⟨3 ◾ j D⟩` (hrec), with `⟨4 ◾ F⟩` for an arg that is a tag and `⟨5 D⟩` marking
the description of numbers. A data value is a flat object `⟨tag f₁ … fₙ⟩` (see
`Erase.lean`); `unpack` gives its payload of nested pairs, `⟨0 tag ⟨0 f₁ … ⟩⟩`, and
`pack` goes back.

    ind D m i x      = m i u (hyps D u),   u = unpack D x
                                          hyps (rec j D') ⟨y, r⟩ = ⟨ind D m j y, hyps D' r⟩
                                          hyps (hrec j D') ⟨k, r⟩ = ⟨fun h => ind D m (j h) (k h), hyps D' r⟩
    out (coit D step i s) = map D (coit D step) i (step i s)

`#eval` reads a value back into a term using its **type**, so results print with
constructor names.
-/

namespace Wiz

/-- Partially applied runtime primitives (closures the runtime itself creates). -/
inductive PapOp where
  /-- `fun s => delim mret marg mrec mhrec (F s)`: args `mret marg mrec mhrec F`, arity 1 -/
  | delimRec
  /-- `fun h => ind D m (j h) (k h)`: args `D m j k`, arity 1 -/
  | indK
  /-- `fun h => f (j h) (k h)`: args `f j k`, arity 1 -/
  | mapK
  /-- `fun j s => coit D step j s`: args `D step`, arity 2 -/
  | coitK
  /-- `fun j i a => scofix f i a`: args `f`, arity 3 -/
  | scofixK
  deriving Repr, Inhabited

inductive RVal where
  | erased
  | obj (tag : Nat) (fields : Array RVal)
  | clo (env : List RVal) (body : ETerm)
  /-- `fix x. body` in `env`: unfolds when applied -/
  | fixv (env : List RVal) (body : ETerm)
  /-- a primitive waiting for more arguments -/
  | pap (op : PapOp) (args : Array RVal)
  /-- a natural number of a type registered with `builtin nat` -/
  | nat (n : Nat)
  /-- a native operation waiting for arguments -/
  | native (op : Name) (args : Array RVal)
  /-- lazy coinductive values -/
  | coit (D step i s : RVal)
  | scofix (f i a : RVal)
  deriving Inhabited

namespace RVal

def arity : PapOp → Nat
  | .delimRec => 6
  | .indK => 5
  | .mapK => 4
  | .coitK => 4
  | .scofixK => 4

/-- A native number looks like its payload when inspected:
`0 ↦ ⟨0 ⟨0⟩ ⟨0 ◾ ◾⟩⟩` and `n+1 ↦ ⟨0 ⟨1⟩ ⟨0 n ⟨0 ◾ ◾⟩⟩⟩`. -/
def natView : Nat → RVal
  | 0 => .obj 0 #[.obj 0 #[], .obj 0 #[.erased, .erased]]
  | n + 1 => .obj 0 #[.obj 1 #[], .obj 0 #[.nat n, .obj 0 #[.erased, .erased]]]

def field (v : RVal) (i : Nat) : RVal :=
  match v with
  | .obj _ fs => fs[i]?.getD .erased
  | .nat n => match natView n with
    | .obj _ fs => fs[i]?.getD .erased
    | _ => .erased
  | _ => .erased

/-- The number a value denotes, if it is one (native, or a unary payload). -/
partial def toNat? : RVal → Option Nat
  | .nat n => some n
  | .obj 0 #[] => some 0
  | .obj 1 #[k] => (toNat? k).map (· + 1)
  | _ => none

/-- The tag of an object (a number's is `0` or `1`). -/
def tagOf : RVal → Nat
  | .obj t _ => t
  | .nat n => if n == 0 then 0 else 1
  | _ => 0

/-- The payload of a flat value, along the description `D` (see `Erase.lean`). -/
partial def unpackWith (apply : RVal → RVal → RVal) (D v : RVal) : RVal :=
  match D with
  | .obj 5 _ => match v with
    | .nat n => natView n
    | .obj 0 _ => natView 0
    | _ => match v.field 0 with
      | .nat n => natView (n + 1)
      | _ => .erased
  | .obj 4 #[_, F] =>
    let t := RVal.obj (tagOf v) #[]
    .obj 0 #[t, rest (apply F t) 0]
  | d => rest d 0
where
  rest (d : RVal) (n : Nat) : RVal :=
    match d with
    | .obj 1 #[_, F] | .obj 4 #[_, F] => let f := v.field n; .obj 0 #[f, rest (apply F f) (n + 1)]
    | .obj 2 #[_, D'] | .obj 3 #[_, _, D'] => .obj 0 #[v.field n, rest D' (n + 1)]
    | _ => .obj 0 #[.erased, .erased]

/-- A payload as a flat value. -/
partial def packWith (apply : RVal → RVal → RVal) (D x : RVal) : RVal :=
  match D with
  | .obj 5 _ => match tagOf (x.field 0) with
    | 0 => .nat 0
    | _ => match (x.field 1).field 0 |>.toNat? with
      | some n => .nat (n + 1)
      | none => .erased
  | .obj 4 #[_, F] => .obj (tagOf (x.field 0)) (fields (apply F (x.field 0)) (x.field 1) #[])
  | d => .obj 0 (fields d x #[])
where
  fields (d x : RVal) (acc : Array RVal) : Array RVal :=
    match d with
    | .obj 1 #[_, F] | .obj 4 #[_, F] => fields (apply F (x.field 0)) (x.field 1) (acc.push (x.field 0))
    | .obj 2 #[_, D'] | .obj 3 #[_, _, D'] => fields D' (x.field 1) (acc.push (x.field 0))
    | _ => acc

/-- (9g) The signature of a function C calls (a callback, an exported function): the
kinds of its parameters and result (letters), and whether the result is in `IO`. -/
structure CallbackSig where
  params : List Char
  result : Char
  io : Bool
  deriving BEq, Inhabited, Repr

/-- `[nn/b]`: the parameters, `/`, then the result, with `!` before it for a result in
`IO`. -/
def CallbackSig.toKey (c : CallbackSig) : String :=
  s!"[{String.ofList c.params}/{if c.io then "!" else ""}{c.result}]"

def CallbackSig.ofKey (s : List Char) : CallbackSig :=
  let ps := s.takeWhile (· != '/')
  let r := (s.dropWhile (· != '/')).drop 1
  let (io, r) := match r with | '!' :: r => (true, r) | r => (false, r)
  { params := ps, result := r.headD 'v', io }

/-- How one argument or result of a foreign function is marshalled: a kind letter, or
(9i) a C struct passed by value, `<ctype|header|f₁=k₁,…>`, whose fields are kinds
again. A struct's `header` is empty when its definition is generated from the fields.
(9g) A Wiz closure passed to C as a callback, a function pointer and a context
pointer, is `k[sig]` (borrowed for the call) or `K[sig]` (`owned`: the C side has a
reference and gives it back with `wiz_release`). -/
inductive FKind where
  | k (c : Char)
  | struct (ctype : String) (header : String) (fields : List (String × FKind))
  | callback (owned : Bool) (sig : CallbackSig)
  deriving BEq, Inhabited, Repr

partial def FKind.toKey : FKind → String
  | .k c => c.toString
  | .callback owned sig => (if owned then "K" else "k") ++ sig.toKey
  | .struct c h fs => "<" ++ c ++ "|" ++ h ++ "|" ++ ",".intercalate (fs.map fun (f, kd) => f ++ "=" ++ kd.toKey) ++ ">"

/-- The text up to the matching `>` (after a `<`), and the rest. -/
def FKind.group (cs : List Char) (depth : Nat) (acc : List Char) : List Char × List Char :=
  match cs with
  | [] => (acc.reverse, [])
  | '<' :: r => FKind.group r (depth + 1) ('<' :: acc)
  | '>' :: r => if depth == 0 then (acc.reverse, r) else FKind.group r (depth - 1) ('>' :: acc)
  | c :: r => FKind.group r depth (c :: acc)

/-- Split at a separator, outside brackets. -/
def FKind.splitTop (cs : List Char) (sep : Char) (depth : Nat := 0) (cur : List Char := []) (acc : List (List Char) := []) :
    List (List Char) :=
  match cs with
  | [] => (cur.reverse :: acc).reverse
  | c :: r =>
    if c == sep && depth == 0 then FKind.splitTop r sep depth [] (cur.reverse :: acc)
    else FKind.splitTop r sep (if c == '<' then depth + 1 else if c == '>' then depth - 1 else depth) (c :: cur) acc

/-- One kind, and the rest of the text. -/
partial def FKind.parseOne (cs : List Char) : Option (FKind × List Char) :=
  match cs with
  | '<' :: r =>
    let (inner, rest) := FKind.group r 0 []
    match FKind.splitTop inner '|' with
    | [c, h, fs] =>
      let fields := if fs.isEmpty then [] else (FKind.splitTop fs ',').filterMap fun f =>
        match FKind.splitTop f '=' with
        | n :: rest => (FKind.parseOne (String.intercalate "=" (rest.map String.ofList)).toList).map fun (kd, _) => (String.ofList n, kd)
        | _ => none
      some (.struct (String.ofList c) (String.ofList h) fields, rest)
    | _ => none
  | 'k' :: '[' :: r => some (.callback false (CallbackSig.ofKey (r.takeWhile (· != ']'))), (r.dropWhile (· != ']')).drop 1)
  | 'K' :: '[' :: r => some (.callback true (CallbackSig.ofKey (r.takeWhile (· != ']'))), (r.dropWhile (· != ']')).drop 1)
  | c :: r => some (.k c, r)
  | [] => none

/-- The kinds of a key's parameter field: letters and bracketed structs. -/
partial def FKind.parseMany (cs : List Char) : List FKind :=
  match FKind.parseOne cs with
  | some (kd, rest) => kd :: FKind.parseMany rest
  | none => []

/-- The letter of a kind (`S` for a struct). -/
def FKind.letter : FKind → Char
  | .k c => c
  | .struct .. => 'S'
  | .callback owned _ => if owned then 'K' else 'k'

/-- A foreign function's key: `extern:cname:kinds:result:io:header:finalizer` (see
`extern`). Kinds: `n` Nat, `u` UInt64, `f` Float64, `s` String, `b` Bool, `v` Unit,
`p` a foreign pointer (the finalizer is for a pointer result), `w` a Wiz value passed as is,
`y` (9i) a byte buffer (`Bytes`) passed as a pointer and a length (two C arguments),
`<…>` a C struct by value (`FKind`). -/
structure ExternSig where
  cname : String
  params : List FKind
  result : FKind
  io : Bool
  header : String
  fin : String := ""

def ExternSig.ofKey? (key : Name) : Option ExternSig :=
  -- a struct's C type may not contain `:`, so splitting is safe
  match key.splitOn ":" with
  | ["extern", c, ps, r, io, h, fin] =>
    some { cname := c, params := FKind.parseMany ps.toList, result := ((FKind.parseMany r.toList).headD (.k 'v')),
           io := io == "io", header := h, fin }
  | _ => none

/-- An exported function (stage 9g), `export:cname:kinds:result:io`: C calls `cname`. -/
def ExternSig.ofExportKey? (key : Name) : Option ExternSig :=
  match key.splitOn ":" with
  | ["export", c, ps, r, io] =>
    some { cname := c, params := ps.toList.map .k, result := .k (r.toList.headD 'v'), io := io == "io", header := "" }
  | _ => none

def exportPrefix : String := "export:"

def nativeArity (key : Name) : Nat :=
  match ExternSig.ofKey? key with
  | some sig => sig.params.length + (if sig.io then 1 else 0)
  | none => match key with
    | "nat.zero" => 0
    | "nat.succ" | "nat.pred" | "nat.log2" => 1
    | _ => 2

end RVal

/-- Erased global definitions, by name. -/
abbrev Code := Std.HashMap Name ETerm

mutual

/-- **Exercise 5.2.** Evaluate an erased term. `proj` of `◾` is `◾` (it was a proof or
a type); `case` branches on the tag of an object; `fix` builds a `fixv`; primitives
go to `runPrim`. -/
partial def run (code : Code) (env : List RVal) : ETerm → RVal
  --<sol
  | .erased => .erased
  | .var i => env[i]?.getD .erased
  | .global n => match code[n]? with
    | some (.prim .unreachable #[.global op]) =>
      -- a definition registered as a native operation (`builtin`)
      if RVal.nativeArity op == 0 then .nat 0 else .native op #[]
    | some t => run code [] t
    | none => panic! s!"no code for {n}"
  | .lam _ b => .clo env b
  | .app f a => apply code (run code env f) (run code env a)
  | .letE _ v b => run code (run code env v :: env) b
  | .obj t fs => .obj t (fs.map (run code env))
  | .proj i t => (run code env t).field i
  | .case s bs => match run code env s with
    | .obj t _ => run code env (bs[t]?.getD (.prim .unreachable #[]))
    | _ => panic! "case on a non-object"
  | .fix _ b => .fixv env b
  | .prim op as => runPrim code op (as.map (run code env))
  | .natLit n => .nat n
  --|ex
  --| | .natLit n => .nat n  -- (given)
  --| | t => sorry
  --sol>

partial def apply (code : Code) (f a : RVal) : RVal :=
  match f with
  | .clo env b => run code (a :: env) b
  | .fixv env b => apply code (run code (.fixv env b :: env) b) a
  | .pap op args =>
    let args := args.push a
    if args.size < RVal.arity op then .pap op args else firePap code op args
  | .native op args =>
    let args := args.push a
    if args.size < RVal.nativeArity op then .native op args else fireNative op args
  | _ => .erased

/-- Native arithmetic. `nat.beq` returns a tag of the prelude's `Bool` (`false`, `true`). -/
partial def fireNative (op : Name) (args : Array RVal) : RVal :=
  let n (i : Nat) : Nat := ((args[i]?.getD .erased).toNat?).getD 0
  match if op.startsWith "nat." then natNative? op (args.map fun a => (a.toNat?).getD 0) else none with
  | some r => .nat r
  | none =>
  match op with
  | "nat.beq" => .obj (if n 0 == n 1 then 1 else 0) #[]
  | "nat.blt" => .obj (if n 0 < n 1 then 1 else 0) #[]
  -- the interpreter doesn't memoise: a suspension is its function
  | "memo" => args[1]?.getD .erased
  -- a few pure foreign functions the interpreter knows itself
  | "extern:wiz_nat_show:n:s:pure::" =>
    let chars := (toString (n 0)).toList.foldr (fun c t => RVal.obj 1 #[.obj 0 #[.nat c.toNat], t]) (.obj 0 #[])
    .obj 0 #[chars]
  | _ => panic! s!"{op}: foreign functions only run in compiled code (wiz run)"

partial def applyN (code : Code) (f : RVal) (as : List RVal) : RVal := as.foldl (apply code) f

partial def firePap (code : Code) : PapOp → Array RVal → RVal
  | .delimRec, #[mret, marg, mrec, mhrec, F, s] => delim code mret marg mrec mhrec (apply code F s)
  | .indK, #[D, m, j, k, h] => ind code D m (apply code j h) (apply code k h)
  | .mapK, #[f, j, k, h] => applyN code f [apply code j h, apply code k h]
  | .coitK, #[D, step, j, s] => .coit D step j s
  | .scofixK, #[f, _, i, a] => .scofix f i a
  | _, _ => panic! "bad partial application"

/-- **Exercise 5.3a.** `ind D m i x = m i u (hyps D u)` with the payload `u = unpack D x`,
where `hyps` walks the description alongside the payload, recursing at each `rec`
field (see the module docstring). `D` may be marked as the description of numbers,
`⟨5 D'⟩`: `unpack` needs the mark, `hyps` walks `D'`, and the recursive calls get `D`. -/
partial def ind (code : Code) (D m i x : RVal) : RVal :=
  --<sol
  let u := RVal.unpackWith (apply code) D x
  let d := match D with
    | .obj 5 #[D'] => D'
    | D => D
  applyN code m [i, u, hyps d u]
where
  hyps (d xs : RVal) : RVal :=
    match d with
    | .obj 0 _ => .erased
    | .obj 1 #[_, F] | .obj 4 #[_, F] => hyps (apply code F (xs.field 0)) (xs.field 1)
    | .obj 2 #[j, D'] => .obj 0 #[ind code D m j (xs.field 0), hyps D' (xs.field 1)]
    | .obj 3 #[_, j, D'] => .obj 0 #[.pap .indK #[D, m, j, xs.field 0], hyps D' (xs.field 1)]
    | _ => panic! "ind: not a description"
  --|ex
  --| sorry
  --sol>

partial def delim (code : Code) (mret marg mrec mhrec D : RVal) : RVal :=
  match D with
  | .obj 0 #[i] => apply code mret i
  | .obj 1 #[_, F] | .obj 4 #[_, F] => applyN code marg [.erased, .erased, F, .pap .delimRec #[mret, marg, mrec, mhrec, F]]
  | .obj 2 #[j, D'] => applyN code mrec [.erased, j, D', delim code mret marg mrec mhrec D']
  | .obj 3 #[_, j, D'] => applyN code mhrec [.erased, .erased, j, D', delim code mret marg mrec mhrec D']
  | _ => panic! "Desc.elim: not a description"

/-- **Exercise 5.3b.** Observe a coinductive value. A `coit` runs one step and re-wraps
the recursive positions (`map`); an `scofix` unfolds once; anything else (a `cocon`,
whose erased form is its payload) is already observed. -/
partial def out (code : Code) (x : RVal) : RVal :=
  --<sol
  match x with
  | .coit D step i s => map D (.pap .coitK #[D, step]) (applyN code step [i, s])
  | .scofix f i a => out code (applyN code f [.erased, .pap .scofixK #[f], i, a])
  | v => v
where
  map (d f xs : RVal) : RVal :=
    match d with
    | .obj 0 _ => xs
    | .obj 1 #[_, F] | .obj 4 #[_, F] => .obj 0 #[xs.field 0, map (apply code F (xs.field 0)) f (xs.field 1)]
    | .obj 2 #[j, D'] => .obj 0 #[applyN code f [j, xs.field 0], map D' f (xs.field 1)]
    | .obj 3 #[_, j, D'] => .obj 0 #[.pap .mapK #[f, j, xs.field 0], map D' f (xs.field 1)]
    | _ => panic! "out: not a description"
  --|ex
  --| sorry
  --sol>

partial def runPrim (code : Code) : Prim → Array RVal → RVal
  | .ind, #[D, m, i, x] => ind code D m i x
  | .delim, #[a, b, c, h, D] => delim code a b c h D
  | .coit, #[D, st, i, s] => .coit D st i s
  | .scofix, #[f, i, a] => .scofix f i a
  | .out, #[x] => out code x
  | .unreachable, _ => panic! "reached an impossible case"
  | .lazyTag, #[x] => match x with
    | .coit .. => .obj 1 #[]
    | .scofix .. => .obj 2 #[]
    | _ => .obj 0 #[]
  | .lazySet, #[_, p] => p
  | .pack, #[D, x] => RVal.packWith (apply code) D x
  | .unpack, #[D, x] | .view .., #[D, x] => RVal.unpackWith (apply code) D x
  | .tag, #[x] => .obj (RVal.tagOf x) #[]
  | .natTag, #[x] => .obj (RVal.tagOf x) #[]
  | .natPred, #[x] => .nat (((x.toNat?).getD 1) - 1)
  | .natSucc, #[x] => .nat (((x.toNat?).getD 0) + 1)
  | .fieldAt, #[x, n] => x.field ((n.toNat?).getD 0)
  | .mkObj, #[t, fs] =>
    let rec collect (l : RVal) (acc : Array RVal) (fuel : Nat) : Array RVal :=
      match fuel, l with
      | f + 1, .obj 0 #[a, rest] => collect rest (acc.push a) f
      | _, _ => acc
    .obj (RVal.tagOf t) (collect fs #[] 100000)
  | _, _ => panic! "bad primitive application"

end

variable {R : Type} [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R]

def RVal.tag? : RVal → Option Nat
  | .obj t _ => some t
  -- a scalar tag (as printed by compiled code)
  | .nat t => some t
  | _ => none

/-- The characters of a value of the registered `string` type,
`String.mk (List.cons (Char.mk n) …)`. -/
partial def RVal.toString? (v : RVal) : Option String := do
  let rec chars (l : RVal) (acc : String) : Option String := do
    match ← l.tag? with
    | 0 => some acc
    | _ =>
      let n ← ((l.field 0).field 0).toNat?
      chars (l.field 1) (acc.push (Char.ofNat n))
  chars (v.field 0) ""

/-- Read a runtime value back as a term of type `ty`, for printing. Numbers and
strings of the registered `nat` and `string` types print as literals. -/
partial def readback (g : Globals R) (builtins : List (Name × Name)) (ty : VTy R) (v : RVal) : Term R :=
  let readback := readback g builtins
  match whnf ty, v with
  | .mu _ _ _ _ _ hint, v =>
    -- (the same test as erasure's: a type shaped like `Nat` is a number, R3)
    if isNatTy { g with builtins := builtins } ty then
      match v.toNat? with
      | some n => .const (toString n) []
      | none => readbackData ty v
    else if hint.map (·.1) == builtins.lookup "string" && hint.isSome then
      match v.toString? with
      | some s => .const s.quote []
      | none => readbackData ty v
    -- (7e) an integer of the registered `int` type, `ofNat n` or `negSucc n`: `n`, `-(n+1)`
    else if hint.map (·.1) == builtins.lookup "int" && hint.isSome then
      match v.tag?, (v.field 0).toNat? with
      | some 0, some n => .const (toString n) []
      | some 1, some n => .const s!"-{n + 1}" []
      | _, _ => readbackData ty v
    else readbackData ty v
  | .sigma _ _ A B _, v =>
    -- the last field of a structure is unboxed (22i): `v` is the field itself
    if unboxedSigma g 1000000 ty then
      let a' := readback A v
      .pair a' (readback (Closure.inst g B (eval g [] a')) .erased)
    else
    let a' := readback A (v.field 0)
    .pair a' (readback (Closure.inst g B (eval g [] a')) (v.field 1))
  -- Q4: a lifted value is the value itself at run time
  | .ulift _ _ A, v => .up (readback A v)
  | .enum ls, .obj t _ => .tag ls t
  | .enum ls, .nat t => .tag ls t
  | .unit _, _ => .tt
  -- an erased function into `Unit` (a phantom tail or structure marker, 22e, 22i): its
  -- one inhabitant
  | .pi .., _ => if erasedFunTy g ty 1000000 then .tt else .const "<function>" []
  | .nu .., _ => .const "<codata>" []
  | _, _ => .tt
where
  readbackData (ty : VTy R) (v : RVal) : Term R :=
    match whnf ty with
    | .mu l I D i _ hint =>
      -- a native value (stage 22d), printed as a number: the model's object around it
      let _ := hint
      let v := match v, reprOfTy? { g with builtins := builtins } ty with
        | .nat n, some ri => RVal.obj ri.tag ((List.range ri.nfields).toArray.map fun k =>
            if k == ri.r then .nat n else .erased)
        | v, _ => v
      let v := match v with
        | .nat n => if isNatTy { g with builtins := builtins } ty then RVal.natView n else unflat D v
        | v => unflat D v
      .con (readback g builtins (vInterp g l I D (muFamily l I D) i) v)
    | _ => .tt
  /-- The payload of a flat value, walking the description (as a value). -/
  unflat (D : Val R) (v : RVal) : RVal :=
    let field (n : Nat) : RVal := match v with
      | .obj _ fs => fs[n]?.getD .erased
      | _ => .erased
    let rec rest (d : Val R) (n : Nat) (fuel : Nat) : RVal :=
      match fuel with
      | 0 => .erased
      | fuel + 1 =>
      match whnf d with
      | .darg _ S F =>
        let f := field n
        .obj 0 #[f, rest (vApp g F (eval g [] (readback g builtins S f))) (n + 1) fuel]
      | .drec _ _ D' | .dhrec _ _ _ D' => .obj 0 #[field n, rest D' (n + 1) fuel]
      | _ => .obj 0 #[.erased, .erased]
    match whnf D with
    | .darg _ S F =>
      match tagField? S with
      | some (ls, lifted) =>
        let t := (v.tag?).getD 0
        .obj 0 #[.obj t #[], rest (vApp g F (if lifted then .up (.tag ls t) else .tag ls t)) 0 10000]
      | none => rest D 0 10000
    | _ => rest D 0 10000

/-- The globals an erased term mentions. -/
partial def ETerm.globals (e : ETerm) (acc : Array Name := #[]) : Array Name :=
  match e with
  | .global n => acc.push n
  | .lam _ b | .fix _ b | .proj _ b => b.globals acc
  | .app f a => a.globals (f.globals acc)
  | .letE _ v b => b.globals (v.globals acc)
  | .obj _ fs | .prim _ fs => fs.foldl (fun acc f => f.globals acc) acc
  | .case s bs => bs.foldl (fun acc b => b.globals acc) (s.globals acc)
  | _ => acc

/-- (HD9) An erased body that compiled code substitutes wherever its definition is
applied, at little cost in code size: under its lambdas, a small application (at most 16
nodes) of variables, projections, globals, `◾` and numerals: a forwarder.
Class methods (`Add.add` is `λ A self. self`: a one-method dictionary is the method
itself), instances (`instAddNat` is `Nat.add`), structure projections and aliases are
of this shape, so `a + b` at `Nat` compiles to the native addition. -/
partial def ETerm.trivialBody : ETerm → Bool
  | .lam _ b => b.trivialBody
  | t => (size t).any (· ≤ 16)
where
  /-- the number of nodes of an application of atoms (`none` for anything else) -/
  size : ETerm → Option Nat
    | .var _ | .erased | .global _ | .natLit _ => some 1
    | .proj _ t => (size t).map (· + 1)
    | .app f a => do let m ← size f; let n ← size a; pure (m + n + 1)
    | _ => none

/-- (HD9) An erased body that builds an object (under its lambdas): an instance of a class
with several methods. Inlined only where a field of it is projected. -/
def ETerm.objBody : ETerm → Bool
  | .lam _ b => b.objBody
  | .obj .. => true
  | _ => false

/-- Erase the definitions reachable from `roots`. (Erasing everything would be wasteful:
recursors of big types are expensive to erase and rarely run.) With `externImpls := false` (the
interpreters, which can't call C), a definition implemented by a foreign function keeps
its own code: `#eval` and `#run` run the model, compiled code the native. Also returns
the definitions that couldn't be erased, with the reasons. -/
def compileReachableE (g : Globals R) (builtins : List (Name × Name)) (roots : List Name)
    (externImpls : Bool := true) (caseShapes : Bool := true) : TCM (Code × List (Name × String)) := do
  let mut code : Code := {}
  let mut failed : List (Name × String) := []
  let mut todo := roots.toArray
  -- definitions registered as native operations
  let natives := builtins.filter fun (key, _) => key != "nat" && key != "string" && key != "int" && !key.startsWith "repr:" &&
    !key.startsWith "cstruct:" && !key.startsWith "seal:" &&
    !key.startsWith RVal.exportPrefix &&
    key != inlineKey
  -- native representations (stage 22d): the interpreters keep the model's objects when
  -- the conversions are foreign functions
  let isExtern (f : Name) := builtins.any fun (k, x) => x == f && k.startsWith "extern:"
  let g := if externImpls then g else
    { g with builtins := g.builtins.filter fun (k, _) => match ReprInfo.parse? k with
      | some (_, ri) => !isExtern ri.mkImpl && !isExtern ri.getImpl
      | none => true }
  -- `attribute [inline]` (22i): the erased bodies of the inline definitions
  let mut inlines : Std.HashMap Name ETerm := {}
  for (k, f) in g.builtins do
    if k == inlineKey then
      if let some d := g.find? f then
        if let .ok e := eraseDecl g d then inlines := inlines.insert f e
  -- the seals of the sealed types with a native representation (22k)
  let nativeSeals := g.builtins.filterMap fun (key, x) =>
    if key.startsWith "seal:" then
      let T : Name := (key.drop 5).toString
      if (reprOf? g.builtins T).isSome then some (x, T) else none
    else none
  -- (HD9) the definitions compiled code substitutes (`trivialBody`) and the objects it
  -- projects from (`objBody`), by name, with each erased body
  let mut trivial : Std.HashMap Name ETerm := {}
  let mut objs : Std.HashMap Name ETerm := {}
  let mut classified : Std.HashSet Name := {}
  -- `attribute [implemented_by m] n`: `n` gets `m`'s code (following chains)
  let rec target (m : Name) : Nat → Name
    | 0 => m
    | fuel + 1 => match (g.find? m).bind (·.impl) with
      | some (.const m' _) =>
        if !externImpls && builtins.any (fun (k, x) => x == m' && k.startsWith "extern:") then m
        else target m' fuel
      | _ => m
  -- the erased code of `n` before inlining (`none`: no such definition), and the reason
  -- if it couldn't be erased
  let eraseOne (n : Name) : Option (ETerm × Option String) :=
    let m := target n 100
    if let some (key, _) := natives.find? (·.2 == m) then
      some (.prim .unreachable #[.global key], none)
    else match g.find? m with
      | none => none
      | some d =>
        -- (an `implemented_by` not followed: the definition itself)
        let d := if d.impl matches some (.const ..) then { d with impl := none } else d
        -- a declaration that can't be erased yet becomes a runtime error if it is reached
        match eraseDecl g d with
        | .ok e => some (e, none)
        | .error err => some (.prim .unreachable #[], some (toString err))
  -- (kept: a definition is erased once, when first called or when reached)
  let mut raw : Std.HashMap Name (Option (ETerm × Option String)) := {}
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if code.contains n then continue
    -- (22k, layer 3) the seal of a type with a native representation stays in the type's
    -- module, except inside the type itself
    unless nativeSeals.isEmpty do
      let m := target n 100
      if let some d := g.find? m then
        let here := (g.declModule[m]?).getD ""
        for (k, T) in nativeSeals do
          if (g.declModule[T]?).getD "" != here then
            if let some v := d.impl <|> d.value then
              if sealOutsideMu (· == k) v then
                throw (.other (s!"cannot compile {n}: {T} has a native representation (it is a sealed type), so generic " ++
                  s!"code over types or descriptions cannot be used at it: {T}'s seal is passed as an argument here"))
    let r ← match raw.get? n with
      | some r => pure r
      | none => do let r := eraseOne n; raw := raw.insert n r; pure r
    let some (e, err) := r | continue
    if let some err := err then
      -- (a refusal, not a gap: running on would give a wrong value)
      if (err.splitOn abstractFieldMsg).length > 1 || (err.splitOn nativeHomeMsg).length > 1 then
        throw (.other s!"cannot erase {n}: {err}")
      failed := (n, err) :: failed
    -- classify the globals `e` mentions (each once), and those their bodies mention
    let mut pending := e.globals
    let mut rounds := 0
    while !pending.isEmpty && rounds < 3 do
      rounds := rounds + 1
      let mut next := #[]
      for f in pending do
        if classified.contains f then continue
        classified := classified.insert f
        -- (not a native, an `implemented_by`, a constructor with a native representation …)
        if builtins.any (·.2 == f) || g.builtins.any (·.2 == f) then continue
        let some df := g.find? f | continue
        if df.value.isNone || df.impl.isSome then continue
        if let .ok b := eraseDecl g df then
          if b.globals.contains f then continue
          if b.trivialBody then trivial := trivial.insert f b; next := b.globals next
          else if b.objBody then objs := objs.insert f b; next := b.globals next
      pending := next
    let e := if e.globals.any (fun f => inlines.contains f || trivial.contains f || objs.contains f) then
      let inl := inlines
      let triv := trivial
      let os := objs
      e.inlineSimp (fun f => if f == n then none else match inl.get? f with
          | some b => some b
          | none => triv.get? f) 8
        (fun f => if f == n then none else os.get? f)
    else e
    -- known tags, and the closures of an unfolded linear `match` (`simpKnown`)
    let e := e.simpKnown
    -- calls of case-shaped definitions (`Bool.and`, …) become `case`s (15h)
    let e ← if caseShapes then do
        for f in e.globals do
          unless raw.contains f do raw := raw.insert f (eraseOne f)
        let known := raw
        pure (e.caseInline fun f => if f == n then none else
          match known.get? f with
          | some (some (b, _)) => b.caseShape?
          | _ => none)
      else pure e
    code := code.insert n e
    todo := e.globals todo
  pure (code, failed.reverse)

/-- The same, ignoring the definitions that couldn't be erased (reaching one is a
runtime error). -/
def compileReachable (g : Globals R) (builtins : List (Name × Name)) (roots : List Name)
    (externImpls : Bool := true) (caseShapes : Bool := true) : TCM Code :=
  return (← compileReachableE g builtins roots externImpls caseShapes).1

/-- Erase every global. -/
def compileAll (g : Globals R) (builtins : List (Name × Name) := []) : TCM Code :=
  compileReachable g builtins g.order.toList

end Wiz
