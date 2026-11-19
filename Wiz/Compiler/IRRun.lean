import Wiz.Compiler.Borrow
import Wiz.Compiler.Run

/-!
# Running the IR, with a checked heap

An interpreter for the IR that keeps an explicit heap of reference-counted objects, so
the output of `RC.lean` can be tested: using a freed object, freeing twice, or ending
with objects still allocated (a leak) are errors. `#run e` compiles `e` through the
whole backend pipeline and runs it here.

Numbers are scalars here (the C runtime adds big numbers). Field 0 of a number is its
constructor tag; any other field of one is an error (see `natField`).
-/

namespace Wiz.IR

/-- Lean core has no `Repr` for `ByteArray`; the IR interpreter's error messages print
a byte buffer as its bytes (stage 21ag). -/
instance : Repr ByteArray := ⟨fun b _ => "bytes" ++ toString b.toList⟩

inductive IVal where
  | num (n : Nat)
  | tag (t : Nat)
  | erased
  /-- a byte buffer (`Bytes`, stage 21ag): a scalar, like a number -/
  | bytes (data : ByteArray)
  /-- an array (`Array`, the interpreters' model of the runtime buffer): a scalar
  holding interpreter values. `dupV`/`dropV` visit the elements, so the heap's
  reference counts stay right -/
  | arr (data : Array IVal)
  | ptr (id : Nat)
  deriving Inhabited, BEq, Repr

inductive Obj where
  | ctor (tag : Nat) (fields : Array IVal)
  | clo (f : Name) (args : Array IVal)
  /-- a cell kept by `reset` for `reuse` -/
  | token (size : Nat)
  deriving Inhabited

structure Heap where
  objs : Std.HashMap Nat (Nat × Obj) := {}
  next : Nat := 0
  allocs : Nat := 0
  /-- steps left, so that a divergent program stops -/
  fuel : Nat := 10000000

abbrev RunM := StateT Heap (Except String)

def alloc (o : Obj) : RunM IVal := do
  let h ← get
  set { h with objs := h.objs.insert h.next (1, o), next := h.next + 1, allocs := h.allocs + 1 }
  pure (.ptr h.next)

def getObj (id : Nat) : RunM (Nat × Obj) := do
  match (← get).objs.get? id with
  | some o => pure o
  | none => throw s!"use of a freed object (#{id})"

/-- An IR value as an interpreter value, for `readback` (and for the model of a
`Bytes` operation that takes or returns text, stage 21ag). -/
partial def toRVal (h : Heap) : IVal → RVal
  | .num n => .nat n
  | .tag t => .obj t #[]
  | .erased => .erased
  | .bytes b => .bytes b
  | .arr xs => .arr (xs.map (toRVal h))
  | .ptr id => match h.objs.get? id with
    | some (_, .ctor 1000 _) => .coit .erased .erased .erased .erased
    | some (_, .ctor 1001 _) => .scofix .erased .erased .erased
    | some (_, .ctor 1002 _) => .coit .erased .erased .erased .erased
    | some (_, .ctor t fs) => .obj t (fs.map (toRVal h))
    | some (_, .clo _ _) => .clo [] .erased
    | some (_, .token _) => .erased
    | none => .erased

/-- A `String` (as `wiz_out_string` builds it) in the IR's heap. -/
def strIVal (s : String) : RunM IVal := do
  let mut l : IVal := .tag 0
  for c in s.toList.reverse do
    let ch ← alloc (.ctor 0 #[.num c.toNat])
    l ← alloc (.ctor 1 #[ch, l])
  alloc (.ctor 0 #[l])

partial def dupV : IVal → RunM Unit
  | .ptr id => do
    let (rc, o) ← getObj id
    modify fun h => { h with objs := h.objs.insert id (rc + 1, o) }
  | .arr xs => xs.forM dupV
  | _ => pure ()

partial def dropV : IVal → RunM Unit
  | .ptr id => do
    let (rc, o) ← getObj id
    if rc > 1 then modify fun h => { h with objs := h.objs.insert id (rc - 1, o) }
    else
      modify fun h => { h with objs := h.objs.erase id }
      match o with
      | .ctor _ fs => fs.forM dropV
      | .clo _ as => as.forM dropV
      | .token _ => pure ()
  | .arr xs => xs.forM dropV
  | _ => pure ()

/-- Field `i` of a number's unary view (`natView`): field 0 is its constructor tag. The
other fields would be fresh objects, which a borrowed `proj` (stage 8e) never frees: the
lowering takes numbers apart with `natTag`/`nat.pred`, so projecting one is a compiler
bug, reported here rather than as a leak at the end (the C runtime stops too). -/
def natField (n : Nat) (i : Nat) : RunM IVal := do
  if i == 0 then return .tag (if n == 0 then 0 else 1)
  throw s!"internal error: proj {i} of the number {n} (use natTag/nat.pred)"

def nativeOp (op : Name) (args : Array IVal) : RunM IVal := do
  let n (i : Nat) : Nat := match args[i]? with
    | some (.num k) => k
    | some (.tag k) => k
    | _ => 0
  if op.startsWith "nat." then
    if let some r := natNative? op ((List.range args.size).toArray.map n) then return .num r
  match op with
  | "nat.beq" => pure (.tag (if n 0 == n 1 then 1 else 0))
  | "nat.blt" => pure (.tag (if n 0 < n 1 then 1 else 0))
  -- the interpreter doesn't memoise: a suspension is its function
  | "memo" => pure (args[1]?.getD (.tag 0))
  | "natTag" => pure (.tag (if n 0 == 0 then 0 else 1))
  | "tag" =>
    let t ← match (args[0]? : Option IVal) with
      | some (.ptr id) => do
        match (← getObj id).2 with
        | .ctor t _ => pure t
        | _ => throw "tag of a closure or token"
      | some (.tag t) => pure t
      | some (.num k) => pure (if k == 0 then 0 else 1)
      | _ => pure 0
    pure (.tag t)
  | "fieldAt" =>
    match (args[0]? : Option IVal), (args[1]? : Option IVal) with
    | some (.ptr id), some (.num i) => do
      let .ctor _ fs := (← getObj id).2 | throw "fieldAt of a closure or token"
      let fv := fs[i]?.getD .erased
      dupV fv
      dropV (.ptr id)
      pure fv
    | some (.num k), some (.num 0) => pure (.num (k - 1))
    | _, _ => throw "fieldAt: bad arguments"
  | "mkObj" =>
    let t := match (args[0]? : Option IVal) with
      | some (.tag t) => t
      | some (.num t) => t
      | _ => 0
    -- the fields: nested pairs ending in ◾
    let mut fs : Array IVal := #[]
    let mut l := (args[1]?).getD .erased
    let mut fuel := 100000
    while fuel > 0 do
      fuel := fuel - 1
      match l with
      | .ptr id =>
        let .ctor _ #[a, rest] := (← getObj id).2 | throw "mkObj: not a list"
        dupV a; dupV rest
        dropV l
        fs := fs.push a
        l := rest
      | _ => break
    if fs.isEmpty then pure (.tag t) else alloc (.ctor t fs)
  | "dropMoved" =>
    -- (drop specialisation) unique: the fields in the mask move out, the cell is freed;
    -- shared: the moved fields get a reference each, and `x` is decremented
    match (args[0]? : Option IVal), (args[1]? : Option IVal) with
    | some (.ptr id), some (.num m) => do
      match ← getObj id with
      | (rc, .ctor _ fs) =>
        let moved (i : Nat) : Bool := i < 62 && (m >>> i) % 2 == 1
        if rc == 1 then
          modify fun h => { h with objs := h.objs.erase id }
          for (f, i) in fs.zipIdx do
            if !moved i then dropV f
        else
          for (f, i) in fs.zipIdx do
            if moved i then dupV f
          dropV (.ptr id)
        pure (.tag 0)
      | _ => throw "dropMoved of a closure or token"
    | some _, some (.num _) => pure (.tag 0)
    | _, _ => throw "dropMoved: bad arguments"
  | "lazyTag" =>
    let t ← match (args[0]? : Option IVal) with
      | some (.ptr id) => do
        match (← getObj id).2 with
        | .ctor 1000 _ => pure 1
        | .ctor 1001 _ => pure 2
        | .ctor 1002 _ => pure 3
        | _ => pure 0
      | _ => pure 0
    args.forM dropV
    pure (.tag t)
  | "lazySet" =>
    -- as in the C runtime: a shared lazy cell becomes ⟨1002 p⟩ (memoised `out`)
    let x := (args[0]?).getD .erased
    let pv := (args[1]?).getD .erased
    match x with
    | .ptr id => do
      match ← getObj id with
      | (rc, .ctor t fs) =>
        if rc > 1 && (t == 1000 || t == 1001) then
          modify fun h => { h with objs := h.objs.insert id (rc - 1, .ctor 1002 #[pv]) }
          fs.forM dropV
          dupV pv
        else dropV x
      | _ => dropV x
    | _ => pure ()
    pure pv
  | _ =>
    match (RVal.ExternSig.ofKey? op).map (·.cname) with
    | some c =>
      let bs (i : Nat) : Option ByteArray := match args[i]? with
        | some (.bytes b) => some b
        | _ => none
      let r ← match c, bs 0, bs 1 with
        -- `Nat.toStringSmall` (`Nat.toString`'s word-sized digits), as `Run.lean` knows it:
        -- `Bytes.show` prints its elements with it
        | "wiz_nat_show", _, _ => pure (some (← strIVal (toString (n 0))))
        | "wiz_bytes_empty", _, _ => pure (some (.bytes ByteArray.empty))
        | "wiz_bytes_push", some b, _ => pure (some (.bytes (BytesModel.push b (n 1))))
        | "wiz_bytes_size", some b, _ => pure (some (.num b.size))
        | "wiz_bytes_get", some b, _ => pure (some (.num (BytesModel.get b (n 1))))
        | "wiz_bytes_of_string", _, _ => do
          -- (the Wiz `String` value's own characters: a non-scalar code point is
          -- U+FFFD, which a Lean `String` could not carry)
          let rv := toRVal (← get) (args[0]?.getD .erased)
          pure ((BytesModel.ofCString rv).map fun b => .bytes b)
        | "wiz_bytes_to_string", some b, _ => do
          pure (some (← strIVal (BytesModel.toCString b)))
        | "wiz_bytes_slice", some b, _ => pure (some (.bytes (BytesModel.slice b (n 1) (n 2))))
        | "wiz_bytes_append", some b, some c => pure (some (.bytes (BytesModel.append b c)))
        | "wiz_bytes_eq", some b, some c => pure (some (.tag (if b == c then 1 else 0)))
        | _, _, _ => pure none
      -- `Array` (stage 12a), over the interpreter's `.arr`
      let r ← match r with
        | some v => pure (some v)
        | none =>
          let ix := match RVal.ExternSig.ofKey? op with
            | some sig => sig.argIndices
            | none => []
          let argAt (j : Nat) : IVal := match ix[j]? with
            | some i => (args[i]?).getD .erased
            | none => .erased
          let idx (j : Nat) : Nat := match argAt j with
            | .num k | .tag k => k
            | _ => 0
          let arr : Option (Array IVal) := match argAt 0 with
            | .arr a => some a
            | _ => none
          match c, arr with
          | "wiz_array_empty", _ => pure (some (.arr #[]))
          | "wiz_array_push", some a => do
            let x := argAt 1
            dupV x
            for v in a do dupV v
            pure (some (.arr (a.push x)))
          | "wiz_array_size", some a => pure (some (.num a.size))
          | "wiz_array_get", some a => do
            let d := argAt 2
            match a[(idx 1)]? with
            | some x => do dupV x; pure (some x)
            | none => do dupV d; pure (some d)
          | "wiz_array_set", some a => do
            let i := idx 1
            let x := argAt 2
            for v in a do dupV v
            if i < a.size then do
              dupV x
              pure (some (.arr (a.set! i x)))
            else pure (some (.arr a))
          | _, _ => pure none
      match r with
      | some v => do args.forM dropV; pure v
      | none => throw s!"{op}: foreign functions only run in compiled code (wiz run)"
    | none => throw s!"{op}: foreign functions only run in compiled code (wiz run)"

mutual

/-- Call a top-level function; the arguments are owned by the callee. -/
partial def call (prog : Std.HashMap Name Decl) (f : Name) (args : Array IVal) : RunM IVal := do
  let some d := prog.get? f | throw s!"no function {f}"
  unless d.params.size == args.size do throw s!"{f} expects {d.params.size} arguments, got {args.size}"
  let env := (d.params.zip args).foldl (fun m (x, v) => m.insert x v) {}
  run prog env {} d.body

partial def apply (prog : Std.HashMap Name Decl) (f : IVal) (args : Array IVal) : RunM IVal := do
  -- `◾` applied is `◾` (as in the runtime's `wiz_apply`)
  if f matches .erased then
    args.forM dropV
    return .erased
  let .ptr id := f | throw "applying a non-closure"
  let (rc, o) ← getObj id
  let .clo g captured := o | throw "applying a non-closure"
  -- take the captured arguments: move them out of a unique closure, else share them
  if rc == 1 then modify fun h => { h with objs := h.objs.erase id }
  else
    captured.forM dupV
    dropV f
  let all := captured ++ args
  let arity := ((prog.get? g).map (·.params.size)).getD 0
  if all.size == arity then call prog g all
  else if all.size < arity then alloc (.clo g all)
  else
    let r ← call prog g (all.extract 0 arity)
    apply prog r (all.extract arity all.size)

partial def run (prog : Std.HashMap Name Decl) (env : Std.HashMap Var IVal)
    (joins : Std.HashMap JoinId (Array Var × Body)) (b : Body) : RunM IVal := do
  modify fun h => { h with fuel := h.fuel - 1 }
  if (← get).fuel == 0 then throw "out of fuel"
  let get (x : Var) : RunM IVal := match env.get? x with
    | some v => pure v
    | none => throw s!"unbound x{x}"
  match b with
  | .vdecl x e rest =>
    let v ← match e with
      | .erased => pure .erased
      | .lit n => pure (.num n)
      | .ctor t as =>
        if as.isEmpty then pure (.tag t) else alloc (.ctor t (← as.mapM get))
      | .proj i y => do
        match ← get y with
        | .ptr id => do
          let .ctor _ fs := (← getObj id).2 | throw "projection from a closure or token"
          -- borrowed: no new reference
          pure (fs[i]?.getD .erased)
        | .num n => natField n i
        | .tag 0 => natField 0 i
        -- a projection of `◾` is `◾` (as in the runtime's `wiz_proj`)
        | .erased => pure .erased
        | v => throw s!"projection from a scalar {repr v}"
      | .fap f as => call prog f (← as.mapM get)
      | .pap f as => alloc (.clo f (← as.mapM get))
      | .ap f as => apply prog (← get f) (← as.mapM get)
      | .prim op as => nativeOp op (← as.mapM get)
      | .reset y => do
        let v ← get y
        match v with
        | .ptr id =>
          match ← getObj id with
          | (1, .ctor _ fs) => do
            fs.forM dropV
            modify fun h => { h with objs := h.objs.insert id (1, .token fs.size) }
            pure v
          | _ => dropV v; pure .erased
        | _ => pure .erased
      | .reuse tok t as => do
        let vs ← as.mapM get
        -- without fields the result is the scalar `t`: the token's cell is just freed
        let fresh : RunM IVal := if vs.isEmpty then pure (.tag t) else alloc (.ctor t vs)
        match ← get tok with
        | .ptr id =>
          match ← getObj id with
          | (_, .token n) =>
            if n == vs.size then
              modify fun h => { h with objs := h.objs.insert id (1, .ctor t vs) }
              pure (.ptr id)
            else
              modify fun h => { h with objs := h.objs.erase id }
              fresh
          | _ => throw "reuse of a non-token"
        | _ => fresh
    run prog (env.insert x v) joins rest
  | .case x alts =>
    let t ← match ← get x with
      | .tag t => pure t
      | .num n => pure (if n == 0 then 0 else 1)
      | .ptr id => do
        match (← getObj id).2 with
        | .ctor t _ => pure t
        | _ => throw "case on a closure or token"
      | .erased => throw "case on ◾"
      | .bytes _ => throw "case on a byte buffer"
      | .arr _ => throw "case on an array"
    match alts[t]? with
    | some alt => run prog env joins alt
    | none => throw s!"no branch for tag {t}"
  | .ret x => get x
  | .jdecl j ps body k => run prog env (joins.insert j (ps, body)) k
  | .jmp j as =>
    let some (ps, body) := joins.get? j | throw s!"no join point j{j}"
    let vs ← as.mapM get
    run prog ((ps.zip vs).foldl (fun m (p, v) => m.insert p v) {}) joins body
  | .dup x rest => dupV (← get x); run prog env joins rest
  | .drop x rest => dropV (← get x); run prog env joins rest
  | .unreachable => throw "reached an impossible case"

end

/-- Run `main`; returns the result (as an interpreter value), the number of objects
allocated, and an error if anything leaked. -/
def runProgram (decls : Array Decl) : Except String (RVal × Nat) := do
  let prog := decls.foldl (fun m d => m.insert d.name d) {}
  let (v, h) ← (call prog "wiz.entry" #[]).run {}
  let r := toRVal h v
  let ((), h) ← (dropV v).run h
  unless h.objs.isEmpty do throw s!"{h.objs.size} objects leaked"
  pure (r, h.allocs)

end Wiz.IR
