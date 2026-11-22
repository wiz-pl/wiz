import HotReload.Check

/-!
# Hot-reload P0: the interpreter

A single fuel-indexed function (`run`) has two commands: evaluate a term, or force
a slot at a generation. This is the shape the STC prototype uses for a total
kernel: no `mutual` block, no `partial`, and the fuel is the only recursion
measure. `read` is a lookup in the generation named by the `Pinned`; a function
value is a closure that stores the generation it was built in, so a nested
reloadable call cannot drift to the current generation (§4.4).

Slot values are thunks: `read` evaluates the body on first use, memoises the value
under `(generation, slot)`, and detects a re-entrant force (`blackhole`). A
divergent body therefore diverges in the reader, not in `install`; the swap stays
bounded (§4.3/§7.2).
-/

namespace HotReload

/-- The two commands of the interpreter. `read g s` is "force slot `s` at
generation `g`"; it is not a term, because the generation is runtime state. -/
inductive Cmd where
  | term (t : Tm)
  | read (g : Nat) (s : SlotId)
  deriving Repr

def envGet? : List Val → Nat → Option Val
  | [], _ => none
  | v :: _, 0 => some v
  | _ :: rest, n + 1 => envGet? rest n

def expectNat (v : Val) : Except Err Nat :=
  match v with
  | .nat n => .ok n
  | _ => .error (.typeError s!"expected Nat, got {Val.render v}")

def binNat (f : Nat → Nat → Nat) (a b : Val) : Except Err Val :=
  match a, b with
  | .nat x, .nat y => .ok (.nat (f x y))
  | _, _ => .error (.typeError s!"expected Nat, got {Val.render a} and {Val.render b}")

/-- Evaluate or force. Every recursive call is on `n`, the predecessor of the
caller's `n + 1`; the extra fuel for a read is spent by the `read` command itself
and then by the body. -/
def run : Nat → Runtime → Nat → List Val → Cmd → Except Err (Val × Runtime)
  | 0, _, _, _, _ => .error .outOfFuel
  | n + 1, rt, g, env, .term tm =>
    match tm with
    | .unit => .ok (.unit, rt)
    | .nat x => .ok (.nat x, rt)
    | .bool b => .ok (.bool b, rt)
    | .str s => .ok (.str s, rt)
    | .var i =>
      match envGet? env i with
      | some v => .ok (v, rt)
      | none => .error (.unbound i)
    | .lam b => .ok (.clos g env b, rt)
    | .app f a =>
      match run n rt g env (.term f) with
      | .error e => .error e
      | .ok (.clos g' env' b, rt1) =>
        match run n rt1 g env (.term a) with
        | .error e => .error e
        | .ok (v, rt2) => run n rt2 g' (v :: env') (.term b)
      | .ok (v, _) => .error (.typeError s!"applying a non-function: {Val.render v}")
    | .add a b =>
      match run n rt g env (.term a) with
      | .error e => .error e
      | .ok (va, rt1) =>
        match run n rt1 g env (.term b) with
        | .error e => .error e
        | .ok (vb, rt2) =>
          match binNat (fun x y => x + y) va vb with
          | .error e => .error e
          | .ok v => .ok (v, rt2)
    | .sub a b =>
      match run n rt g env (.term a) with
      | .error e => .error e
      | .ok (va, rt1) =>
        match run n rt1 g env (.term b) with
        | .error e => .error e
        | .ok (vb, rt2) =>
          match binNat (fun x y => x - y) va vb with
          | .error e => .error e
          | .ok v => .ok (v, rt2)
    | .mul a b =>
      match run n rt g env (.term a) with
      | .error e => .error e
      | .ok (va, rt1) =>
        match run n rt1 g env (.term b) with
        | .error e => .error e
        | .ok (vb, rt2) =>
          match binNat (fun x y => x * y) va vb with
          | .error e => .error e
          | .ok v => .ok (v, rt2)
    | .eq a b =>
      match run n rt g env (.term a) with
      | .error e => .error e
      | .ok (va, rt1) =>
        match run n rt1 g env (.term b) with
        | .error e => .error e
        | .ok (vb, rt2) => .ok (.bool (Val.beq va vb), rt2)
    | .ifE c t e =>
      match run n rt g env (.term c) with
      | .error err => .error err
      | .ok (.bool true, rt1) => run n rt1 g env (.term t)
      | .ok (.bool false, rt1) => run n rt1 g env (.term e)
      | .ok (v, _) => .error (.typeError s!"if on a non-Bool: {Val.render v}")
    | .pair a b =>
      match run n rt g env (.term a) with
      | .error e => .error e
      | .ok (va, rt1) =>
        match run n rt1 g env (.term b) with
        | .error e => .error e
        | .ok (vb, rt2) => .ok (.pair va vb, rt2)
    | .fst p =>
      match run n rt g env (.term p) with
      | .error e => .error e
      | .ok (.pair a _, rt1) => .ok (a, rt1)
      | .ok (v, _) => .error (.typeError s!"fst of a non-pair: {Val.render v}")
    | .snd p =>
      match run n rt g env (.term p) with
      | .error e => .error e
      | .ok (.pair _ b, rt1) => .ok (b, rt1)
      | .ok (v, _) => .error (.typeError s!"snd of a non-pair: {Val.render v}")
    | .nil _ => .ok (.nil, rt)
    | .cons h tail =>
      match run n rt g env (.term h) with
      | .error e => .error e
      | .ok (vh, rt1) =>
        match run n rt1 g env (.term tail) with
        | .error e => .error e
        | .ok (vt, rt2) => .ok (.cons vh vt, rt2)
    | .none _ => .ok (.none, rt)
    | .some v =>
      match run n rt g env (.term v) with
      | .error e => .error e
      | .ok (vv, rt1) => .ok (.some vv, rt1)
    | .read s => run n rt g env (.read g s)
    | .readAt p s =>
      match run n rt g env (.term p) with
      | .error e => .error e
      | .ok (.pinned g', rt1) => run n rt1 g env (.read g' s)
      | .ok (v, _) => .error (.typeError s!"readAt expects a Pinned, got {Val.render v}")
    | .const name =>
      match rt.helpers.find? (fun h => h.name == name) with
      | none => .error (.noHelper name)
      | some h => run n rt g [] (.term h.body)
    | .snapshot =>
      .error (.typeError "snapshot : IO Pinned cannot appear in a pure term")
  | n + 1, rt, _, _, .read gs s =>
    match rt.findGen gs with
    | none => .error (.noGen gs)
    | some gen =>
      match gen.findSlot s with
      | none => .error (.noSlot gs s)
      | some slot =>
        match memoFind rt.memo gs s with
        | some v => .ok (v, rt)
        | none =>
          if rt.forcing.contains (gs, s) then .error (.blackhole gs s)
          else
            let rt1 := { rt with forcing := (gs, s) :: rt.forcing }
            match run n rt1 gs [] (.term slot.body) with
            | .error e => .error e
            | .ok (v, rt2) =>
              .ok (v, { rt2 with
                          memo := ((gs, s), v) :: rt2.memo
                          forcing := rt.forcing })

def eval (fuel : Nat) (rt : Runtime) (g : Nat) (env : List Val) (t : Tm) :
    Except Err (Val × Runtime) :=
  run fuel rt g env (.term t)

/-- Apply a closure value. This is only for tests and the small examples; a term
application goes through `run`'s `.app` case. -/
def applyVal (fuel : Nat) (rt : Runtime) (f : Val) (a : Val) :
    Except Err (Val × Runtime) :=
  match f with
  | .clos g env body => run fuel rt g (a :: env) (.term body)
  | _ => .error (.typeError s!"applyVal on a non-function: {Val.render f}")

/-- `read p o`: one table load at the pinned generation. The memo update is the
only state change; the generation is never mutated. -/
def Runtime.read (rt : Runtime) (fuel : Nat) (p : Pinned) (o : Observable) :
    Except Err (Val × Runtime) :=
  match rt.findGen p.gen with
  | none => .error (.noGen p.gen)
  | some g =>
    match g.findSlot o.slot with
    | none => .error (.noSlot p.gen o.slot)
    | some s =>
      if s.ty == o.ty then run fuel rt p.gen [] (.read p.gen o.slot)
      else .error (.typeError "the Observable's type does not match the slot type")

/-- The derived one-shot read: one snapshot, one read. Two `readNow`s are two
snapshots and may see two generations; use `withPinned` for a consistent scope. -/
def Runtime.readNow (rt : Runtime) (fuel : Nat) (o : Observable) :
    Except Err (Val × Runtime) :=
  let p := rt.snapshot
  rt.read fuel p o

/-- The derived consistent scope: one snapshot for the whole continuation. -/
def Runtime.withPinned (rt : Runtime) (fuel : Nat) {α : Type}
    (k : Pinned → Runtime → Except Err (α × Runtime)) : Except Err (α × Runtime) :=
  k rt.snapshot rt

/-- The generation-local counter of a slot. This is the note's `version`; see
`revision` for the content hash and `README.md` roadblock 2 for the naming
decision (C7). -/
def Runtime.version (rt : Runtime) (p : Pinned) (o : Observable) : Except Err Nat :=
  match rt.findGen p.gen with
  | none => .error (.noGen p.gen)
  | some g =>
    match g.findSlot o.slot with
    | none => .error (.noSlot p.gen o.slot)
    | some s => .ok s.version

/-- The content identity of a slot body in this generation. This is what a memo,
`native_refl` key, or scry finding should use (not the generation id). -/
def Runtime.revision (rt : Runtime) (p : Pinned) (o : Observable) : Except Err String :=
  match rt.findGen p.gen with
  | none => .error (.noGen p.gen)
  | some g =>
    match g.findSlot o.slot with
    | none => .error (.noSlot p.gen o.slot)
    | some s => .ok s.revision

/-- The `#check x` line: the type is stable, the value is not printed (it would be
an unpinned read), and the slot/generation/revision are an info message (C11). -/
def Runtime.checkLine (rt : Runtime) (p : Pinned) (o : Observable) :
    Except Err String :=
  match rt.findGen p.gen with
  | none => .error (.noGen p.gen)
  | some g =>
    match g.findSlot o.slot with
    | none => .error (.noSlot p.gen o.slot)
    | some s =>
      .ok (s!"{s.surface} : Observable {Ty.render s.ty}\n" ++
        s!"  slot {s.id}, latest checked generation {g.id}, revision {s.revision}\n" ++
        s!"  read it with `read p {s.surface}` for `p : Pinned`; `snapshot : IO Pinned`")

end HotReload
