import Wiz
import Tests.Harness
import Tests.Elab

open Wiz

set_option compiler.extract_closed false

/-!
# Elaborator fuzzing

A seeded, grammar-driven generator of Wiz programs, and the properties a campaign
checks on every generated input:

* it does not panic and does not hang (the driver runs a campaign in a child process
  under `timeout`, so a crash or a hang is the campaign's exit status, and the seed
  printed before the input identifies it);
* acceptance and elaboration are deterministic (the same input, elaborated twice from
  the initial state, gives the same messages, the same declarations and the same
  definition bodies);
* a rejection always has a diagnostic, and every diagnostic's span is inside the
  input;
* `wiz fmt`'s output of an accepted input is still accepted, and declares the same
  things (`Fmt` is reported, not fixed here);
* a generated *ground* `Nat` definition evaluates to the value the generator meant
  (a miscompile oracle for `match`, `let`, the recursor and the kernel's evaluator);
* the inputs the generator means to be ill-typed (wrong type, missing argument,
  `refl` at a false equation, a universe off by one, …) are rejected.

Mutation inputs are generated too (`Sample.expect := .reject`): a well-typed program
with one declaration replaced by a template that must be rejected.  Every finding is
minimised (delta-debugging over commands) and printed with its seed; `--out DIR` also
writes it there.

`tests --elab-fuzz N SEED` runs the long campaign (see `Tests/Groups/ElabFuzz.lean`).
-/

namespace Tests.ElabFuzz

/-! ## A small deterministic random source -/

/-- SplitMix64: 64-bit state, reproducible on every platform (Nat arithmetic wrapped at
64 bits), and no dependency on a global random source. -/
structure Rng where
  state : UInt64 := 0
  deriving Repr, Inhabited

def Rng.step (r : Rng) : UInt64 × Rng :=
  let s := r.state + 0x9E3779B97F4A7C15
  let z0 := s
  let z1 := (z0 ^^^ (z0 >>> 30)) * 0xBF58476D1CE4E5B9
  let z2 := (z1 ^^^ (z1 >>> 27)) * 0x94D049BB133111EB
  (z2 ^^^ (z2 >>> 31), { state := s })

def Rng.ofSeed (seed : Nat) : Rng :=
  -- mix the seed in, so that 0, 1, 2, … give unrelated streams
  let r : Rng := { state := UInt64.ofNat seed }
  let (x, _) := r.step
  { state := x }

def Rng.below (r : Rng) (n : Nat) : Nat × Rng :=
  if n == 0 then (0, r) else
    let (x, r) := r.step
    ((x % UInt64.ofNat n).toNat, r)

/-! ## The generation monad -/

structure GState where
  rng : Rng
  fresh : Nat := 0
  deriving Repr, Inhabited

abbrev G := StateM GState

def G.rand (n : Nat) : G Nat := do
  let s ← get
  let (v, r) := s.rng.below n
  set { s with rng := r }
  pure v

def G.freshName (p : String) : G String := do
  let s ← get
  set { s with fresh := s.fresh + 1 }
  pure (p ++ toString s.fresh)

def G.oneOf (xs : Array String) (fallback : String := "") : G String := do
  if xs.isEmpty then pure fallback else
    pure xs[← G.rand xs.size]!

def G.bool : G Bool := do pure ((← G.rand 2) == 0)

/-- Weighted choice among monadic alternatives, each with a weight. -/
def G.weighted {α : Type} (xs : Array (Nat × G α)) (fallback : G α) : G α := do
  let total := xs.foldl (fun a (w, _) => a + w) 0
  if total == 0 then fallback else
    let mut k ← G.rand total
    for (w, x) in xs do
      if k < w then return (← x)
      k := k - w
    fallback

def G.eval {α : Type} (seed : Nat) (g : G α) : α :=
  (g.run { rng := Rng.ofSeed seed, fresh := 0 }).1

/-! ## The type language the generator writes in -/

inductive Ty where
  | nat
  | bool
  | unit
  | list (t : Ty)
  | prod (a b : Ty)
  | arr (a b : Ty)
  | enum (n : Nat)
  | wrap (t : Ty)
  | tree
  deriving Repr, BEq, Inhabited

partial def Ty.render : Ty → String
  | .nat => "Nat"
  | .bool => "Bool"
  | .unit => "Unit"
  | .list t => s!"(List {t.render})"
  | .prod a b => s!"({a.render} × {b.render})"
  | .arr a b => s!"({a.render} → {b.render})"
  | .enum n => s!"(Enum [{String.intercalate ", " ((List.range n).map (fun i => s!"e{i}"))}])"
  | .wrap t => s!"(Wrap {t.render})"
  | .tree => "Tree"

/-- Types a generated declaration may have.  No `Unit`/`Enum 0` at the top (they make
the generated term trivial), and arrows only one level deep to keep terms small. -/
def Ty.small : Array Ty :=
  #[.nat, .bool, .unit, .list .nat, .list .bool, .prod .nat .nat, .prod .bool .nat,
    .arr .nat .nat, .arr .nat .bool, .arr .bool .nat, .enum 1, .enum 2, .wrap .nat,
    .tree]

def Ty.deep : Array Ty :=
  Ty.small ++ #[.list (.list .nat), .prod (.prod .nat .nat) .nat, .arr .nat (.list .nat),
    .arr (.list .nat) .nat, .wrap (.list .nat), .prod .nat (.arr .nat .nat),
    .arr (.prod .nat .nat) .nat]

def Ty.all : Array Ty := Ty.deep

/-! ## The fixed prelude the generated programs sit on

The names are chosen so the generator can spell every type and every shape it needs;
`Nat` is an inductive with equations rather than a builtin, so a generated program never
depends on `lib/`. -/

def prelude : String := "
inductive Nat where
  | zero
  | succ (n : Nat)

inductive Bool where
  | true
  | false

inductive List (A : Type) where
  | nil
  | cons (x : A) (xs : List A)

inductive Wrap (A : Type) where
  | mk (x : A)

inductive Tree where
  | leaf
  | node (l r : Tree)

structure Pair where
  fst : Nat
  snd : Nat

def add : Nat → Nat → Nat
  | .zero, n => n
  | .succ m, n => .succ (add m n)

def pred : Nat → Nat
  | .zero => .zero
  | .succ n => n

def double : Nat → Nat
  | .zero => .zero
  | .succ n => .succ (.succ (double n))

def fib : Nat → Nat
  | .zero => .zero
  | .succ n => add (fib n) (fib n)

def not : Bool → Bool
  | .true => .false
  | .false => .true

def and : Bool → Bool → Bool
  | .true, b => b
  | .false, _ => .false

def isZero : Nat → Bool
  | .zero => .true
  | .succ _ => .false

def append {A : Type} : List A → List A → List A
  | .nil, ys => ys
  | .cons x xs, ys => .cons x (append xs ys)

def length {A : Type} : List A → Nat
  | .nil => .zero
  | .cons _ xs => .succ (length xs)

def swap {A B : Type} (p : A × B) : B × A := (p.2, p.1)

def id.{u} {A : Type u} (x : A) : A := x

def size : Tree → Nat
  | .leaf => .zero
  | .node l r => .succ (add (size l) (size r))

def unwrap {A : Type} (w : Wrap A) : A :=
  match w with
  | .mk x => x
"

/-- The prelude's globals as `(name, type)`. -/
def preludeGlobals : List (String × Ty) :=
  [("Nat.zero", .nat), ("pred", .arr .nat .nat), ("double", .arr .nat .nat),
   ("fib", .arr .nat .nat), ("Bool.true", .bool), ("Bool.false", .bool),
   ("not", .arr .bool .bool), ("isZero", .arr .nat .bool), ("Tree.leaf", .tree),
   ("size", .arr .tree .nat), ("add", .arr .nat (.arr .nat .nat)),
   ("and", .arr .bool (.arr .bool .bool))]

def candidates (ctx : List (String × Ty)) (ty : Ty) : List String :=
  (ctx.filter (·.2 == ty)).map (·.1) ++ (preludeGlobals.filter (·.2 == ty)).map (·.1)

/-- A leaf term of `ty` (no variables), used at depth 0. -/
partial def leafTerm (ty : Ty) : String :=
  match ty with
  | .nat => "Nat.zero"
  | .bool => "Bool.true"
  | .unit => "()"
  | .list t => s!"(List.nil : {(Ty.list t).render})"
  | .prod a b => s!"((({leafTerm a}) : {a.render}), (({leafTerm b}) : {b.render}))"
  | .arr a b => s!"(fun (_ : {a.render}) => (({leafTerm b}) : {b.render}))"
  | .enum _ => "'e0"
  | .wrap t => s!"(Wrap.mk ({leafTerm t}))"
  | .tree => "Tree.leaf"

/-! ## Terms

Every generated term is parenthesised where it is used as an argument, so the printer
never has to reason about precedence.  The generator is typed: it is given the type it
must produce and the variables in scope, so most samples are accepted (the point is to
elaborate them, not only to reject them); the deliberately ill-typed samples come from
the templates below. -/

partial def genTerm (ctx : List (String × Ty)) (ty : Ty) (d : Nat) : G String := do
  let cands := candidates ctx ty
  let structural : Array (Nat × G String) := #[
    (if cands.isEmpty then 0 else 30, do
      pure (← G.oneOf cands.toArray (leafTerm ty))),
    (8, do
      -- apply a function variable in scope whose result is the target type
      let fs := ctx.filterMap fun (n, t) => match t with
        | .arr a b => if b == ty then some (n, a) else none
        | _ => none
      if fs.isEmpty then pure (leafTerm ty)
      else
        let (n, a) ← G.weighted (fs.map fun p => (1, pure p)).toArray (pure ("_", .nat))
        let arg ← genTerm ctx a (d - 1)
        pure s!"({n} ({arg}))"),
    (6, do pure s!"(({← genTerm ctx ty (d - 1)}) : {ty.render})")
  ]
  if d == 0 then
    if cands.isEmpty then pure (leafTerm ty)
    else pure (← G.oneOf cands.toArray (leafTerm ty))
  else do
    let shape : Array (Nat × G String) :=
      structural ++
      #[(14, do
          -- a let of a random type, then the target
          let ty1 ← G.weighted (Ty.small.map (fun t => (1, pure t))) (pure .nat)
          let e1 ← genTerm ctx ty1 (d - 1)
          let x ← G.freshName "v"
          let e2 ← genTerm ((x, ty1) :: ctx) ty (d - 1)
          -- the ascribed binder type does not give the body an expected type when the
          -- `let` itself is inferred (e.g. an argument of a polymorphic function)
          pure s!"((let {x} : {ty1.render} := ({e1}); ({e2})) : {ty.render})"),
        (10, do
          -- a `let (a, b)` pattern over a random pair
          let a1 ← G.weighted (Ty.small.map (fun t => (1, pure t))) (pure .nat)
          let a2 ← G.weighted (Ty.small.map (fun t => (1, pure t))) (pure .nat)
          let e1 ← genTerm ctx (.prod a1 a2) (d - 1)
          let x ← G.freshName "a"
          let y ← G.freshName "b"
          let e2 ← genTerm ((x, a1) :: (y, a2) :: ctx) ty (d - 1)
          -- a pattern `let` is not inferable: ascribe it, so it may sit in an inferred
          -- position (e.g. the right-hand side of another `let (x, y)`)
          pure s!"((let ({x}, {y}) := ({e1}); ({e2})) : {ty.render})"),
        (5, do
          -- an `⟨a, b⟩` pattern over the generated `Pair` structure
          let e1 ← genTerm ctx (.nat) (d - 1)
          let e2 ← genTerm ctx (.nat) (d - 1)
          let x ← G.freshName "p"
          let y ← G.freshName "q"
          let body ← genTerm ((x, .nat) :: (y, .nat) :: ctx) ty (d - 1)
          pure s!"((let ⟨{x}, {y}⟩ := (⟨({e1}), ({e2})⟩ : Pair); ({body})) : {ty.render})"),
        (8, do
          -- `match` on Nat, at any target type
          let scrut ← genTerm ctx .nat (d - 1)
          let z ← genTerm ctx ty (d - 1)
          let k ← G.freshName "k"
          let s ← genTerm ((k, .nat) :: ctx) ty (d - 1)
          pure s!"(match (({scrut}) : Nat) with | .zero => ({z}) | .succ {k} => ({s}))"),
        (5, do
          -- `match` on Bool
          let scrut ← genTerm ctx .bool (d - 1)
          let a ← genTerm ctx ty (d - 1)
          let b ← genTerm ctx ty (d - 1)
          pure s!"(match (({scrut}) : Bool) with | .true => ({a}) | .false => ({b}))"),
        (4, do
          -- `match` on a list, at any target type
          let t ← G.weighted (Ty.small.map (fun t => (1, pure t))) (pure .nat)
          let scrut ← genTerm ctx (.list t) (d - 1)
          let z ← genTerm ctx ty (d - 1)
          let x ← G.freshName "x"
          let xs ← G.freshName "xs"
          let s ← genTerm ((x, t) :: (xs, .list t) :: ctx) ty (d - 1)
          pure s!"(match (({scrut}) : {(Ty.list t).render}) with | .nil => ({z}) | .cons {x} {xs} => ({s}))"),
        (8, do
          -- `(fun (x : A) => body) arg`
          let a ← G.weighted (Ty.small.map (fun t => (1, pure t))) (pure .nat)
          let x ← G.freshName "x"
          let body ← genTerm ((x, a) :: ctx) ty (d - 1)
          let arg ← genTerm ctx a (d - 1)
          pure s!"((fun ({x} : {a.render}) => (({body}) : {ty.render})) ({arg}))")
        ]
    let perTy : Array (Nat × G String) :=
      match ty with
      | .nat => #[
          (10, do pure s!"(Nat.succ ({← genTerm ctx .nat (d - 1)}))"),
          (10, do
            let a ← genTerm ctx .nat (d - 1)
            let b ← genTerm ctx .nat (d - 1)
            pure s!"(add ({a}) ({b}))"),
          (6, do pure s!"(pred ({← genTerm ctx .nat (d - 1)}))"),
          (6, do pure s!"(double ({← genTerm ctx .nat (d - 1)}))"),
          (4, do pure s!"(fib ({← genTerm ctx .nat (d - 1)}))")]
      | .bool => #[
          (10, do pure s!"(not ({← genTerm ctx .bool (d - 1)}))"),
          (8, do
            let a ← genTerm ctx .bool (d - 1)
            let b ← genTerm ctx .bool (d - 1)
            pure s!"(and ({a}) ({b}))"),
          (8, do pure s!"(isZero ({← genTerm ctx .nat (d - 1)}))")]
      | .unit => #[(4, (pure "()" : G String))]
      | .list t => #[
          (10, do
            let x ← genTerm ctx t (d - 1)
            let xs ← genTerm ctx (.list t) (d - 1)
            pure s!"(List.cons ({x}) ({xs}))"),
          (8, do
            let a ← genTerm ctx (.list t) (d - 1)
            let b ← genTerm ctx (.list t) (d - 1)
            pure s!"(append ({a}) ({b}))")]
      | .prod a b => #[
          (10, do
            -- the components are checked (a tuple component may be inferred: a bare
            -- `let (x, y)` there is not inferable, so each component is ascribed)
            let x ← genTerm ctx a (d - 1)
            let y ← genTerm ctx b (d - 1)
            pure s!"((({x}) : {a.render}), (({y}) : {b.render}))"),
          (6, do pure s!"(swap ({← genTerm ctx (.prod b a) (d - 1)}))"),
          -- a projection from a pair variable in scope whose field is the target type
          (8, do
            let fields := ctx.filterMap fun (n, t) => match t with
              | .prod x y => if x == ty then some (n, 1) else if y == ty then some (n, 2) else none
              | _ => none
            if fields.isEmpty then pure (leafTerm ty)
            else
              let (n, i) ← G.weighted (fields.map fun p => (1, pure p)).toArray (pure ("_", 1))
              pure s!"({n}.{i})")]
      | .arr a b => #[
          (10, do
            let x ← G.freshName "x"
            let body ← genTerm ((x, a) :: ctx) b (d - 1)
            pure s!"(fun ({x} : {a.render}) => (({body}) : {b.render}))")]
      | .enum n => #[
          (if n == 0 then 0 else 10, do
            pure s!"'e{← G.rand n}"),
          (if n == 0 then 0 else 6, do
            -- `ecase` on every tag: one branch per label, at the target type
            let scrut ← genTerm ctx (.enum n) (d - 1)
            let arms ← (List.range n).mapM fun _ => genTerm ctx ty (d - 1)
            pure s!"((ecase (({scrut}) : {(Ty.enum n).render}) [{", ".intercalate (arms.map fun a => s!"({a})")}]) : {ty.render})")]
      | .wrap t => #[
          (10, do pure s!"(Wrap.mk ({← genTerm ctx t (d - 1)}))")]
      | .tree => #[
          (8, do
            let a ← genTerm ctx .tree (d - 1)
            let b ← genTerm ctx .tree (d - 1)
            pure s!"(Tree.node ({a}) ({b}))")]
    G.weighted (perTy ++ shape) (pure (leafTerm ty))

/-! ## Ground `Nat` terms with a known value

A separate generator, because here the value matters: the campaign evaluates the
definition the elaborator stored and compares it with this number. -/

partial def genGroundNat (env : List (String × Nat)) (d : Nat) : G (String × Nat) := do
  if d == 0 then
    if env.isEmpty then pure ("Nat.zero", 0)
    else
      let (n, v) ← G.weighted (env.map fun e => (1, pure e)).toArray (pure ("Nat.zero", 0))
      pure (n, v)
  else
    let base : Array (Nat × G (String × Nat)) := #[
      (4, pure ("Nat.zero", 0)),
      (if env.isEmpty then 0 else 14, do
        let (n, v) ← G.weighted (env.map fun e => (1, pure e)).toArray (pure ("Nat.zero", 0))
        pure (n, v)),
      (14, do
        let (a, va) ← genGroundNat env (d - 1)
        pure (s!"(Nat.succ ({a}))", va + 1)),
      (10, do
        let (a, va) ← genGroundNat env (d - 1)
        let (b, vb) ← genGroundNat env (d - 1)
        pure (s!"(add ({a}) ({b}))", va + vb)),
      (6, do
        let (a, va) ← genGroundNat env (d - 1)
        pure (s!"(pred ({a}))", va - 1)),
      (6, do
        let (a, va) ← genGroundNat env (d - 1)
        pure (s!"(double ({a}))", va * 2)),
      (8, do
        let (a, va) ← genGroundNat env (d - 1)
        let x ← G.freshName "g"
        let (b, vb) ← genGroundNat ((x, va) :: env) (d - 1)
        pure (s!"(let {x} := ({a}); ({b}))", vb)),
      (6, do
        let x ← G.freshName "g"
        let arg := 4
        let (b, vb) ← genGroundNat ((x, arg) :: env) (d - 1)
        pure (s!"((fun ({x} : Nat) => ({b})) (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))",
          vb)),
      (6, do
        let (a, va) ← genGroundNat env (d - 1)
        let (z, vz) ← genGroundNat env (d - 1)
        let k ← G.freshName "gk"
        let (s, vs) ← genGroundNat ((k, va - 1) :: env) (d - 1)
        pure (s!"(match ({a}) with | .zero => ({z}) | .succ {k} => ({s}))",
          if va == 0 then vz else vs))
    ]
    G.weighted base (pure ("Nat.zero", 0))

/-! ## Declarations -/

/-- What the generator means the campaign to conclude about a sample. -/
inductive Expect where
  /-- the elaborator must accept it (any error is a finding) -/
  | accept
  /-- the elaborator must reject it (acceptance is a soundness finding) -/
  | reject
  /-- either verdict is fine; the other properties still apply -/
  | any
  deriving Repr, BEq, Inhabited

structure Sample where
  seed : Nat
  source : String
  expect : Expect := .any
  /-- the features the sample was meant to exercise (reported with a finding) -/
  features : List String := []
  /-- `(definition, expected value)` pairs, checked by evaluation -/
  nats : List (String × Nat) := []
  /-- a short human description of the shape -/
  what : String := ""
  deriving Inhabited

/-- Generate a well-typed declaration: a `def` (with binders, generated term), a
recursive `def` by equations, a `mutual` block, or a feature template. -/
def genDecl (features : List String) : G (String × List String × List (String × Nat)) := do
  let name ← G.freshName "d"
  match ← G.rand 12 with
  | 0 | 1 => do
      -- a plain def with 0–2 binders
      let ty ← G.weighted (Ty.all.map (fun t => (1, pure t))) (pure .nat)
      let nbind ← G.rand 3
      let mut ctx : List (String × Ty) := []
      let mut binders : String := ""
      let mut fs := ["def"]
      for _ in [0:nbind] do
        let bty ← G.weighted (Ty.small.map (fun t => (1, pure t))) (pure .nat)
        let x ← G.freshName "x"
        binders := binders ++ s!" ({x} : {bty.render})"
        ctx := (x, bty) :: ctx
        fs := "binder" :: fs
      let body ← genTerm ctx ty 3
      pure (s!"def {name}{binders} : {ty.render} := {body}", fs ++ features, [])
  | 2 => do
      -- a recursive def over Nat, then one over List
      let base ← genTerm [] .nat 1
      let k ← G.freshName "n"
      let step ← genTerm [(k, .nat)] .nat 2
      pure (s!"def {name} : Nat → Nat\n  | .zero => {base}\n  | .succ {k} => {step}",
        "recursion" :: features, [])
  | 3 => do
      let a ← G.freshName "m"
      let b ← G.freshName "n"
      pure (s!"mutual
def {a} : Nat → Nat
  | .zero => .zero
  | .succ k => {b} k
def {b} : Nat → Nat
  | .zero => .succ .zero
  | .succ k => {a} k
end", "mutual" :: features, [])
  | 4 => do
      -- a universe-polymorphic definition: level parameters, `Sort`, and a level
      -- expression; each template's levels are the ones its body actually has
      match ← G.rand 6 with
      | 0 => pure ("def " ++ name ++ ".{u} (A : Type u) : Type u := A → A",
          "universe" :: "levels" :: features, [])
      | 1 => pure ("def " ++ name ++ ".{u, v} (A : Type u) (B : Type v) : Type (max u v) := A × B",
          "universe" :: "levels" :: "max" :: features, [])
      | 2 => pure ("def " ++ name ++ ".{u, v} (A : Type u) (B : Type v) : Type (max u v) := A → B",
          "universe" :: "levels" :: "max" :: features, [])
      | 3 => pure ("def " ++ name ++ ".{u} (A : Type u) : Type (max u 1) := A → Type",
          "universe" :: "levels" :: "max" :: features, [])
      | 4 => pure ("def " ++ name ++ ".{u} : Type (u + 1) := Type u",
          "universe" :: "levels" :: "succ" :: features, [])
      | _ => pure ("def " ++ name ++ ".{u, v} (A : Sort (imax u v)) : Sort (imax u v) := A → A",
          "universe" :: "levels" :: "imax" :: features, [])
  | 5 => do
      -- instance search: a class, a base instance, a derived instance, a use
      let c ← G.freshName "C"
      let m ← G.freshName "m"
      let i ← G.freshName "i"
      let u ← G.freshName "u"
      pure ("class " ++ c ++ " (A : Type) where
  " ++ m ++ " : A → A
instance " ++ i ++ " : " ++ c ++ " Nat where
  " ++ m ++ " := fun x => Nat.succ x
def " ++ u ++ " (A : Type) [" ++ c ++ " A] (a : A) : A := " ++ c ++ "." ++ m ++ " a
def " ++ u ++ "b : Nat := " ++ u ++ " Nat Nat.zero", "class" :: "instance" :: "search" :: features, [])
  | 6 => do
      -- a structure: construction, projection, update
      let x ← G.freshName "p"
      let a ← genTerm [] .nat 1
      let b ← genTerm [] .nat 1
      pure ("def " ++ name ++ " (" ++ x ++ " : Pair) : Pair := { " ++ x ++ " with fst := add (" ++ a ++ ") (" ++ b ++ ") }
def " ++ name ++ "b : Nat := (" ++ name ++ " (⟨" ++ a ++ ", " ++ b ++ "⟩ : Pair)).fst",
        "structure" :: "update" :: features, [])
  | 7 => do
      -- implicit arguments: inference, named, explicit `@`
      let a ← genTerm [] .nat 1
      let ty ← G.weighted (Ty.small.map (fun t => (1, pure t))) (pure .nat)
      let body ← genTerm [] ty 1
      pure ("def " ++ name ++ " {A : Type} (x : A) : A := x
def " ++ name ++ "b : " ++ ty.render ++ " := " ++ name ++ " (" ++ body ++ ")
def " ++ name ++ "c : " ++ ty.render ++ " := " ++ name ++ " (A := " ++ ty.render ++ ") (" ++ body ++ ")
def " ++ name ++ "e : Nat := " ++ name ++ " (" ++ a ++ ")", "implicit" :: "named-arg" :: features, [])
  | 8 => do
      -- pattern-matching `let`s (pair, structure, unit)
      let a ← genTerm [] .nat 1
      let b ← genTerm [] .nat 1
      pure ("def " ++ name ++ " : Nat :=
  let (x, y) := (((" ++ a ++ ") : Nat), ((" ++ b ++ ") : Nat));
  add x y

def " ++ name ++ "b : Nat :=
  let ⟨x, y⟩ := (⟨(" ++ a ++ "), (" ++ b ++ ")⟩ : Pair);
  add x y

def " ++ name ++ "c : Nat := let () := (); (" ++ a ++ ")", "let" :: "pattern" :: features, [])
  | 9 => do
      -- an axiom (an opaque constant) and a `#check` of it
      let ty ← G.weighted (Ty.all.map (fun t => (1, pure t))) (pure .nat)
      pure ("axiom " ++ name ++ " : " ++ ty.render ++ "\n#check " ++ name,
        "axiom" :: "check" :: features, [])
  | 10 => do
      -- a partial definition (`partial (default := w)`), and a dependent function
      let x ← G.freshName "x"
      let body ← genTerm [(x, .nat)] .nat 2
      let dep ← G.freshName "dep"
      pure ("partial (default := fun n => n) def " ++ name ++ " (" ++ x ++ " : Nat) : Nat := " ++ body ++
        "\ndef " ++ dep ++ " : (A : Type) → A → A := fun A y => y\ndef " ++ dep ++
        "b : Nat := " ++ dep ++ " Nat Nat.zero",
        "partial" :: "dependent" :: features, [])
  | _ => do
      -- a coinductive observation: `coinductive`, corecursion with equations
      let st ← G.freshName "Stream"
      pure ("coinductive " ++ st ++ " (A : Type) where
  head : A
  tail : " ++ st ++ " A

def repeat" ++ st ++ " {A : Type} (a : A) : " ++ st ++ " A
  | .head => a
  | .tail => repeat" ++ st ++ " a

def " ++ name ++ " : Nat := (repeat" ++ st ++ " Nat.zero).head",
        "coinductive" :: "corecursion" :: features, [])

/-- A declaration that must be rejected.  Each template is a class of ill-typed
program the elaborator must not accept (acceptance is a soundness finding). -/
def genReject (features : List String) : G (String × List String) := do
  let name ← G.freshName "bad"
  let (src, what) ← match ← G.rand 10 with
    | 0 => pure (s!"def {name} : Nat = Bool := refl Nat", "refl at a false equation")
    | 1 => pure (s!"def {name} : Nat := Bool.true", "a Bool where a Nat is expected")
    | 2 => pure (s!"def {name} : Nat := add Nat.zero", "a missing argument")
    | 3 => pure (s!"def {name} (x : Nat) : Nat := x x", "a Nat applied as a function")
    | 4 => pure (s!"def {name} : Type := Type", "Type at its own level")
    | 5 => pure (s!"def {name} : Nat := Nat.succ (Bool.true)", "a Bool in a Nat constructor")
    | 6 => pure (s!"def {name} : Nat := Nat.succ Nat.zero Nat.zero", "too many arguments")
    | 7 => pure (s!"def {name} : List Nat := List.cons Bool.true List.nil",
        "an element of the wrong type")
    | 8 => pure (s!"def {name} : (Nat → Nat) := Nat.zero", "a Nat where a function is expected")
    | _ => pure (s!"def {name} : Nat := Nat.zero\n def {name} : Nat := Nat.succ Nat.zero",
        "a duplicate declaration")
  pure (src, what :: "reject" :: features)

/-- A well-typed program with one mutation that may or may not typecheck: the point is
that whichever way it goes, the elaborator's verdict must be stable and a rejection
must have a span. -/
def genMutant (features : List String) : G (String × List String) := do
  let d ← genDecl features
  let (decl, fs, _) := d
  let mut src := decl
  let mut what := "mutant"
  match ← G.rand 6 with
  | 0 => do
      src := src ++ "\ndef mutantHole : Nat := _"
      what := "hole in a def"
  | 1 => do
      src := src ++ "\ndef mutantHole (x : Nat) : Nat := _"
      what := "hole in a binder body"
  | 2 => do
      src := src ++ "\ndef mutantHole : Nat := (fun x => x)"
      what := "unapplied lambda"
  | 3 => do
      src := src ++ "\ndef mutantHole : Nat :=\n  let x := Nat.zero;\n  x x"
      what := "shadowed application"
  | 4 => do
      src := src ++ "\n#check mutantHole"
      what := "check of an unknown name"
  | _ => do
      src := src ++ "\ndef mutantHole : Nat :=\n  match Nat.zero with\n  | .zero => Nat.zero"
      what := "missing match alternative"
  pure (src, what :: fs)

/-- One generated input. -/
def genSample (seed : Nat) (depth : Nat := 3) : Sample :=
  G.eval seed do
    let kind ← G.weighted #[(60, pure "well"), (25, pure "reject"), (15, pure "mutant")] (pure "well")
    match kind with
    | "reject" => do
        let (decl, fs) ← genReject []
        pure { seed, source := prelude ++ "\n" ++ decl ++ "\n", expect := .reject,
               features := fs, what := "reject template" }
    | "mutant" => do
        let (decl, fs) ← genMutant []
        pure { seed, source := prelude ++ "\n" ++ decl ++ "\n", expect := .any,
               features := fs, what := "mutation" }
    | _ => do
        -- a well-typed program: one or two declarations, and a ground Nat definition
        let n ← G.rand 3
        let mut src := prelude ++ "\n"
        let mut fs : List String := []
        let mut nats : List (String × Nat) := []
        for _ in [0:n + 1] do
          let (decl, dfs, dns) ← genDecl []
          src := src ++ decl ++ "\n\n"
          fs := dfs ++ fs
          nats := dns ++ nats
        let (gterm, gval) ← genGroundNat [] depth
        let gname ← G.freshName "ground"
        src := src ++ s!"def {gname} : Nat := {gterm}\n"
        pure { seed, source := src, expect := .accept, features := "ground-nat" :: fs,
               nats := (gname, gval) :: nats, what := "well-typed program" }

/-! ## The properties -/

structure Failure where
  /-- a stable short name for the class of the finding -/
  kind : String
  /-- the evidence (error text, counts, …) -/
  detail : String
  deriving Repr, Inhabited

def Failure.render (f : Failure) : String := s!"{f.kind}: {f.detail}"

def errorsOf (s : CommandState ZeroOneMany) : Array Msg :=
  s.messages.filter (·.severity == .error)

def renderMsgs (input : String) (s : CommandState ZeroOneMany) : String :=
  "\n".intercalate (s.messages.toList.map (·.render input))

/-- The declarations the elaborator made, in order, with their types and values: what
"the elaboration" means for determinism and for the formatter round-trip. -/
def signature (g : Globals ZeroOneMany) : String :=
  "\n".intercalate ((Array.toList g.order).map fun n => s!"{n}\t{repr (g.find? n)}")

/-- A normal form is a `Nat` numeral: `Nat.zero`, or `Nat.succ` applied to one. -/
partial def natVal? (t : Term ZeroOneMany) : Option Nat :=
  -- a constructor: `con (pair (tag labels i) payload)`; `Nat.succ`'s payload is
  -- `(n, proof, ())`
  match t with
  | .con (.pair (.tag _ i) payload) =>
    if i == 0 then some 0
    else match payload with
      | .pair n _ => (natVal? n).map (· + 1)
      | _ => none
  | _ => none

/-- The span of a diagnostic is inside the input (`start ≤ stop ≤ length`). -/
def sevName : Severity → String
  | .error => "error"
  | .warning => "warning"
  | .info => "info"

def spanOk (input : String) (m : Msg) : Bool :=
  m.info.start ≤ input.length && m.info.stop ≤ input.length && m.info.start ≤ m.info.stop

/-- Every property of one sample.  Runs the frontend twice from the initial state (the
second run is what "stable across re-runs" means), evaluates the ground `Nat`
definitions, and formats and re-checks an accepted input. -/
structure Checked where
  failures : Array Failure := #[]
  accepted : Bool := false

def checkSample (s : Sample) : IO Checked := do
  let mut fs : Array Failure := #[]
  let input := s.source
  let s1 := Wiz.runFrontend (R := ZeroOneMany) input
  let s2 := Wiz.runFrontend (R := ZeroOneMany) input
  let e1 := errorsOf s1
  let e2 := errorsOf s2
  -- acceptance and messages are the same on both runs
  if (e1.isEmpty != e2.isEmpty) then
    fs := fs.push { kind := "nondeterministic-acceptance",
                    detail := s!"first: {e1.size} errors, second: {e2.size}" }
  let m1 := renderMsgs input s1
  let m2 := renderMsgs input s2
  if m1 != m2 then
    fs := fs.push { kind := "nondeterministic-messages",
                    detail := s!"first:\n{m1}\nsecond:\n{m2}" }
  let sig1 := signature s1.globals
  let sig2 := signature s2.globals
  if sig1 != sig2 then
    fs := fs.push { kind := "nondeterministic-elaboration",
                    detail := "the two runs' declarations differ" }
  -- expectations
  match s.expect with
  | .accept =>
    unless e1.isEmpty do
      fs := fs.push { kind := "well-typed-rejected", detail := e1[0]!.text }
  | .reject =>
    if e1.isEmpty then
      fs := fs.push { kind := "ill-typed-accepted",
                      detail := s!"the program elaborated with no errors ({e1.size})" }
  | .any => pure ()
  -- every diagnostic has a span inside the input
  for m in e1 ++ s1.messages.filter (·.severity == .warning) do
    unless spanOk input m do
      fs := fs.push { kind := "diagnostic-outside-input",
                      detail := s!"{sevName m.severity}: {m.text} at [{m.info.start}, {m.info.stop}) of {input.length}" }
  if !e1.isEmpty then
    -- a rejection must carry at least one diagnostic
    if s1.messages.all (·.severity != .error) then
      fs := fs.push { kind := "rejected-without-diagnostic", detail := "no error message" }
  -- the ground Nat values
  if e1.isEmpty then
    for (n, v) in s.nats do
      match s1.globals.find? n with
      | none => fs := fs.push { kind := "missing-definition", detail := n }
      | some d =>
        match d.value with
        | none => fs := fs.push { kind := "definition-without-value", detail := n }
        | some val =>
          match natVal? (Wiz.nf s1.globals val) with
          | none => fs := fs.push { kind := "ground-nat-not-a-numeral",
                                    detail := s!"{n}: expected {v}, got {repr (Wiz.nf s1.globals val)}" }
          | some got => unless got == v do
              fs := fs.push { kind := "miscompile",
                              detail := s!"{n}: expected {v}, got {got}" }
  -- the formatter round-trip (reported, not fixed here)
  if e1.isEmpty then
    let fr := Fmt.run ({} : CommandState ZeroOneMany) input { width := 100 }
    if fr.errors.isEmpty && fr.refused.isEmpty then
      let s3 := Wiz.runFrontend (R := ZeroOneMany) fr.text
      let e3 := errorsOf s3
      if !e3.isEmpty then
        fs := fs.push { kind := "fmt-output-rejected", detail := e3[0]!.text }
      else
        let sig3 := signature s3.globals
        if sig3 != sig1 then
          fs := fs.push { kind := "fmt-changes-elaboration",
                          detail := "the formatted text declares different things" }
  pure { failures := fs, accepted := e1.isEmpty }

/-! ## Minimisation

Delta-debugging over commands: drop a command while the same finding (its kind, and for
a rejection the same error text) still happens.  Commands are found by the parser, with
the same tables the campaign used. -/

def commandSpans (input : String) : Array (Nat × Nat) := Id.run do
  let chars := input.toList.toArray
  let mut pos := 0
  let mut out : Array (Nat × Nat) := #[]
  while pos < chars.size do
    let p := skipWs chars pos
    if p >= chars.size then break
    match parseCommand chars Builtin.tables p with
    | .ok (cmd, stop) =>
      out := out.push (cmd.info.start, stop)
      pos := stop
    | .error _ =>
      pos := recoverPos chars p
  out

/-- Remove the commands at `drop` (indices into `spans`). -/
def withoutCommands (input : String) (spans : Array (Nat × Nat)) (drop : List Nat) : String :=
  Id.run do
    let mut out := ""
    let mut prev := 0
    for (span, i) in spans.zipIdx do
      if drop.contains i then
        out := out ++ String.ofList (input.toList.toArray.extract prev span.1 |>.toList)
        prev := span.2
    out := out ++ String.ofList (input.toList.toArray.extract prev input.length |>.toList)
    out

/-- Does `src` still show `target`?  For a rejection finding the same error text must
still be there (positions move while shrinking); other findings keep their class. -/
def stillFails (target : Failure) (src : String) : IO Bool := do
  -- keep the sample's intended verdict: a `well-typed-rejected` is only a finding under
  -- `accept`, an `ill-typed-accepted` only under `reject`
  let expect := if target.kind == "ill-typed-accepted" then Expect.reject else .accept
  let ck ← checkSample { seed := 0, source := src, expect }
  match ck.failures.toList.find? (·.kind == target.kind) with
  | none => pure false
  | some f =>
    -- a rejection's first error text is the finding; the other classes stay the same
    -- while the seed numbers and spans of a smaller input change
    if target.kind == "well-typed-rejected" || target.kind == "fmt-output-rejected" then
      pure (f.detail == target.detail)
    else pure true

/-- The smallest command list still showing the finding (a bounded greedy pass). -/
def minimise (target : Failure) (src : String) (rounds : Nat := 8) : IO String := do
  let mut best := src
  for _ in [0:rounds] do
    let spans := commandSpans best
    let mut dropped := false
    for i in [0:spans.size] do
      if spans.size ≤ 1 then break
      let cand := withoutCommands best spans [i]
      if ← stillFails target cand then
        best := cand
        dropped := true
        break
    unless dropped do break
  pure best

/-! ## The campaign -/

structure Campaign where
  count : Nat := 64
  seed : Nat := 1
  /-- an explicit seed list (a fixed corpus); `count`/`seed` are then ignored -/
  seeds : Option (List Nat) := none
  depth : Nat := 3
  /-- write findings (source, seed and details) under this directory -/
  out : Option String := none
  /-- minimise each finding (commands only; can be slow) -/
  shrink : Bool := true
  deriving Inhabited

def writeFinding (dir : String) (seed : Nat) (f : Failure) (src : String) : IO Unit := do
  IO.FS.createDirAll dir
  let base := s!"{dir}/{f.kind}-{seed}"
  IO.FS.writeFile (base ++ ".wiz") src
  IO.FS.writeFile (base ++ ".txt")
    s!"seed: {seed}\nkind: {f.kind}\n{ f.detail }\n\n--- source ---\n{src}\n"

/-- Run `c.count` samples from `c.seed`; returns the number of findings.  Each sample's
seed is printed (and flushed) before it runs, so a crash or a hang in the child process
is attributable to the last printed seed. -/
def runCampaign (c : Campaign) : IO Nat := do
  let stdout ← IO.getStdout
  let mut findings := 0
  let mut accepted := 0
  let mut rejected := 0
  let mut feats : List (String × Nat) := []
  let seeds := c.seeds.getD ((List.range c.count).map (· + c.seed))
  for seed in seeds do
    let sample := genSample seed c.depth
    IO.println s!"begin {seed} {sample.what}"
    stdout.flush
    for f in sample.features do
      feats := match feats.find? (·.1 == f) with
        | some (k, _) => feats.map fun (k', n') => if k' == k then (k', n' + 1) else (k', n')
        | none => (f, 1) :: feats
    let ck ← checkSample sample
    if ck.accepted then accepted := accepted + 1 else rejected := rejected + 1
    for f in ck.failures do
      findings := findings + 1
      IO.println s!"FAIL {seed} {f.render}"
      stdout.flush
      if c.shrink then
        let small ← minimise f sample.source
        IO.println s!"MINIMISED {seed} ({small.length} chars)\n{small}"
        if let some dir := c.out then writeFinding dir seed f small
      else
        if let some dir := c.out then writeFinding dir seed f sample.source
    IO.println s!"end {seed} {ck.failures.size}"
    stdout.flush
  IO.println s!"stats: accepted={accepted} rejected={rejected}"
  let sorted := feats.mergeSort (fun a b => a.1 < b.1)
  IO.println s!"features: {", ".intercalate (sorted.map fun (k, n) => s!"{k}={n}")}"
  IO.println s!"campaign: {seeds.length} inputs{(if c.seeds.isSome then " from the fixed corpus" else s!" from seed {c.seed}")}, {findings} finding(s)"
  pure findings

/-- `--elab-fuzz N SEED [--depth D] [--out DIR] [--no-shrink]`. -/
partial def parseCampaign (c : Campaign) (positional : Nat := 0) : List String → Except String Campaign
  | [] => .ok c
  | "--depth" :: d :: r => match d.toNat? with
    | some n => parseCampaign { c with depth := n } positional r
    | none => .error s!"--depth needs a number: {d}"
  | "--out" :: d :: r => parseCampaign { c with out := some d } positional r
  | "--seeds" :: d :: r => match d.splitOn "," |>.mapM String.toNat? with
    | some ss => parseCampaign { c with seeds := some ss } positional r
    | none => .error s!"--seeds needs comma-separated numbers: {d}"
  | "--no-shrink" :: r => parseCampaign { c with shrink := false } positional r
  | "--seed" :: d :: r => match d.toNat? with
    | some n => parseCampaign { c with seed := n } positional r
    | none => .error s!"--seed needs a number: {d}"
  | n :: r => match n.toNat? with
    | some k =>
      match positional with
      | 0 => parseCampaign { c with count := k } 1 r
      | 1 => parseCampaign { c with seed := k } 2 r
      | _ => .error s!"unexpected argument: {n}"
    | none => .error s!"not a count or a flag: {n}"

def main (args : List String) : IO UInt32 := do
  match parseCampaign {} 0 args with
  | .error e => IO.eprintln e; pure 2
  | .ok c =>
    let n ← runCampaign c
    pure (if n == 0 then 0 else 1)


/-- `--elab-fuzz-replay FILE [accept|reject]`: run the properties on a saved input
(the second argument is its intended verdict, `accept` by default) and minimise every
finding, as the campaign does. -/
def replayMain (args : List String) : IO UInt32 := do
  let (file, expect) := match args with
    | [f] => (f, Expect.accept)
    | [f, "accept"] => (f, .accept)
    | [f, "reject"] => (f, .reject)
    | [f, "any"] => (f, .any)
    | _ => ("", .accept)
  if file == "" then
    IO.eprintln "usage: --elab-fuzz-replay FILE [accept|reject|any]"
    return 2
  let text ← IO.FS.readFile file
  let ck ← checkSample { seed := 0, source := text, expect, what := file }
  for f in ck.failures do
    IO.println f.render
    let small ← minimise f text
    IO.println s!"--- minimised ({small.length} chars) ---\n{small}"
  IO.println s!"{ck.failures.size} finding(s)"
  pure (if ck.failures.isEmpty then 0 else 1)

/-! ## Inspection modes (development aids, not test cases) -/

def dumpMain : IO UInt32 := do
  for i in [1:9] do
    let s := genSample i
    IO.println s!"===== seed {i}: {s.what}; expect {repr s.expect}; {s.features} ====="
    IO.println s.source
  pure 0

def oneMain (args : List String) : IO UInt32 := do
  match args with
  | [n] => match n.toNat? with
    | some seed =>
      let s := genSample seed
      IO.println s!"--- seed {seed}: {s.what}; expect {repr s.expect}; {s.features} ---"
      IO.println s.source
      IO.println "--- findings ---"
      for f in (← checkSample s).failures do IO.println f.render
      pure 0
    | none => IO.eprintln s!"not a seed: {n}"; pure 2
  | _ => IO.eprintln "usage: --elab-fuzz-sample SEED"; pure 2

end Tests.ElabFuzz
