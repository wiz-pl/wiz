/-!
# Universe levels

As in Lean: `Sort 0` is `Prop`, `Sort (u+1)` is `Type u`.

    Sort u : Sort (u+1)
    ((x : A) → B) : Sort (imax u v)     when A : Sort u, B : Sort v

`imax u v` is `0` when `v` is `0` and `max u v` otherwise. This makes `Prop`
**impredicative**: a Π into a proposition is a proposition, whatever it quantifies
over. Observational equality (stage 4) relies on that.

Declarations can be **universe polymorphic**: `def id.{u} {A : Sort u} (x : A) : A`
has a level parameter `u`, and each use `id.{v}` instantiates it.

The kernel needs to decide level equality, for example `max u (u+1) = u+1`. We
normalise levels to a canonical form, and two levels are equal if their normal forms
are. This is complete for `zero`/`succ`/`max`/`param`. For `imax` it is a sound
approximation, the same trade-off Lean makes.
-/

namespace Wiz

abbrev Name := String

inductive Level where
  | zero
  | succ (l : Level)
  | max (a b : Level)
  | imax (a b : Level)
  | param (name : String)
  /-- level metavariable (elaborator only) -/
  | mvar (id : Nat)
  /-- (mandatory sorts) a component sort of a `Π`/`Σ` (or a `ULift`'s content's sort)
  that the elaborator has not written yet: the sorts pass (`Wiz/Elab/Mark.lean`) fills
  every one before the kernel sees the declaration, and the kernel rejects one. The level
  unifier never assigns it. -/
  | hole
  deriving Repr, BEq, Inhabited, Hashable

namespace Level

def ofNat : Nat → Level
  | 0 => zero
  | n + 1 => succ (ofNat n)

instance : OfNat Level n := ⟨ofNat n⟩

def addOffset (l : Level) : Nat → Level
  | 0 => l
  | n + 1 => succ (addOffset l n)

/-- Substitute level parameters. -/
def instParams (ps : List String) (us : List Level) : Level → Level
  | param n => match ps.idxOf? n with
    | some i => us[i]?.getD (param n)
    | none => param n
  | succ l => succ (instParams ps us l)
  | max a b => max (instParams ps us a) (instParams ps us b)
  | imax a b => imax (instParams ps us a) (instParams ps us b)
  -- (the leaves by name, here and below: a new constructor must get its own case)
  | zero => zero
  | mvar m => mvar m
  | .hole => .hole

/-- Replace level metavariables using `f`. -/
partial def instMVars (f : Nat → Option Level) : Level → Level
  | mvar m => match f m with
    | some l => instMVars f l
    | none => mvar m
  | succ l => succ (instMVars f l)
  | max a b => max (instMVars f a) (instMVars f b)
  | imax a b => imax (instMVars f a) (instMVars f b)
  | zero => zero
  | param n => param n
  | .hole => .hole

def params : Level → List String
  | param n => [n]
  | succ l => params l
  | max a b | imax a b => params a ++ params b
  | zero | mvar _ | hole => []

def hasMVar : Level → Bool
  | mvar _ => true
  | succ l => hasMVar l
  | max a b | imax a b => hasMVar a || hasMVar b
  | zero | param _ | hole => false

/-- Does the level contain a `hole` (a sort the sorts pass has not filled)? -/
def hasHole : Level → Bool
  | hole => true
  | succ l => hasHole l
  | max a b | imax a b => hasHole a || hasHole b
  | zero | param _ | mvar _ => false

/-! ## Normal forms

A normal form is a list of `(atom, offset)` pairs read as the `max` of `atom + offset`,
where an atom is `none` (the constant zero), a parameter, a metavariable, or an `imax`
that couldn't be simplified. The list is sorted and has at most one entry per atom.
The constant entry is dropped if another entry already guarantees it. -/

inductive Atom where
  | const
  | param (n : String)
  | mvar (m : Nat)
  | imax (a b : List (Atom × Nat))
  /-- `Level.hole`: an opaque atom (the kernel rejects a hole before comparing levels) -/
  | hole
  deriving BEq, Repr, Inhabited

/-- A total order on atoms, so normal forms can be sorted. -/
partial def Atom.lt : Atom → Atom → Bool
  | .const, .const => false
  | .const, _ => true
  | _, .const => false
  | .param a, .param b => a < b
  | .param _, _ => true
  | _, .param _ => false
  | .mvar a, .mvar b => a < b
  | .mvar _, _ => true
  | _, .mvar _ => false
  | .hole, .hole => false
  | .hole, _ => true
  | _, .hole => false
  | .imax a b, .imax c d => toString (repr (a, b)) < toString (repr (c, d))

abbrev NF := List (Atom × Nat)

private def insertNF (x : Atom × Nat) : NF → NF
  | [] => [x]
  | y :: ys =>
    if x.1 == y.1 then (y.1, Nat.max x.2 y.2) :: ys
    else if x.1.lt y.1 then x :: y :: ys
    else y :: insertNF x ys

private def mergeNF (a b : NF) : NF := a.foldl (fun acc x => insertNF x acc) b

private def cleanup (n : NF) : NF :=
  let others := n.filter (·.1 != .const)
  let maxOther := others.foldl (fun m x => Nat.max m x.2) 0
  match n.find? (·.1 == .const) with
  | some (_, c) => if !others.isEmpty && c ≤ maxOther then others else n
  | none => n

/-- Is the level certainly nonzero? -/
private def nfNonZero (n : NF) : Bool := n.any fun (_, k) => k > 0

partial def normalize : Level → NF
  | zero => [(.const, 0)]
  | succ l => cleanup ((normalize l).map fun (a, k) => (a, k + 1))
  | max a b => cleanup (mergeNF (normalize a) (normalize b))
  -- (`b`'s normal form once: `normalize (max a b)` would normalise it again, and a chain
  -- of `imax`es along a telescope (a structure's constructor, say) exponentially often)
  | imax a b =>
    let nb := normalize b
    if nfNonZero nb then cleanup (mergeNF (normalize a) nb)
    else if nb == [(.const, 0)] then [(.const, 0)]
    else [(.imax (normalize a) nb, 0)]
  | param n => [(.param n, 0)]
  | mvar m => [(.mvar m, 0)]
  | .hole => [(.hole, 0)]

/-- Is the level nonzero under every instantiation of its parameters? -/
def isNeverZero (l : Level) : Bool := (normalize l).any fun (_, k) => k > 0

/-- A parameter that decides whether some `imax` in `l` is zero, if any. -/
def imaxParam? : Level → Option String
  | succ l => imaxParam? l
  | max a b => imaxParam? a <|> imaxParam? b
  | imax a b =>
    imaxParam? a <|> imaxParam? b <|> (if isNeverZero b then none else (params b).head?)
  | _ => none

/-- Definitional equality of levels. Normal forms decide it except for `imax`, so when
they differ we split on a parameter `p` that an `imax` depends on: `p = 0` or
`p = p' + 1` (where every `imax … p` becomes a `max`). -/
def equiv (a b : Level) : Bool := go 8 a b
where
  go (fuel : Nat) (a b : Level) : Bool :=
    normalize a == normalize b || match fuel, imaxParam? a <|> imaxParam? b with
      | fuel + 1, some p =>
        let set (u : Level) (l : Level) := instParams [p] [u] l
        go fuel (set zero a) (set zero b) && go fuel (set (succ (param p)) a) (set (succ (param p)) b)
      | _, _ => false

/-- `a ≤ b` for every instantiation (as far as `equiv` can tell). -/
def le (a b : Level) : Bool := equiv (max a b) b

/-- The least upper bound, kept small: `a` or `b` when one is below the other. -/
def join (a b : Level) : Level := if b.le a then a else if a.le b then b else max a b

/-- A small `k` with `l ≤ k + 1`: `k` for `succ k`, `u` for a parameter `u`. -/
def predBound : Level → Level
  | zero => zero
  | succ l => l
  | max a b => join (predBound a) (predBound b)
  | imax a b => join (predBound a) (predBound b)
  | l => l

/-- The level as a number, if it is closed. -/
def toNat? : Level → Option Nat
  | zero => some 0
  | succ l => (toNat? l).map (· + 1)
  | max a b => do return Nat.max (← toNat? a) (← toNat? b)
  | imax a b => do
    let b' ← toNat? b
    if b' == 0 then return 0 else return Nat.max (← toNat? a) b'
  | _ => none

/-- Is the level `0`? A closed level is computed (`toNat?`, exact: after a constant's
level parameters are instantiated the levels in its body are closed); otherwise `equiv`
decides (it answers `false` when it does not know). The proof marker `prf.{l}` suspends
its term exactly when this holds. -/
def isZero (l : Level) : Bool :=
  match toNat? l with
  | some n => n == 0
  | none => equiv l zero

/-- `l` as `base + k` with `k` maximal. -/
def toOffset : Level → Level × Nat
  | succ l => let (b, k) := toOffset l; (b, k + 1)
  | l => (l, 0)

partial def format : Level → String
  | l => match toNat? l with
    | some n => toString n
    | none => match toOffset l with
      | (b, 0) => match b with
        | param n => n
        | mvar m => s!"?u{m}"
        | hole => "_"
        | max a c => s!"max {formatArg a} {formatArg c}"
        | imax a c => s!"imax {formatArg a} {formatArg c}"
        | _ => "?"
      | (b, k) => s!"{formatArg b}+{k}"
where
  formatArg (l : Level) : String :=
    let s := format l
    if s.contains ' ' || s.contains '+' then s!"({s})" else s

instance : ToString Level := ⟨format⟩

end Level

end Wiz
