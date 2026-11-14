# Resources in Wiz

Wiz has several ways to talk about resources (memory cells, borrows, channel endpoints,
locks, effects), built at different stages. This page shows what they have in common and
how they fit together, using **one running example**: swapping two numbers through two
mutable borrows. The example is `examples/resources.wiz` (checked by the test group
`feral`). The design behind this page, with the plan for what comes next, is in
`wiz-notes/cohesion-resources.md`.

| layer | what it says | where |
|---|---|---|
| quantities | a value at quantity `1` is used exactly once: it can't be copied or dropped | the kernel ([4d](stages/04-data.md), [9e](stages/09-ffi.md)) |
| linear tokens | an opaque value at `1`, indexed by the resource it is about | `Chan p`, `MVar.Hole m`, `Lock.Guard l` ([25c–d](stages/25-concurrency.md)); `Eff1` ([10c](stages/10-effects.md)) |
| regions | a borrow lives in a scope `ρ`; nothing of `ρ` leaves it | `lib/Region.wiz` ([22g](stages/22-numbers.md)) |
| optics | a borrow of a place is its value plus a way to put it back | `lib/Optic.wiz` (Lens, `Lens.Indep`, `zoom`) |
| Feral | Rust's ownership in Wiz syntax, lowered to regions and optics | `lib/Feral.wiz` ([22j](stages/22-numbers.md)) |
| separation logic | an owned cell is `l ↦ v`; `⋆` splits the heap; the frame rule | `lib/HProp.wiz`, `lib/Hoare.wiz`, `lib/HoareTactics.wiz` ([24](stages/24-separation-logic.md)) |
| the bridge | a `&mut` to a heap cell is: read, run the function, write back | `lib/HeapBorrow.wiz` |

## One idea: one owner, handed back

Every layer says the same thing in its own terms: **a resource has exactly one owner, and
whoever borrows it hands it back.**

| | owned | borrowed exclusively | two at once (disjoint) | what a borrower can't touch |
|---|---|---|---|---|
| quantities and tokens | `(1 c : Chan p)` | `MVar.borrow m k` hands `k` a linear `Hole m` it must `fill` | two linear variables | variables it isn't passed |
| regions (Feral) | a `let mut` local | `Uniq.borrow σ s body`: `body` gets a `Uniq ρ S` and a `Lent ρ S` token in place of the lender | `Uniq.both`, two scopes | the lender, while lent (`Lent` has no operations) |
| optics | the whole `S` | `Lens S A`: the place's value and the backward function | `Lens.pair` of `Lens.Indep` lenses | every place independent of the lens (`zoom.frame`) |
| separation logic | `l ↦ v` | `wp (get l k) Q = ∃v. l ↦ v ⋆ (l ↦ v −∗ …)` | `(p ↦ a) ⋆ (q ↦ b)` | the frame (`Triple.frame`) |

The **frame rule** is the same fact read three ways: in types, a function can't touch what
it isn't given; in optics, a zoom through `l` keeps any place `m` with `Lens.Indep l m`
(`zoom.frame`); in separation logic, `{P} c {Q}` gives `{P ⋆ H} c {Q ⋆ H}`.

## The running example

### 1. Feral: the surface

```
feral
  fn swap {'a 'b} (x : &'a mut U64) (y : &'b mut U64) : Unit := {
    let t := *x;
    *x := *y;
    *y := t
  }
  fn swap_vals (a : U64) (b : U64) : U64 × U64 := {
    let mut x := a;
    let mut y := b;
    swap (&mut x) (&mut y);
    (x, y)
  }
end
```

Borrowing `x` twice (`swap (&mut x) (&mut x)`) is E0499, reported by Feral's front end and,
in the lowered program, by the kernel ([22j](stages/22-numbers.md)).

### 2. Regions and the functional model

`#lower` shows what `swap` is: a function of two linear borrow handles (`Uniq1`: used
once, handed back on every path, `Result1`) that hands both back.

```
def swap {ρa ρb : Region} (1 x : (Uniq1 ρa U64)) (1 y : (Uniq1 ρb U64)) : Result1 Unit ((1 _ : (Uniq1 ρa U64)) × (Uniq1 ρb U64)) :=
  let 1 (d_2, x) := Uniq1.peek x;
  let t := d_2;
  let 1 (d_5, y) := Uniq1.peek y;
  let 1 x := Uniq1.write x d_5;
  let 1 y := Uniq1.write y t;
  Result1.ok (()) (x, y)
```

`swap_vals` opens a `Uniq1.borrow` scope for each local; the scope's region `ρ` is fresh,
so no handle outlives it. There is no heap here: a `&mut` is a value passed in and passed
back (the Aeneas reading), so the specification is about values, and is proved by
computation:

```
feral
  …
  spec swap ensures (final x = old y) ensures (final y = old x)
  spec swap_vals ensures (result = (b, a))
end
def swap_ok (a b : U64) : swap.Spec a b := (rfl, rfl)
def swap_vals_spec (a b : U64) : swap_vals.Spec a b := rfl
```

A `spec` item states a function's specification as a Wiz proposition, `f.Spec`, which
is then proved in Wiz. In a clause an argument stands for its value, `result` for the
returned value, and `old x`/`final x` for an `&mut` argument's value on entry and when
the borrow ends. A linear handle can't be read in a proposition (its value is only
reachable by consuming it with `Uniq1.peek`/`end`), so `Spec` takes the `&mut` arguments'
*values*, lends them to the call in the borrow scopes a caller would open, and states the
clauses on the values the scopes hand back (`final x` is the lender's final value, so no
prophecy is needed). `swap.Spec a b` is

```
def swap.Spec (x : U64) (y : U64) : Prop :=
  Result.Holds (fun (r : ((Unit × U64) × U64)) => (r.2 = y) × (r.1.2 = x)) (
    Uniq1.borrow Region.static x (fun ρ1 h1 l1 x =>
      Uniq1.borrowIn ρ1 y x (fun ρ2 h2 l2 x y => swap x y)))
```

`Result.Holds P r` is total correctness (the call doesn't panic and `P` holds of its
value); `Result.All` is the partial reading.

### 3. Separation logic: the same function on heap cells

On a heap whose cells `p` and `q` hold the two numbers, calling the function is: read both
cells, run it, write the final values back. `lib/HeapBorrow.wiz` names that
(`Prog.borrowMut`, `Prog.borrowMut2`, and `Prog.borrowShr` for a `&`):

```
def swapCells (p q : Nat) : Prog U64 Unit :=
  Prog.borrowMut2 p q (fun a b => Result.map (fun (r : U64 × U64) => ((), r)) (swap_vals a b))
```

It can be verified two ways. The `x`-tactics ([24d](stages/24-separation-logic.md)) step
through it, computing the Feral function as they go:

```
def swapCells_spec (p q : Nat) (a b : U64) :
    Triple ((p ↦ a) ⋆ (q ↦ b)) (swapCells p q) (fun _ => (p ↦ b) ⋆ (q ↦ a)) := by
  xgo
```

Or the bridge turns the *functional* specification into the heap triple, with no
reasoning about the heap at all:

```
Prog.borrowMut2_spec : … Result.Holds (fun x => Q x.1 x.2.1 x.2.2) (f a b) →
  Triple ((p ↦ a) ⋆ (q ↦ b)) (Prog.borrowMut2 p q f)
    (fun c => ∃ v w. \[Q c v w] ⋆ ((p ↦ v) ⋆ (q ↦ w)))
```

This is the division of labour Wiz follows (decision CS9): **safe Feral code is verified in
the functional model**, and separation logic is the reading of the same program on
addresses, for what the functional model can't express (raw pointers, shared mutable
cells, threads). The frame comes for free: `xapp (swapCells_spec p q a b)` proves that a
third cell `r ↦ c` is untouched.

### 4. Quantities: the same discipline on tokens

The handles above are ordinary (ω) values: aliasing is ruled out by the shape of Feral's
lowering, not yet by types ([22g](stages/22-numbers.md), known gaps). Tokens that *are*
linear already exist, and follow the same "hand it back" shape in continuation-passing
style:

```
MVar.borrow : (m : MVar A) → (1 k : (a : A) → (1 h : MVar.Hole m) → IO B) → IO B
MVar.fill   : (m : MVar A) → (1 h : MVar.Hole m) → A → (1 next : IO B) → IO B
```

`MVar.Hole m` is `Uniq.borrow`'s `Lent` token made linear: the borrower must refill
exactly that cell, exactly once. When linear `match` lands (linear-case design, stage 2)
the region handles become linear the same way, and `Uniq.borrow`'s body must hand its
handle back on every path, including errors.

### 5. Effects

`lib/Eff.wiz`'s `State` effect is a third reading of a cell: an operation `get`/`put` in a
row, handled by `runState`. Its `Commute` proofs (two operations can be reordered) are, for
states on disjoint cells, what `⋆` gives for free; relating `Eff` state to `Prog` (an
effect observation into `W`, [24c](stages/24-separation-logic.md)) is planned, not built.

## Glossary: the same thing under different names

| idea | QTT / IO | Region / Feral | Optic | sep logic | Eff |
|---|---|---|---|---|---|
| a resource's index | `Hole m`, `Guard l` | region `ρ` | — | location `l` | — |
| exclusive access | `(1 h : Hole m)` | `Uniq ρ A`, `Mut ρ A S` | `Lens`, `Store A S` | `l ↦ v` | `State S` |
| shared access | ω value | `Shr ρ A` | `Lens.get` | `l ↦ v`, kept | `Reader` |
| maybe there | — | `MutOpt` | `Affine`, `ALens` | `∃`/`∨` over ownership | — |
| disjointness | separate variables | separate scopes | `Lens.Indep` | `⋆` | `Commute` |
| failure | `Chan.cancel` | `Result.err` | `Result` | `Prog.fail`, `wp fail = \[False]` | `Exn` |
| at most once | — (1 is exact) | Rust moves | `Affine` | `htop` (cells may be dropped) | `Eff1` (one-shot) |
