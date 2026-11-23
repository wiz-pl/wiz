import Wiz.Core.Term
import Wiz.Core.QPoly

/-!
# Values: the semantic domain for normalisation by evaluation

Values are terms that have been evaluated as far as possible:

* binders are represented by **closures** (an environment plus an unevaluated body), so
  instantiating a binder is just "evaluate the body in an extended environment";
* stuck computations are **neutrals**: a head (a local variable, an axiom or a
  metavariable) followed by a **spine** of eliminations waiting on it, such as
  applications `f a`, projections `p.1`, or a `let (x, y) := p; …` split.

Local variables inside values use **de Bruijn levels** (counting from the *outside*:
the first variable ever bound is level 0). Levels don't need shifting when you go under
a binder, which is why NbE uses them for values while terms use indices.

Converting level `x` to an index in a context of size `l`: `ix = l - x - 1`.

Reference: András Kovács, *elaboration-zoo* (github.com/AndrasKovacs/elaboration-zoo),
especially `01-eval-closures-debruijn` and `02-typecheck-closures-debruijn`.
-/

namespace Wiz

/-! ### A memoising thunk

Lean's `Thunk` is not memoising in this toolchain (`Thunk.get` is `fun x => x.fn ()`),
so a glued definition or a lazy induction that kept a plain one would be recomputed on
every `whnf`: conversion of a value behind a definition then re-evaluates the definition
at each step, exponentially on a machine's run (issue #256). `memoThunk` is a `Thunk`
whose function remembers its first result.

The cell's function is the pure computation that the value denotes: a definition's value
term evaluated at the captured levels and globals, in the empty environment, or a
projection/application of one. Forcing the same thunk twice therefore gives the same
result. A cell is owned by one `.unfold`/`.lazyInd` node; the value node itself may be
shared between occurrences and declarations (`Globals.valCache`, one entry per
`(name, levels)`), which is sound because `Globals` is persistent: insertion keeps the old
value, and an entry is dropped when a change can change what it computes
(`Globals.valCache`'s docstring). This is the invariant that makes the `unsafe`
implementation below unobservable; it is the same arrangement `Budget` uses for a counter
behind a pure interface. -/
unsafe def memoThunkImpl {α : Type} [Inhabited α] (f : Unit → α) : Thunk α := unsafeBaseIO do
  let cell ← IO.mkRef (none : Option α)
  pure (Thunk.mk fun _ => unsafeBaseIO do
    match ← cell.get with
    | some v => pure v
    | none =>
      let v := f ()
      cell.set (some v)
      pure v)

/-- A `Thunk` computed at most once. -/
@[implemented_by memoThunkImpl] opaque memoThunk {α : Type} [Inhabited α] (f : Unit → α) : Thunk α

abbrev Env (R : Type) := List (Val R)
abbrev VTy (R : Type) := Val R

/-- The head of the value that a kernel-internal failure leaves behind. Lean's `panic!`
(an eliminator applied to a value of the wrong shape, `xs[i]!` out of range) prints a
message and goes on with the type's default value. That default was `Sort 0`, a
well-formed type and proposition, which the checker then accepted (audit F2, K6). It is
now a **stuck unknown**: a constant that no declaration has, so nothing computes on it,
and a term read back from it is rejected (`unknown constant`). The batch commands do
not go on at all (`Wiz.exitOnPanic`). See `wiz-notes/kernel-lint.md`. -/
def kernelPanicName : Name := "kernel panic✝"

instance {R : Type} : Inhabited (Val R) := ⟨.neutral (.global kernelPanicName []) #[]⟩

/-- A quantity value as a polynomial: a literal, or a quantity variable. `none` for
anything else (a stuck computation, or an elaborator metavariable). -/
partial def Val.toPoly? {R : Type} [QRig R] [DecidableEq R] : Val R → Option (QPoly R)
  | .unfold _ _ _ v => Val.toPoly? v.get
  | .lazyInd _ _ _ _ _ _ _ _ _ _ v => Val.toPoly? v.get
  | .qlit r => some (QPoly.const r)
  | .neutral (.local l) #[] => some (QPoly.var l)
  | _ => none

/-- The value of the local variable at level `l`. -/
def Val.var {R : Type} (l : Lvl) : Val R := .neutral (.local l) #[]

/-- Heads are equal if they are the same variable, or the same global at equivalent
levels. (The stage 4c heads contain values, which `convNe` compares.) -/
def Head.equiv {R : Type} : Head R → Head R → Bool
  | .local a, .local b => a == b
  | .global n us, .global m vs =>
    n == m && us.length == vs.length && (us.zip vs).all fun (u, v) => u.equiv v
  | .mvar a, .mvar b => a == b
  | _, _ => false

/-- (13b) A type that is opaque here (`Globals.opaqueTo?`): its head and module. -/
def Globals.opaqueHere? {R : Type} (g : Globals R) : Val R → Option (Name × String)
  | .neutral (.global T _) _ => (g.opaqueTo? T).map (T, ·)
  | _ => none

end Wiz
