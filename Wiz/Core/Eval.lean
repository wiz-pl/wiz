import Wiz.Core.Value
import Wiz.Core.Templates

/-!
# Evaluation, quotation, normalisation

Normalisation by evaluation (NbE) in two halves:

* `eval : Env → Term → Val` interprets syntax into the semantic domain. β-reduction
  happens for free, because applying a `Val.lam` just evaluates its closure body.
* `quote : Lvl → Val → Term` reads a value back into β-normal syntax, going under
  binders by applying closures to fresh variables `Val.var l`.

`nf = quote ∘ eval`.

Every eliminator has a semantic version (`vApp`, `vFst`, `vSnd`, `vSplit`,
`vAbsurd`). Each computes when its argument is a constructor (a β-rule) and otherwise
pushes itself onto the neutral's spine.

Globals are **glued** (stage 7a): `const n` evaluates to `Val.unfold`, which keeps the
name and computes the unfolding only when `whnf` needs it. Definitions marked `inline`
(constructors), or all of them when `Globals.eager` is set (as `nf` does), are
δ-unfolded at once. Axioms (no
definition) become neutrals.

These are `partial` because the untyped evaluator need not terminate (`Ω = (λx. x x)(λx. x x)`).
On well-typed terms they do.
-/

namespace Wiz

variable {R : Type} [QRig R] [DecidableEq R] [QuantitySyntax R]

/-- Are two quantity values equal? `none` if either is not a polynomial (unknown). -/
def sameQty (a b : Val R) : Option Bool := do
  return QPoly.equiv (← a.toPoly?) (← b.toPoly?)

/-- Are two quantities certainly different: both literals (no variables), and different?
`False` between two types is decided only then. Polynomials with variables that differ
(`q` and `1`) can become equal under a substitution (`q := 1`), so the equation must stay
stuck there: computing it to `False` proved `False` (P1, `wiz-notes/p1-stable.md`). -/
def qtyApart (a b : Val R) : Bool :=
  match a.toPoly?, b.toPoly? with
  | some p, some q => match p.isConst?, q.isConst? with
    | some _, some _ => !QPoly.equiv p q
    | _, _ => false
  | _, _ => false

/-- Unfold glued values (`Val.unfold`) until the head is not a definition: do this before
matching on a value's shape. -/
partial def whnf : Val R → Val R
  | .unfold _ _ _ v => whnf v.get
  | .lazyInd _ _ _ _ _ _ _ _ _ v => whnf v.get
  | v => v

/-- A value with its suspended inductions on constructors computed (`vInd`): they are
lazy for speed alone, so wherever a value's shape or read-back is looked at without `whnf`
(`quote`, the elaborator's unifier) they count as what they compute, as before they were
lazy. Inductions on numerals stay folded (`Val.lazyInd` since stage 7). -/
partial def unlazyCon : Val R → Val R
  | v@(.lazyInd _ _ _ _ _ _ _ x _ val) => if whnf x matches .con _ then unlazyCon val.get else v
  | v => v

/-- **Exercise 4.4b.** First projection. -/
partial def vFst : Val R → Val R
  -- (given) a projection of a glued value stays glued, like an application (`vApp`):
  -- `(f a).1` is computed only when needed (`f a` may be a big computation)
  | .unfold n us sp v => .unfold n us (sp.push .fst) (Thunk.mk fun _ => vFst v.get)
  | .lazyInd l I D w P m i x sp v => .lazyInd l I D w P m i x (sp.push .fst) (Thunk.mk fun _ => vFst v.get)  -- (given)
  --<sol
  | .pair a _ => a
  | .neutral h sp => .neutral h (sp.push .fst)
  | _ => panic! "vFst: ill-typed"
  --|ex
  --| | v => sorry
  --sol>

/-- **Exercise 4.4c.** Second projection. -/
partial def vSnd : Val R → Val R
  | .unfold n us sp v => .unfold n us (sp.push .snd) (Thunk.mk fun _ => vSnd v.get)  -- (given)
  | .lazyInd l I D w P m i x sp v => .lazyInd l I D w P m i x (sp.push .snd) (Thunk.mk fun _ => vSnd v.get)  -- (given)
  --<sol
  | .pair _ b => b
  | .neutral h sp => .neutral h (sp.push .snd)
  | _ => panic! "vSnd: ill-typed"
  --|ex
  --| | v => sorry
  --sol>

/-- `down` (Q4): `down (up a) ↦ a`; stuck on a neutral. -/
partial def vDown : Val R → Val R
  | .unfold _ _ _ v => vDown v.get
  | .lazyInd l I D w P m i x sp v => .lazyInd l I D w P m i x (sp.push .down) (Thunk.mk fun _ => vDown v.get)
  | .up a => a
  | .neutral h sp => .neutral h (sp.push .down)
  | _ => panic! "vDown: ill-typed"

/-- A description's tag field (Q4): `Enum ls`, or `ULift (Enum ls)` in a data type whose
universe is above `Type` (the tag is then lifted, `true`). -/
def tagField? (S : Val R) : Option (List Name × Bool) :=
  match whnf S with
  | .enum ls => some (ls, false)
  | .ulift _ A => match whnf A with
    | .enum ls => some (ls, true)
    | _ => none
  | _ => none

/-- The arity of a registered operation on numbers. -/
def natOpArity : Name → Nat
  | "nat.zero" => 0
  | "nat.succ" | "nat.pred" | "nat.log2" => 1
  | _ => 2

/-- The registered operations on numbers that return a number, computed natively. The
kernel, the interpreters and the native runtime (`runtime/`) agree with these, and
with the Prelude's definitions (`Nat.div`, …): `n / 0 = 0`, `n % 0 = n`, `log2 0 = 0`. -/
def natNative? : Name → Array Nat → Option Nat
  | "nat.succ", #[a] => some (a + 1)
  | "nat.pred", #[a] => some (a - 1)
  | "nat.add", #[a, b] => some (a + b)
  | "nat.sub", #[a, b] => some (a - b)
  | "nat.mul", #[a, b] => some (a * b)
  | "nat.div", #[a, b] => some (a / b)
  | "nat.mod", #[a, b] => some (a % b)
  | "nat.pow", #[a, b] => some (a ^ b)
  | "nat.land", #[a, b] => some (a &&& b)
  | "nat.lor", #[a, b] => some (a ||| b)
  | "nat.xor", #[a, b] => some (a ^^^ b)
  | "nat.shiftLeft", #[a, b] => some (a <<< b)
  | "nat.shiftRight", #[a, b] => some (a >>> b)
  | "nat.log2", #[a] => some a.log2
  | _, _ => none

/-- The value of a global registered as an operation on numbers (`builtin nat.add := …`):
`nat.zero` is the literal `0`, and an operation is a closure whose body is a
`Term.natOp` on its arguments, so it computes natively when they are literals. -/
def vBuiltin? (g : Globals R) (n : Name) : Option (Val R) := do
  -- (its `nat.` key: other registrations on `n`, such as `inline`, don't hide it)
  let (k, _) ← g.builtins.find? fun (k, m) => m == n && k.startsWith "nat."
  if k == "nat.zero" then some (.natLit 0)
  else if natOpArity k == 1 then some (.lam "a" (.mk [] (.natOp k #[.var 0])))
  else some (.lam "a" (.mk [] (.lam "b" (.natOp k #[.var 1, .var 0]))))

/-- `absurd` is always stuck: the empty type has no constructors. (A glued value is
unfolded first, as `Kernel.wiz` does: `absurd (lemma h)` was a panic, and the value that
came back was `Sort 0`; `wiz-notes/soundness-audit.md`, F2.) -/
partial def vAbsurd (m : Val R) : Val R → Val R
  | .unfold _ _ _ v => vAbsurd m v.get
  | .lazyInd _ _ _ _ _ _ _ _ _ v => vAbsurd m v.get
  | .neutral h sp => .neutral h (sp.push (.absurd m))
  | _ => panic! "vAbsurd: ill-typed"

/-- `(a → b) × (b → a)`: equality of propositions (propositional extensionality) -/
def vIff (a b : Val R) : Val R :=
  .sigma "_" (.qlit 0) (.pi "_" .default (.qlit 0) a (.mk [b] (.var 1)) (some 0))
    (.mk [a, b] (.pi "_" .default (.qlit 0) (.var 2) (.var 2) (some 0))) (some 0)

/-- Is this type (in weak head normal form) a proposition? `none` when its sort can't be
seen: a neutral, or a `Π`/`Σ` without a sort or with one that depends on a universe
parameter. Type equality needs to know: two propositions are equal when equivalent,
whatever their shapes (`True = (True → True)`), and comparing them by shape instead
proved `False` (a proposition can be the domain of a function type in `Type`). -/
def propSort? : Val R → Option Bool
  | .pi _ _ _ _ _ (some s) | .sigma _ _ _ _ (some s) | .unit s | .empty s | .ulift s _ =>
    if s.equiv 0 then some true else if s.isNeverZero then some false else none
  | .sort _ | .qty | .enum _ | .desc .. | .mu .. | .nu .. | .size | .sizeLt _ => some false
  | .neutral (.eq ..) #[] | .neutral (.eqTy ..) #[] => some true
  | _ => none

/-- The position of the last `absurd` in a spine. What comes before it is a term of an
empty type; what comes after is typed by its motive. -/
def lastAbsurd? (sp : Array (Elim R)) : Option Nat :=
  (List.range sp.size).reverse.find? fun i => match sp[i]? with
    | some (.absurd _) => true
    | _ => false

/-- (P2) What a closure's instantiation is once a read-back's step budget has run out
(`Budget`): stuck. -/
def outOfSteps : Val R := .neutral (.global " out of steps" []) #[]

/-- (P2) Is this neutral head a proof? Suspended proofs, the proof heads, and (with
`lazyProofs`) a stuck cast between propositions. -/
def proofHead (h : Head R) : Bool :=
  match h with
  | .prf .. | .refl .. | .reflTy _ | .transp .. => true
  | .cast A B _ _ => propSort? (whnf A) == some true && propSort? (whnf B) == some true
  | _ => false

/-- The predecessor of a size, for `con`/`cocon`/`out`: `↑s ↦ s`, `∞ ↦ ∞`; `none`
for a size variable, which can't be built from or observed. -/
partial def sizePred? : Val R → Option (Val R)
  | .unfold _ _ _ v => sizePred? v.get
  | .lazyInd _ _ _ _ _ _ _ _ _ v => sizePred? v.get
  | .szInf => some .szInf
  | .szSuc s => some s
  | _ => none

/-- The mark `vEq` puts at the end of the closure of a Σ it computed from an equation
(13n): a neutral whose head is a global name that cannot be written (it starts with a
space), so no user term evaluates to a closure that carries it. -/
def eqReductMark : Val R := .neutral (.global " eq-reduct" []) #[]

/-- The equation `a =_A b` that `vEq` computed (at a Σ type `A`) to this Σ, read back from
its closure: `(A, a, b)`. Only a Σ that carries `eqReductMark` qualifies. With
`Globals.quoteEqs` (the elaborator), `quote` reads such a Σ back as the equation `a = b`
(which evaluates to it again), so the equation survives a read-back (a `match` clause's
motive), and `rfl` can prove it by one `refl`. -/
def eqSigmaSides? : Val R → Option (Val R × Val R × Val R)
  | .sigma "e" _ _ (.mk [b, a, _, _, A, .neutral (.global " eq-reduct" []) #[]] _) _ => some (A, a, b)
  | _ => none

mutual

/-- **Exercise 1.1.** Evaluate a term in an environment.

* `var ix`: look it up in `env` (index 0 is the head).
* `const n us`: if there is a definition, a **glued** value `unfold n us #[] t`, where
  the thunk `t` evaluates the definition in the *empty* environment, after
  instantiating its level parameters with `us` (`Term.instLevels`). Declarations
  marked `inline` (constructors), or all of them if `g.eager`, are evaluated right
  away instead. Without a definition it is a stuck `neutral (.global n us) #[]`.
* `pi`/`lam`: don't evaluate the body; capture it with `env` in a `Closure`.
* `app`: evaluate both sides and use `vApp`.
* `letE`: evaluate the value and push it onto the environment for the body.
* `ann`: annotations have no computational content.
* `mvar`: (given) metavariables are stuck neutrals.

**Exercise 4.10** (stage 4c): `eq` uses `vEq`, `eqTy` uses `vEqType`, `cast` uses
`vCast`, and the proofs `refl`, `reflTy` and `transp` are stuck heads (proofs never
compute).

**Exercise 4.3** (stage 4b): the structural types. Constructors evaluate their parts,
`sigma` captures its second component in a closure, and eliminators use `vFst`,
`vSnd`, `vSplit` and `vAbsurd`. -/
partial def eval (g : Globals R) (env : Env R) : Term R → Val R
  -- (given) Q4: lifting
  | .ulift l A => .ulift l (eval g env A)
  | .up a => .up (eval g env a)
  | .down t => vDown (eval g env t)
  -- (given) P2: a marked term whose sort is `0` is a proof: suspended, never looked into.
  -- (At another level, or one that is still a parameter, it is an ordinary term.)
  | .prf l t => if l.isZero then suspend g env t else eval g env t
  --<sol
  -- (the checker rejects a variable out of scope before anything evaluates it; if one
  -- gets here it is a stuck unknown, not a panic's default value, `Sort 0`)
  | .var ix => env[ix]?.getD (.neutral (.global "out of scope✝" []) #[])
  | .const n us => if let some v := vBuiltin? g n then v else match g.find? n with
    | some { value := some v, levelParams, inline, .. } =>
      if inline || g.eager then eval g [] (g.instValue n v levelParams us)
      else .unfold n us #[] (Thunk.mk fun _ => eval g [] (g.instValue n v levelParams us))
    | _ => .neutral (.global n us) #[]
  | .natLit n => .natLit n
  | .natOp op args => vNatOp g op (args.map (eval g env))
  | .sort l => .sort l
  | .pi x bi q dom cod s => .pi x bi (eval g env q) (eval g env dom) (.mk env cod) s
  | .lam x body => .lam x (.mk env body)
  | .app f a => vApp g (eval g env f) (eval g env a)
  | .letE _ _ _ val body => eval g (eval g env val :: env) body
  | .ann tm _ => eval g env tm
  | .mvar m => .neutral (.mvar m) #[]
  | .sigma x q a b s => .sigma x (eval g env q) (eval g env a) (.mk env b) s
  | .pair a b => .pair (eval g env a) (eval g env b)
  | .fst t => vFst (eval g env t)
  | .snd t => vSnd (eval g env t)
  | .split q s z m x y b => vSplit g (eval g env q) (eval g env s) z (.mk env m) x y (.mk env b)
  | .unit l => .unit l
  | .tt => .tt
  | .empty l => .empty l
  | .absurd m t => vAbsurd (eval g env m) (eval g env t)
  -- (η for Unit: `u` is `()`, so the eliminator is its body)
  | .letUnit _ b => eval g env b
  | .eq A a b => vEq g (eval g env A) (eval g env a) (eval g env b)
  | .eqTy A B => vEqType g (eval g env A) (eval g env B)
  | .cast A B e t =>
    let vA := eval g env A
    let vB := eval g env B
    vCast g vA vB (suspend g env e) (eval g env t)
  | .refl A a => .neutral (.refl (eval g env A) (eval g env a)) #[]
  | .reflTy X => .neutral (.reflTy (eval g env X)) #[]
  | .transp A a P p b e =>
    let vA := eval g env A
    let va := eval g env a
    let vP := eval g env P
    let vb := eval g env b
    .neutral (.transp vA va vP (suspend g env p) vb (suspend g env e)) #[]
  | .qty => .qty
  | .qlit r => .qlit r
  | .enum ls => .enum ls
  | .tag ls i => .tag ls i
  | .ecase z m s bs => vEcase g z (.mk env m) (eval g env s) env bs
  | .desc l I => .desc l (eval g env I)
  | .dret i => .dret (eval g env i)
  | .darg q S D => .darg (eval g env q) (eval g env S) (eval g env D)
  | .drec q j D => .drec (eval g env q) (eval g env j) (eval g env D)
  | .dhrec q H j D => .dhrec (eval g env q) (eval g env H) (eval g env j) (eval g env D)
  | .delim v P a b c h D =>
    vDelim g v (eval g env P) (eval g env a) (eval g env b) (eval g env c) (eval g env h) (eval g env D)
  | .mu l I D i s h => .mu l (eval g env I) (eval g env D) (eval g env i) (eval g env s) (evalHint g env h)
  | .con x => .con (eval g env x)
  | .ind l I D v P m i x =>
    vInd g l (eval g env I) (eval g env D) v (eval g env P) (eval g env m) (eval g env i) (eval g env x)
  | .nu l I D i s h => .nu l (eval g env I) (eval g env D) (eval g env i) (eval g env s) (evalHint g env h)
  | .out x => vOut g (eval g env x)
  | .size => .size
  | .szInf => .szInf
  | .szSuc s => match eval g env s with
    | .szInf => .szInf
    | v => .szSuc v
  | .sizeLt s => .sizeLt (eval g env s)
  | .sfix l I D v P f s i x =>
    vSfix g l (eval g env I) (eval g env D) v (eval g env P) (eval g env f) (eval g env s)
      (eval g env i) (eval g env x)
  | .cocon x => .cocon (eval g env x)
  | .scase l q I D v P m s i x =>
    vScase g l (eval g env q) (eval g env I) (eval g env D) v (eval g env P) (eval g env m) (eval g env s)
      (eval g env i) (eval g env x)
  | .scofix l I D A f s i a =>
    .scofix l (eval g env I) (eval g env D) (eval g env A) (eval g env f) (eval g env s)
      (eval g env i) (eval g env a)
  | .coit l I D S st i s =>
    .coit l (eval g env I) (eval g env D) (eval g env S) (eval g env st) (eval g env i) (eval g env s)
  --|ex
  --| | .var ix => sorry
  --| -- (given) numerals; `vBuiltin?` registered operations
  --| | .natLit n => .natLit n
  --| | .natOp op args => vNatOp g op (args.map (eval g env))
  --| | .const n us => if let some v := vBuiltin? g n then v else sorry
  --| | .sort l => sorry
  --| | .pi x bi q dom cod s => sorry
  --| | .lam x body => sorry
  --| | .app f a => sorry
  --| | .letE _ _ _ val body => sorry
  --| | .ann tm _ => sorry
  --| | .mvar m => .neutral (.mvar m) #[]
  --| -- Exercise 4.3
  --| | .sigma x q a b s => sorry
  --| | .pair a b => sorry
  --| | .fst t => sorry
  --| | .snd t => sorry
  --| | .split q s z m x y b => sorry
  --| | .unit l => sorry
  --| | .tt => sorry
  --| | .empty l => sorry
  --| | .absurd m t => sorry
  --| -- Exercise 4.10
  --| | .eq A a b => sorry
  --| | .eqTy A B => sorry
  --| | .cast A B e t => sorry
  --| | .refl A a => sorry
  --| | .reflTy X => sorry
  --| | .transp A a P p b e => sorry
  --| | .qty => .qty
  --| | .qlit r => .qlit r
  --| -- Exercise 4.18: constructors evaluate their parts; eliminators use
  --| -- vEcase, vDelim, vInd and vOut.
  --| | .enum ls => sorry
  --| | .tag ls i => sorry
  --| | .ecase z m s bs => sorry
  --| | .desc l I => sorry
  --| | .dret i => sorry
  --| | .darg q S D => sorry
  --| | .drec q j D => sorry
  --| | .dhrec q H j D => sorry
  --| | .delim v P a b c h D => sorry
  --| | .mu l I D i s h => sorry
  --| | .con x => sorry
  --| | .ind l I D v P m i x => sorry
  --| | .nu l I D i s h => sorry
  --| | .out x => sorry
  --| | .coit l I D S st i s => sorry
  --| | .size => .size
  --| | .szInf => .szInf
  --| | .szSuc s => match eval g env s with
  --|   | .szInf => .szInf
  --|   | v => .szSuc v
  --| | .sizeLt s => .sizeLt (eval g env s)
  --| -- Exercise 4.22: the sized primitives (vSfix, and cocon/scofix are values)
  --| | .sfix l I D v P f s i x => sorry
  --| | .cocon x => sorry
  --| | .scase l q I D v P m s i x => sorry
  --| | .scofix l I D A f s i a => sorry
  --sol>

/-- (P2) A proof: a marked one (`Term.prf`), or a position the syntax marks (`cast`'s
equation, `transp`'s proofs). With `g.lazyProofs`, a suspended proof (`Head.prf`), never
evaluated; otherwise evaluated as usual. (A marker on a marker is one suspension.) -/
partial def suspend (g : Globals R) (env : Env R) (t : Term R) : Val R :=
  match t with
  | .prf _ t => suspend g env t
  | t =>
    if g.lazyProofs then .neutral (.prf env t) #[]
    else eval g env t

/-- Evaluate a display hint's arguments. -/
partial def evalHint (g : Globals R) (env : Env R) :
    Option (Name × List Level × List (Term R)) → Option (Name × List Level × List (Val R))
  | some (n, us, as) => some (n, us, as.map (eval g env))
  | none => none

/-- **Exercise 1.2a.** Semantic application.
A `lam` β-reduces; a neutral grows its spine (with `Elim.app`). Anything else is a
type error that the checker should have ruled out (use `panic!`). -/
partial def vApp (g : Globals R) : Val R → Val R → Val R
  -- (given) a glued application grows its spine, and its unfolding lazily
  | .unfold n us sp v, a => .unfold n us (sp.push (.app a)) (Thunk.mk fun _ => vApp g v.get a)
  | .lazyInd l I D w P m i x sp v, a => .lazyInd l I D w P m i x (sp.push (.app a)) (Thunk.mk fun _ => vApp g v.get a)
  --<sol
  | .lam _ c, a => Closure.inst g c a
  | .neutral h sp, a => .neutral h (sp.push (.app a))
  | _, _ => panic! "vApp: ill-typed application"
  --|ex
  --| | f, a => sorry
  --sol>

/-- **Exercise 1.2b.** Instantiate a closure with a value for its bound variable. -/
partial def Closure.inst (g : Globals R) : Closure R → Val R → Val R
  --<sol
  | .mk env body, a => match g.budget with
    | none => eval g (a :: env) body
    -- (P2, outside the kernel) reading a proof back, within its step budget
    | some b => if b.tick then eval g (a :: env) body else outOfSteps
  --|ex
  --| | .mk env body, a => sorry
  --sol>

/-- Instantiate a closure over two binders (`a` first, then `b`). -/
partial def Closure.inst2 (g : Globals R) : Closure R → Val R → Val R → Val R
  | .mk env body, a, b => match g.budget with
    | none => eval g (b :: a :: env) body
    | some bud => if bud.tick then eval g (b :: a :: env) body else outOfSteps

/-- **Exercise 4.4a.** `let (x, y) := s; body`: β-reduces on a `pair`, gets stuck on a
neutral. -/
partial def vSplit (g : Globals R) (q : Val R) (s : Val R) (z : Name) (m : Closure R) (x y : Name)
    (body : Closure R) : Val R :=
  let s := whnf s
  --<sol
  match s with
  | .pair a b => Closure.inst2 g body a b
  -- (P2) a proof is never evaluated to a pair: split it by η (`Σ` has η)
  | .neutral h sp =>
    if g.lazyProofs && proofHead h then Closure.inst2 g body (vFst s) (vSnd s)
    else .neutral h (sp.push (.split q z m x y body))
  | _ => panic! "vSplit: ill-typed"
  --|ex
  --| sorry
  --sol>

/- ### Data (stage 4d)

`vEcase`, `vDelim`, `vInd` and `vOut` compute on canonical arguments and are stuck on
neutrals. `vInd` and `vOut` use the description templates of `Wiz.Core.Templates`. -/

/-- `λ j. μ^s D j` and `λ j. ν^s D j` at a given size. -/
partial def muFamilyAt (l : Level) (I D s : Val R) : Val R :=
  .lam "j" (.mk [s, D, I] (.mu l (.var 3) (.var 2) (.var 0) (.var 1) none))

partial def nuFamilyAt (l : Level) (I D s : Val R) : Val R :=
  .lam "j" (.mk [s, D, I] (.nu l (.var 3) (.var 2) (.var 0) (.var 1) none))

/-- `λ j. μ D j`, the family being defined, as a value. -/
partial def muFamily (l : Level) (I D : Val R) : Val R :=
  .lam "j" (.mk [D, I] (.mu l (.var 2) (.var 1) (.var 0) .szInf none))

partial def nuFamily (l : Level) (I D : Val R) : Val R :=
  .lam "j" (.mk [D, I] (.nu l (.var 2) (.var 1) (.var 0) .szInf none))

/-- `⟦D⟧ X i` -/
partial def vInterp (g : Globals R) (l : Level) (I D X i : Val R) : Val R :=
  [I, D, X, i].foldl (vApp g) (eval g [] (Templates.interpTm l))

/-- `All D X P i xs` -/
partial def vAll (g : Globals R) (l v : Level) (I D X P i xs : Val R) : Val R :=
  [I, D, X, P, i, xs].foldl (vApp g) (eval g [] (Templates.allTm l v))

/-- **Exercise 4.19a.** `ecase` on a tag picks the branch (evaluated in `env`). -/
partial def vEcase (g : Globals R) (z : Name) (m : Closure R) (s : Val R) (env : Env R)
    (bs : List (Term R)) : Val R :=
  let s := whnf s
  --<sol
  match s with
  -- (a tag beyond the branches is ill-typed, like any other scrutinee that is not a tag:
  -- it was `var 0`, the innermost variable of `env`, silently)
  | .tag _ i => match bs[i]? with
    | some b => eval g env b
    | none => panic! "vEcase: tag out of range"
  | .neutral h sp => .neutral h (sp.push (.ecase z m env bs))
  | _ => panic! "vEcase: ill-typed"
  --|ex
  --| sorry
  --sol>

/-- **Exercise 4.19b.** The description eliminator:

    delim (ret i)     ↦ mret i
    delim (arg q S D) ↦ marg q S D (fun s => delim (D s))
    delim (rec q j D) ↦ mrec q j D (delim D)
    delim (hrec q H j D) ↦ mhrec q H j D (delim D)

The `fun s => …` is a closure over a small template, as in `vEq`. -/
partial def vDelim (g : Globals R) (v : Level) (P mret marg mrec mhrec D : Val R) : Val R :=
  let D := whnf D
  --<sol
  match D with
  | .dret i => vApp g mret i
  | .darg q S E =>
    -- s0 E1 mhrec2 mrec3 marg4 mret5 P6
    let ih : Val R := .lam "s" (.mk [E, mhrec, mrec, marg, mret, P]
      (.delim v (.var 6) (.var 5) (.var 4) (.var 3) (.var 2) (.app (.var 1) (.var 0))))
    [q, S, E, ih].foldl (vApp g) marg
  | .drec q j E => [q, j, E, vDelim g v P mret marg mrec mhrec E].foldl (vApp g) mrec
  | .dhrec q H j E => [q, H, j, E, vDelim g v P mret marg mrec mhrec E].foldl (vApp g) mhrec
  | .neutral h sp => .neutral h (sp.push (.delim v P mret marg mrec mhrec))
  | _ => panic! "vDelim: ill-typed"
  --|ex
  --| sorry
  --sol>

/-- A numeral as a constructor, one step deep: `0 ↦ zero`, `n+1 ↦ succ (natLit n)`, using
the constructors' definitions (not their `vBuiltin?` values). Other values are
unchanged. -/
partial def vNatView (g : Globals R) : Val R → Val R
  | .natLit n =>
    let ctor (k : Name) : Val R := match (g.builtins.lookup k).bind g.find? with
      | some { value := some v, .. } => eval g [] v
      | _ => panic! s!"numerals need `builtin {k}`"
    if n == 0 then ctor "nat.zero" else vApp g (ctor "nat.succ") (.natLit (n - 1))
  | v => v

/-- One step of a `Nat` operation whose result does not depend on a possibly-stuck
argument: `Nat.add 0 x ↦ x`, `Nat.mul 0 x ↦ 0`, `Nat.sub x 0 ↦ x`, `Nat.pow b 0 ↦ 1`.
Conversion does this before comparing a glued application by its spine: otherwise
`Nat.mul 0 s` against `Nat.mul 0 t` first compares the stuck applications `s` and `t`
(which may be large, or the very comparison being decided), only to find `0 = 0`.
The reduction is cheap: the definition's pattern match selects the zero branch before
forcing the other argument. -/
partial def vNatStep (g : Globals R) (v : Val R) : Val R :=
  match v with
  | .unfold n _ sp _ =>
    let zeroAt (i : Nat) : Bool := match sp[i]? with
      | some (.app (.natLit 0)) => true
      | _ => false
    if zeroAt 0 then
      match g.builtinKey? n with
      | some "nat.add" | some "nat.mul" => whnf v
      | _ => v
    else if zeroAt 1 then
      match g.builtinKey? n with
      | some "nat.sub" | some "nat.pow" => whnf v
      | _ => v
    else v
  | _ => v

/-- A `Nat` operation with a zero argument whose result does not depend on the other
argument: `Nat.add 0 x ↦ x`, `Nat.mul 0 x ↦ 0`, `Nat.sub x 0 ↦ x`, `Nat.pow b 0 ↦ 1`.
These are the definition's own reductions (the pattern match selects the zero branch
first), but they must not *force* the other argument: `Nat.mul 0 x` would otherwise
`whnf` an expensive or stuck `x` (a `Nat.div` under comparison) just to check whether it
is a numeral. -/
partial def natFast? (op : Name) (args : Array (Val R)) : Option (Val R) :=
  match op, args with
  | "nat.mul", #[x, _] => match whnf x with | .natLit 0 => some (.natLit 0) | _ => none
  | "nat.add", #[x, y] => match whnf x with | .natLit 0 => some y | _ => none
  | "nat.sub", #[x, y] => match whnf y with | .natLit 0 => some x | _ => none
  | "nat.pow", #[_, y] => match whnf y with | .natLit 0 => some (.natLit 1) | _ => none
  | _, _ => none

/-- A registered operation applied to all its arguments: native arithmetic on literals,
otherwise the operation's definition. -/
partial def vNatOp (g : Globals R) (op : Name) (args : Array (Val R)) : Val R :=
  if let some v := natFast? op args then v else
  -- the arguments as numerals, stopping at the first that isn't one: forcing the rest
  -- could run a numeral's recursion all the way down (`d * 2^64` is `d + d * (2^64 - 1)`,
  -- whose second argument is the next step, and so on)
  let lits : Option (Array Nat) := args.foldlM (init := #[]) fun acc a => match whnf a with
    | .natLit n => some (acc.push n)
    | _ => none
  let d : Val R := match (g.builtins.lookup op).bind g.find? with
    | some { value := some v, .. } => eval g [] v
    | _ => panic! s!"no definition for builtin {op}"
  -- not computed natively: the definition, kept glued under its name (`Nat.pred n`, not
  -- its unfolding; `succ` is a constructor). `a - n` with `a` stuck and `n` a numeral is
  -- `pred` applied `n` times to `a` (`Nat.subFrom` recurses on the numeral), a stuck term
  -- of size `n` built one step at a time (`x - 55296` ran out of memory): it stays the
  -- stuck application instead, compared by its arguments. (Not on a metavariable: it may
  -- still compute.)
  let unfold : Unit → Val R := fun _ =>
    let stuckSub : Bool := op == "nat.sub" && match args.map whnf with
      | #[.neutral h _, .natLit (_ + 1)] => !(h matches .mvar _)
      | _ => false
    match g.builtins.lookup op with
    | some n =>
      if stuckSub then .neutral (.global n []) (args.map .app)
      else if op == "nat.succ" then args.foldl (vApp g) d
      else .unfold n [] (args.map .app) (Thunk.mk fun _ => args.foldl (vApp g) d)
    | none => panic! s!"no definition for builtin {op}"
  match lits with
  | some ns => match natNative? op ns, op, ns with
    | some n, _, _ => .natLit n
    -- comparisons return a `Bool`: the definition's own result on small numerals
    | none, "nat.beq", #[a, b] =>
      whnf (vApp g (vApp g d (.natLit 0)) (.natLit (if a == b then 0 else 1)))
    | none, "nat.blt", #[a, b] =>
      whnf (vApp g (vApp g d (.natLit 0)) (.natLit (if a < b then 1 else 0)))
    | none, _, _ => unfold ()
  | none => unfold ()

/-- `hyps D X P f i xs` by `Templates.hypsTm`: the definition. -/
partial def vHypsTemplate (g : Globals R) (l v : Level) (I D X P f i xs : Val R) : Val R :=
  [I, D, X, P, f, i, xs].foldl (vApp g) (eval g [] (Templates.hypsTm l v))

/-- (given) `hyps D X P f i xs` computed directly on a canonical description, one step of
`Templates.hypsTm`'s `Desc.elim` at a time, without evaluating the template (most of the
cost of a data operation: `wiz-notes/kernel-eval.md`, F2):

    ret j        ↦ ()
    arg q S E    ↦ hyps (E xs.1) xs.2
    rec q j E    ↦ (f j xs.1, hyps E xs.2)
    hrec q H j E ↦ (fun h => f (j h) (xs.1 h), hyps E xs.2)

On a description that isn't canonical (stuck), the template from there on, which is what
the template itself reduces to after the steps already taken. -/
partial def vHyps (g : Globals R) (l v : Level) (I D X P f i xs : Val R) : Val R :=
  match whnf D with
  | .dret _ => .tt
  | .darg _ _ E => vHyps g l v I (vApp g E (vFst xs)) X P f i (vSnd xs)
  | .drec _ j E => .pair (vApp g (vApp g f j) (vFst xs)) (vHyps g l v I E X P f i (vSnd xs))
  | .dhrec _ _ j E =>
    -- h0 x1 j2 f3
    .pair (.lam "h" (.mk [vFst xs, j, f] (.app (.app (.var 3) (.app (.var 2) (.var 0))) (.app (.var 1) (.var 0)))))
      (vHyps g l v I E X P f i (vSnd xs))
  | _ => vHypsTemplate g l v I D X P f i xs

/-- **Exercise 4.19c.** Induction computes on constructors:

    ind P m i (con xs) ↦ m i xs (hyps D (μ D) P (fun j y => ind P m j y) i xs)

(`Templates.hypsTm`; the `fun j y => …` is a template closure). -/
partial def vIndStep (g : Globals R) (l : Level) (I D : Val R) (v : Level) (P m i x : Val R) : Val R :=
  let x := vNatView g (whnf x)
  --<sol
  match x with
  | .con xs =>
    -- y0 j1 m2 P3 D4 I5
    let f : Val R := .lam "j" (.mk [m, P, D, I]
      (.lam "y" (.ind l (.var 5) (.var 4) v (.var 3) (.var 2) (.var 1) (.var 0))))
    let hyps := vHyps g l v I D (muFamily l I D) P f i xs
    [i, xs, hyps].foldl (vApp g) m
  | .neutral h sp => .neutral h (sp.push (.ind l I D v P m i))
  | _ => panic! "vInd: ill-typed"
  --|ex
  --| sorry
  --sol>

/-- `ind` on a numeral `n + 1`, or on a constructor, is computed only when needed
(`Val.lazyInd`): the hypotheses of `con xs` are `ind` on its recursive fields, so
computing them eagerly would go all the way down (to `0`, or to the end of a list) even
for a method that ignores them (a `match`: `T.casesOn`), which made a `match` on a list
cost its length (`wiz-notes/kernel-eval.md`). Not for a normal form (`g.eager`, `nf`):
`ind` on a constructor is a redex, which a normal form must not contain; and not with
`--eager-proofs` (`!g.lazyProofs`), where the evaluator runs everything as it did before
(the D1 experiments' loops are loops of that evaluator). -/
partial def vInd (g : Globals R) (l : Level) (I D : Val R) (v : Level) (P m i x : Val R) : Val R :=
  match whnf x with
  | .natLit (_ + 1) => .lazyInd l I D v P m i x #[] (Thunk.mk fun _ => vIndStep g l I D v P m i x)
  | .con _ => if g.eager || !g.lazyProofs then vIndStep g l I D v P m i x
    else .lazyInd l I D v P m i x #[] (Thunk.mk fun _ => vIndStep g l I D v P m i x)
  | _ => vIndStep g l I D v P m i x

/-- **Exercise 4.22a.** Sized recursion unfolds on a constructor, with the recursive
calls at size `∞` (sizes are irrelevant at runtime):

    sfix P f s i (con xs) ↦ f ∞ (fun j i y => sfix P f j i y) i (con xs) -/
partial def vSfix (g : Globals R) (l : Level) (I D : Val R) (v : Level) (P f s i x : Val R) : Val R :=
  let x := vNatView g (whnf x)
  --<sol
  match x with
  | .con _ =>
    -- y0 i1 j2 f3 P4 D5 I6
    let rec_ : Val R := .lam "j" (.mk [f, P, D, I] (.lam "i" (.lam "y"
      (.sfix l (.var 6) (.var 5) v (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)))))
    [.szInf, rec_, i, x].foldl (vApp g) f
  | .neutral h sp => .neutral h (sp.push (.sfix l I D v P f s i))
  | _ => panic! "vSfix: ill-typed"
  --|ex
  --| sorry
  --sol>

/-- **Exercise 4.22b.** Sized case analysis: `scase P m s i (con xs) ↦ m ∞ i xs` (the
size of the fields is irrelevant at runtime, and so is the case's quantity `q`). -/
partial def vScase (g : Globals R) (l : Level) (q I D : Val R) (v : Level) (P m s i x : Val R) : Val R :=
  let x := vNatView g (whnf x)
  --<sol
  match x with
  | .con xs => [.szInf, i, xs].foldl (vApp g) m
  | .neutral h sp => .neutral h (sp.push (.scase l q I D v P m s i))
  | _ => panic! "vScase: ill-typed"
  --|ex
  --| sorry
  --sol>

/-- **Exercise 4.19d.** Observing an unfolding runs one step and re-wraps the
recursive positions:

    out (coit S step i s) ↦ map D S (ν D) (fun j s => coit S step j s) i (step i s) -/
partial def vOut (g : Globals R) (x : Val R) : Val R :=
  let x := whnf x
  --<sol
  match x with
  | .coit l I D S step i s =>
    -- s0 j1 step2 S3 D4 I5
    let f : Val R := .lam "j" (.mk [step, S, D, I]
      (.lam "s" (.coit l (.var 5) (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))))
    [I, D, S, nuFamily l I D, f, i, [i, s].foldl (vApp g) step].foldl (vApp g) (eval g [] (Templates.mapTm l))
  | .cocon xs => xs
  | .scofix l I D A f _ i a =>
    -- a0 i1 f2 A3 D4 I5
    let rec_ : Val R := .lam "i" (.mk [f, A, D, I]
      (.lam "a" (.scofix l (.var 5) (.var 4) (.var 3) (.var 2) .szInf (.var 1) (.var 0))))
    vOut g ([.szInf, rec_, i, a].foldl (vApp g) f)
  -- a cast between two `ν` types of a family is observed through (`vCastData`)
  | .neutral (.cast A B e t) #[] => match whnf A, famPayloadEq? g (whnf A) (whnf B) e with
    | .nu .., some (Xi, Xi', e') => vCast g Xi Xi' e' (vOut g t)
    | _, _ => .neutral (.cast A B e t) #[.out]
  | .neutral h sp => .neutral h (sp.push .out)
  | _ => panic! "vOut: ill-typed"
  --|ex
  --| sorry
  --sol>

/- ### Observational equality (stage 4c)

`a = b` at type `A` is not an inductive type. It **computes** by `A`:

    (f = g : (x : A) → B)    ↦  (x :0 A) → f x = g x                    funext
    (p = q : (x : A) × B)    ↦  (e :0 p.1 = q.1) × cast (B p.1) (B q.1) _ p.2 = q.2
    (u = v : Unit), Empty    ↦  True
    (P = Q : Prop)           ↦  (P → Q) × (Q → P)                       propext
    (X = Y : Type u)         ↦  vEqType X Y
    otherwise (A neutral)    ↦  stuck: neutral (Head.eq A a b)

Some results need new binders (`(x :0 A) → …`). Values can't contain Lean functions,
so these are **closures over small term templates**: the closure's environment holds
the values involved, and the template refers to them by de Bruijn index. Index 0 is
the new binder, and index `i + 1` is the environment's `i`-th entry.

All generated binders have quantity 0, since they are inside propositions.

Reference: Pujet & Tabareau, *Observational Equality: Now for Good* (POPL 2022). -/

/-- **Exercise 4.11a.** Observational equality at type `A`. See the table above.
`p = q` at a Σ type needs a proof that `B p.1 = B q.1`; build it with
`transp A₁ p.1 (fun y _ => B p.1 = B y) (reflTy (B p.1)) q.1 e`. For `Prop`, use
`Level.equiv l 0`; for `Type u` (`Level.isNeverZero`) it's `vEqType`. Otherwise
it's stuck. At a proposition (`propSort?`), the equation is `True` (proof irrelevance);
in the Σ rule, if `A₁` is a proposition, the proof is just `reflTy (B p.1)`. -/
partial def vEq (g : Globals R) (A a b : Val R) : Val R :=
  -- numerals: decide directly, or else look one step inside (`vNatView`)
  if let (.natLit n, .natLit m) := (whnf a, whnf b) then (if n == m then .unit 0 else .empty 0) else
  -- (stuck, it keeps its sides as written: their names, for display and for `match`)
  let stuck : Val R := .neutral (.eq A a b) #[]
  let A := whnf A
  let a := vNatView g (whnf a)
  let b := vNatView g (whnf b)
  -- (given) Q4: at `ULift A`, by `A`: the boxed values are equal when their contents are;
  -- a lifted proposition has one inhabitant up to η, so the equation is `True`
  if let .ulift _ A₁ := A then
    match propSort? (whnf A₁) with
    | some true => .unit 0
    | some false => vEq g A₁ (vDown a) (vDown b)
    | none => .neutral (.eq A a b) #[]
  else
  --<sol
  let v (i : Nat) : Term R := .var i
  -- at a proposition: proof irrelevance (an equation at a proposition is ill typed, and
  -- any two proofs are convertible, so it is `True`; never `False`)
  if propSort? A == some true then .unit 0 else
  match A with
  | .pi x _ _ A₁ B _ =>
    -- (x :0 A₁) → (B x ∋ a x = b x); env: b, a, B
    .pi x .default (.qlit 0) A₁ (.mk [b, a, .lam x B] (.eq (.app (v 3) (v 0)) (.app (v 2) (v 0)) (.app (v 1) (v 0)))) (some 0)
  | .sigma x _ A₁ B _ =>
    -- env (inside the Σ, after `e`): b, a, B, A₁
    let P : Term R := .lam "y" (.lam "_" (.eqTy (.app (v 5) (.fst (v 4))) (.app (v 5) (v 1))))
    -- (if `A₁` is a proposition, `p.1 ≡ q.1` by irrelevance, so `B p.1 ≡ B q.1`: `reflTy`
    -- proves it, and `transp` along a proposition would be ill typed)
    let apB : Term R := if propSort? (whnf A₁) == some true then .reflTy (.app (v 3) (.fst (v 2)))
      else .transp (v 4) (.fst (v 2)) P (.reflTy (.app (v 3) (.fst (v 2)))) (.fst (v 1)) (v 0)
    let body : Term R := .eq (.app (v 3) (.fst (v 1)))
      (.cast (.app (v 3) (.fst (v 2))) (.app (v 3) (.fst (v 1))) apB (.snd (v 2))) (.snd (v 1))
    -- the equation's own type `A` and the mark ride along at the end of the environment,
    -- unused by the body: `eqSigmaSides?` reads `A`, `a`, `b` back, so that `quote` gives
    -- back the equation and the elaborator's `rfl` proves it by one `refl` (13n)
    .sigma "e" (.qlit 0) (vEq g A₁ (vFst a) (vFst b)) (.mk [b, a, .lam x B, A₁, A, eqReductMark] body) (some 0)
  | .unit _ | .empty _ => .unit 0
  | .enum _ => match a, b with
    | .tag _ i, .tag _ j => if i == j then .unit 0 else .empty 0
    | _, _ => stuck
  | .mu l I D i _ _ => match a, b with
    | .con x, .con y => (vEqPayload g l I (muFamily l I D) i D x y).getD stuck
    | _, _ => stuck
  | .sort l =>
    if l.equiv 0 then
      -- (a → b) × (b → a)
      vIff a b
    else if l.isNeverZero then vEqType g a b
    else stuck
  -- equality of description codes, structurally (4g)
  | .desc l I => vEqDesc g l I a b
  | _ => stuck
  --|ex
  --| sorry
  --sol>

/-- Equality of two payloads `x y : ⟦D⟧ X i`, by the description: constructor by
constructor, so that `succ m = succ n` is `m = n` (and not, through the Σ rule, an
equation with a cast along the tags' equation, which without regularity would be stuck):

    ret j          ↦ True                       (the index proofs are irrelevant)
    arg q (Enum) E ↦ by the tags: equal ↦ the rest at `E tag`; different ↦ the
                     Σ rule (a pair whose first component is False); not both tags ↦
                     none (the whole equation is stuck)
    arg q S E      ↦ `x = y` at the Σ type `⟦arg q S E⟧ X i` (the Σ rule)
    rec q j E      ↦ (x.1 = y.1 : X j) × (the rest at E), or just x.1 = y.1 if E is `ret`
    hrec q H j E   ↦ (x.1 = y.1 : (h : H) → X (j h)) × (the rest at E), likewise

The choice between rules depends only on `D` and on whether tags are canonical (computed or
stuck), so it is stable under substitution. -/
partial def vEqPayload (g : Globals R) (l : Level) (I X i D x y : Val R) : Option (Val R) :=
  let pairTy (A B : Val R) : Val R := .sigma "_" (.qlit 0) A (.mk [B] (.var 1)) (some 0)
  -- a field's equation, and the rest's unless the rest is just `ret` (whose equation is
  -- `True`): decided by the description, so `succ m = succ n` is `m = n` and the
  -- nesting doesn't depend on how a number is written (`2 = 2` is `True`, and so is
  -- `succ (succ zero) = succ (succ zero)`)
  let withRest (A E r : Val R) : Val R := match whnf E with
    | .dret _ => A
    | _ => pairTy A r
  match whnf D with
  | .dret _ => some (.unit 0)
  | .darg q S E => match tagField? S with
    | some (_, lifted) =>
      let tagOf (v : Val R) : Val R := whnf (if lifted then vDown (vFst v) else vFst v)
      match tagOf x, tagOf y with
      | .tag ls a, .tag _ b =>
        let t : Val R := if lifted then .up (.tag ls a) else .tag ls a
        if a == b then vEqPayload g l I X i (vApp g E t) (vSnd x) (vSnd y)
        -- different tags: the Σ rule, whose first component is `False`
        else some (vEq g (vInterp g l I (.darg q S E) X i) x y)
      | _, _ => none
    | _ => some (vEq g (vInterp g l I (.darg q S E) X i) x y)
  | .drec _ j E => do
    let r ← vEqPayload g l I X i E (vSnd x) (vSnd y)
    pure (withRest (vEq g (vApp g X j) (vFst x) (vFst y)) E r)
  | .dhrec q H j E => do
    let r ← vEqPayload g l I X i E (vSnd x) (vSnd y)
    -- h0 j1 X2
    let F : Val R := .pi "h" .default q H (.mk [j, X] (.app (.var 2) (.app (.var 1) (.var 0)))) none
    pure (withRest (vEq g F (vFst x) (vFst y)) E r)
  | _ => none

/-- **Exercise 4.11b.** Equality of types:

    ((x :q A) → B) = ((x :q A') → B')  ↦  (e :0 A' = A) × ((x :0 A') → B (cast A' A e x) = B' x)
    ((x :q A) × B) = ((x :q A') × B')  ↦  (e :0 A = A') × ((x :0 A) → B x = B' (cast A A' e x))
    Sort u = Sort v, Unit = Unit, …     ↦  True if the levels are equivalent; False if
                                           both are closed and differ; stuck otherwise
    different type formers, or
    different quantities (two literals) ↦  False; a quantity variable on either side ↦ stuck
    a neutral on either side            ↦  stuck: neutral (Head.eqTy X Y)

Why can't `Sort u = Sort v` be `False` when `u` and `v` are different parameters?
(Instantiate them with the same level.) -/
partial def vEqType (g : Globals R) (X Y : Val R) : Val R :=
  let X := whnf X
  let Y := whnf Y
  -- (given) Q4: `ULift A = ULift B ↦ A = B` (at the same level); `ULift` is a type former
  -- of its own, so `ULift A = B` for any other former `B` is `False` (see `canonical`)
  if let (.ulift u A, .ulift w B) := (X, Y) then
    if propSort? X == some true && propSort? Y == some true then vIff X Y
    else if u.equiv w then vEqType g A B
    else if u.toNat?.isSome && w.toNat?.isSome then .empty 0
    else .neutral (.eqTy X Y) #[]
  else
  --<sol
  let v (i : Nat) : Term R := .var i
  let levels (u w : Level) : Val R :=
    if u.equiv w then .unit 0
    else if u.toNat?.isSome && w.toNat?.isSome then .empty 0
    else .neutral (.eqTy X Y) #[]
  let canonical : Val R → Bool
    | .pi .. | .sigma .. | .sort _ | .unit _ | .empty _ | .enum _ | .desc .. | .mu .. | .nu .. | .ulift .. => true
    | _ => false
  -- propositions are equal when equivalent; a proposition is never a type of another sort
  let pX := propSort? X
  let pY := propSort? Y
  if pX == some true && pY == some true then vIff X Y else
  if pX.isNone || pY.isNone then .neutral (.eqTy X Y) #[] else
  if pX != pY then .empty 0 else
  match X, Y with
  | .pi _ _ q A B _, .pi _ _ q' A' B' _ =>
    if qtyApart q q' then .empty 0 else if sameQty q q' != some true then .neutral (.eqTy X Y) #[] else
    -- env (inside the Σ, after `e`): B', B, A', A; inside the Π add `x`
    .sigma "e" (.qlit 0) (vEqType g A' A) (.mk [.lam "x" B', .lam "x" B, A', A]
      (.pi "x" .default (.qlit 0) (v 3) (.eqTy (.app (v 3) (.cast (v 4) (v 5) (v 1) (v 0))) (.app (v 2) (v 0))) (some 0))) (some 0)
  | .sigma _ q A B _, .sigma _ q' A' B' _ =>
    if qtyApart q q' then .empty 0 else if sameQty q q' != some true then .neutral (.eqTy X Y) #[] else
    .sigma "e" (.qlit 0) (vEqType g A A') (.mk [.lam "x" B', .lam "x" B, A', A]
      (.pi "x" .default (.qlit 0) (v 4) (.eqTy (.app (v 3) (v 0)) (.app (v 2) (.cast (v 5) (v 4) (v 1) (v 0)))) (some 0))) (some 0)
  | .sort u, .sort w | .unit u, .unit w | .empty u, .empty w => levels u w
  | .enum ls, .enum ls' => if ls.length == ls'.length then .unit 0 else .empty 0
  | .desc l I, .desc l' I' => if l.equiv l' then vEqType g I I' else .neutral (.eqTy X Y) #[]
  -- (4g) by the codes, for every `I`, `D`, `D'` (no syntactic shortcut, nothing simplified):
  -- the equation between the codes `(I, D, i) = (I', D', i')` at `famCodeTy l`
  | .mu l I D i s _, .mu l' I' D' i' s' _ | .nu l I D i s _, .nu l' I' D' i' s' _ =>
    if !(l.equiv l' && sizeEqTrue s s') then .neutral (.eqTy X Y) #[] else
    vEq g (famCodeTy l) (.pair I (.pair D i)) (.pair I' (.pair D' i'))
  | _, _ => if canonical X && canonical Y then .empty 0 else .neutral (.eqTy X Y) #[]
  --|ex
  --| sorry
  --sol>

/-- **Exercise 4.11c.** `cast A B e t`, computing by the two types:

    cast ((x : A₁) → B₁) ((x : A₂) → B₂) e f
      ↦ fun x => cast (B₁ (cast A₂ A₁ e.1 x)) (B₂ x) (e.2 x) (f (cast A₂ A₁ e.1 x))
    cast ((x : A₁) × B₁) ((x : A₂) × B₂) e p
      ↦ (cast A₁ A₂ e.1 p.1, cast (B₁ p.1) (B₂ (cast A₁ A₂ e.1 p.1)) (e.2 p.1) p.2)
    cast (Sort u) (Sort u) e t ↦ t;  Unit ↦ (); Empty ↦ t
    otherwise ↦ stuck: neutral (Head.cast A B e t)

The Π case needs a template (it builds a lambda); the Σ case can be computed
directly. Quantities must match, or it's stuck. -/
partial def vCast (g : Globals R) (A B e t : Val R) : Val R :=
  let A := whnf A
  let B := whnf B
  -- (given) Q4: through `down`, at a level that is never `0` (a lifted type that is a
  -- proposition is cast by the equivalence, below)
  if let (.ulift u A₁, .ulift w B₁) := (A, B) then
    if u.isNeverZero && u.equiv w then .up (vCast g A₁ B₁ e (vDown t))
    else if propSort? A == some true && propSort? B == some true then
      if g.lazyProofs then .neutral (.cast A B e t) #[] else vApp g (vFst e) t
    else .neutral (.cast A B e t) #[]
  else
  --<sol
  let v (i : Nat) : Term R := .var i
  let stuck : Val R := .neutral (.cast A B e t) #[]
  -- between propositions, `e` is an equivalence
  -- (P2, `lazyProofs`) the cast is a proof itself, so nothing ever needs its value: stuck
  if propSort? A == some true && propSort? B == some true then
    if g.lazyProofs then stuck else vApp g (vFst e) t else
  -- (given, U5b) at a `Π`/`Σ` whose sort is not known (no annotation, or a level with
  -- parameters), the equation `e` proves is stuck (`vEqType`), so it is no pair to project:
  -- the cast is stuck exactly when the equation is. (Computing here gave `e.1` on a
  -- `reflTy`, a term the kernel then rejected.)
  let known : Bool := (propSort? A).isSome && (propSort? B).isSome
  match A, B with
  | .pi x _ q A₁ B₁ _, .pi _ _ q' A₂ B₂ _ =>
    if !known || sameQty q q' != some true then stuck else
    -- env: t, e, B₂, B₁, A₂, A₁; index 0 is the new `x`
    let c : Term R := .cast (v 5) (v 6) (.fst (v 2)) (v 0)
    .lam x (.mk [t, e, .lam x B₂, .lam x B₁, A₂, A₁]
      (.cast (.app (v 4) c) (.app (v 3) (v 0)) (.app (.snd (v 2)) (v 0)) (.app (v 1) c)))
  | .sigma _ q A₁ B₁ _, .sigma _ q' A₂ B₂ _ =>
    if !known || sameQty q q' != some true then stuck else
    let t₁ := vFst t
    let c₁ := vCast g A₁ A₂ (vFst e) t₁
    .pair c₁ (vCast g (Closure.inst g B₁ t₁) (Closure.inst g B₂ c₁) (vApp g (vSnd e) t₁) (vSnd t))
  | .sort u, .sort w | .empty u, .empty w => if u.equiv w then t else stuck
  | .unit u, .unit w => if u.equiv w then .tt else stuck
  | .enum ls, .enum ls' => if ls.length == ls'.length then t else stuck
  -- regularity at inert types (InReg): the evaluator's fast path. `A` and `B` equal by
  -- `groundEqTy`, which is invariant under conversion and stable under substitution, and
  -- needs no conversion. The rule itself (`A ≡ B` by conversion) is applied by the
  -- conversion checker to the casts that stay stuck (`unCast` in `Conv.lean`).
  | _, _ =>
    if groundEqTy g 0 A B then t else
    vCastData g A B e t stuck
  --|ex
  --| sorry
  --sol>


/-- An **inert** type: first-order data, whose values contain no functions, no proofs
but index equations at inert types, and no values of a neutral type: `Enum`, `Unit`,
`Σ`s of inert types, and `μ` types whose index type and fields are inert (`rec` fields;
`arg` fields at inert types; not `hrec`). At an inert type, a cast between equal types
is the identity (regularity, restricted): there it never creates a redex, since an inert
value has no λ to apply, and on a constructor it agrees with `vCastData` up to proof
irrelevance. (The Abel–Coquand box has a `Prop` field, so it is not inert.) `depth`
bounds the nesting of `μ`s in fields. -/
partial def inertTy (g : Globals R) (depth : Nat) (A : Val R) : Bool :=
  depth < 8 &&
  match whnf A with
  | .enum _ => true
  | .unit l => l.isNeverZero
  | .ulift l A₁ => l.isNeverZero && inertTy g (depth + 1) A₁
  | .sigma _ _ A₁ B (some s) => s.isNeverZero && inertTy g (depth + 1) A₁ &&
      inertTy g (depth + 1) (Closure.inst g B (groundAtom (1000 + depth)))
  | .mu _ I D _ _ _ => inertTy g (depth + 1) I && inertDesc g (depth + 1) D
  | _ => false

/-- Every field of the description is inert (`inertTy`). -/
partial def inertDesc (g : Globals R) (depth : Nat) (D : Val R) : Bool :=
  depth < 8 &&
  match whnf D with
  | .dret _ => true
  | .drec _ _ E => inertDesc g depth E
  | .darg _ S E => match tagField? S with
    | some (ls, lifted) => (List.range ls.length).all fun k =>
      inertDesc g depth (vApp g E (if lifted then .up (.tag ls k) else .tag ls k))
    | none => inertTy g (depth + 1) S && inertDesc g depth (vApp g E (groundAtom (2000 + depth)))
  | _ => false

/- ### Ground equality at inert types (P1)

InReg's side condition must not flip under substitution, and must give the same answer
for convertible inputs: otherwise `cast A B e t` fires on one side of a conversion and is
stuck on the other (`wiz-notes/inert-regularity-probe.wiz`). Syntactic equality
(`sameVal`) fails the second test (`Fin (f p)` and `Fin (f q)` for proofs `p q`, or a
glued name and its unfolding). `groundEqTy` answers `true` only for two inert types that
are equal and have **no free variable in a relevant position**:

* types: `Enum`, `Unit`, `ULift`, `Σ` and `μ` by their parts (inert shapes only);
* values at an inert type, by the type: tags, numerals and constructors by their parts;
  `Unit` and propositions (the index equations at `ret`) are skipped, `Σ` is compared by
  projections (η);
* a neutral is equal only to itself, and only if it is an **atom**: a fresh constant
  standing for a variable bound *inside* the comparison (under a `Σ` or an `arg`),
  with projections. Every other
  neutral (a free variable, `f p`, a stuck cast) gives `false`: the cast is stuck.

Why it is stable: a value of an inert type is convertible only to values with the same
canonical skeleton and neutrals in the same places (η at `Unit` and `Σ` and irrelevance
are what the comparison skips). So "ground and equal" is decided the same way for
convertible inputs, and a substitution doesn't change a ground value (atoms are never
substituted). A `false` may become `true` after a substitution (a free variable replaced
by a constructor): that is stuck ⟶ fires, which is allowed. -/

/-- The `d`-th atom of `groundEqTy`: a neutral whose head is a reserved global name (it
starts with a space, so it is no identifier and no declaration). Unlike a variable at a
large level, it can't collide with a variable of the context, however deep. -/
partial def groundAtom (d : Nat) : Val R := .neutral (.global s!" atom{d}" []) #[]

/-- Two neutrals that are the same atom, with the same projections. -/
partial def groundAtomEq : Val R → Val R → Bool
  | .neutral (.global x _) sp, .neutral (.global y _) sp' =>
    x.startsWith " atom" && x == y && sp.size == sp'.size &&
      (sp.zip sp').all fun
        | (.fst, .fst) | (.snd, .snd) | (.down, .down) => true
        | _ => false
  | _, _ => false

/-- A size equal to another, ground: `∞`, or `↑` of ground sizes. -/
partial def groundSizeEq (s s' : Val R) : Bool :=
  match whnf s, whnf s' with
  | .szInf, .szInf => true
  | .szSuc a, .szSuc b => groundSizeEq a b
  | a, b => groundAtomEq a b

/-- Two inert types, equal and ground (see above). `d` counts binders, for fresh atoms, and
bounds the nesting. -/
partial def groundEqTy (g : Globals R) (d : Nat) (A B : Val R) : Bool :=
  d < 64 &&
  match whnf A, whnf B with
  | .enum ls, .enum ls' => ls.length == ls'.length
  | .unit l, .unit l' => l.isNeverZero && l.equiv l'
  | .ulift l A₁, .ulift l' B₁ => l.isNeverZero && l.equiv l' && groundEqTy g (d + 1) A₁ B₁
  | .sigma _ q A₁ B₁ _, .sigma _ q' A₂ B₂ _ =>
    sameQty q q' == some true && groundEqTy g (d + 1) A₁ A₂ &&
      let x := groundAtom d
      groundEqTy g (d + 1) (Closure.inst g B₁ x) (Closure.inst g B₂ x)
  | .mu l I D i s _, .mu l' I' D' i' s' _ =>
    l.equiv l' && groundSizeEq s s' && groundEqTy g (d + 1) I I' &&
      groundEqDesc g (d + 1) I D D' && groundEqVal g (d + 1) I i i'
  | _, _ => false

/-- Two descriptions of inert fields (`ret`, `rec`, `arg` at an inert type), equal and
ground. A tag field is compared branch by branch; any other field under an atom. -/
partial def groundEqDesc (g : Globals R) (d : Nat) (I D D' : Val R) : Bool :=
  d < 64 &&
  -- (one closed global at the same levels, `T.desc` of a type without parameters say: the
  -- same description, without walking every constructor of it)
  (match D, D' with
    | .unfold n us #[] _, .unfold n' us' #[] _ =>
      n == n' && us.length == us'.length && (us.zip us').all fun (u, u') => u.equiv u'
    | _, _ => false) ||
  match whnf D, whnf D' with
  | .dret j, .dret j' => groundEqVal g d I j j'
  | .drec q j E, .drec q' j' E' =>
    sameQty q q' == some true && groundEqVal g d I j j' && groundEqDesc g d I E E'
  | .darg q S E, .darg q' S' E' =>
    sameQty q q' == some true && groundEqTy g (d + 1) S S' &&
      match tagField? S with
      | some (ls, lifted) => (List.range ls.length).all fun k =>
        let t : Val R := if lifted then .up (.tag ls k) else .tag ls k
        groundEqDesc g (d + 1) I (vApp g E t) (vApp g E' t)
      | none =>
        let x := groundAtom d
        groundEqDesc g (d + 1) I (vApp g E x) (vApp g E' x)
  | _, _ => false

/-- Two values of an inert type `T`, equal and ground, by `T`. -/
partial def groundEqVal (g : Globals R) (d : Nat) (T a b : Val R) : Bool :=
  let T := whnf T
  if propSort? T == some true then true else
  let a := whnf a
  let b := whnf b
  if let (.natLit n, .natLit m) := (a, b) then n == m else
  match T with
  | .unit _ => true
  | .enum _ => match a, b with
    | .tag _ i, .tag _ j => i == j
    | _, _ => groundAtomEq a b
  | .sigma _ _ A₁ B₁ _ =>
    let a₁ := vFst a
    groundEqVal g d A₁ a₁ (vFst b) && groundEqVal g d (Closure.inst g B₁ a₁) (vSnd a) (vSnd b)
  | .ulift _ A₁ => groundEqVal g d A₁ (vDown a) (vDown b)
  | .mu l I D i _ _ => match vNatView g a, vNatView g b with
    | .con x, .con y => groundEqVal g d (vInterp g l I D (muFamily l I D) i) x y
    | a, b => groundAtomEq a b
  | _ => false

/-- A size as conversion sees it (`sizeView` in `Conv.lean`): `∞` (any `↑ᵏ ∞`, `none`), or a
base with a number of `↑`s. -/
partial def sizeViewE : Val R → Option (Val R) × Nat
  | .unfold _ _ _ v => sizeViewE v.get
  | .lazyInd _ _ _ _ _ _ _ _ _ v => sizeViewE v.get
  | .szInf => (none, 0)
  | .szSuc s => let (b, k) := sizeViewE s; (b, k + 1)
  | v => (some v, 0)

/-- Two sizes are equal (4g), decided as conversion decides it (`sizeEq` in `Conv.lean`):
`↑ᵏ ∞ = ↑ᵐ ∞`, and `↑ᵏ x = ↑ᵐ y` when `k = m` and `x`, `y` are the same variable or
metavariable. Anything else is unknown (`false`: the μ/ν rules are stuck). -/
partial def sizeEqTrue (s s' : Val R) : Bool :=
  match sizeViewE s, sizeViewE s' with
  | (none, _), (none, _) => true
  | (some x, k), (some y, m) => k == m && (match x, y with
    | .neutral (.local a) #[], .neutral (.local b) #[] => a == b
    | .neutral (.mvar a) #[], .neutral (.mvar b) #[] => a == b
    | _, _ => false)
  | _, _ => false

/-- **Equality of description codes** (4g), `D =_{Desc l I} D'`, by the constructors:

    ret j = ret j'                  ↦  j =_I j'
    arg q S E = arg q' S' E'        ↦  (e :0 S ≡ S') × ((s :0 S) → E s = E' (cast S S' e s))
    rec q j E = rec q' j' E'        ↦  (j =_I j') × (E = E')
    hrec q H j E = hrec q' H' j' E' ↦  ((e :0 H ≡ H') × ((h :0 H) → j h =_I j' (cast H H' e h))) × (E = E')
    different constructors          ↦  False
    quantities two different constants ↦  False;  otherwise unequal (a variable) ↦ stuck
    a neutral on either side        ↦  stuck

The shape of the result depends only on the two heads (and the quantities), never on
syntactic equality or on what a component computes to, so it is stable under
substitution. The rests (`E = E'`) are closures: they compute when looked at. Field types
are compared by type equality, which compares propositions (a lifted proof field
`ULift P`) by equivalence. -/
partial def vEqDesc (g : Globals R) (l : Level) (I D D' : Val R) : Val R :=
  let v (i : Nat) : Term R := .var i
  let D := whnf D
  let D' := whnf D'
  let stuck : Val R := .neutral (.eq (.desc l I) D D') #[]
  -- quantities: equal ↦ go on; two different *constant* polynomials ↦ `False`; anything else (a
  -- quantity variable against a literal or another variable) ↦ stuck, since a
  -- substitution could make them equal
  let qty (q q' : Val R) (k : Unit → Val R) : Val R := match sameQty q q' with
    | some true => k ()
    | some false => if qtyApart q q' then .empty 0 else stuck
    | none => stuck
  -- `(e :0 S ≡ S') × ((x :0 S) → F x = F' (cast S S' e x))` at type `T`
  -- (inside `e`: e0 S1 S'2 F3 F'4 T5; inside `x`: one more)
  let along (S S' F F' T : Val R) : Val R :=
    .sigma "e" (.qlit 0) (vEqType g S S') (.mk [S, S', F, F', T]
      (.pi "x" .default (.qlit 0) (v 1) (.eq (v 6) (.app (v 4) (v 0)) (.app (v 5) (.cast (v 2) (v 3) (v 1) (v 0)))) (some 0))) (some 0)
  -- `A × (E = E')` (inside `_`: _0 E1 E'2 I3)
  let andRest (A E E' : Val R) : Val R :=
    .sigma "_" (.qlit 0) A (.mk [E, E', I] (.eq (.desc l (v 3)) (v 1) (v 2))) (some 0)
  match D, D' with
  | .dret j, .dret j' => vEq g I j j'
  | .darg q S E, .darg q' S' E' => qty q q' fun _ => along S S' E E' (.desc l I)
  | .drec q j E, .drec q' j' E' => qty q q' fun _ => andRest (vEq g I j j') E E'
  | .dhrec q H j E, .dhrec q' H' j' E' => qty q q' fun _ => andRest (along H H' j j' I) E E'
  | .dret _, .darg .. | .dret _, .drec .. | .dret _, .dhrec ..
  | .darg .., .dret _ | .darg .., .drec .. | .darg .., .dhrec ..
  | .drec .., .dret _ | .drec .., .darg .. | .drec .., .dhrec ..
  | .dhrec .., .dret _ | .dhrec .., .darg .. | .dhrec .., .drec .. => .empty 0
  | _, _ => stuck

/-- The type of a family's code (4g): `(J : Sort (l+1)) × (D : Desc_l J) × J`. Equality of
two `μ`/`ν` types is equality at this type of `(I, D, i)` and `(I', D', i')`, which the
Σ rule computes to `(e : I ≡ I') × ((e' : cast _ D = D') × (cast _ (cast _ i) = i'))`. -/
partial def famCodeTy (l : Level) : Val R :=
  let s : Level := .succ (.succ l)
  let ω : Val R := .qlit QuantitySyntax.explicitDefault
  -- J0
  .sigma "I" ω (.sort (.succ l)) (.mk [] (.sigma "D" (.qlit QuantitySyntax.explicitDefault) (.desc l (.var 0)) (.var 1) (some s))) (some s)

/-- The payload equation of a cast between two `μ` (or two `ν`) types (4g):

    A = μ^s_l I D i,  B = μ^s_l I' D' i',  e : A ≡ B,  that is  e : (I, D, i) = (I', D', i')
    at `famCodeTy l`;  s = ↑s' or ∞
    ↦  (⟦D⟧ (μ^{s'} I D) i,  ⟦D'⟧ (μ^{s'} I' D') i',  ê)
    ê := transp (famCodeTy l) (I, D, i) (λ t _. ⟦D⟧ (μ^{s'} I D) i ≡ ⟦t.2.1⟧ (μ^{s'} t.1 t.2.1) t.2.2)
           (reflTy (⟦D⟧ (μ^{s'} I D) i)) (I', D', i') e

`ê` is well typed: at `t = (I, D, i)` the motive is `⟦D⟧ … ≡ ⟦D⟧ …`, proved by `reflTy`.
Uses only the levels and the sizes' heads: no syntactic test. -/
partial def famPayloadEq? (g : Globals R) (A B e : Val R) : Option (Val R × Val R × Val R) :=
  let go (nu : Bool) (l l' : Level) (I D i s I' D' i' s' : Val R) : Option (Val R × Val R × Val R) := do
    if !(l.equiv l' && sizeEqTrue s s') then none
    let sp ← sizePred? s
    let fam (I D : Val R) : Val R := if nu then nuFamilyAt l I D sp else muFamilyAt l I D sp
    let Xi := vInterp g l I D (fam I D) i
    let Xi' := vInterp g l I' D' (fam I' D') i'
    -- under `t _`: _0 t1 Xi2 sp3; under `k`: k0 _1 t2 Xi3 sp4
    let famT : Term R := .lam "k" (if nu then .nu l (.fst (.var 2)) (.fst (.snd (.var 2))) (.var 0) (.var 4) none
      else .mu l (.fst (.var 2)) (.fst (.snd (.var 2))) (.var 0) (.var 4) none)
    let P : Val R := .lam "t" (.mk [Xi, sp] (.lam "_" (.eqTy (.var 2)
      ((Templates.interpTm l).app (.fst (.var 1)) |>.app (.fst (.snd (.var 1))) |>.app famT |>.app (.snd (.snd (.var 1)))))))
    pure (Xi, Xi', .neutral (.transp (famCodeTy l) (.pair I (.pair D i)) P (.neutral (.reflTy Xi) #[]) (.pair I' (.pair D' i')) e) #[])
  match A, B with
  | .mu l I D i s _, .mu l' I' D' i' s' _ => go false l l' I D i s I' D' i' s'
  | .nu l I D i s _, .nu l' I' D' i' s' _ => go true l l' I D i s I' D' i' s'
  | _, _ => none

/-- `cast` at the data types, by the value (no regularity):

    cast (Desc l I) (Desc l I') e D        by `D` (`e : I = I'`):
      ret i ↦ ret (cast I I' e i);   arg q S E ↦ arg q S (fun s => cast _ _ e (E s))
      rec q j E ↦ rec q (cast I I' e j) (cast _ _ e E)
      hrec q H j E ↦ hrec q H (fun h => cast I I' e (j h)) (cast _ _ e E)
    cast (μ^s I D i) (μ^s I' D' i') e (con x)  ↦ con (cast (⟦D⟧ μ^s' i) (⟦D'⟧ μ^s' i') e' x)
    cast (ν^s I D i) (ν^s I' D' i') e (cocon x) ↦ cocon (cast (⟦D⟧ ν^s' i) (⟦D'⟧ ν^s' i') e' x)

where `s = ↑s'` (or `∞`), `e` proves the code equation (`vEqType` at μ/ν, 4g), and `e'`
is `famPayloadEq?`'s equation (one `transp` along `e`). The payload's cast casts every field, so a proof field becomes the
equivalence applied to it (`vCast` between propositions), and a field at a neutral type
stays a stuck cast. A numeral is a value of `builtin nat`, a type with an index in
`Unit` and no proof or neutral fields: its cast is itself (what the rule computes, up
to proof irrelevance). Otherwise stuck. -/
partial def vCastData (g : Globals R) (A B e t stuck : Val R) : Val R :=
  let v (i : Nat) : Term R := .var i
  match A, B with
  | .desc l I, .desc l' I' =>
    if !l.equiv l' then stuck else
    match whnf t with
    | .dret i => .dret (vCast g I I' e i)
    -- s0 E1 e2 I'3 I4
    | .darg q S E => .darg q S (.lam "s" (.mk [E, e, I', I] (.cast (.desc l (v 4)) (.desc l (v 3)) (v 2) (.app (v 1) (v 0)))))
    | .drec q j E => .drec q (vCast g I I' e j) (vCast g A B e E)
    -- h0 j1 e2 I'3 I4
    | .dhrec q H j E => .dhrec q H (.lam "h" (.mk [j, e, I', I] (.cast (v 4) (v 3) (v 2) (.app (v 1) (v 0)))))
        (vCast g A B e E)
    | _ => stuck
  | .mu .., .mu .. =>
    let t := whnf t
    -- (a numeral at a ground type was handled by InReg, `groundEqTy`)
    match vNatView g t with
    | .con x => match famPayloadEq? g A B e with
      | some (Xi, Xi', e') => .con (vCast g Xi Xi' e' x)
      | none => stuck
    | _ => stuck
  | .nu .., .nu .. => match whnf t with
    | .cocon x => match famPayloadEq? g A B e with
      | some (Xi, Xi', e') => .cocon (vCast g Xi Xi' e' x)
      | none => stuck
    | _ => stuck
  | _, _ => stuck

/-- **Exercise 1.3.** Read a value back into syntax in a context of `l` local variables.
To quote under a binder, instantiate the closure with `Val.var l` and quote the
result at `l + 1`. Remember to convert levels back into indices. A neutral's head can
be a local, a global or a metavariable, and its spine is folded over the head: so far
only `Elim.app`, with the other eliminations in Exercise 4.5.

**Exercise 4.12** (stage 4c): quote the heads `eq`, `eqTy`, `cast`, `refl`, `reflTy`
and `transp` (just quote their components).

**Exercise 4.5** (stage 4b): quote the structural types and the `fst`, `snd`, `split`
and `absurd` eliminations. A `split`'s motive is under one binder and its body under
two. -/
partial def quote (g : Globals R) (l : Lvl) : Val R → Term R
  -- (given) a glued value keeps its name
  | .unfold n us sp _ => quote g l (.neutral (.global n us) sp)
  -- (folded only on a numeral, as before kernel-eval: `ind` on a constructor is lazy for
  -- speed alone and reads back as what it computes, so read-back is unchanged)
  | .lazyInd lv I D v P m i x sp val =>
    if (whnf x matches .con _) then quote g l (unlazyCon val.get) else
    sp.foldl (fun t e => match e with
      | .app a => .app t (quote g l a)
      | .fst => .fst t
      | .snd => .snd t
      | .down => .down t
      -- (the spine of a glued induction only ever takes applications and projections:
      -- `vApp`, `vFst`, `vSnd`, `vDown`. Anything else here is a bug, not something to drop.)
      | .split .. | .absurd _ | .ecase .. | .delim .. | .ind .. | .sfix .. | .scase .. | .out =>
        panic! "quote: an elimination that a glued induction cannot carry")
      (.ind lv (quote g l I) (quote g l D) v (quote g l P) (quote g l m) (quote g l i) (quote g l x))
  --<sol
  | .neutral h sp =>
    let hd : Unit → Term R := fun _ => match h with
      -- (a variable at or above the level read back at has no index: truncated
      -- subtraction would name another variable, which once proved `False` (S1). It reads
      -- back as a stuck unknown, which no term is equal to and the kernel rejects.)
      | .local x => if x < l then .var (l - x - 1) else .const "kernel panic✝" []
      | .global n us => .const n us
      | .mvar m => .mvar m
      | .eq A a b => .eq (quote g l A) (quote g l a) (quote g l b)
      | .eqTy A B => .eqTy (quote g l A) (quote g l B)
      | .cast A B e t => .cast (quote g l A) (quote g l B) (quote g l e) (quote g l t)
      | .refl A a => .refl (quote g l A) (quote g l a)
      | .reflTy X => .reflTy (quote g l X)
      | .transp A a P p b e =>
        .transp (quote g l A) (quote g l a) (quote g l P) (quote g l p) (quote g l b) (quote g l e)
      | .prf env t => quote g l (eval g env t)
    let elims (acc : Term R) (sp : Array (Elim R)) : Term R := sp.foldl (init := acc) fun acc e => match e with
      | .app v => .app acc (quote g l v)
      | .fst => .fst acc
      | .snd => .snd acc
      | .split q z m x y b =>
        .split (quote g l q) acc z (quote g (l + 1) (Closure.inst g m (Val.var l)))
          x y (quote g (l + 2) (Closure.inst2 g b (Val.var l) (Val.var (l + 1))))
      | .absurd m => .absurd (quote g l m) acc
      | .ecase z m env bs =>
        .ecase z (quote g (l + 1) (Closure.inst g m (Val.var l))) acc
          (bs.map fun b => quote g l (eval g env b))
      | .delim v P a b c h => .delim v (quote g l P) (quote g l a) (quote g l b) (quote g l c) (quote g l h) acc
      | .ind lv I D v P m i => .ind lv (quote g l I) (quote g l D) v (quote g l P) (quote g l m) (quote g l i) acc
      | .out => .out acc
      | .down => .down acc
      | .scase lv q I D v P m s i =>
        .scase lv (quote g l q) (quote g l I) (quote g l D) v (quote g l P) (quote g l m) (quote g l s) (quote g l i) acc
      | .sfix lv I D v P f s i =>
        .sfix lv (quote g l I) (quote g l D) v (quote g l P) (quote g l f) (quote g l s) (quote g l i) acc
    -- (P2) a proof head (a suspended proof, `refl`, `transp`, a stuck cast between
    -- propositions) is a proof up to its last `absurd`: past it the value need not be one
    -- (`absurd M p : M`, for any `M`), so those eliminations are always read back.
    if !(g.lazyProofs && proofHead h) then elims (hd ()) sp else
    let k := (lastAbsurd? sp).getD sp.size
    let pre := sp.extract 0 k
    let post := sp.extract k sp.size
    if g.quoteErasesProofs then
      -- the kernel's own comparisons never evaluate a suspended proof, and never compare
      -- two proofs: every proof reads back as `()`, a suspended one and a stuck `refl`,
      -- `reflTy`, `transp` or cast between propositions alike. (Alike matters: the same
      -- proof can be a `refl` head where its term was evaluated and a suspension where it
      -- was read back marked and evaluated again, and two types that differ only so must
      -- not compare as different: that made a cast stuck, in `lib/Vec.wiz`.)
      elims .tt post
    else
      -- outside the kernel (the elaborator, `#reduce`): a suspended proof is evaluated, so
      -- that the term read back is a normal form, which the kernel can check again (a
      -- substituted `(p, q).1` has no inferable type). The proof is read back *marked*:
      -- in a relevant position the kernel requires the marker.
      let p : Term R := match h with
        | .prf env t => match g.budget with
          -- (inside a read-back: on its budget)
          | some _ => quote g l (vElims g (eval g env t) pre)
          -- a read-back starts: the proof is evaluated and read back within a budget of
          -- steps. If it runs out, the proof reads back as a constant that says so (and
          -- that the kernel rejects).
          | none =>
            let (tm, used) := Budget.run g.proofSteps fun b =>
              let g' := { g with budget := some b }
              quote g' l (vElims g' (eval g' env t) pre)
            let tm : Term R := if used > g.proofSteps then .const (Budget.message g.proofSteps) [] else tm
            if g.traceProofSteps then dbgTrace s!"proof-steps {used}" fun _ => tm else tm
        | _ => elims (hd ()) pre
      let p : Term R := match p with
        | .prf .. => p
        | p => .prf .zero p
      elims p post
  | .sort k => .sort k
  | .pi x bi q a b s => .pi x bi (quote g l q) (quote g l a) (quote g (l + 1) (Closure.inst g b (Val.var l))) s
  | .lam x b => .lam x (quote g (l + 1) (Closure.inst g b (Val.var l)))
  | v@(.sigma x q a b s) => match (if g.quoteEqs then eqSigmaSides? v else none) with
    -- (13n) a computed equation reads back as the equation, which evaluates to it again
    | some (A, a', b') => .eq (quote g l A) (quote g l a') (quote g l b')
    | none => .sigma x (quote g l q) (quote g l a) (quote g (l + 1) (Closure.inst g b (Val.var l))) s
  | .pair a b => .pair (quote g l a) (quote g l b)
  | .unit k => .unit k
  | .tt => .tt
  | .empty k => .empty k
  | .qty => .qty
  | .qlit r => .qlit r
  | .enum ls => .enum ls
  | .tag ls i => .tag ls i
  | .desc k I => .desc k (quote g l I)
  | .dret i => .dret (quote g l i)
  | .darg q S D => .darg (quote g l q) (quote g l S) (quote g l D)
  | .drec q j D => .drec (quote g l q) (quote g l j) (quote g l D)
  | .dhrec q H j D => .dhrec (quote g l q) (quote g l H) (quote g l j) (quote g l D)
  | .mu k I D i s h => .mu k (quote g l I) (quote g l D) (quote g l i) (quote g l s) (h.map fun (n, us, as) => (n, us, as.map (quote g l)))
  | .con x => .con (quote g l x)
  | .natLit n => .natLit n
  | .ulift k A => .ulift k (quote g l A)
  | .up a => .up (quote g l a)
  | .nu k I D i s h => .nu k (quote g l I) (quote g l D) (quote g l i) (quote g l s) (h.map fun (n, us, as) => (n, us, as.map (quote g l)))
  | .size => .size
  | .szInf => .szInf
  | .szSuc s => .szSuc (quote g l s)
  | .sizeLt s => .sizeLt (quote g l s)
  | .cocon x => .cocon (quote g l x)
  | .scofix k I D A f s i a =>
    .scofix k (quote g l I) (quote g l D) (quote g l A) (quote g l f) (quote g l s) (quote g l i) (quote g l a)
  | .coit k I D S st i s =>
    .coit k (quote g l I) (quote g l D) (quote g l S) (quote g l st) (quote g l i) (quote g l s)
  --|ex
  --| | .natLit n => .natLit n  -- (given)
  --| | v => sorry
  --sol>

/-- Apply a whole spine of eliminations to a value (used to unfold solved metas). -/
partial def vElims (g : Globals R) (v : Val R) (sp : Array (Elim R)) : Val R :=
  sp.foldl (init := v) fun v e => match e with
    | .app a => vApp g v a
    | .fst => vFst v
    | .snd => vSnd v
    | .split q z m x y b => vSplit g q v z m x y b
    | .absurd m => vAbsurd m v
    | .ecase z m env bs => vEcase g z m v env bs
    | .delim lv P a b c h => vDelim g lv P a b c h v
    | .ind l I D lv P m i => vInd g l I D lv P m i v
    | .out => vOut g v
    | .down => vDown v
    | .sfix l I D lv P f s i => vSfix g l I D lv P f s i v
    | .scase l q I D lv P m s i => vScase g l q I D lv P m s i v

end

/-- Normal form of a closed term (every definition unfolded). -/
def nf (g : Globals R) (t : Term R) : Term R :=
  let g := { g with eager := true, quoteEqs := false }
  quote g 0 (eval g [] t)

end Wiz
