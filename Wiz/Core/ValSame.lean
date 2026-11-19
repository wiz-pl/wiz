import Wiz.Core.Conv

/-!
# A budgeted structural comparison of values (prototype, not in the trusted path)

`valSame n a b` answers "are these two values the *same* value, structurally?" within
`n` nodes. `none` means "not shown the same" (not "different"): the caller must fall back
to the real comparison. The direction is the sound one for a shortcut — `some` must imply
`conv` — and this is the Lean-side counterpart of `valSame` in `selfhost/Kernel.wiz`
(stage 20e), which the kernel uses for stuck `ecase`s.

Only identities are used, never conversion:

* binder names and `BinderInfo` are ignored (conversion ignores them);
* hints on `μ`/`ν` are compared strictly (a stricter test loses hits, never soundness);
* closure bodies are compared with `Term`'s `BEq` and their environments recursively;
* thunks are never forced: two `unfold`s are the same only with the same head, levels and
  spine; two `lazyInd`s only with the same parameters and spine;
* proofs are compared structurally (two occurrences of the same proof value are the same
  value); there is no "all proofs are equal" rule here.

Every rule is an identity of the denoted value, so `some` ⇒ the two values are the same
value, hence convertible. The function is `partial` only so that a fuel-free caller could
loop; `fuel` bounds it.
-/

namespace Wiz

variable {R : Type} [QRig R] [DecidableEq R] [QuantitySyntax R]

private def andSame (a : Option Nat) (k : Nat → Option Nat) : Option Nat :=
  match a with
  | some n => k n
  | none => none

private def lvlsEq (us us' : List Level) : Bool :=
  us.length == us'.length && (us.zip us').all fun (u, u') => u == u'

mutual

/-- Structural identity of two values, with a node budget. -/
partial def valSame (fuel : Nat) : Val R → Val R → Option Nat
  | 0, _, _ => none
  | n + 1, a, b =>
    match a, b with
    | .sort l, .sort l' => if l == l' then some n else none
    | .pi _ _ q dom cod σ, .pi _ _ q' dom' cod' σ' =>
      andSame (valSame n q q') fun k =>
        andSame (valSame k dom dom') fun k =>
          if σ.dom.equiv σ'.dom && σ.cod.equiv σ'.cod then closureSame k cod cod' else none
    | .lam _ c, .lam _ c' => closureSame n c c'
    | .sigma _ q fst snd σ, .sigma _ q' fst' snd' σ' =>
      andSame (valSame n q q') fun k =>
        andSame (valSame k fst fst') fun k =>
          if σ.dom.equiv σ'.dom && σ.cod.equiv σ'.cod then closureSame k snd snd' else none
    | .pair x y, .pair x' y' =>
      andSame (valSame n x x') fun k => valSame k y y'
    | .unit l, .unit l' => if l == l' then some n else none
    | .tt, .tt => some n
    | .empty l, .empty l' => if l == l' then some n else none
    | .qty, .qty => some n
    | .qlit r, .qlit r' => if r == r' then some n else none
    | .enum ls, .enum ls' => if ls.length == ls'.length then some n else none
    | .tag ls i, .tag ls' j => if i == j && ls.length == ls'.length then some n else none
    | .desc l I, .desc l' I' => if l == l' then valSame n I I' else none
    | .dret i, .dret i' => valSame n i i'
    | .darg q S D, .darg q' S' D' =>
      andSame (valSame n q q') fun k =>
        andSame (valSame k S S') fun k => valSame k D D'
    | .drec q j D, .drec q' j' D' =>
      andSame (valSame n q q') fun k =>
        andSame (valSame k j j') fun k => valSame k D D'
    | .dhrec q H j D, .dhrec q' H' j' D' =>
      andSame (valSame n q q') fun k =>
        andSame (valSame k H H') fun k =>
          andSame (valSame k j j') fun k => valSame k D D'
    | .mu l I D i s h pr, .mu l' I' D' i' s' h' pr' =>
      if !(l == l' && pr == pr' && hintSame h h') then none else
      andSame (valSame n I I') fun k =>
        andSame (valSame k D D') fun k =>
          andSame (valSame k i i') fun k => valSame k s s'
    | .con x, .con x' => valSame n x x'
    | .nu l I D i s h, .nu l' I' D' i' s' h' =>
      if !(l == l' && hintSame h h') then none else
      andSame (valSame n I I') fun k =>
        andSame (valSame k D D') fun k =>
          andSame (valSame k i i') fun k => valSame k s s'
    | .size, .size => some n
    | .szInf, .szInf => some n
    | .szSuc s, .szSuc s' => valSame n s s'
    | .sizeLt s, .sizeLt s' => valSame n s s'
    | .cocon x, .cocon x' => valSame n x x'
    | .scofix l I D A f s i x, .scofix l' I' D' A' f' s' i' x' =>
      if l != l' then none else
      andSame (valSame n I I') fun k =>
        andSame (valSame k D D') fun k =>
          andSame (valSame k A A') fun k =>
            andSame (valSame k f f') fun k =>
              andSame (valSame k s s') fun k =>
                andSame (valSame k i i') fun k => valSame k x x'
    | .coit l I D S st i s, .coit l' I' D' S' st' i' s' =>
      if l != l' then none else
      andSame (valSame n I I') fun k =>
        andSame (valSame k D D') fun k =>
          andSame (valSame k S S') fun k =>
            andSame (valSame k st st') fun k =>
              andSame (valSame k i i') fun k => valSame k s s'
    | .natLit m, .natLit m' => if m == m' then some n else none
    | .ulift k l A, .ulift k' l' A' =>
      if k == k' && l == l' then valSame n A A' else none
    | .up x, .up x' => valSame n x x'
    | .neutral h sp, .neutral h' sp' =>
      andSame (headSame n h h') fun k => spineSame k sp sp'
    | .unfold n₀ us sp _, .unfold n₀' us' sp' _ =>
      if !(n₀ == n₀' && lvlsEq us us') then none
      else spineSame n sp sp'
    | .unfold n₀ us sp _, .neutral (.global n₀' us') sp' =>
      if n₀ == n₀' && lvlsEq us us' then spineSame n sp sp' else none
    | .neutral (.global n₀ us) sp, .unfold n₀' us' sp' _ =>
      if n₀ == n₀' && lvlsEq us us' then spineSame n sp sp' else none
    | .lazyInd l I D v P m i x pr sp _, .lazyInd l' I' D' v' P' m' i' x' pr' sp' _ =>
      if !(l == l' && v == v' && pr == pr') then none else
      andSame (valSame n I I') fun k =>
        andSame (valSame k D D') fun k =>
          andSame (valSame k P P') fun k =>
            andSame (valSame k m m') fun k =>
              andSame (valSame k i i') fun k =>
                andSame (valSame k x x') fun k => spineSame k sp sp'
    | _, _ => none

/-- Two closures denote the same value when their bodies are the same term and their
environments the same values. -/
partial def closureSame (fuel : Nat) : Closure R → Closure R → Option Nat
  | 0, _ => none
  | n + 1, .mk env body, .mk env' body' =>
    if body == body' then envSame n env env' else none

partial def envSame (fuel : Nat) : Env R → Env R → Option Nat
  | 0, _, _ => none
  | n + 1, [], [] => some n
  | n + 1, v :: r, v' :: r' =>
    andSame (valSame n v v') fun k => envSame k r r'
  | _, _, _ => none

partial def spineSame (fuel : Nat) (sp sp' : Array (Elim R)) : Option Nat :=
  if fuel == 0 || sp.size != sp'.size then none
  else spineSameGo fuel sp sp' 0

/-- `spineSame`'s loop; only called with equal sizes, so `sp'[i]` exists. -/
partial def spineSameGo (fuel : Nat) (sp sp' : Array (Elim R)) (i : Nat) : Option Nat :=
  if fuel == 0 then none
  else if i < sp.size then
    andSame (elimSame (fuel - 1) sp[i]! sp'[i]!) fun k => spineSameGo k sp sp' (i + 1)
  else some fuel

partial def elimSame (fuel : Nat) : Elim R → Elim R → Option Nat
  | 0, _ => none
  | n + 1, a, b =>
    match a, b with
    | .app x, .app x' => valSame n x x'
    | .fst, .fst | .snd, .snd | .out, .out | .down, .down => some n
    | .split q _ m _ _ body, .split q' _ m' _ _ body' =>
      andSame (valSame n q q') fun k =>
        andSame (closureSame k m m') fun k => closureSame k body body'
    | .absurd m, .absurd m' => valSame n m m'
    | .ecase _ m env bs, .ecase _ m' env' bs' =>
      andSame (closureSame n m m') fun k =>
        andSame (envSame k env env') fun k =>
          if bs.length == bs'.length then
            let rec go (k : Nat) (xs ys : List (Term R)) : Option Nat :=
              match xs, ys with
              | [], [] => some k
              | x :: xs, y :: ys => if x == y then go k xs ys else none
              | _, _ => none
            go k bs bs'
          else none
    | .delim v P a b c h, .delim v' P' a' b' c' h' =>
      if v != v' then none else
      andSame (valSame n P P') fun k =>
        andSame (valSame k a a') fun k =>
          andSame (valSame k b b') fun k =>
            andSame (valSame k c c') fun k => valSame k h h'
    | .ind l I D v P m i pr, .ind l' I' D' v' P' m' i' pr' =>
      if !(l == l' && v == v' && pr == pr') then none else
      andSame (valSame n I I') fun k =>
        andSame (valSame k D D') fun k =>
          andSame (valSame k P P') fun k =>
            andSame (valSame k m m') fun k =>
              andSame (valSame k i i') fun k => some k
    | .sfix l I D v P f s i, .sfix l' I' D' v' P' f' s' i' =>
      if !(l == l' && v == v') then none else
      andSame (valSame n I I') fun k =>
        andSame (valSame k D D') fun k =>
          andSame (valSame k P P') fun k =>
            andSame (valSame k f f') fun k =>
              andSame (valSame k s s') fun k => valSame k i i'
    | .scase l q I D v P m s i, .scase l' q' I' D' v' P' m' s' i' =>
      if !(l == l' && v == v') then none else
      andSame (valSame n q q') fun k =>
        andSame (valSame k I I') fun k =>
          andSame (valSame k D D') fun k =>
            andSame (valSame k P P') fun k =>
              andSame (valSame k m m') fun k =>
                andSame (valSame k s s') fun k => valSame k i i'
    | _, _ => none

/-- Hints are display metadata that conversion ignores; comparing them strictly only
loses hits. The budget restarts for a hint's arguments (they are small). -/
partial def hintSame : Option (Name × List Level × List (Val R)) →
    Option (Name × List Level × List (Val R)) → Bool
  | none, none => true
  | some (m, us, as), some (m', us', as') =>
    m == m' && lvlsEq us us' && as.length == as'.length &&
      Id.run do
        let mut ok := true
        for a in as, a' in as' do
          if (valSame 64 a a').isNone then ok := false
        ok
  | _, _ => false

partial def headSame (fuel : Nat) : Head R → Head R → Option Nat
  | 0, _ => none
  | n + 1, a, b =>
    match a, b with
    | .local x, .local y => if x == y then some n else none
    | .global m us, .global m' us' =>
      if m == m' && lvlsEq us us' then some n else none
    | .mvar x, .mvar y => if x == y then some n else none
    | .eq A x y, .eq A' x' y' =>
      andSame (valSame n A A') fun k =>
        andSame (valSame k x x') fun k => valSame k y y'
    | .eqTy A B, .eqTy A' B' =>
      andSame (valSame n A A') fun k => valSame k B B'
    | .cast A B e t, .cast A' B' e' t' =>
      andSame (valSame n A A') fun k =>
        andSame (valSame k B B') fun k =>
          andSame (valSame k e e') fun k => valSame k t t'
    | .refl A x, .refl A' x' =>
      andSame (valSame n A A') fun k => valSame k x x'
    | .reflTy X, .reflTy X' => valSame n X X'
    | .transp A x P p y e, .transp A' x' P' p' y' e' =>
      andSame (valSame n A A') fun k =>
        andSame (valSame k x x') fun k =>
          andSame (valSame k P P') fun k =>
            andSame (valSame k p p') fun k =>
              andSame (valSame k y y') fun k => valSame k e e'
    | .prf env t, .prf env' t' =>
      if t == t' then envSame n env env' else none
    | _, _ => none

end

end Wiz
