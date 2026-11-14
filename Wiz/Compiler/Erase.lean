import Wiz.Core.Check
import Wiz.Compiler.Push

/-!
# Erasure

Stage 5 starts compilation. A kernel-checked term is turned into an **untyped**
program (`ETerm`) by erasing everything with no runtime content:

* types (anything whose type is a `Sort`), proofs (anything whose type is a `Prop`),
  sizes, quantities, and universe levels all become `◾` (`ETerm.erased`);
* arguments to, and `let`s of, quantity `0` become `◾`. QTT guarantees an erased
  variable is never needed at runtime, so this is the payoff of stage 1.

Binders are kept (an erased argument is passed as `◾`), so de Bruijn indices don't
change. A later pass can drop them.

**Data representation.** The payload of a value of `μ D i` is nested pairs
`(tag, f₁, …, fₙ, e, ())`. At runtime it is **flat**: one object `⟨tag f₁ … fₙ⟩`, with
the constructor's tag as the object's tag (or `⟨0 f₁ … fₙ⟩` if the description doesn't
start with a choice of tag), and `◾` in the places of erased fields. Numbers of the
registered `nat` type stay numbers. A constructor applied to its fields becomes the
object directly; case analysis reads the fields directly (`resolveViews`). Code that
handles payloads generically (`ind` with hypotheses) converts with the primitives
`pack` and `unpack`, which walk the description.

The generic eliminators (`ind`, `Desc.elim`, the `map` behind coiteration) become
runtime **primitives** that walk the description, which is itself an ordinary runtime
value. A description whose first argument is a tag, `Desc.arg (Enum ls) F`, is marked:
`⟨4 ◾ F⟩` instead of `⟨1 ◾ F⟩`, so that `pack` knows to use the tag. For a number,
`ind` and the conversions get the description wrapped as `⟨5 D⟩`.

Erasure is **type-directed**, so it is bidirectional like the kernel: `eraseCheck`
knows the expected type, `eraseInfer` computes it with the kernel's `infer`.
-/

namespace Wiz

/-- A type with a **native representation** (`attribute [implemented_by mk get] T.mk`,
stage 22d): compiled code builds its values with `mk` (which has the constructor's type)
and reads its one runtime field with `get`, so the value itself can be anything the
natives agree on (a machine word, an array). The model's object would be
`⟨tag f₀ … fₙ₋₁⟩` with every field but `r` erased; the constructor's argument `p` is that
field. -/
structure ReprInfo where
  mkImpl : Name
  getImpl : Name
  tag : Nat
  nfields : Nat
  r : Nat
  mkArity : Nat
  p : Nat
  getArity : Nat
  deriving Repr, BEq, Inhabited

namespace ReprInfo

/-- The registration: a builtin key `repr:T:mk:get:tag:nfields:r:mkArity:p:getArity`
(registered under the constructor's name), so it is cached with the other builtins. -/
def key (T : Name) (i : ReprInfo) : Name :=
  s!"repr:{T}:{i.mkImpl}:{i.getImpl}:{i.tag}:{i.nfields}:{i.r}:{i.mkArity}:{i.p}:{i.getArity}"

def parse? (key : Name) : Option (Name × ReprInfo) :=
  if !key.startsWith "repr:" then none else
  match key.splitOn ":" with
  | ["repr", T, mkI, getI, tag, nf, r, ma, p, ga] => do
    pure (T, { mkImpl := mkI, getImpl := getI, tag := ← tag.toNat?, nfields := ← nf.toNat?, r := ← r.toNat?,
               mkArity := ← ma.toNat?, p := ← p.toNat?, getArity := ← ga.toNat? })
  | _ => none

end ReprInfo

/-- The native representation of the type named `T`, if any. -/
def reprOf? (builtins : List (Name × Name)) (T : Name) : Option ReprInfo :=
  builtins.findSome? fun (k, _) => match ReprInfo.parse? k with
    | some (T', i) => if T' == T then some i else none
    | none => none

/-- Runtime primitives: the generic eliminators, interpreted by walking descriptions. -/
inductive Prim where
  /-- `ind D m i x` -/
  | ind
  /-- `delim mret marg mrec mhrec D` -/
  | delim
  /-- `coit D step i s` -/
  | coit
  /-- `scofix f i a` -/
  | scofix
  /-- `out x` -/
  | out
  /-- reached an absurd case -/
  | unreachable
  /-- `0` for an observed coinductive value, `1` for a `coit`, `2` for an `scofix`, `3`
  for a lazy cell already observed (the backend's `out` is written with it) -/
  | lazyTag
  /-- `lazySet x p`: `p`, after overwriting the lazy cell `x` with its payload `p`, so
  that `out` is memoised (the backend's `out`; the interpreter just returns `p`) -/
  | lazySet
  /-- `pack D x`: a payload of nested pairs as a flat object (see below) -/
  | pack
  /-- `unpack D v`: a flat object as its payload of nested pairs -/
  | unpack
  /-- `view D x`: the payload of `x`, seen through projections (removed by `resolveViews`);
  with `repr`, `x` is a native value (stage 22d) -/
  | view (absorbed nat : Bool) (repr : Option ReprInfo := none)
  /-- the tag of an object, as a 0-field object -/
  | tag
  /-- the tag (`0` zero, `1` successor) and the field of a number -/
  | natTag
  | natPred
  | natSucc
  /-- `fieldAt v n`: field `n` (a runtime number) of an object -/
  | fieldAt
  /-- `mkObj t fs`: an object with the tag of `t` and the fields listed by `fs`
  (nested pairs ending in `◾`) -/
  | mkObj
  deriving Repr, BEq, Inhabited

inductive ETerm where
  | erased
  | var (ix : Nat)
  | global (name : Name)
  | lam (x : Name) (body : ETerm)
  | app (f a : ETerm)
  | letE (x : Name) (val body : ETerm)
  /-- an object with a tag and fields: pairs are `obj 0 #[a, b]`, tags `obj i #[]` -/
  | obj (tag : Nat) (fields : Array ETerm)
  | proj (i : Nat) (t : ETerm)
  /-- branch on the tag of an object -/
  | case (scrut : ETerm) (branches : Array ETerm)
  /-- `fix x. body`: general recursion (termination was checked by the kernel) -/
  | fix (x : Name) (body : ETerm)
  | prim (op : Prim) (args : Array ETerm)
  /-- a numeral, a native number at runtime -/
  | natLit (n : Nat)
  deriving Repr, Inhabited

namespace ETerm

/-- Shift free variables (`≥ cut`) up by `k`. -/
partial def lift (k : Nat) (cut : Nat := 0) : ETerm → ETerm
  | var i => if i ≥ cut then var (i + k) else var i
  | lam x b => lam x (lift k (cut + 1) b)
  | app f a => app (lift k cut f) (lift k cut a)
  | letE x v b => letE x (lift k cut v) (lift k (cut + 1) b)
  | obj t fs => obj t (fs.map (lift k cut))
  | proj i t => proj i (lift k cut t)
  | case s bs => case (lift k cut s) (bs.map (lift k cut))
  | fix x b => fix x (lift k (cut + 1) b)
  | prim op as => prim op (as.map (lift k cut))
  | t => t

def apps (f : ETerm) (as : List ETerm) : ETerm := as.foldl app f

/-- Replace variable `k` (at depth `d`) by `s` (a term outside the binders), lowering
the variables above it. -/
partial def instVar (k : Nat) (s : ETerm) (d : Nat := 0) : ETerm → ETerm
  | var i => if i < k + d then var i else if i == k + d then s.lift d else var (i - 1)
  | lam x b => lam x (instVar k s (d + 1) b)
  | app f a => app (instVar k s d f) (instVar k s d a)
  | letE x v b => letE x (instVar k s d v) (instVar k s (d + 1) b)
  | obj t fs => obj t (fs.map (instVar k s d))
  | proj i t => proj i (instVar k s d t)
  | case sc bs => case (instVar k s d sc) (bs.map (instVar k s d))
  | fix x b => fix x (instVar k s (d + 1) b)
  | prim op as => prim op (as.map (instVar k s d))
  | t => t

/-- A closure that only calls the global `fn`: `λ x… . fn a…` with variables and `◾` as
arguments (a derived implementation's direct call, `Push`). -/
partial def isCallOf (fn : Name) : ETerm → Bool
  | lam _ b => isCallOf fn b
  | t =>
    let rec spine : ETerm → List ETerm → ETerm × List ETerm
      | app f a, acc => spine f (a :: acc)
      | t, acc => (t, acc)
    match spine t [] with
    | (global g, args) => g == fn && args.all fun a => match a with
      | var _ => true
      | erased => true
      | _ => false
    | _ => false

/-- `let ih := λ x… . fn …` (a direct call passed on as a closure, in a derived
implementation): substituted, so that where it is applied it is a call. -/
partial def inlineCalls (fn : Name) : ETerm → ETerm
  | letE x v b =>
    let v := inlineCalls fn v
    let b := inlineCalls fn b
    if isCallOf fn v && v matches lam .. then beta (instVar 0 v 0 b) else letE x v b
  | lam x b => lam x (inlineCalls fn b)
  | app f a => app (inlineCalls fn f) (inlineCalls fn a)
  | obj t fs => obj t (fs.map (inlineCalls fn))
  | proj i t => proj i (inlineCalls fn t)
  | case sc bs => case (inlineCalls fn sc) (bs.map (inlineCalls fn))
  | fix x b => fix x (inlineCalls fn b)
  | prim op as => prim op (as.map (inlineCalls fn))
  | t => t
where
  /-- `(λ x. b) a` (as the substitution leaves it) is `let x := a; b` -/
  beta : ETerm → ETerm
    | app f a => match beta f with
      | lam x b => letE x (beta a) b
      | f => app f (beta a)
    | lam x b => lam x (beta b)
    | letE x v b => letE x (beta v) (beta b)
    | obj t fs => obj t (fs.map beta)
    | proj i t => proj i (beta t)
    | case sc bs => case (beta sc) (bs.map beta)
    | fix x b => fix x (beta b)
    | prim op as => prim op (as.map beta)
    | t => t

partial def toString : ETerm → String
  | erased => "◾"
  | var i => s!"#{i}"
  | global n => n
  | lam x b => s!"(λ{x}. {toString b})"
  | app f a => s!"({toString f} {toString a})"
  | letE x v b => s!"(let {x} := {toString v}; {toString b})"
  | obj t fs => s!"⟨{t}{String.join (fs.toList.map (" " ++ toString ·))}⟩"
  | proj i t => s!"{toString t}.{i}"
  | case s bs => s!"(case {toString s} [{", ".intercalate (bs.toList.map toString)}])"
  | fix x b => s!"(fix {x}. {toString b})"
  | prim op as => s!"({reprStr op}{String.join (as.toList.map (" " ++ toString ·))})"
  | natLit n => s!"{n}"

instance : ToString ETerm := ⟨toString⟩

end ETerm

namespace ReprInfo

/-- `get x` (implicit arguments erased) -/
def getApp (i : ReprInfo) (x : ETerm) : ETerm :=
  ETerm.apps (.global i.getImpl) (List.replicate (i.getArity - 1) .erased ++ [x])

/-- `mk ◾ … f … ◾` -/
def mkApp (i : ReprInfo) (f : ETerm) : ETerm :=
  ETerm.apps (.global i.mkImpl) ((List.range i.mkArity).map fun k => if k == i.p then f else .erased)

/-- The model's flat object of a native value `x`. -/
def toModel (i : ReprInfo) (x : ETerm) : ETerm :=
  .obj i.tag ((List.range i.nfields).toArray.map fun k => if k == i.r then i.getApp x else .erased)

end ReprInfo

variable {R : Type} [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R]

/-- Is a position at quantity `q` erased? The kernel's own test (`QPoly.isErased`, used by
`Ctx.erasedAt`): a position the kernel checked in erased mode must become `◾` here. -/
private def isZeroQ (q : Val R) : Bool := match q.toPoly? with
  | some p => p.isErased
  | none => false

/-- Is `ty` an **erased function into `Unit`**, `(0 x₁ : D₁) → … → (0 xₙ : Dₙ) → Unit` with
`n ≥ 1` (`n ≥ 0` with `allowUnit`)? Such a type has one inhabitant up to η,
`fun _ … _ => ()`, and nothing can be learnt from applying it, so its values have no
runtime content. This is the shape of a phantom tail (22e) and of a structure's marker
(22i), but the test is on the **shape of the type** only: the quantities and the final
`Unit`, which conversion and type equality compare, and never a binder name or an `Enum`
label, which they ignore (R3 of the soundness audit). A neutral type (a type variable, a
stuck match) is not of this shape: generic code keeps the value, and applies it with the
runtime's `ap`, which answers `◾` for `◾`. -/
partial def erasedFunTy (g : Globals R) (ty : VTy R) (lvl : Nat) (allowUnit : Bool := false) : Bool :=
  match whnf ty with
  | .unit _ => allowUnit
  | .pi _ _ q _ cod _ => isZeroQ q && erasedFunTy g (Closure.inst g cod (.var lvl)) (lvl + 1) true
  | _ => false

/-- Values of this type have no runtime content: types, proofs, sizes, quantities, erased
functions into `Unit` (`erasedFunTy`: phantom tails), and lifts of these (`ULift`, Q4: a
lifted proof is still a proof at run time). -/
partial def erasable (ctx : Ctx R) (ty : VTy R) : Bool :=
  match whnf ty with
  | .sort _ | .size | .sizeLt _ | .qty => true
  | .ulift _ _ A => erasable ctx A
  | .pi .. => erasedFunTy ctx.globals ty ctx.lvl || isPropTy ctx ty
  | _ => isPropTy ctx ty
where
  /-- `isProp`, but from the sorts a `Π`/`Σ` carries (mandatory, checked by the kernel):
  `typeSort?` would recompute them from every component, which along a structure's
  telescope of `n` fields, asked once per field, is quadratic. A wrong "erasable" is a
  miscompilation, so this relies on the kernel having validated the sorts
  (`checkComponentSort`): every term erasure is given has been checked, a definition's
  implementation for the compiler included (`checkImpl`; Status.md, T1). -/
  isPropTy (ctx : Ctx R) (ty : VTy R) : Bool :=
    match whnf ty with
    | .pi _ _ _ _ _ σ => if σ.hasHole then isProp ctx.globals ctx.tys ty else σ.cod.equiv 0
    | .sigma _ _ _ _ σ => if σ.hasHole then isProp ctx.globals ctx.tys ty else σ.sigmaSort.equiv 0
    | _ => isProp ctx.globals ctx.tys ty

/-- **Unboxed newtypes** (stage 22i), behind `--unbox-structs` (`Globals.unboxStructs`;
off by default). Is `ty` a Σ whose second component is an erased function into `Unit`
(`erasedFunTy`), as the last field of a structure is (its second component is the
structure's tail)? Then a value of it is represented by its first component alone:
building it is the identity, `.1` is the identity, `.2` is `◾`. A one-field structure
(`Shr ρ A`, a newtype) is then its field, and an `n`-field one is `n - 1` pairs instead
of `n`.

The decision is a function of the Σ type alone, with its second component taken at a
**variable** (never at the pair's actual first component: building, projecting and
reading back must agree), and by shape, so that two convertible types get one
representation (R3). But it is **not stable under substitution**: generic code over
`A × B` sees a neutral `B` and keeps the pair, and `B` can be instantiated with a
structure's tail (`first (S.mk 5)` with `first : A × B → A`), so the caller's value and
the callee's code disagree. No test on the second component can be stable, hence the
default: every pair is a pair (`wiz-notes/repr-shape.md`). -/
def unboxedSigma (g : Globals R) (lvl : Nat) (ty : VTy R) : Bool :=
  g.unboxStructs &&
  match whnf ty with
  -- (a second component that is itself a `Σ`, the next field, is not a tail: don't
  -- evaluate the rest of the telescope to find out)
  | .sigma _ _ _ (.mk _ (.sigma ..)) _ => false
  | .sigma _ _ _ B _ => erasedFunTy g (Closure.inst g B (.var lvl)) (lvl + 1)
  | _ => false

/-- (linear-case stage 2) Does a value of this type carry nothing at run time: `erasable`
(the predicate erasure itself uses, so the two can't drift), `Unit`, or a `Σ` of such
(a structure with only contentless fields), after `whnf` (so a named `def Tk := Unit`
counts)? -/
partial def contentless (ctx : Ctx R) (ty : VTy R) : Bool :=
  erasable ctx ty ||
  match whnf ty with
  | .unit _ => true
  | .sigma x _ A B _ => contentless ctx A && contentless (ctx.bind x [] A) (Closure.inst ctx.globals B (.var ctx.lvl))
  | _ => false

/-- (linear-case stage 2) Is the result of the function type `ty` (under its Πs)
contentless, or is a prefix of it already erasable? `extern` and `implemented_by` refuse
such a type: an effect behind it would be dropped by erasure. (`IO A` is a Π over the
linear `World` into `A × World`, which is never contentless.) -/
partial def resultContentless (g : Globals R) (ty : VTy R) : Bool :=
  go { globals := g } ty 1000
where
  go (ctx : Ctx R) (ty : VTy R) : Nat → Bool
    | 0 => false
    | fuel + 1 =>
      if contentless ctx ty then true else
      match whnf ty with
      | .pi x _ _ A B _ => go (ctx.bind x [] A) (Closure.inst ctx.globals B (.var ctx.lvl)) fuel
      | _ => false

/-- Is the result of the function type `ty` (under its Πs) a proposition? Then an
`implemented_by` for it is allowed: the implementation is ordinary Wiz code, a proof,
erased like the definition, so no effect can be lost (externs still refuse it). -/
partial def resultProp (g : Globals R) (ty : VTy R) : Bool :=
  go { globals := g } ty 1000
where
  go (ctx : Ctx R) (ty : VTy R) : Nat → Bool
    | 0 => false
    | fuel + 1 =>
      match whnf ty with
      | .pi x _ _ A B _ => go (ctx.bind x [] A) (Closure.inst ctx.globals B (.var ctx.lvl)) fuel
      | ty => isProp ctx.globals ctx.tys ty

/-- (linear-case stage 2, defence in depth) Is `t` an application of a foreign function
(`extern`)? Its call is kept even where its type is erasable: an effect never hides in a
value that erasure drops. (`extern` itself refuses a pure `Unit` result; this covers a
polymorphic native whose result type is instantiated with an erasable one.) -/
def externCall (g : Globals R) (t : Term R) : Bool :=
  match t.spine.1 with
  | .const n _ => g.builtins.any fun (k, x) => x == n && k.startsWith "extern:"
  | _ => false

/-- A call of a generated `T.casesOn` (or `casesOn1`, `casesOnA`), unfolded and beta-reduced: as a function, its
arguments (the branches) would all be computed before the call; unfolded, they sit in
the branches of a `case` and only the one taken runs. -/
def unfoldCases? (g : Globals R) (t : Term R) : Option (Term R) := do
  let (.const n us, args) := t.spine | none
  -- (also the linear `T.casesOn1` and the additive `T.casesOnA`: a `match` on a linear
  -- handle, `Uniq`, `Result1`, is otherwise a call with its branches as closures)
  unless n.endsWith ".casesOn" || n.endsWith ".casesOn1" || n.endsWith ".casesOnA" do none
  let d ← g.find? n
  let v ← d.value
  -- the arguments are annotated with their types, so that the kernel can still infer
  -- the places they end up in (the motive applied, a branch under a cast)
  let rec beta : Term R → Term R → List (Term R) → Option (Term R)
    | .lam _ b, .pi _ _ _ A B _, a :: as =>
      let a' := if a matches .var _ | .const .. | .ann .. then a else .ann a A
      beta (b.instantiateAt 0 a') (B.instantiateAt 0 a') as
    | _, _, _ :: _ => none
    | b, _, [] => some b
  -- only when every binder gets an argument
  let rec arity : Term R → Nat
    | .lam _ b => arity b + 1
    | _ => 0
  -- (P2: without the markers of the level-generic eliminator, which mark nothing here)
  let v := (v.instLevels d.levelParams us).stripMarks
  let k := arity v
  if args.length < k then none
  let b ← beta v (d.type.instLevels d.levelParams us) (args.take k)
  pure ((args.drop k).foldl .app b)

/-- Is this description shaped like the natural numbers' (over the index type `Unit`: a
choice between two tags, the first with no field, the second with one recursive field)? -/
def natShaped (g : Globals R) (I D : Val R) : Bool :=
  let isRet (d : Val R) : Bool := match whnf d with
    | .dret _ => true
    | _ => false
  let isUnit : Bool := match whnf I with
    | .unit _ => true
    | _ => false
  isUnit &&
  match whnf D with
  | .darg _ S F => match whnf S with
    | .enum [a, b] =>
      isRet (vApp g F (.tag [a, b] 0)) &&
      (match whnf (vApp g F (.tag [a, b] 1)) with
        | .drec _ _ E => isRet E
        | _ => false)
    | _ => false
  | _ => false

/-- Are the values of `ty` (a `μ`) numbers at runtime? Yes for the registered `nat` type
and for every type of its shape (`natShaped`): the name on a `μ` is display metadata,
which conversion ignores, so a type convertible to `Nat` (a copy of its declaration, or
the `μ` written out) must get `Nat`'s representation (R3). The name is only a shortcut. -/
def isNatTy (g : Globals R) (ty : Val R) : Bool :=
  match g.builtins.lookup "nat", whnf ty with
  | some N, .mu _ I D _ _ hint =>
    (match hint with | some (T, _, _) => T == N | none => false) || natShaped g I D
  | _, _ => false

/-- The sealed type a `μ`'s index type names (22k): `sealed inductive T` puts its seal, the
axiom `T.seal✝`, among the erased domains of the index tail (after the indices of an
indexed family). A constant without a value is compared by name, so this is a function
of the type up to conversion, unlike the display name on the `μ`. -/
partial def sealedIx? (g : Globals R) (I : Val R) (lvl : Nat := 2000000) : Option Name :=
  match whnf I with
  | .sigma _ _ _ B _ => sealedIx? g (Closure.inst g B (.var lvl)) (lvl + 1)
  | .pi _ _ _ dom cod _ =>
    let here : Option Name := match whnf dom with
      | .neutral (.global k _) sp =>
        if sp.isEmpty then g.builtins.findSome? fun (key, x) =>
          if x == k && key.startsWith "seal:" then some (key.drop 5).toString else none
        else none
      | _ => none
    here <|> sealedIx? g (Closure.inst g cod (.var lvl)) (lvl + 1)
  | _ => none

/-- The type with a native representation that `ty` is, with the representation: found
by the seal of a sealed type (a native representation needs `sealed`), never by the
display name. -/
def nativeTy? (g : Globals R) (ty : Val R) : Option (Name × ReprInfo) :=
  match whnf ty with
  | .mu _ I _ _ _ _ =>
    match sealedIx? g I with
    | some T => (reprOf? g.builtins T).map (T, ·)
    | none => none
  | _ => none

/-- The native representation of a `μ` type, if it has one. -/
def reprOfTy? (g : Globals R) (ty : Val R) : Option ReprInfo := (nativeTy? g ty).map (·.2)

/-- The start of the message with which erasure refuses a description whose first field
has an abstract type (`neutralFieldTy`). Unlike a term erasure can't handle yet, this is
never turned into a run-time error (`compileReachableE`). -/
def abstractFieldMsg : String := "cannot compile a description whose first field has a type that is not known here"

/-- Is this field type not known yet: a neutral (a type variable, a stuck match), or a
lift of one? Then `tagField?` could change its answer under substitution. -/
def neutralFieldTy (S : Val R) : Bool :=
  match whnf S with
  | .neutral .. => true
  | .ulift _ _ A => match whnf A with
    | .neutral .. => true
    | _ => false
  | _ => false

/-- The start of the message with which erasure refuses to build or take apart a value
with a native representation outside its type's module (`nativeHome?`). Fatal, like
`abstractFieldMsg`. -/
def nativeHomeMsg : String := "cannot compile: a value of a type with a native representation is built or taken apart outside the type's module"

/-- **Native values come from their module** (layer 3 of `wiz-notes/repr-shape.md` §4C.6).
If `ty` has a native representation and its constructor is private (R5: the module keeps
an invariant the natives rely on, as `n < 2^w` for words), then a `con` at `ty` and an
eliminator on a value of `ty` may be erased only in a declaration of the type's own
module. The elaborator already refuses them elsewhere (13b); this is the same rule on
the kernel's terms, whatever the elaborator did, because compiled code's agreement with
the definitions rests on it. Returns the type's name and module when the declaration
being erased (`g.module`, set by `eraseDecl`) is not of that module. -/
def nativeHome? (g : Globals R) (ty : Val R) : Option (Name × String) :=
  match nativeTy? g ty with
  | some (T, _) =>
    let ctorPrivate := g.privates.fold (init := false) fun acc n _ =>
      acc || (n.startsWith (T ++ ".") && n != T ++ ".desc" && n != sealName T)
    let home := (g.declModule[T]?).getD ""
    if ctorPrivate && home != g.module then some (T, home) else none
  | none => none

def nativeHomeError (T : Name) (home : String) : TypeError :=
  .other (nativeHomeMsg ++ s!" ({T}, of module {home}): use {T}'s functions")

/-- Does a seal (`isSeal`) occur in `t` outside a complete `μ` type? (Layer 3, (i): the
seal of a type with a native representation as a type argument, or the type's
description as an argument, is how generic code would come to handle a native value as
the model's object.) -/
partial def sealOutsideMu (isSeal : Name → Bool) : Term R → Bool
  | .const n _ => isSeal n
  | .mu .. => false
  | t => (t.forChildren (m := StateM Bool) (fun _ => pure ())
      (fun _ c => modify (· || sealOutsideMu isSeal c)) |>.run false).2

/-- Does a description start with a choice of tag, `Desc.arg (Enum ls) F`? Then the
tag is the flat object's tag. -/
def startsWithTag (D : Val R) : Bool :=
  match whnf D with
  | .darg _ S _ => (tagField? S).isSome
  | _ => false

private def stripAnn : Term R → Term R
  | .ann t _ => stripAnn t
  | t => t

/-- The fields of a literal payload: the term `x` and its erasure `x'` walked along the
description `d` (one field per `arg`, `rec` and `hrec`, up to the `ret`). -/
partial def flatFields (g : Globals R) (ctx : Ctx R) (d : Val R) (x : Term R) (x' : ETerm) :
    Option (Array ETerm) :=
  match whnf d with
  | .dret _ => some #[]
  | .darg _ _ F => match stripAnn x, x' with
    | .pair a r, .obj 0 #[a', r'] => (flatFields g ctx (vApp g F (ctx.eval a)) r r').map (#[a'] ++ ·)
    | _, _ => none
  | .drec _ _ D' | .dhrec _ _ _ D' => match stripAnn x, x' with
    | .pair _ r, .obj 0 #[a', r'] => (flatFields g ctx D' r r').map (#[a'] ++ ·)
    | _, _ => none
  | _ => none

/-- A literal payload as a flat object: its tag and fields. -/
def flatCon (g : Globals R) (ctx : Ctx R) (D : Val R) (x : Term R) (x' : ETerm) : Option (Nat × Array ETerm) :=
  if startsWithTag D then
    match whnf D, stripAnn x, x' with
    | .darg _ _ F, .pair a r, .obj 0 #[.obj k #[], r'] => (flatFields g ctx (vApp g F (ctx.eval a)) r r').map (k, ·)
    | _, _, _ => none
  else (flatFields g ctx D x x').map (0, ·)

/-- `f` without the binder it is under, if it is a variable or a projection of one
(then `fun x => f x` is `f`: evaluating `f` has no effect and terminates). -/
partial def etaHead? : ETerm → Option ETerm
  | .var 0 => none
  | .var i => some (.var (i - 1))
  | .proj k t => (etaHead? t).map (.proj k)
  | _ => none

/-- A use of a value's payload: `view D x` as an argument (see `resolveViews`). -/
def viewOf (g : Globals R) (D : Val R) (xty : Val R) (D' x' : ETerm) : ETerm :=
  if let some ri := reprOfTy? g xty then .prim (.view (startsWithTag D) false ri) #[D', x'] else
  let nat := isNatTy g xty
  .prim (.view (startsWithTag D) nat) #[if nat then .obj 5 #[D'] else D', x']

mutual

/-- The free variables of a term (as indices at its top). -/
partial def Wiz.IR.freeIdx' (t : Term R) (depth : Nat := 0) (acc : Std.HashSet Nat := {}) : Std.HashSet Nat :=
  match t with
  | .var i => if i ≥ depth then acc.insert (i - depth) else acc
  | t => Id.run do
    let mut acc := acc
    let ((), acc') := (t.forChildren (m := StateM (Std.HashSet Nat)) (fun _ => pure ())
      (fun d c => modify fun a => Wiz.IR.freeIdx' c (depth + d) a)).run acc
    acc := acc'
    pure acc

/-- The type of `p.2`, for `p` a pair whose second component has type `B`: `B` at
`p.1`, evaluating `p` only if `B` mentions it (as `Ctx.instArg`: along a chain of
projections `p.2.2.….1`, a structure's field, evaluating `p` at every step would be
quadratic in the chain's length). -/
partial def sndType (ctx : Ctx R) (B : Closure R) (p : Term R) : VTy R :=
  match B with
  | .mk env body =>
    Wiz.eval ctx.globals ((if body.hasVar 0 then vFst (ctx.eval p) else .unit .zero) :: env) body

/-- (The fallback runs the kernel's `infer` in erased mode: it wants the type only, and
this context's quantities are approximate. **Erasure is not the checker**: in erased mode
`infer` does not notice a relevant misuse (a projection of a linear pair, a read of an
erased field), so nothing here may be taken as a second check of the term.)

The type of a term that is already known to be well typed, without checking it
again: along an elimination spine only (heads, applications, projections, annotations,
`ecase`, `ind`), else by the kernel's `infer`. Erasure asks for the type of every
subterm, so a full `infer` at each would re-check each subterm once per enclosing node:
quadratic in the nesting depth of the deep `casesOn` trees that `match` produces. -/
partial def quickType (ctx : Ctx R) (t : Term R) : TCM (VTy R) := do
  let g := ctx.globals
  match t with
  | .var ix => pure ctx.types[ix]!
  | .const n us => match g.find? n with
    | some d => pure (Wiz.eval g [] (d.type.instLevels d.levelParams us))
    | none => throw (.unboundGlobal n)
  | .app f a => match whnf (← quickType ctx f) with
    | .pi _ _ _ _ cod _ => pure (ctx.instArg cod a)
    | _ => return (← infer { ctx with erased := true } t).1
  | .fst p => match whnf (← quickType ctx p) with
    | .sigma _ _ A _ _ => pure A
    | _ => return (← infer { ctx with erased := true } t).1
  | .snd p => match whnf (← quickType ctx p) with
    -- (`p` is evaluated only if the type of the second component mentions the first)
    | .sigma _ _ _ B _ => pure (sndType ctx B p)
    | _ => return (← infer { ctx with erased := true } t).1
  | .ann _ ty => pure (ctx.eval ty)
  | .down p => match whnf (← quickType ctx p) with
    | .ulift _ _ A => pure A
    | _ => return (← infer { ctx with erased := true } t).1
  | .ecase _ m s _ => pure (Closure.inst g (.mk ctx.env m) (ctx.eval s))
  | .ind _ _ _ _ P _ i x => pure (vApp g (vApp g (ctx.eval P) (ctx.eval i)) (ctx.eval x))
  | _ => return (← infer { ctx with erased := true } t).1

/-- **Exercise 5.1a.** Erase `t`, checking it against `ty`.

* if `ty` is `erasable`, the result is `◾`;
* `lam` against a Π: erase the body under the binder;
* `pair` against a Σ: an object `obj 0 #[a, b]`, with `a` erased if the Σ's quantity
  is `0`; at an `unboxedSigma` (the second component is a structure's tail, 22i),
  just `a` (the last field of a structure is unboxed);
* `con x` against `μ D i`: erase the payload `x` against `⟦D⟧ (μ D) i`, then make it
  flat: `flatCon` gives the tag and fields of a literal payload (`obj k fs`; for the
  `nat` type, `natLit 0` or the successor applied to the field); otherwise
  `prim .pack #[D', x']` (with `D'` wrapped as `obj 5 #[D']` for `nat`);
* `cocon x` against `ν`: just the erased payload;
* `dret`/`darg`/`drec`/`dhrec` against `Desc I`: descriptions are runtime data, as
  `obj 0 #[i]`, `obj 1 #[◾, D]` (`obj 4 #[◾, D]` if `S` is an `Enum`), `obj 2 #[j, D]`
  and `obj 3 #[◾, j, D]`;
* `tt` is `◾`; `letE` keeps the binder (with `◾` for a `0` let);
* everything else: `eraseInfer`. -/
partial def eraseCheck (ctx : Ctx R) (t : Term R) (ty : VTy R) (inDesc : Bool := false) : TCM ETerm := do
  if erasable ctx ty then
    if externCall ctx.globals t && !ctx.erased then return .letE "_" (← eraseSpine ctx t).1 .erased
    return .erased
  -- (given) Q4: `ULift` has no runtime content: `up a` is `a`
  if let (.up a, .ulift _ _ A) := (t, whnf ty) then return ← eraseCheck ctx a A
  -- (given) P2: a marked proof is erased; another marker is transparent
  if let .prf l x := t then return ← (if l.isZero then pure .erased else eraseCheck ctx x ty)
  --<sol
  let g := ctx.globals
  match t, whnf ty with
  | .lam x b, .pi _ _ q dom cod _ =>
    let some p := q.toPoly? | throw (.other "erasure: unknown quantity")
    let b' ← eraseCheck (ctx.bind x p dom) b (Closure.inst g cod (Val.var ctx.lvl)) inDesc
    -- η for an infinitary field with a lifted domain (Q4): `fun h => f (up h)` (reading
    -- it) and `fun h => f (down h)` (building it) are `f` at run time
    if b matches .app _ (.up (.var 0)) || b matches .app _ (.down (.var 0)) then
      if let .app f (.var 0) := b' then
        if let some f' := etaHead? f then return f'
    return .lam x b'
  | .pair a b, .sigma _ q A B _ =>
    let a' ← if isZeroQ q then pure .erased else eraseCheck ctx a A
    -- the last field of a structure: the pair is its first component (22i)
    if unboxedSigma g ctx.lvl ty then return a'
    let b' ← eraseCheck ctx b (ctx.instArg B a)
    return .obj 0 #[a', b']
  | .con x, .mu l I D i s _ =>
    if let some (T, home) := nativeHome? g ty then throw (nativeHomeError T home)
    let x' ← eraseCheck ctx x (vInterp g l I D (muFamilyAt l I D ((sizePred? s).getD .szInf)) i)
    -- a native representation: the native constructor, applied to the runtime field
    if let some ri := reprOfTy? g ty then
      match flatCon g ctx D x x' with
      | some (_, fs) => return ri.mkApp (fs[ri.r]?.getD .erased)
      | none =>
        let D' ← eraseCheck ctx (quote g ctx.lvl D) (.desc l I)
        return .letE "o" (.prim .pack #[D', x']) (ri.mkApp (.proj ri.r (.var 0)))
    let nat := isNatTy g ty
    match flatCon g ctx D x x', nat with
    | some (k, fs), false => return .obj k fs
    | some (0, _), true => return .natLit 0
    | some (_, fs), true =>
      match g.builtins.lookup "nat.succ", fs[0]? with
      | some succ, some f => return .app (.global succ) f
      | _, _ => return .prim .pack #[.obj 5 #[← eraseCheck ctx (quote g ctx.lvl D) (.desc l I)], x']
    | none, _ =>
      let D' ← eraseCheck ctx (quote g ctx.lvl D) (.desc l I)
      return .prim .pack #[if nat then .obj 5 #[D'] else D', x']
  | .cocon x, .nu l I D i s _ =>
    eraseCheck ctx x (vInterp g l I D (nuFamilyAt l I D ((sizePred? s).getD .szInf)) i)
  | .dret i, .desc _ I => return .obj 0 #[← eraseCheck ctx i I]
  | .darg _ S D, .desc l I =>
    let vS := ctx.eval S
    -- The mark below is this description's whole run-time knowledge of `S`, and code at
    -- a known type decides the same thing from the type (`startsWithTag`). At the head of
    -- a description they must agree for every instance, so `S` must be known here.
    if !inDesc && neutralFieldTy vS then
      throw (.other (abstractFieldMsg ++ " " ++
        s!"(`Desc.arg` at `{ctx.showTerm S}`, a type variable or a stuck term): whether its values carry a " ++
        "constructor tag would depend on how that type is instantiated. Give the first field a known type " ++
        "(for a choice of constructors, `Enum […]`)"))
    let D' ← eraseCheck ctx D (.pi "s" .default (.qlit QuantitySyntax.explicitDefault) vS
      (.mk [I] (.desc l (.var 1))) ⟨.succ l, .succ (.succ l)⟩) true
    -- a choice of tag is marked, for `pack`
    return .obj (if (tagField? vS).isSome then 4 else 1) #[.erased, D']
  | .drec _ j D, .desc l I =>
    return .obj 2 #[← eraseCheck ctx j I, ← eraseCheck ctx D (.desc l I) true]
  | .dhrec _ H j D, .desc l I =>
    let jTy : VTy R := .pi "h" .default (.qlit QuantitySyntax.explicitDefault) (ctx.eval H) (.mk [I] (.var 1)) ⟨.succ l, .succ l⟩
    return .obj 3 #[.erased, ← eraseCheck ctx j jTy, ← eraseCheck ctx D (.desc l I) true]
  | .tt, _ => return .erased
  | .letE x q ty' v b, _ =>
    let vTy := ctx.eval ty'
    let some p := (ctx.eval q).toPoly? | throw (.other "erasure: unknown quantity")
    let v' ← if p.isErased then pure .erased else eraseCheck ctx v vTy
    let b' ← eraseCheck (ctx.define x p vTy (ctx.eval v)) b ty inDesc
    return .letE x v' b'
  -- (linear-case stage 2) `let () := u; b`: `u` is evaluated, then `b` (a strict `let`
  -- whose variable `b` doesn't use; never dropped as dead code: `u` is a call, not a
  -- pure value, unless it is `()` itself)
  | .letUnit u b, _ => do
    let u' ← if u matches .tt then pure .erased else pure (← eraseInfer ctx u).1
    let b' ← eraseCheck ctx b ty inDesc
    return .letE "_" u' (b'.lift 1 0)
  -- the type is known (and not erasable), so don't infer the whole application again
  | .app .., _ => match unfoldCases? g t with
    | some t' => eraseCheck ctx t' ty inDesc
    | none => return (← eraseSpine ctx t).1
  | _, _ => return (← eraseInfer ctx t ty inDesc).1
  --|ex
  --| sorry
  --sol>

/-- **Exercise 5.1b.** Erase `t`, computing its type with the kernel's `infer`.

* variables, globals, applications (an argument to a `0`-quantity Π is `◾`);
* `fst`/`snd` are `proj 0`/`proj 1`; `split` binds the projections with `let`s; but
  at an `unboxedSigma` (22i) `fst` is the value itself, `snd` is `◾`;
* `ecase` on a tag is `case`; `cast` is its argument; `ann` is its term;
* the eliminators `ind`, `Desc.elim`, `out`, `coit`, `scofix` become primitives;
  `sfix` becomes a `fix`, and `scase` applies its method to the payload. -/
partial def eraseInfer (ctx : Ctx R) (t : Term R) (known : Option (VTy R) := none) (inDesc : Bool := false) :
    TCM (ETerm × VTy R) := do
  -- (given) P2: a marker that is not a proof's is transparent
  if let .prf l x := t then
    if !l.isZero then return ← eraseInfer ctx x known inDesc
  -- (`known`: the type, when the caller has it. Otherwise `quickType`, which off the
  -- elimination spine asks the kernel's `infer`: that checks the whole term again, once
  -- per enclosing node, quadratic in the depth of a `match`'s tree of `split`s)
  --<sol
  -- a projection: the pair first, and the projection's type from the pair's. (Asking
  -- `quickType` here and again at each projection below would walk the rest of a chain
  -- `p.2.2.….1`, a structure's field, once per step: quadratic in its length.) If the
  -- pair can't be erased, the general path below decides (the projection may still be
  -- erasable).
  if let some (p, isFst) := (match t with | .fst p => some (p, true) | .snd p => some (p, false) | _ => none) then
    if let .ok (p', pty) := eraseInfer ctx p then
      if let .sigma _ _ A B _ := whnf pty then
        let ty := known.getD (if isFst then A else sndType ctx B p)
        if erasable ctx ty then return (.erased, ty)
        let unboxed := unboxedSigma ctx.globals ctx.lvl pty
        return (if isFst then (if unboxed then p' else .proj 0 p') else (if unboxed then .erased else .proj 1 p'), ty)
  --|ex
  --sol>
  let ty ← match known with
    | some ty => pure ty
    | none => quickType ctx t
  if erasable ctx ty then
    if externCall ctx.globals t && !ctx.erased then return (.letE "_" (← eraseSpine ctx t).1 .erased, ty)
    return (.erased, ty)
  if let .natLit n := t then return (.natLit n, ty)
  -- (given) Q4: `down t` is `t`
  if let .down x := t then return (← eraseE ctx x, ty)
  --<sol
  let g := ctx.globals
  let e : ETerm ← match t with
    | .var ix => pure (.var ix)
    | .const n _ => pure (.global n)
    | .app .. => match unfoldCases? g t with
      | some t' => pure (← eraseInfer ctx t' ty inDesc).1
      | none => pure (← eraseSpine ctx t).1
    | .ann tm ty' => eraseCheck ctx tm (ctx.eval ty') inDesc
    | .letE .. | .letUnit .. => eraseCheck ctx t ty inDesc
    | .fst p => do
      let (p', pty) ← eraseInfer ctx p
      pure (if unboxedSigma g ctx.lvl pty then p' else .proj 0 p')
    | .snd p => do
      let (p', pty) ← eraseInfer ctx p
      pure (if unboxedSigma g ctx.lvl pty then .erased else .proj 1 p')
    | .split sq s _ m x y b => do
      -- a split at 0 never computes its scrutinee (the kernel checks it as an erased
      -- position): both components are `◾`
      let zero := isZeroQ (ctx.eval sq)
      let (s', sty) ← if zero then pure (.erased, ← quickType ctx s) else eraseInfer ctx s
      let .sigma _ q A B _ := whnf sty | throw (.other "erasure: split of a non-pair")
      let some pq := q.toPoly? | throw (.other "erasure: unknown quantity")
      -- let s := s'; let x := s.0; let y := s.1; b   (b lives under x, y: lift past s)
      let vx := Val.var ctx.lvl
      let ctx₂ := (ctx.bind x pq A).bind y [] (Closure.inst g B vx)
      -- the body's type, as the kernel checks it: the motive at the pair (the body may
      -- be a pair or a λ, which have no inferred type)
      let b' ← eraseCheck ctx₂ b (Closure.inst g (.mk ctx.env m) (.pair vx (Val.var (ctx.lvl + 1)))) inDesc
      if zero then
        pure (.letE "s" .erased (.letE x .erased (.letE y .erased (b'.lift 1 2))))
      else
      if unboxedSigma g ctx.lvl sty then
        pure (.letE "s" s' (.letE x (.var 0) (.letE y .erased (b'.lift 1 2))))
      else
      pure (.letE "s" s' (.letE x (.proj 0 (.var 0)) (.letE y (.proj 1 (.var 1)) (b'.lift 1 2))))
    | .ecase _ m s bs => do
      let (s', sty) ← eraseInfer ctx s
      let .enum ls := whnf sty | throw (.other "erasure: case on a non-tag")
      let mc : Closure R := .mk ctx.env m
      let bs' ← bs.toArray.mapIdxM fun k b => eraseCheck ctx b (Closure.inst g mc (.tag ls k)) inDesc
      pure (.case s' bs')
    -- (checked against its own type: it may be a function that can't be inferred)
    | .cast A _ _ x => eraseCheck ctx x (ctx.eval A)
    | .absurd .. => pure (.prim .unreachable #[])
    -- eliminators: their function arguments are erased against the kernel's types
    | .ind l I D v P m i x => do
      let w := QuantitySyntax.explicitDefault
      let (vI, vD, vP) := (ctx.eval I, ctx.eval D, ctx.eval P)
      let m' ← eraseCheck ctx m (indMethodTy g l v vI vD vP w)
      -- case analysis (the method ignores its hypotheses): don't compute them
      let isCases := match m with
        | .lam _ (.lam _ (.lam _ body)) => !(Wiz.IR.freeIdx' body).contains 0
        | _ => false
      let D' ← eraseCheck ctx D (.desc l vI)
      let xty ← quickType ctx x
      if let some (T, home) := nativeHome? g xty then throw (nativeHomeError T home)
      if isCases then pure (.apps m' [← eraseCheck ctx i vI, viewOf g vD xty D' (← eraseE ctx x), .erased])
      else
        let D' := if isNatTy g xty then .obj 5 #[D'] else D'
        let x' ← eraseE ctx x
        -- (a native value: the generic eliminator walks the model's object)
        let x' := match reprOfTy? g xty with
          | some ri => ri.toModel x'
          | none => x'
        pure (.prim .ind #[D', m', ← eraseCheck ctx i vI, x'])
    | .delim v P a b c h D => do
      let dty ← quickType ctx D
      let .desc l I := whnf dty | throw (.other "erasure: Desc.elim on a non-description")
      let (ta, tb, tc, th) := delimMethodTys g l v I (ctx.eval P) QuantitySyntax.explicitDefault
      let _ := v
      pure (.prim .delim #[← eraseCheck ctx a ta, ← eraseCheck ctx b tb, ← eraseCheck ctx c tc,
        ← eraseCheck ctx h th, ← eraseE ctx D])
    | .out x => pure (.prim .out #[← eraseE ctx x])
    | .coit l I D S st i s => do
      let (vI, vD) := (ctx.eval I, ctx.eval D)
      let stTy := coitStepTy g l vI vD (ctx.eval S) QuantitySyntax.explicitDefault
      pure (.prim .coit #[← eraseCheck ctx D (.desc l vI), ← eraseCheck ctx st stTy, ← eraseCheck ctx i vI,
        ← eraseCheck ctx s (vApp g (ctx.eval S) (ctx.eval i))])
    | .scofix l I D A f _ i a => do
      let (vI, vD, vA) := (ctx.eval I, ctx.eval D, ctx.eval A)
      let fTy := scofixFunTy g l vI vD vA QuantitySyntax.explicitDefault
      pure (.prim .scofix #[← eraseCheck ctx f fTy, ← eraseCheck ctx i vI,
        ← eraseCheck ctx a (vApp g vA (ctx.eval i))])
    | .sfix l I D v P f _ i x => do
      -- (fix self. λ i x. f ◾ (λ j i y. self i y) i x) i x
      let (vI, vD, vP) := (ctx.eval I, ctx.eval D, ctx.eval P)
      let f' ← eraseCheck ctx f (sfixFunTy g l v vI vD vP QuantitySyntax.explicitDefault)
      let recE : ETerm := .lam "j" (.lam "i" (.lam "y" (.apps (.var 5) [.var 1, .var 0])))
      let body : ETerm := .lam "i" (.lam "x" (.apps (f'.lift 3) [.erased, recE, .var 1, .var 0]))
      pure (.apps (.fix "self" body) [← eraseCheck ctx i vI, ← eraseE ctx x])
    | .scase l q I D v P m s i x => do
      -- m ◾ i payload   (a value of μ is its payload; K1: the quantity plays no part,
      -- except that a case at 0 has an erased scrutinee, whose payload is ◾)
      let (vI, vD, vP) := (ctx.eval I, ctx.eval D, ctx.eval P)
      let vq := ctx.eval q
      let mTy := scaseMethodTy g l v vI vD vP (ctx.eval s) vq
      let _ := v
      let m' ← eraseCheck ctx m mTy
      let i' ← eraseCheck ctx i vI
      if (vq.toPoly?.map (·.isErased)) == some true then
        pure (.apps m' [.erased, i', .erased])
      else
      let xty ← quickType ctx x
      if let some (T, home) := nativeHome? g xty then throw (nativeHomeError T home)
      let D' ← eraseCheck ctx D (.desc l vI)
      pure (.apps m' [.erased, i', viewOf g vD xty D' (← eraseE ctx x)])
    | .tag _ i => pure (.obj i #[])
    | _ => throw (.other s!"erasure: unexpected term {ctx.showTerm t}")
  return (e, ty)
  --|ex
  --| sorry
  --sol>

/-- Erase a term in inference mode, keeping only the program. -/
partial def eraseE (ctx : Ctx R) (t : Term R) : TCM ETerm := return (← eraseInfer ctx t).1

/-- Erase an application spine `h a₁ … aₙ` at once, returning its type: erasing `f a`
by erasing `f` recursively would re-infer every prefix (quadratic in long chains such
as string literals). -/
partial def eraseSpine (ctx : Ctx R) (t : Term R) : TCM (ETerm × VTy R) := do
  let (h, args) := t.spine
  let (h', hty) ← eraseInfer ctx h
  let mut acc := h'
  let mut fty := hty
  for a in args do
    match whnf fty with
    | .pi _ _ q dom cod _ =>
      let a' ← if isZeroQ q then pure .erased else eraseCheck ctx a dom
      acc := .app acc a'
      fty := ctx.instArg cod a
    | _ => throw (.other "erasure: application of a non-function")
  -- an erased head (a function into `Unit`, `erasedFunTy`) applied: nothing to run
  pure (if h' matches .erased then .erased else acc, fty)

end

/-! ### Resolving views

Redexes `(λ x. b) a` become `let x := a; b`. Case analysis gets a value's payload as `view D x`. Its projections are resolved
against the flat object: with `x` bound to `y`, the payload's `.0` is the tag of `y`
(`prim .tag`, or a `case` on `y` itself), and `.1.….1.0` (`j` times `.1`) is field
`j - 1`. Without a tag in front (`absorbed = false`) it is field `j`; for a number, the
tag and field are `natTag` and `natPred`. A view used any other way is converted with
`unpack`. -/

/-- A variable bound to (a suffix of) a payload: `j` levels into the view of the flat
value at level `y`; `D` is the description, valid at level `dLvl`. -/
structure Virt where
  y : Nat
  j : Nat
  absorbed : Bool
  nat : Bool
  D : ETerm
  dLvl : Nat
  /-- `y` is a native value (stage 22d): its runtime field is read with `get` -/
  repr : Option ReprInfo := none

/-- The field that `.0` of a view reaches, at depth `d`. -/
def Virt.field (v : Virt) (d : Nat) : ETerm :=
  let y := ETerm.var (d - 1 - v.y)
  if let some ri := v.repr then
    if v.absorbed && v.j == 0 then .obj ri.tag #[]
    else if (if v.absorbed then v.j - 1 else v.j) == ri.r then ri.getApp y else .erased
  else
  if v.absorbed then
    if v.j == 0 then .prim (if v.nat then .natTag else .tag) #[y]
    else if v.nat then .prim .natPred #[y] else .proj (v.j - 1) y
  else .proj v.j y

/-- The view as an ordinary payload, at depth `d`. -/
def Virt.materialize (v : Virt) (d : Nat) : ETerm :=
  let y : ETerm := .var (d - 1 - v.y)
  let y := match v.repr with
    | some ri => ri.toModel y
    | none => y
  (List.range v.j).foldl (fun t _ => .proj 1 t) (.prim .unpack #[v.D.lift (d - v.dLvl), y])

private def isView : ETerm → Bool
  | .prim (.view ..) _ => true
  | _ => false

mutual

private partial def rwV (d : Nat) (env : List (Option Virt)) : ETerm → Sum Virt ETerm
  | .var i => match env[i]? with
    | some (some v) => .inl v
    | _ => .inr (.var i)
  | .proj k t => match rwV d env t with
    | .inl v => if k == 1 then .inl { v with j := v.j + 1 } else .inr (v.field d)
    | .inr t' => .inr (.proj k t')
  | t => .inr (rw d env t)

private partial def rw (d : Nat) (env : List (Option Virt)) (t : ETerm) : ETerm :=
  match t with
  | .var i => match env[i]? with
    | some (some v) => v.materialize d
    | _ => .var i
  | .proj .. => match rwV d env t with
    | .inl v => v.materialize d
    | .inr t' => t'
  | .letE x (.prim (.view ab nat repr) #[D, e]) b =>
    -- let y := e; let x := ◾; b   (b lives under x and y: lift past y)
    let v : Virt := { y := d, j := 0, absorbed := ab, nat, D := rw d env D, dLvl := d, repr }
    .letE "y" (rw d env e) (.letE x .erased (rw (d + 2) (some v :: none :: env) (b.lift 1 1)))
  | .letE x val b => match rwV d env val with
    | .inl v => .letE x .erased (rw (d + 1) (some v :: env) b)
    | .inr val' => .letE x val' (rw (d + 1) (none :: env) b)
  | .app .. =>
    let (h, args) := spine t []
    let viewy (a : ETerm) : Bool := isView a || (rwV d env a matches .inl _)
    match h with
    -- `(λ x… . b) a…` is `let x := a; …` (in a strict language), and doesn't need a closure
    | .lam .. => rw d env (toLets h args 0)
    -- `(case s [b…]) a…` with a view among simple arguments: `case s [b a…, …]`
    | .case s bs =>
      if args.all simple && args.any viewy then rw d env (.case s (bs.map (ETerm.apps · args)))
      else args.foldl (fun f a => .app f (rw d env a)) (rw d env h)
    | _ => args.foldl (fun f a => .app f (rw d env a)) (rw d env h)
  | .case s bs =>
    let s' := match rwV d env s with
      | .inl v => v.materialize d
      | .inr s' => s'
    -- `case` reads the tag of an object itself
    let s' := match s' with
      | .prim .tag #[y] => y
      | s' => s'
    .case s' (bs.map (rw d env))
  | .lam x b => .lam x (rw (d + 1) (none :: env) b)
  | .fix x b => .fix x (rw (d + 1) (none :: env) b)
  | .obj tg fs => .obj tg (fs.map (rw d env))
  | .prim (.view _ _ repr) #[D, e] =>
    let e := rw d env e
    .prim .unpack #[rw d env D, match repr with | some ri => ri.toModel e | none => e]
  | .prim op as => .prim op (as.map (rw d env))
  | t => t
where
  spine : ETerm → List ETerm → ETerm × List ETerm
    | .app f a, acc => spine f (a :: acc)
    | t, acc => (t, acc)
  simple : ETerm → Bool
    | .var _ | .erased => true
    | .proj _ t => simple t
    | _ => false
  toLets : ETerm → List ETerm → Nat → ETerm
    | .lam x b, a :: as, k => .letE x (a.lift k) (toLets b as (k + 1))
    | b, as, k => ETerm.apps b (as.map (·.lift k))

end

/-- Resolve the views of a closed erased term. -/
def resolveViews (e : ETerm) : ETerm := rw 0 [] e

/-- Erase a closed term against its type, with views resolved. (`inDesc`: see `eraseDecl`.) -/
def eraseTop (ctx : Ctx R) (t : Term R) (ty : VTy R) (inDesc : Bool := false) : TCM ETerm :=
  return resolveViews (← eraseCheck ctx t ty inDesc)

/-- Is `d` the description that `coinductive T` generated (`T.desc`, with `T` a `ν`)? The
tag mark is read only for data (`pack`, `unpack`, `ind`); a `ν`'s payload is nested
pairs whatever its description starts with, and a parameterised `coinductive` type's
description does start with a field of an abstract type (`Signal A`: `Desc.arg A …`). -/
def isNuDesc (g : Globals R) (d : Decl R) : Bool :=
  d.name.endsWith ".desc" &&
  match (g.find? (String.ofList (d.name.toList.take (d.name.length - 5)))).bind (·.value) with
  | some v => underLams v
  | none => false
where
  underLams : Term R → Bool
    | .lam _ b => underLams b
    | .nu .. => true
    | _ => false

/-- Erase a global definition. -/
def eraseDecl (g : Globals R) (d : Decl R) : TCM ETerm := do
  -- the compiler's version (direct recursion), if the elaborator made one
  let some v := d.impl <|> d.value | return .prim .unreachable #[]
  -- (the kernel has checked it, like the value: `checkImpl`, `addPartialImpl`; it has
  -- accepted the term: nothing to require of its markers, `proof`)
  -- (`module`: the declaration's own, for `nativeHome?`)
  let ctx : Ctx R := { globals := { g with module := (g.declModule[d.name]?).getD "" }, proof := true }
  -- compiled equations (derived from the value, `deriveImpl`): the calls a nested split
  -- reverted go into its branches, and a constructor rebuilt from a branch's fields is the
  -- scrutinee (`Push`), if the result type-checks (else the step before, else the impl as
  -- is). Not checked to agree with the impl: equal by construction, trusted like erasure,
  -- as is the substitution of call closures afterwards (`ETerm.inlineCalls`)
  let derived := g.pushCalls && d.impl.isSome && d.value.isSome && Push.mentions d.name v
  let v := if derived then
      let ok (t : Term R) : Bool := (check ctx t (ctx.eval d.type)) matches .ok _
      let pushed := Push.betaCalls d.name ((Push.pushCalls g d.name v).getD v)
      let reused := Push.reuseScrutinee g 0 pushed
      if reused != v && ok reused then reused
      else if pushed != v && ok pushed then pushed
      else v
    else v
  -- universe polymorphism has no runtime content, but `Sort 0` would make motives
  -- propositions (and everything erasable): erase the `Type` instance
  let us := d.levelParams.map fun _ => Level.succ .zero
  -- (P2: the markers of level-generic terms mark nothing at this instance)
  let e ← eraseTop ctx (v.instLevels d.levelParams us).stripMarks (ctx.eval (d.type.instLevels d.levelParams us)) (isNuDesc g d)
  return if derived then e.inlineCalls d.name else e

end Wiz
