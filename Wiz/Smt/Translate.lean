import Wiz.Core.Eval

/-!
# Goals as SMT-LIB 2 (stage 28a): the translation the `smt` tactic trusts

`translate` turns a goal (its context and type, as kernel values) into an SMT-LIB script
whose `unsat` means the goal holds. **This function is in the trusted base of `smt`**
(with the solver), so it is small and conservative: it recognises a fixed set of
definitions by name, and everything else of a known sort becomes an *atom*, a fresh
constant (two atoms are the same constant when their terms are the same). Abstracting a
subterm to a constant is sound (a formula valid for an arbitrary value is valid for this
one); it only loses completeness.

The fragment (wiz-notes/smt.md §3.2):
* Props: `→` between propositions, `¬`, `∧`, `∨`, `↔`, `True`, `False`, `a = b` at a
  sort below; a `∀` over a sort at the goal's top (a fresh constant).
* `Bool`: `.true`, `.false`, `Bool.and/or/not/xor`, `Nat.lt/le/beq`, word comparisons.
* `Nat` as `Int` with `x ≥ 0` for every variable and atom; `+ *`, `succ`, `pred`,
  truncated `-`, `/` and `%` with Wiz's `x / 0 = 0`, `x % 0 = x`, `Nat.max`.
* `UIntN w` (`w` a numeral ≥ 1) as `(_ BitVec w)`: `add sub mul neg div mod land lor xor
  not`, shifts and `testBit` by numerals, `beq lt le`, `ofNat`, `toNat`, `zero`, `max`.
  **Ranges**: every `UIntN w` value is below `2^w` (its constructor carries the proof,
  stage 22l), and on such values the definitions are the bit-vector operations. (Before
  22l the kernel's `UIntN 8` had values like `ofBitsTrusted 300`, where `not (not x) = x`
  fails, and the translation required a range hypothesis for every word.)
* Anything else: a premise or hypothesis outside the fragment is dropped (sound: the
  problem only gets harder); a goal outside it is an error.
-/

namespace Wiz.Smt

open Wiz

variable {R : Type} [QRig R] [DecidableEq R] [QuantitySyntax R]

inductive SSort where
  | bool | nat | int
  | bv (w : Nat)
  deriving BEq, Repr, Inhabited

def SSort.smt : SSort → String
  | .bool => "Bool"
  | .nat | .int => "Int"
  | .bv w => s!"(_ BitVec {w})"

structure TState (R : Type) where
  /-- `declare-const` lines, assertions -/
  decls : Array String := #[]
  asserts : Array String := #[]
  /-- the SMT name and sort of each local variable, by level (none: not translated) -/
  locals : Array (Option (String × SSort)) := #[]
  /-- atoms: the level and the term quoted there (de Bruijn indices mean different
  variables at different levels), its name and sort -/
  atoms : Array (Nat × Term R × String × SSort) := #[]
  /-- what to show in a counterexample: SMT name, the user's name -/
  shown : Array (String × String) := #[]
  /-- word constants and their widths -/
  words : Array (String × Nat × String) := #[]
  next : Nat := 0

abbrev TM (R : Type) := StateT (TState R) (Except String)

/-- What the solver is asked, and how to read its model. -/
structure Query where
  script : String
  shown : Array (String × String)
  deriving Inhabited

private def sanitize (x : String) : String :=
  let s := String.mk (x.toList.filter fun c => c.isAlphanum || c == '_')
  if s.isEmpty then "x" else s

private def fresh (base : String) : TM R String := do
  let s ← get
  set { s with next := s.next + 1 }
  pure s!"{sanitize base}_{s.next}"

private def declare (name : String) (srt : SSort) (shown : Option String) : TM R Unit := do
  modify fun s => { s with decls := s.decls.push s!"(declare-const {name} {srt.smt})" }
  if srt == .nat then modify fun s => { s with asserts := s.asserts.push s!"(>= {name} 0)" }
  if let .bv w := srt then modify fun s => { s with words := s.words.push (name, w, shown.getD name) }
  if let some u := shown then modify fun s => { s with shown := s.shown.push (name, u) }

/-- The arguments of an application spine (none if it has projections or eliminators). -/
private def spineArgs (sp : Array (Elim R)) : Option (List (Val R)) :=
  sp.toList.mapM fun | .app a => some a | _ => none

/-- Unfold glued values. -/
private partial def wh (v : Val R) : Val R := whnf v

/-- The *position* of a constructor value's tag and its fields (a constructor is
`con (tag, fields…)`; an enumeration's value may be a bare tag). Never its label: types are
structural, so `inductive Flip | true | false` is convertible with `Bool`, and `Flip.true`
*is* `Bool.false` (tag 0), whatever it is called (smt-review B1). The caller knows the
library type (`sortOf`) and reads the position against its declaration: `Bool` is
`false | true`, `Nat` is `zero | succ`. -/
private def ctor? (v : Val R) : Option (Nat × List (Val R)) :=
  let tagOf : Val R → Option Nat
    | .tag ls i | .up (.tag ls i) => if i < ls.length then some i else none
    | _ => none
  let rec parts : Nat → Val R → List (Val R)
    | 0, _ => []
    | n + 1, .pair a b => a :: parts n b
    | _, t => [t]
  match wh v with
  | .con (.pair t rest) => (tagOf t).map fun c => (c, (parts 8 rest).map fun | .up x => x | x => x)
  | t => (tagOf t).map fun c => (c, [])

/-- Is `n` the library's? The translation
recognises definitions by name (lib/Prelude.wiz, lib/Word.wiz, lib/Logic.wiz), so a user's own `UIntN.not` (in a file that does not
import Word) must not be read as `bvnot`. A module root can't replace the toolchain's
`Prelude` or `Word` (Module.shadowed). -/
def fromLib (g : Globals R) (n : Name) : Bool :=
  match g.declModule.get? n with
  | some m => m == "Prelude" || m == "Word" || m == "Logic" || m == "Int"
  | none => false

/-- The sort of a type, if it is one of the fragment's. -/
partial def sortOf (g : Globals R) (A : Val R) : Option SSort :=
  match A with
  | .neutral (.global "UIntN" _) sp =>
    -- (outside lib/Word.wiz a sealed type with private constructors is opaque)
    if !fromLib g "UIntN" then none else
    match spineArgs sp with
    | some [w] => match wh w with
      | .natLit (n + 1) => some (.bv (n + 1))
      | _ => none
    | _ => none
  | .unfold n _ sp v => match n, spineArgs sp with
    | "Int", some [] => if fromLib g "Int" then some .int else sortOf g v.get
    | _, _ => sortOf g v.get
  | .lazyInd .. => sortOf g (wh A)
  | .mu _ _ _ _ _ (some (T, _, args)) => if !fromLib g T then none else match T, args with
    | "Nat", [] => some .nat
    | "Bool", [] => some .bool
    | "Int", [] => some .int
    | "UIntN", args =>
      -- (the width is the type's one parameter; a sealed type's hint may carry more)
      match args.filterMap (fun a => match wh a with | .natLit n => some n | _ => none) with
      | [n + 1] => some (.bv (n + 1))
      | _ => none
    | _, _ => none
  | _ => none

private def bin (op : String) (a b : String) : String := s!"({op} {a} {b})"

mutual

/-- A term of sort `s`. -/
partial def term (g : Globals R) (lvl : Nat) (v : Val R) (s : SSort) : TM R String := do
  match v with
  | .natLit n => match s with
    | .nat | .int => return toString n
    | _ => atom g lvl v s
  | .unfold n _ sp val =>
    match ← known g lvl n (spineArgs sp) s with
    | some r => return r
    | none => term g lvl val.get s
  | .lazyInd .. => term g lvl (wh v) s
  | .neutral (.global n _) sp =>
    match ← known g lvl n (spineArgs sp) s with
    | some r => return r
    | none => atom g lvl v s
  | .neutral (.local l) #[] =>
    match (← get).locals[l]? with
    | some (some (x, s')) => if s' == s then return x else atom g lvl v s
    | _ => atom g lvl v s
  | _ =>
    match s, ctor? v with
    -- (positions in lib/Prelude.wiz's `inductive Bool | false | true` and
    -- `inductive Nat | zero | succ n`)
    | .bool, some (0, _) => return "false"
    | .bool, some (1, _) => return "true"
    | .nat, some (0, _) => return "0"
    | .nat, some (1, n :: _) => return bin "+" (← term g lvl n .nat) "1"
    | _, _ => atom g lvl v s

/-- A fresh constant for a term the translation does not look into. -/
partial def atom (g : Globals R) (lvl : Nat) (v : Val R) (s : SSort) : TM R String := do
  let t := quote g lvl v
  if let some (_, _, x, _) := (← get).atoms.find? fun (l', t', _, s') => l' == lvl && t' == t && s' == s then return x
  let x ← fresh "atom"
  modify fun st => { st with atoms := st.atoms.push (lvl, t, x, s) }
  declare x s none
  return x

/-- A definition the fragment knows, applied to `args`, at sort `s`. -/
partial def known (g : Globals R) (lvl : Nat) (n : Name) (args? : Option (List (Val R))) (s : SSort) :
    TM R (Option String) := do
  let some args := args? | return none
  unless fromLib g n do return none
  let t (v : Val R) (s' : SSort) := term g lvl v s'
  let lit? (v : Val R) : Option Nat := match wh v with | .natLit k => some k | _ => none
  -- a word operation's width must be this sort's
  let width (w : Val R) : Option Nat := match lit? w with
    | some (k + 1) => some (k + 1)
    | _ => none
  match s, n, args with
  -- Nat
  | .nat, "Nat.add", [a, b] => return bin "+" (← t a .nat) (← t b .nat)
  | .nat, "Nat.mul", [a, b] => return bin "*" (← t a .nat) (← t b .nat)
  | .nat, "Nat.sub", [a, b] => let a ← t a .nat; let b ← t b .nat; return s!"(ite (>= {a} {b}) (- {a} {b}) 0)"
  | .nat, "Nat.div", [a, b] => let a ← t a .nat; let b ← t b .nat; return s!"(ite (= {b} 0) 0 (div {a} {b}))"
  | .nat, "Nat.mod", [a, b] => let a ← t a .nat; let b ← t b .nat; return s!"(ite (= {b} 0) {a} (mod {a} {b}))"
  | .nat, "Nat.pred", [a] => let a ← t a .nat; return s!"(ite (= {a} 0) 0 (- {a} 1))"
  | .nat, "Nat.succ", [a] => return bin "+" (← t a .nat) "1"
  | .nat, "Nat.max", [a, b] => let a ← t a .nat; let b ← t b .nat; return s!"(ite (< {a} {b}) {b} {a})"
  | .nat, "UIntN.toNat", [w, a] => match width w with
    | some k => return s!"(bv2nat {← t a (.bv k)})"
    | none => return none
  -- Bool
  | .bool, "Bool.and", [a, b] => return bin "and" (← t a .bool) (← t b .bool)
  | .bool, "Bool.or", [a, b] => return bin "or" (← t a .bool) (← t b .bool)
  | .bool, "Bool.xor", [a, b] => return bin "xor" (← t a .bool) (← t b .bool)
  | .bool, "Bool.not", [a] => return s!"(not {← t a .bool})"
  | .bool, "Nat.lt", [a, b] => return bin "<" (← t a .nat) (← t b .nat)
  | .bool, "Nat.le", [a, b] => return bin "<=" (← t a .nat) (← t b .nat)
  | .bool, "Nat.beq", [a, b] => return bin "=" (← t a .nat) (← t b .nat)
  | .bool, "UIntN.beq", [w, a, b] => wordRel g lvl w a b "="
  | .bool, "UIntN.lt", [w, a, b] => wordRel g lvl w a b "bvult"
  | .bool, "UIntN.le", [w, a, b] => wordRel g lvl w a b "bvule"
  | .bool, "UIntN.testBit", [w, a, i] => match width w, lit? i with
    | some k, some j => if j < k then return s!"(= ((_ extract {j} {j}) {← t a (.bv k)}) #b1)" else return "false"
    | _, _ => return none
  -- words: the width argument must be this sort's
  | .bv k, op, w :: rest => do
    if width w != some k then return none
    let tw (v : Val R) := t v (.bv k)
    match op, rest with
    | "UIntN.add", [a, b] => return bin "bvadd" (← tw a) (← tw b)
    | "UIntN.sub", [a, b] => return bin "bvsub" (← tw a) (← tw b)
    | "UIntN.mul", [a, b] => return bin "bvmul" (← tw a) (← tw b)
    | "UIntN.neg", [a] => return s!"(bvneg {← tw a})"
    -- `x / 0 = 0` in Wiz; SMT-LIB's `bvudiv` gives all ones
    | "UIntN.div", [a, b] => let a ← tw a; let b ← tw b; return s!"(ite (= {b} (_ bv0 {k})) (_ bv0 {k}) (bvudiv {a} {b}))"
    -- `x % 0 = x` in both
    | "UIntN.mod", [a, b] => return bin "bvurem" (← tw a) (← tw b)
    | "UIntN.land", [a, b] => return bin "bvand" (← tw a) (← tw b)
    | "UIntN.lor", [a, b] => return bin "bvor" (← tw a) (← tw b)
    | "UIntN.xor", [a, b] => return bin "bvxor" (← tw a) (← tw b)
    | "UIntN.not", [a] => return s!"(bvnot {← tw a})"
    | "UIntN.shiftLeft", [a, i] => match lit? i with
      | some j => if j < k then return s!"(bvshl {← tw a} (_ bv{j} {k}))" else return s!"(_ bv0 {k})"
      | none => return none
    | "UIntN.shiftRight", [a, i] => match lit? i with
      | some j => if j < k then return s!"(bvlshr {← tw a} (_ bv{j} {k}))" else return s!"(_ bv0 {k})"
      | none => return none
    | "UIntN.ofNat", [a] => return s!"((_ int2bv {k}) {← t a .nat})"
    | "UIntN.zero", [] => return s!"(_ bv0 {k})"
    | "UIntN.max", [] => return s!"(bvnot (_ bv0 {k}))"
    | _, _ => return none
  | _, _, _ => return none

partial def wordRel (g : Globals R) (lvl : Nat) (w a b : Val R) (op : String) : TM R (Option String) := do
  match wh w with
  | .natLit (k + 1) => return some (bin op (← term g lvl a (.bv (k + 1))) (← term g lvl b (.bv (k + 1))))
  | _ => return none

end

/-- A proposition (none: not in the fragment). -/
partial def prop (g : Globals R) (lvl : Nat) (P : Val R) : TM R (Option String) := do
  let sub (Q : Val R) : TM R (Option String) := prop g lvl Q
  let two (op : String) (a b : Val R) : TM R (Option String) := do
    let some a ← sub a | return none
    let some b ← sub b | return none
    return some (bin op a b)
  match P with
  | .unfold n _ sp val =>
    match (if fromLib g n then n else ""), spineArgs sp with
    | "Not", some [a] => return (← sub a).map fun a => s!"(not {a})"
    | "And", some [a, b] => two "and" a b
    | "Or", some [a, b] => two "or" a b
    | "Iff", some [a, b] => two "=" a b
    | _, _ => prop g lvl val.get
  | .lazyInd .. => prop g lvl (wh P)
  | .unit _ => return some "true"
  | .empty _ => return some "false"
  | .neutral (.eq A a b) #[] =>
    match sortOf g A with
    | some s =>
      -- (an equation between booleans is `=` on `Bool`)
      let a ← term g lvl a s
      let b ← term g lvl b s
      return some (bin "=" a b)
    | none => return none
  | .pi _ _ _ dom cod _ =>
    -- an implication between propositions (the body must not mention the proof)
    if (sortOf g dom).isSome then return none
    let some a ← sub dom | return none
    let before ← get
    modify fun s => { s with locals := s.locals.push none }
    let r ← prop g (lvl + 1) (Closure.inst g cod (Val.var lvl))
    modify fun s => { s with locals := before.locals }
    return r.map fun b => bin "=>" a b
  | _ => return none

/-- Assert a hypothesis (a premise or a context entry): dropped if it is outside the
fragment. -/
def hyp (g : Globals R) (lvl : Nat) (P : Val R) : TM R Unit := do
  let saved ← get
  match (prop g lvl P).run saved with
  | .ok (some h, s) =>
    set s
    modify fun s => { s with asserts := s.asserts.push h }
  | _ => set saved

/-- The query for goal `ty` in context (`names`, `types`, `bound`, outermost first). -/
partial def translate (g : Globals R) (names : List Name) (types : List (Val R)) (bound : List Bool)
    (ty : Val R) : Except String Query := do
  let go : TM R Unit := do
    -- the context: variables of the fragment's sorts, and hypotheses
    for ((x, A), (b, j)) in (names.zip types).zip (bound.zip (List.range names.length)) do
      if !b then
        modify fun s => { s with locals := s.locals.push none }
        continue
      match sortOf g A with
      | some srt =>
        let n ← fresh x
        declare n srt (some x)
        modify fun s => { s with locals := s.locals.push (some (n, srt)) }
      | none =>
        modify fun s => { s with locals := s.locals.push none }
        hyp g j A
    -- the goal: peel `∀`s and premises
    let rec peel (lvl : Nat) (T : Val R) (fuel : Nat) : TM R Unit := do
      match fuel, wh T with
      | 0, _ => throw "smt: the goal has too many binders"
      | fuel + 1, .pi x _ _ dom cod _ =>
        match sortOf g dom with
        | some srt =>
          let n ← fresh x
          declare n srt (some x)
          modify fun s => { s with locals := s.locals.push (some (n, srt)) }
        | none =>
          hyp g lvl dom
          modify fun s => { s with locals := s.locals.push none }
        peel (lvl + 1) (Closure.inst g cod (Val.var lvl)) fuel
      | _, _ =>
        match ← prop g lvl T with
        | some p => modify fun s => { s with asserts := s.asserts.push s!"(not {p})" }
        | none => throw "smt: the goal is not in the fragment (propositions built from →, ¬, ∧, ∨, ↔ and equations at Bool, Nat and UIntN with a numeral width)"
    peel names.length ty 1000
  match go.run {} with
  | .error e => .error e
  | .ok ((), s) =>
    let body := "\n".intercalate (s.decls.toList ++ s.asserts.toList.map (s!"(assert {·})"))
    let getv := if s.shown.isEmpty then "" else
      s!"\n(get-value ({" ".intercalate (s.shown.toList.map (·.1))}))"
    pure { script := s!"(set-logic ALL)\n{body}\n(check-sat){getv}\n", shown := s.shown }

end Wiz.Smt
