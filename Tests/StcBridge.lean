import Tests.Elab
import STC.F0.Syntax
import Lean.Data.Json

/-!
# The `MTm → F0.Tm` bridge, its corpus, and a per-class report

CORE-1.2 of `wiz-notes/roadmap/wiz-core-next.md` (M1.2): the STC fragment `F0`
(`STC/F0/`) has no translation from the terms the differential test uses (`MTm`,
`Tests/Elab.lean`). This file is the translation and the quantity that makes it
testable: a checked-in corpus of `MTm` values with their expected `F0.Tm` (or the class
of the rejection), and a deterministic `Report` per class.

The filter is the one the design note names: binders at `ω` only, closed levels, no
quantities other than `ω`, no `Desc`/`μ`/`ν`/sizes/`split`/numerals. `MTm` has no
`split` or numeral constructor, so those two classes are unreachable from this corpus;
every other class is reachable and has a case.

Nothing is dropped silently: `go` returns either a term or the class *and the offending
former* (`why`), and `Report` counts both. The classes are

* `core` — translated (the only class whose cases expect a term);
* `qty` — a binder or field at a quantity other than `ω`;
* `level` — a level F0 cannot write: a level parameter, a `const` with level arguments,
  or a closed sort above `Sort 2`;
* `desc` — `Desc`/`μ` and their constructors and eliminators;
* `size` — sizes (`size`, `szInf`, `sizeLt`, `mus`, `sfix`);
* `nu` — `ν` and its operations;
* `sort` — the components' sorts are not syntactically determined (the elaborator's
  sorts pass would be needed); counted rather than guessed.

The `Π`/`Σ` sort annotation F0 requires is computed by `sortOf`, which reads it off the
former (`Unit s : Sort s`, `Π s A B : Sort s`, …) and from a context of binder sorts.
A `Π` whose domain is, say, a `const` or an `app` is `sort`: that is the sorts pass,
not the bridge.

`toF0Sig` translates a declaration list and reports each declaration separately; the
`Report` for `MTm.globalDefs` is the note's accepted shape: `idU`, `A`, `a`, `twice`
and `caseF` translate, `idP`/`constP`/`polyK`/`dLv` are `level`, and `Nat`/`zero`/`one`
are `desc`.

The corpus is data (`Tests/data/stc-bridge/corpus.json`), the report is checked in
(`Tests/data/stc-bridge/report.txt`) and compared byte for byte, and the group
`=stc-bridge` (`Tests/Groups/StcBridge.lean`) runs both. One case mutates an expectation
on purpose and requires the failure to name its class and case id.
-/

namespace Tests.StcBridge

open Tests.Elab (MTm MLvl)
open STC.F0 (Tm Srt Decl Sig)

/-! ## The classes -/

/-- The corpus's classes. `core` is a translated term; the others name the first feature
that puts a term outside F0. -/
inductive Class where
  | core
  | qty
  | level
  | desc
  | size
  | nu
  | sort
  deriving Repr, DecidableEq, BEq, Hashable, Inhabited

namespace Class

/-- The class's name, as the report prints it. -/
def name : Class → String
  | .core => "core"
  | .qty => "qty"
  | .level => "level"
  | .desc => "desc"
  | .size => "size"
  | .nu => "nu"
  | .sort => "sort"

/-- Every class, in report order. -/
def all : List Class := [.core, .qty, .level, .desc, .size, .nu, .sort]

/-- Parse a class name (the corpus's `class` and `outside` fields). -/
def parse : String → Option Class
  | "core" => some .core
  | "qty" => some .qty
  | "level" => some .level
  | "desc" => some .desc
  | "size" => some .size
  | "nu" => some .nu
  | "sort" => some .sort
  | _ => none

end Class

/-- Why the filter refused a term: the class and the former that triggered it. -/
structure Outside where
  klass : Class
  why : String
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The filter's answer for one term. -/
inductive Result where
  | translated (t : Tm)
  | rejected (o : Outside)
  deriving Repr, Inhabited

/-- A refusal with its class and former. -/
def outside (klass : Class) (why : String) : Result := .rejected ⟨klass, why⟩

/-! ## Sorts -/

/-- The F0 sort for a level number: `0 = Prop`, `1 = Sort 1`, `2 = Sort 2`. F0 has no
`Sort 3`. -/
def srtOfLevel : Nat → Option Srt
  | 0 => some .prop
  | 1 => some .u0
  | 2 => some .u1
  | _ => none

/-- A closed level, if it has one (`succ`/`max`/`imax` of numerals). -/
def MLvl.closed : MLvl → Option Nat
  | .num n => some n
  | .param _ => none
  | .succ l => (MLvl.closed l).map (· + 1)
  | .max a b => do return max (← MLvl.closed a) (← MLvl.closed b)
  | .imax a b => do
      let a ← MLvl.closed a
      let b ← MLvl.closed b
      return if b = 0 then 0 else max a b

/-- The sort of a translated term, when F0's formers determine it without the sorts
pass. `Γ` is the sorts of the enclosing binders, innermost first. A `const` is not
resolved: a `Π`/`Σ` over one is `sort`, not the bridge's guess. -/
def sortOf (Γ : List Srt) : Tm → Option Srt
  | .var i => Γ[i]?
  | .sort s => s.succ?
  | .unit s => some s
  | .empty s => some s
  | .enum _ => some .u0
  | .pi s _ _ => some s
  | .sigma s _ _ => some s
  | .eq _ _ _ => some .prop
  | .eqTy _ _ => some .prop
  | .refl _ _ => some .prop
  | .reflTy _ => some .prop
  | .ulift s _ => some s
  | .ann _ A => sortOf Γ A
  | .absurd M _ => sortOf Γ M
  | .letUnit _ b => sortOf Γ b
  | .letE A _ b => do
      let i ← sortOf Γ A
      sortOf (i :: Γ) b
  | _ => none

/-- The sort of a `Π`/`Σ`'s two components, from the translated components. -/
def componentSorts (ta tb : Tm) : Option (Srt × Srt) := do
  let i ← sortOf [] ta
  let j ← sortOf [i] tb
  pure (i, j)

/-! ## The translation -/

/-- The answer for a `Π`/`Σ` from the answers for its components. Not recursive: `go`
translates the components, so the structural recursion never crosses this function. -/
def binderResult (isPi : Bool) (ra rb : Result) (sorts : Option (Nat × Nat) := none) : Result :=
  match ra, rb with
  | .rejected o, _ => .rejected o
  | _, .rejected o => .rejected o
  | .translated ta, .translated tb =>
    match sorts with
    | some (i, j) =>
      match srtOfLevel i, srtOfLevel j with
      | some si, some sj =>
        if isPi then .translated (.pi (Srt.imax si sj) ta tb)
        else .translated (.sigma (Srt.max si sj) ta tb)
      | _, _ =>
        outside .level (if isPi then "sorted/pi" else "sorted/sigma")
    | none =>
      match componentSorts ta tb with
      | some (si, sj) =>
        if isPi then .translated (.pi (Srt.imax si sj) ta tb)
        else .translated (.sigma (Srt.max si sj) ta tb)
      | none =>
        outside .sort (if isPi then "pi/component-sort" else "sigma/component-sort")

/-- `MTm → F0.Tm`, or the class and former that put it outside the fragment. Partial: the
translation is total on the corpus, but Lean does not need to see a decreasing measure
for a test-only function (the branch list is handled by a local recursion). -/
partial def go (t : MTm) : Result :=
  match t with
    -- core formers
    | .var i => .translated (.var i)
    | .univ n =>
      match srtOfLevel (n + 1) with
      | some s => .translated (.sort s)
      | none => outside .level "univ"
    | .prop => .translated (.sort .prop)
    | .ptrue => .translated (.unit .prop)
    | .pfalse => .translated (.empty .prop)
    | .unit n =>
      match srtOfLevel (n + 1) with
      | some s => .translated (.unit s)
      | none => outside .level "unit"
    | .empty n =>
      match srtOfLevel (n + 1) with
      | some s => .translated (.empty s)
      | none => outside .level "empty"
    | .pi a b => binderResult true (go a) (go b)
    | .sigma a b => binderResult false (go a) (go b)
    | .lam b =>
      match go b with
      | .rejected o => .rejected o
      | .translated tb => .translated (.lam tb)
    | .app f a =>
      match go f with
      | .rejected o => .rejected o
      | .translated tf =>
        match go a with
        | .rejected o => .rejected o
        | .translated ta => .translated (.app tf ta)
    | .letE A v b =>
      match go A with
      | .rejected o => .rejected o
      | .translated tA =>
        match go v with
        | .rejected o => .rejected o
        | .translated tv =>
          match go b with
          | .rejected o => .rejected o
          | .translated tb => .translated (.letE tA tv tb)
    | .ann t A =>
      match go t with
      | .rejected o => .rejected o
      | .translated tterm =>
        match go A with
        | .rejected o => .rejected o
        | .translated tA => .translated (.ann tterm tA)
    | .pair a b =>
      match go a with
      | .rejected o => .rejected o
      | .translated ta =>
        match go b with
        | .rejected o => .rejected o
        | .translated tb => .translated (.pair ta tb)
    | .fst p =>
      match go p with
      | .rejected o => .rejected o
      | .translated tp => .translated (.fst tp)
    | .snd p =>
      match go p with
      | .rejected o => .rejected o
      | .translated tp => .translated (.snd tp)
    | .star => .translated .tt
    | .exfalso M t =>
      match go M with
      | .rejected o => .rejected o
      | .translated tM =>
        match go t with
        | .rejected o => .rejected o
        | .translated tterm => .translated (.absurd tM tterm)
    | .letUnit u b =>
      match go u with
      | .rejected o => .rejected o
      | .translated tu =>
        match go b with
        | .rejected o => .rejected o
        | .translated tb => .translated (.letUnit tu tb)
    | .enum k => .translated (.enum k)
    | .tag k i => .translated (.tag k i)
    | .ecase M s bs =>
      match go M with
      | .rejected o => .rejected o
      | .translated tM =>
        match go s with
        | .rejected o => .rejected o
        | .translated ts =>
          let rec branches : List MTm → Result
            | [] => .translated .bnil
            | b :: bs =>
              match go b with
              | .rejected o => .rejected o
              | .translated tb =>
                match branches bs with
                | .rejected o => .rejected o
                | .translated tbs => .translated (.bcons tb tbs)
          match branches bs with
          | .rejected o => .rejected o
          | .translated tbs => .translated (.ecase tM ts tbs)
    | .eq A a b =>
      match go A with
      | .rejected o => .rejected o
      | .translated tA =>
        match go a with
        | .rejected o => .rejected o
        | .translated ta =>
          match go b with
          | .rejected o => .rejected o
          | .translated tb => .translated (.eq tA ta tb)
    | .eqTy A B =>
      match go A with
      | .rejected o => .rejected o
      | .translated tA =>
        match go B with
        | .rejected o => .rejected o
        | .translated tB => .translated (.eqTy tA tB)
    | .refl A a =>
      match go A with
      | .rejected o => .rejected o
      | .translated tA =>
        match go a with
        | .rejected o => .rejected o
        | .translated ta => .translated (.refl tA ta)
    | .reflTy X =>
      match go X with
      | .rejected o => .rejected o
      | .translated tX => .translated (.reflTy tX)
    | .cast A B e t =>
      match go A with
      | .rejected o => .rejected o
      | .translated tA =>
        match go B with
        | .rejected o => .rejected o
        | .translated tB =>
          match go e with
          | .rejected o => .rejected o
          | .translated te =>
            match go t with
            | .rejected o => .rejected o
            | .translated tterm => .translated (.cast tA tB te tterm)
    | .transp A a P p b e =>
      match go A with
      | .rejected o => .rejected o
      | .translated tA =>
        match go a with
        | .rejected o => .rejected o
        | .translated ta =>
          match go P with
          | .rejected o => .rejected o
          | .translated tP =>
            match go p with
            | .rejected o => .rejected o
            | .translated tp =>
              match go b with
              | .rejected o => .rejected o
              | .translated tb =>
                match go e with
                | .rejected o => .rejected o
                | .translated te => .translated (.transp tA ta tP tp tb te)
    | .ulift k l A =>
      match go A with
      | .rejected o => .rejected o
      | .translated tA =>
        match srtOfLevel k, srtOfLevel l with
        | some sk, some sl =>
          if sl = .prop then outside .level "ulift/prop"
          else
            match sortOf [] tA with
            | some s => if s = sk then .translated (.ulift sl tA) else outside .sort "ulift/k"
            | none => .translated (.ulift sl tA)
        | _, _ => outside .level "ulift"
    | .up a =>
      match go a with
      | .rejected o => .rejected o
      | .translated ta => .translated (.up ta)
    | .down t =>
      match go t with
      | .rejected o => .rejected o
      | .translated tterm => .translated (.down tterm)
    | .sorted i j t =>
      match t with
      | .pi a b => binderResult true (go a) (go b) (some (i, j))
      | .sigma a b => binderResult false (go a) (go b) (some (i, j))
      | _ => go t
    -- a global: closed in F0, so no level arguments
    | .const c ls =>
      if ls.isEmpty then .translated (.const c) else outside .level "const/levels"
    | .sortParam _ => outside .level "sortParam"
    | .sortLv l =>
      match MLvl.closed l with
      | some k =>
        match srtOfLevel k with
        | some s => .translated (.sort s)
        | none => outside .level "sortLv/range"
      | none => outside .level "sortLv/open"
    -- quantities other than ω
    | .piq .many a b => binderResult true (go a) (go b)
    | .piq _ _ _ => outside .qty "piq"
    | .sigmaq .many a b => binderResult false (go a) (go b)
    | .sigmaq _ _ _ => outside .qty "sigmaq"
    | .letq .many A v b =>
      match go A with
      | .rejected o => .rejected o
      | .translated tA =>
        match go v with
        | .rejected o => .rejected o
        | .translated tv =>
          match go b with
          | .rejected o => .rejected o
          | .translated tb => .translated (.letE tA tv tb)
    | .letq _ _ _ _ => outside .qty "letq"
    | .scaseq .many _ _ _ _ _ _ _ _ _ => outside .size "scase"
    | .scaseq _ _ _ _ _ _ _ _ _ _ => outside .qty "scaseq"
    -- a `Desc` former: still outside F0 whether or not its field is at `ω`; the quantity
    -- is the finer answer when it applies
    | .darg _ _ .many => outside .desc "darg"
    | .darg _ _ _ => outside .qty "darg"
    | .drec _ _ .many => outside .desc "drec"
    | .drec _ _ _ => outside .qty "drec"
    | .dhrec _ _ _ .many => outside .desc "dhrec"
    | .dhrec _ _ _ _ => outside .qty "dhrec"
    -- Desc and μ
    | .desc _ _ => outside .desc "desc"
    | .dret _ => outside .desc "dret"
    | .delim _ _ _ _ _ _ _ => outside .desc "delim"
    | .mu _ _ _ _ => outside .desc "mu"
    | .con _ => outside .desc "con"
    | .ind _ _ _ _ _ _ _ _ => outside .desc "ind"
    -- sizes
    | .size => outside .size "size"
    | .szInf => outside .size "szInf"
    | .szSuc _ => outside .size "szSuc"
    | .sizeLt _ => outside .size "sizeLt"
    | .mus _ _ _ _ _ => outside .size "mus"
    | .sfix _ _ _ _ _ _ _ _ _ => outside .size "sfix"
    | .scase _ _ _ _ _ _ _ _ _ => outside .size "scase"
    -- ν
    | .nu _ _ _ _ _ => outside .nu "nu"
    | .out _ => outside .nu "out"
    | .cocon _ => outside .nu "cocon"
    | .scofix _ _ _ _ _ _ _ _ => outside .nu "scofix"
    | .coit _ _ _ _ _ _ _ => outside .nu "coit"
    -- the proof marker is a kernel-evaluator hint; F0 has no markers and needs none
    | .prf _ t => go t


/-- `MTm → F0.Tm`, `none` outside the fragment. `go` keeps the class; this is the shape
the design note names. -/
def toF0 (t : MTm) : Option Tm :=
  match go t with
  | .translated t => some t
  | .rejected _ => none

/-! ## The signature -/

/-- One declaration's answer. -/
inductive DeclResult where
  | translated (d : Decl)
  | rejected (o : Outside)
  deriving Repr

/-- Translate a declaration list, in order, into an F0 signature (most recent first).
Each declaration is classified separately: a level-polymorphic declaration is `level`,
and a value or type outside the fragment carries that class. -/
def declGo (name : String) (ps : List String) (v : Option MTm) (ty : MTm) : DeclResult :=
  if !ps.isEmpty then .rejected ⟨.level, "level-params"⟩
  else
    match go ty with
    | .rejected o => .rejected o
    | .translated tty =>
      match v with
      | none => .translated { name := name, type := tty, value := none }
      | some v =>
        match go v with
        | .rejected o => .rejected o
        | .translated tv => .translated { name := name, type := tty, value := some tv }

/-- `toF0Sig`: the F0 signature of the declarations that are in the fragment, and one
answer per declaration (`MTm.globalDefs` order). -/
def toF0Sig (ds : List (String × List String × Option MTm × MTm)) :
    List Decl × List (String × DeclResult) :=
  let step (acc : List Decl × List (String × DeclResult))
      (d : String × List String × Option MTm × MTm) :=
    let (n, ps, v, ty) := d
    match declGo n ps v ty with
    | .translated decl => (decl :: acc.1, acc.2 ++ [(n, .translated decl)])
    | .rejected o => (acc.1, acc.2 ++ [(n, .rejected o)])
  ds.foldl step ([], [])

/-! ## Rendering and the report -/

/-- The three sorts, spelled as `STC.lean` spells them. -/
def renderSrt : Srt → String
  | .prop => "prop"
  | .u0 => "u0"
  | .u1 => "u1"

/-- A canonical, injective rendering of an F0 term. The corpus stores expected terms in
this syntax; `go` and the corpus are compared through it, so the data is readable and a
changed translation shows the two sides. -/
def renderTm : Tm → String
  | .var i => s!"(var {i})"
  | .const c => s!"(const {c})"
  | .sort s => s!"(sort {renderSrt s})"
  | .pi s A B => s!"(pi {renderSrt s} {renderTm A} {renderTm B})"
  | .lam b => s!"(lam {renderTm b})"
  | .app f a => s!"(app {renderTm f} {renderTm a})"
  | .letE A v b => s!"(letE {renderTm A} {renderTm v} {renderTm b})"
  | .letUnit u b => s!"(letUnit {renderTm u} {renderTm b})"
  | .ann t A => s!"(ann {renderTm t} {renderTm A})"
  | .sigma s A B => s!"(sigma {renderSrt s} {renderTm A} {renderTm B})"
  | .pair a b => s!"(pair {renderTm a} {renderTm b})"
  | .fst p => s!"(fst {renderTm p})"
  | .snd p => s!"(snd {renderTm p})"
  | .unit s => s!"(unit {renderSrt s})"
  | .tt => "tt"
  | .empty s => s!"(empty {renderSrt s})"
  | .absurd M t => s!"(absurd {renderTm M} {renderTm t})"
  | .enum n => s!"(enum {n})"
  | .tag n i => s!"(tag {n} {i})"
  | .ecase M s bs => s!"(ecase {renderTm M} {renderTm s} {renderTm bs})"
  | .bnil => "bnil"
  | .bcons b bs => s!"(bcons {renderTm b} {renderTm bs})"
  | .eq A a b => s!"(eq {renderTm A} {renderTm a} {renderTm b})"
  | .eqTy A B => s!"(eqTy {renderTm A} {renderTm B})"
  | .refl A a => s!"(refl {renderTm A} {renderTm a})"
  | .reflTy A => s!"(reflTy {renderTm A})"
  | .cast A B e t => s!"(cast {renderTm A} {renderTm B} {renderTm e} {renderTm t})"
  | .transp A a P p b e =>
    s!"(transp {renderTm A} {renderTm a} {renderTm P} {renderTm p} {renderTm b} {renderTm e})"
  | .ulift s A => s!"(ulift {renderSrt s} {renderTm A})"
  | .up a => s!"(up {renderTm a})"
  | .down t => s!"(down {renderTm t})"

/-- What a corpus case expects. -/
inductive Expect where
  /-- the rendered F0 term (`renderTm`) -/
  | f0 (rendered : String)
  /-- a rejection: its class and the former -/
  | outside (klass : Class) (why : String)
  deriving Repr, BEq, DecidableEq

/-- One corpus case: an id, the term, and the expected answer. -/
structure Case where
  id : String
  mtm : MTm
  expect : Expect

/-- A case whose answer does not match its expectation. -/
structure Failure where
  klass : Class
  id : String
  expected : String
  got : String
  deriving Repr

namespace Failure

/-- One line, naming the class and the case. -/
def render (f : Failure) : String :=
  s!"{f.klass.name} {f.id}: expected {f.expected}, got {f.got}"

end Failure

/-- The class a case expects (its expectation's class). -/
def Expect.klass : Expect → Class
  | .f0 _ => .core
  | .outside k _ => k

def Expect.render : Expect → String
  | .f0 s => s
  | .outside k w => s!"outside {k.name} ({w})"

/-- Check one case. -/
def checkCase (c : Case) : Except Failure Unit :=
  match c.expect, go c.mtm with
  | .f0 want, .translated t =>
    let got := renderTm t
    if got == want then .ok () else .error { klass := .core, id := c.id, expected := want, got := got }
  | .f0 want, .rejected o =>
    .error { klass := .core, id := c.id, expected := want,
             got := s!"outside {o.klass.name} ({o.why})" }
  | .outside k w, .translated t =>
    .error { klass := k, id := c.id, expected := s!"outside {k.name} ({w})",
             got := s!"translated {renderTm t}" }
  | .outside k w, .rejected o =>
    if o.klass == k && o.why == w then .ok ()
    else .error { klass := k, id := c.id, expected := s!"outside {k.name} ({w})",
                  got := s!"outside {o.klass.name} ({o.why})" }

/-- One class's tally. `translated`/`rejected` count what the translation did; `reasons`
counts the actual `why` tags of the rejected cases, in first-seen order. -/
structure ClassTally where
  klass : Class
  cases : Nat
  agreed : Nat
  translated : Nat
  rejected : Nat
  reasons : List (String × Nat)
  deriving Repr

/-- The corpus's report. -/
structure Report where
  total : Nat
  agreed : Nat
  classes : List ClassTally
  failures : List Failure
  deriving Repr

/-- Count `why` tags in first-seen order. -/
def reasonsOf (cs : List Case) : List (String × Nat) :=
  let rec loop (seen : List (String × Nat)) : List Case → List (String × Nat)
    | [] => seen.reverse
    | c :: rest =>
      match go c.mtm with
      | .translated _ => loop seen rest
      | .rejected o =>
        match seen.find? (fun (w, _) => w == o.why) with
        | some (w0, _) =>
          loop (seen.map fun (w', n') => if w' == w0 then (w', n' + 1) else (w', n')) rest
        | none => loop ((o.why, 1) :: seen) rest
  loop [] cs

/-- Tally the corpus by expected class, in `Class.all` order. -/
def reportOf (classes : List (Class × Case)) : Report :=
  let failures := classes.filterMap fun (_, c) =>
    match checkCase c with
    | .ok _ => none
    | .error f => some f
  let tallies := Class.all.filterMap fun k =>
    let here := (classes.filter (·.1 == k)).map (·.2)
    if here.isEmpty then none
    else
      some { klass := k,
             cases := here.length,
             agreed := (here.filter (fun c => (checkCase c).isOk)).length,
             translated := (here.filter fun c => match go c.mtm with
               | .translated _ => true | .rejected _ => false).length,
             rejected := (here.filter fun c => match go c.mtm with
               | .translated _ => false | .rejected _ => true).length,
             reasons := reasonsOf here }
  { total := classes.length, agreed := classes.length - failures.length,
    classes := tallies, failures := failures }

/-- Left-pad-free fixed-width field. -/
def pad (s : String) (n : Nat) : String :=
  s ++ String.ofList (List.replicate (n - s.length) ' ')

/-- Deterministic rendering: one line per class, then the coverage line, then one line
per failure. The checked-in file is this string. -/
def Report.render (r : Report) : String :=
  let header := s!"stc-bridge corpus: {r.total} cases, {r.agreed} agreed, {r.failures.length} failed"
  let cols := s!"  {pad "class" 7}{pad "cases" 7}{pad "agreed" 7}{pad "translated" 12}{pad "rejected" 10}why"
  let row (t : ClassTally) :=
    let why := if t.reasons.isEmpty then "-"
      else ", ".intercalate (t.reasons.map fun (w, n) => s!"{w} {n}")
    s!"  {pad t.klass.name 7}{pad (toString t.cases) 7}{pad (toString t.agreed) 7}" ++
      s!"{pad (toString t.translated) 12}{pad (toString t.rejected) 10}{why}"
  let countOf (k : Class) : Nat :=
    (r.classes.find? (·.klass == k)).map (·.cases) |>.getD 0
  let coverage := "stc-bridge: translated " ++ toString (countOf .core) ++
    ", " ++ ", ".intercalate (Class.all.filter (· != .core) |>.map fun k =>
      s!"outside-{k.name} {countOf k}")
  let fails := r.failures.map fun f => "  failure: " ++ f.render
  String.intercalate "\n" ([header, cols] ++ r.classes.map row ++ [coverage] ++ fails)

/-- One declaration's line in the signature report. -/
structure SigLine where
  name : String
  klass : Class
  why : String

/-- The report for `toF0Sig`. `sig` is the F0 signature of the translated declarations;
`lines` has one entry per input declaration, in input order. -/
structure SigReport where
  sig : List Decl
  lines : List SigLine

def SigReport.translated (r : SigReport) : Nat :=
  (r.lines.filter (·.klass == .core)).length

def SigReport.render (r : SigReport) (title : String) : String :=
  let outside := r.lines.filter (fun l => l.klass != .core)
  let header := s!"stc-bridge signature ({title}): {r.lines.length} declarations, " ++
    s!"{r.translated} translated, {outside.length} outside"
  let body := Class.all.filterMap fun k =>
    let here := r.lines.filter (fun l => l.klass == k)
    if here.isEmpty then none
    else some (s!"  {pad (if k == .core then "translated" else k.name) 11}" ++
      ", ".intercalate (here.map (·.name)))
  String.intercalate "\n" ([header] ++ body)

/-- The report for a declaration list, split out so the group can pin it. -/
def sigReport (ds : List (String × List String × Option MTm × MTm)) : SigReport :=
  let (sig, outs) := toF0Sig ds
  let lines := outs.map fun (n, r) =>
    match r with
    | .translated _ => ({ name := n, klass := .core, why := "" } : SigLine)
    | .rejected o => { name := n, klass := o.klass, why := o.why }
  { sig := sig, lines := lines }

/-! ## The corpus file -/

/-- The JSON decoder's state: one class section. -/
structure CorpusClass where
  klass : Class
  note : String
  cases : List Case

def asArr (j : Lean.Json) : Except String (Array Lean.Json) := j.getArr?
def asStr (j : Lean.Json) : Except String String := j.getStr?
def asNat (j : Lean.Json) : Except String Nat := j.getNat?

def optField? (j : Lean.Json) (k : String) : Except String (Option Lean.Json) :=
  match j.getObjVal? k with
  | .ok v => pure (some v)
  | .error _ => pure none

def decodeQty : String → Except String Wiz.ZeroOneMany
  | "zero" => pure .zero
  | "one" => pure .one
  | "many" => pure .many
  | s => throw s!"quantity: expected zero/one/many, got {s}"

partial def decodeMLvl (j : Lean.Json) : Except String MLvl := do
  let a ← asArr j
  let some head := a[0]? | throw "level: empty array"
  let s ← asStr head
  let xs := a.toList.tail
  match s, xs with
  | "num", [n] => pure (.num (← asNat n))
  | "param", [p] => MLvl.param <$> asStr p
  | "succ", [l] => MLvl.succ <$> decodeMLvl l
  | "max", [a, b] => pure (.max (← decodeMLvl a) (← decodeMLvl b))
  | "imax", [a, b] => pure (.imax (← decodeMLvl a) (← decodeMLvl b))
  | _, _ => throw s!"level: unknown constructor or arity: {s} ({xs.length})"

/-- Decode one `MTm` from the corpus's JSON. Every constructor is named; an unknown tag is
an error, not a hole. -/
partial def decodeMTm (j : Lean.Json) : Except String MTm := do
  let a ← asArr j
  let some head := a[0]? | throw "MTm: empty array"
  let s ← asStr head
  let xs := a.toList.tail
  match s, xs with
  | "var", [i] => pure (.var (← asNat i))
  | "univ", [n] => pure (.univ (← asNat n))
  | "pi", [a, b] => pure (.pi (← decodeMTm a) (← decodeMTm b))
  | "lam", [b] => pure (.lam (← decodeMTm b))
  | "app", [f, a] => pure (.app (← decodeMTm f) (← decodeMTm a))
  | "letE", [A, v, b] => pure (.letE (← decodeMTm A) (← decodeMTm v) (← decodeMTm b))
  | "ann", [t, A] => pure (.ann (← decodeMTm t) (← decodeMTm A))
  | "sigma", [a, b] => pure (.sigma (← decodeMTm a) (← decodeMTm b))
  | "pair", [a, b] => pure (.pair (← decodeMTm a) (← decodeMTm b))
  | "fst", [p] => pure (.fst (← decodeMTm p))
  | "snd", [p] => pure (.snd (← decodeMTm p))
  | "unit", [n] => pure (.unit (← asNat n))
  | "star", [] => pure .star
  | "empty", [n] => pure (.empty (← asNat n))
  | "exfalso", [m, t] => pure (.exfalso (← decodeMTm m) (← decodeMTm t))
  | "letUnit", [u, b] => pure (.letUnit (← decodeMTm u) (← decodeMTm b))
  | "enum", [k] => pure (.enum (← asNat k))
  | "tag", [k, i] => pure (.tag (← asNat k) (← asNat i))
  | "ecase", [m, sc, bs] => do
      let bs ← (← asArr bs).toList.mapM decodeMTm
      pure (.ecase (← decodeMTm m) (← decodeMTm sc) bs)
  | "prop", [] => pure .prop
  | "ptrue", [] => pure .ptrue
  | "pfalse", [] => pure .pfalse
  | "eq", [A, a, b] => pure (.eq (← decodeMTm A) (← decodeMTm a) (← decodeMTm b))
  | "eqTy", [A, B] => pure (.eqTy (← decodeMTm A) (← decodeMTm B))
  | "refl", [A, a] => pure (.refl (← decodeMTm A) (← decodeMTm a))
  | "reflTy", [X] => pure (.reflTy (← decodeMTm X))
  | "cast", [A, B, e, t] => pure (.cast (← decodeMTm A) (← decodeMTm B) (← decodeMTm e) (← decodeMTm t))
  | "transp", [A, a, P, p, b, e] =>
      pure (.transp (← decodeMTm A) (← decodeMTm a) (← decodeMTm P) (← decodeMTm p)
        (← decodeMTm b) (← decodeMTm e))
  | "desc", [l, I] => pure (.desc (← asNat l) (← decodeMTm I))
  | "dret", [i] => pure (.dret (← decodeMTm i))
  | "darg", [S, E, q] => pure (.darg (← decodeMTm S) (← decodeMTm E) (← decodeQty (← asStr q)))
  | "drec", [j, E, q] => pure (.drec (← decodeMTm j) (← decodeMTm E) (← decodeQty (← asStr q)))
  | "dhrec", [H, j, E, q] =>
      pure (.dhrec (← decodeMTm H) (← decodeMTm j) (← decodeMTm E) (← decodeQty (← asStr q)))
  | "delim", [v, P, a, b, c, h, D] =>
      pure (.delim (← asNat v) (← decodeMTm P) (← decodeMTm a) (← decodeMTm b) (← decodeMTm c)
        (← decodeMTm h) (← decodeMTm D))
  | "mu", [l, I, D, i] => pure (.mu (← asNat l) (← decodeMTm I) (← decodeMTm D) (← decodeMTm i))
  | "con", [x] => pure (.con (← decodeMTm x))
  | "ind", [l, I, D, v, P, m, i, x] =>
      pure (.ind (← asNat l) (← decodeMTm I) (← decodeMTm D) (← asNat v) (← decodeMTm P)
        (← decodeMTm m) (← decodeMTm i) (← decodeMTm x))
  | "const", [n, ls] => do
      let ls ← (← asArr ls).toList.mapM asNat
      pure (.const (← asStr n) ls)
  | "sortParam", [u] => pure (.sortParam (← asStr u))
  | "sortLv", [l] => pure (.sortLv (← decodeMLvl l))
  | "piq", [q, a, b] => pure (.piq (← decodeQty (← asStr q)) (← decodeMTm a) (← decodeMTm b))
  | "sigmaq", [q, a, b] => pure (.sigmaq (← decodeQty (← asStr q)) (← decodeMTm a) (← decodeMTm b))
  | "letq", [q, A, v, b] =>
      pure (.letq (← decodeQty (← asStr q)) (← decodeMTm A) (← decodeMTm v) (← decodeMTm b))
  | "size", [] => pure .size
  | "szInf", [] => pure .szInf
  | "szSuc", [s] => pure (.szSuc (← decodeMTm s))
  | "sizeLt", [s] => pure (.sizeLt (← decodeMTm s))
  | "mus", [l, I, D, i, sz] =>
      pure (.mus (← asNat l) (← decodeMTm I) (← decodeMTm D) (← decodeMTm i) (← decodeMTm sz))
  | "sfix", [l, I, D, v, P, f, sz, i, x] =>
      pure (.sfix (← asNat l) (← decodeMTm I) (← decodeMTm D) (← asNat v) (← decodeMTm P)
        (← decodeMTm f) (← decodeMTm sz) (← decodeMTm i) (← decodeMTm x))
  | "nu", [l, I, D, i, sz] =>
      pure (.nu (← asNat l) (← decodeMTm I) (← decodeMTm D) (← decodeMTm i) (← decodeMTm sz))
  | "out", [x] => pure (.out (← decodeMTm x))
  | "cocon", [x] => pure (.cocon (← decodeMTm x))
  | "scofix", [l, I, D, A, f, sz, i, a] =>
      pure (.scofix (← asNat l) (← decodeMTm I) (← decodeMTm D) (← decodeMTm A)
        (← decodeMTm f) (← decodeMTm sz) (← decodeMTm i) (← decodeMTm a))
  | "coit", [l, I, D, S, st, i, sz] =>
      pure (.coit (← asNat l) (← decodeMTm I) (← decodeMTm D) (← decodeMTm S)
        (← decodeMTm st) (← decodeMTm i) (← decodeMTm sz))
  | "scase", [l, I, D, v, P, m, sc, i, x] =>
      pure (.scase (← asNat l) (← decodeMTm I) (← decodeMTm D) (← asNat v) (← decodeMTm P)
        (← decodeMTm m) (← decodeMTm sc) (← decodeMTm i) (← decodeMTm x))
  | "scaseq", [q, l, I, D, v, P, m, sc, i, x] =>
      pure (.scaseq (← decodeQty (← asStr q)) (← asNat l) (← decodeMTm I) (← decodeMTm D)
        (← asNat v) (← decodeMTm P) (← decodeMTm m) (← decodeMTm sc) (← decodeMTm i)
        (← decodeMTm x))
  | "sorted", [i, j, t] => pure (.sorted (← asNat i) (← asNat j) (← decodeMTm t))
  | "ulift", [k, l, A] => pure (.ulift (← asNat k) (← asNat l) (← decodeMTm A))
  | "up", [a] => pure (.up (← decodeMTm a))
  | "down", [t] => pure (.down (← decodeMTm t))
  | "prf", [l, t] => pure (.prf (← decodeMLvl l) (← decodeMTm t))
  | _, _ => throw s!"MTm: unknown constructor or arity: {s} ({xs.length})"

/-- Decode one case. Exactly one of `f0` (a rendered term) and `outside` (+ `why`). -/
def decodeCase (j : Lean.Json) : Except String Case := do
  let id ← asStr (← j.getObjVal? "id")
  let mtm ← decodeMTm (← j.getObjVal? "mtm")
  let f0? ← optField? j "f0"
  let outside? ← optField? j "outside"
  match f0?, outside? with
  | some f0, none => pure { id := id, mtm := mtm, expect := .f0 (← asStr f0) }
  | none, some k => do
      let kn ← asStr k
      let some klass := Class.parse kn | throw s!"case {id}: unknown class {kn}"
      let why ← asStr (← j.getObjVal? "why")
      pure { id := id, mtm := mtm, expect := .outside klass why }
  | some _, some _ => throw s!"case {id}: both f0 and outside"
  | none, none => throw s!"case {id}: neither f0 nor outside"

/-- Parse the corpus (the JSON text). -/
def parseCorpus (text : String) : Except String (List CorpusClass) := do
  let root ← Lean.Json.parse text
  let cs ← asArr (← root.getObjVal? "classes")
  cs.toList.mapM fun cj => do
    let kn ← asStr (← cj.getObjVal? "class")
    let some klass := Class.parse kn | throw s!"unknown class {kn}"
    let note ← asStr (← cj.getObjVal? "note")
    let cases ← (← asArr (← cj.getObjVal? "cases")).toList.mapM decodeCase
    let _ ← cases.mapM fun c => do
      unless c.expect.klass == klass do
        throw s!"case {c.id}: expected class {c.expect.klass.name} in section {klass.name}"
      pure ()
    pure { klass := klass, note := note, cases := cases }

/-- Flatten the corpus to `(class, case)` pairs, in file order. -/
def CorpusClass.pairs (cs : List CorpusClass) : List (Class × Case) :=
  cs.flatMap fun c => c.cases.map (c.klass, ·)

/-- The self-test of the failure path: take the first translated case, state a deliberately
wrong expectation, and return the failure. Fails if the wrong expectation agrees. -/
def wrongExpectation (cs : List CorpusClass) : Except String Failure := do
  let some c := (cs.flatMap (·.cases)).find? fun c =>
      match c.expect with
      | .f0 _ => true
      | .outside _ _ => false
    | throw "the corpus has no translated case to mutate"
  match checkCase { c with expect := .outside .qty "piq" } with
  | .error f => pure f
  | .ok () => throw "a deliberately wrong expectation agreed: the report proves nothing"

end Tests.StcBridge
