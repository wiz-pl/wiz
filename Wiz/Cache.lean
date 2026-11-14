import Wiz.Query
import Wiz.Module

/-!
# The shared cache

The query engine's memo table, on disk: a command's **effect** (the declarations it
adds, its messages, and its registrations) is stored in `<cache dir>/<key>.wizc` (`wiz --cache DIR`), where
the key is the chained content hash of the command and everything before it (and a
version salt). Elaboration is deterministic, so a shared directory is a shared cache:
two machines elaborating the same text compute the same keys and the same effects.

Commands that change the grammar or the macros (`syntax`, `macro_rules`, `notation`,
attributes, `import`, user-defined commands) aren't cached; they are cheap to rerun.
Declarations read from the cache were checked by the kernel when they were stored, so
they are trusted.

The format is S-expressions; quantities are written with the rig's literal syntax.
-/

namespace Wiz.Cache

variable {R : Type} [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R] [IsoCache R]

inductive Sx where
  | a (s : String)
  | l (xs : Array Sx)
  deriving Inhabited

partial def Sx.render : Sx → String
  | .a s => if !s.isEmpty && s.toList.all (fun c => c.isAlphanum || "._-+*'→✝".toList.contains c) then s else s.quote
  | .l xs => "(" ++ " ".intercalate (xs.toList.map Sx.render) ++ ")"

/-- Parse an S-expression (atoms are bare words or Lean-style string literals). -/
partial def Sx.parse (s : String) : Option Sx :=
  match go s.toList with
  | some (x, rest) => if rest.all (·.isWhitespace) then some x else none
  | none => none
where
  go (cs : List Char) : Option (Sx × List Char) := do
    let cs := cs.dropWhile (·.isWhitespace)
    match cs with
    | '(' :: rest =>
      let rec items (cs : List Char) (acc : Array Sx) : Option (Array Sx × List Char) :=
        match cs.dropWhile (·.isWhitespace) with
        | ')' :: rest => some (acc, rest)
        | [] => none
        | cs => do let (x, rest) ← go cs; items rest (acc.push x)
      let (xs, rest) ← items rest #[]
      return (.l xs, rest)
    | '"' :: rest =>
      let rec str (cs : List Char) (acc : List Char) : Option (String × List Char) :=
        match cs with
        | '\\' :: 'n' :: cs => str cs ('\n' :: acc)
        | '\\' :: 't' :: cs => str cs ('\t' :: acc)
        | '\\' :: 'x' :: h₁ :: h₂ :: cs =>
          let hex (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87
          str cs (Char.ofNat (16 * hex h₁ + hex h₂) :: acc)
        | '\\' :: 'u' :: '{' :: cs =>
          let ds := cs.takeWhile (· != '}')
          let hex (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87
          str (cs.drop (ds.length + 1)) (Char.ofNat (ds.foldl (fun n c => 16 * n + hex c) 0) :: acc)
        | '\\' :: c :: cs => str cs (c :: acc)
        | '"' :: cs => some (String.ofList acc.reverse, cs)
        | c :: cs => str cs (c :: acc)
        | [] => none
      let (s, rest) ← str rest []
      return (.a s, rest)
    | [] => none
    | cs =>
      let w := cs.takeWhile fun c => !c.isWhitespace && c != '(' && c != ')'
      if w.isEmpty then none else return (.a (String.ofList w), cs.drop w.length)

def node (tag : String) (xs : List Sx) : Sx := .l (#[.a tag] ++ xs.toArray)
def nat (n : Nat) : Sx := .a (toString n)
def str (s : String) : Sx := .a s
def list (xs : List Sx) : Sx := .l xs.toArray

partial def level : Level → Sx
  | .zero => .a "0"
  | .succ l => node "S" [level l]
  | .max a b => node "max" [level a, level b]
  | .imax a b => node "imax" [level a, level b]
  | .param n => node "p" [str n]
  | .mvar m => node "m" [nat m]

def bi : BinderInfo → Sx
  | .default => .a "d" | .implicit => .a "i" | .instImplicit => .a "I"

partial def term : Term R → Sx
  | .var i => node "var" [nat i]
  | .const n us => node "const" [str n, list (us.map level)]
  | .sort l => node "sort" [level l]
  | .pi x b q A B s => node "pi" [str x, bi b, term q, term A, term B, optLevel s]
  | .lam x b => node "lam" [str x, term b]
  | .app f a => node "app" [term f, term a]
  | .letE x q t v b => node "let" [str x, term q, term t, term v, term b]
  | .ann t ty => node "ann" [term t, term ty]
  | .mvar m => node "mvar" [nat m]
  | .sigma x q a b s => node "sigma" [str x, term q, term a, term b, optLevel s]
  | .pair a b => node "pair" [term a, term b]
  | .fst t => node "fst" [term t]
  | .snd t => node "snd" [term t]
  | .split q s z m x y b => node "split" [term q, term s, str z, term m, str x, str y, term b]
  | .unit l => node "unit" [level l]
  | .tt => .a "tt"
  | .empty l => node "empty" [level l]
  | .absurd m t => node "absurd" [term m, term t]
  | .letUnit u b => node "letUnit" [term u, term b]
  | .eq A a b => node "eq" [term A, term a, term b]
  | .eqTy A B => node "eqTy" [term A, term B]
  | .refl A a => node "refl" [term A, term a]
  | .reflTy X => node "reflTy" [term X]
  | .cast A B e t => node "cast" [term A, term B, term e, term t]
  | .transp A a P p b e => node "transp" [term A, term a, term P, term p, term b, term e]
  | .qty => .a "qty"
  | .qlit r => node "q" [str (QuantitySyntax.display r)]
  | .enum ls => node "enum" [list (ls.map str)]
  | .tag ls i => node "tag" [list (ls.map str), nat i]
  | .ecase z m s bs => node "ecase" [str z, term m, term s, list (bs.map term)]
  | .desc l I => node "desc" [level l, term I]
  | .dret i => node "dret" [term i]
  | .darg q S D => node "darg" [term q, term S, term D]
  | .drec q j D => node "drec" [term q, term j, term D]
  | .dhrec q H j D => node "dhrec" [term q, term H, term j, term D]
  | .delim v P a b c h D => node "delim" [level v, term P, term a, term b, term c, term h, term D]
  | .mu l I D i s h => node "mu" [level l, term I, term D, term i, term s, hint h]
  | .con x => node "con" [term x]
  | .ind l I D v P m i x => node "ind" [level l, term I, term D, level v, term P, term m, term i, term x]
  | .nu l I D i s h => node "nu" [level l, term I, term D, term i, term s, hint h]
  | .out x => node "out" [term x]
  | .size => .a "size"
  | .szInf => .a "inf"
  | .szSuc s => node "szSuc" [term s]
  | .sizeLt s => node "sizeLt" [term s]
  | .sfix l I D v P f s i x => node "sfix" [level l, term I, term D, level v, term P, term f, term s, term i, term x]
  | .scase l q I D v P m s i x => node "scase" [level l, term q, term I, term D, level v, term P, term m, term s, term i, term x]
  | .cocon x => node "cocon" [term x]
  | .scofix l I D A f s i a => node "scofix" [level l, term I, term D, term A, term f, term s, term i, term a]
  | .coit l I D S st i s => node "coit" [level l, term I, term D, term S, term st, term i, term s]
  | .natLit n => node "nat" [nat n]
  | .natOp op as => node "natOp" [str op, list (as.toList.map term)]
  | .ulift l A => node "ulift" [level l, term A]
  | .up a => node "up" [term a]
  | .down t => node "down" [term t]
  | .prf l t => node "prf" [level l, term t]
where
  optLevel : Option Level → Sx
    | none => .a "none"
    | some l => node "some" [level l]
  hint : Option (Name × List Level × List (Term R)) → Sx
    | none => .a "none"
    | some (n, us, as) => node "hint" [str n, list (us.map level), list (as.map term)]

/-! ## Decoding -/

def atom? : Sx → Option String
  | .a s => some s
  | _ => none
def items? : Sx → Option (Array Sx)
  | .l xs => some xs
  | _ => none

partial def dlevel : Sx → Option Level
  | .a "0" => some .zero
  | .l #[.a "S", l] => (dlevel l).map .succ
  | .l #[.a "max", a, b] => return .max (← dlevel a) (← dlevel b)
  | .l #[.a "imax", a, b] => return .imax (← dlevel a) (← dlevel b)
  | .l #[.a "p", .a n] => some (.param n)
  | .l #[.a "m", .a n] => n.toNat?.map .mvar
  | _ => none

def dbi : Sx → Option BinderInfo
  | .a "d" => some .default | .a "i" => some .implicit | .a "I" => some .instImplicit | _ => none

partial def dterm : Sx → Option (Term R)
  | .a "tt" => some .tt
  | .a "qty" => some .qty
  | .a "size" => some .size
  | .a "inf" => some .szInf
  | .l xs => do
    let tag ← atom? (xs[0]?.getD (.a ""))
    let x (i : Nat) : Sx := xs[i]?.getD (.a "")
    let t (i : Nat) : Option (Term R) := dterm (x i)
    let s (i : Nat) : Option String := atom? (x i)
    let n (i : Nat) : Option Nat := (s i).bind String.toNat?
    let lv (i : Nat) : Option Level := dlevel (x i)
    let ts (i : Nat) : Option (List (Term R)) := do (← items? (x i)).toList.mapM dterm
    let ss (i : Nat) : Option (List String) := do (← items? (x i)).toList.mapM atom?
    let hint (i : Nat) : Option (Option (Name × List Level × List (Term R))) :=
      match x i with
      | .a "none" => some none
      | .l #[.a "hint", .a nm, us, as] => do
        some (some (nm, ← (← items? us).toList.mapM dlevel, ← (← items? as).toList.mapM dterm))
      | _ => none
    let olv (i : Nat) : Option (Option Level) :=
      match x i with
      | .a "none" => some none
      | .l #[.a "some", l] => (dlevel l).map some
      | _ => none
    match tag with
    | "var" => return .var (← n 1)
    | "const" => return .const (← s 1) (← (← items? (x 2)).toList.mapM dlevel)
    | "sort" => return .sort (← lv 1)
    | "pi" => return .pi (← s 1) (← dbi (x 2)) (← t 3) (← t 4) (← t 5) (← olv 6)
    | "lam" => return .lam (← s 1) (← t 2)
    | "app" => return .app (← t 1) (← t 2)
    | "let" => return .letE (← s 1) (← t 2) (← t 3) (← t 4) (← t 5)
    | "ann" => return .ann (← t 1) (← t 2)
    | "mvar" => return .mvar (← n 1)
    | "sigma" => return .sigma (← s 1) (← t 2) (← t 3) (← t 4) (← olv 5)
    | "pair" => return .pair (← t 1) (← t 2)
    | "fst" => return .fst (← t 1)
    | "snd" => return .snd (← t 1)
    | "split" => return .split (← t 1) (← t 2) (← s 3) (← t 4) (← s 5) (← s 6) (← t 7)
    | "unit" => return .unit (← lv 1)
    | "empty" => return .empty (← lv 1)
    | "absurd" => return .absurd (← t 1) (← t 2)
    | "letUnit" => return .letUnit (← t 1) (← t 2)
    | "eq" => return .eq (← t 1) (← t 2) (← t 3)
    | "eqTy" => return .eqTy (← t 1) (← t 2)
    | "refl" => return .refl (← t 1) (← t 2)
    | "reflTy" => return .reflTy (← t 1)
    | "cast" => return .cast (← t 1) (← t 2) (← t 3) (← t 4)
    | "transp" => return .transp (← t 1) (← t 2) (← t 3) (← t 4) (← t 5) (← t 6)
    | "q" => return .qlit (← QuantitySyntax.ofLiteral (← s 1))
    | "enum" => return .enum (← ss 1)
    | "tag" => return .tag (← ss 1) (← n 2)
    | "ecase" => return .ecase (← s 1) (← t 2) (← t 3) (← ts 4)
    | "desc" => return .desc (← lv 1) (← t 2)
    | "dret" => return .dret (← t 1)
    | "darg" => return .darg (← t 1) (← t 2) (← t 3)
    | "drec" => return .drec (← t 1) (← t 2) (← t 3)
    | "dhrec" => return .dhrec (← t 1) (← t 2) (← t 3) (← t 4)
    | "delim" => return .delim (← lv 1) (← t 2) (← t 3) (← t 4) (← t 5) (← t 6) (← t 7)
    | "mu" => return .mu (← lv 1) (← t 2) (← t 3) (← t 4) (← t 5) (← hint 6)
    | "con" => return .con (← t 1)
    | "ind" => return .ind (← lv 1) (← t 2) (← t 3) (← lv 4) (← t 5) (← t 6) (← t 7) (← t 8)
    | "nu" => return .nu (← lv 1) (← t 2) (← t 3) (← t 4) (← t 5) (← hint 6)
    | "out" => return .out (← t 1)
    | "szSuc" => return .szSuc (← t 1)
    | "sizeLt" => return .sizeLt (← t 1)
    | "sfix" => return .sfix (← lv 1) (← t 2) (← t 3) (← lv 4) (← t 5) (← t 6) (← t 7) (← t 8) (← t 9)
    | "scase" => return .scase (← lv 1) (← t 2) (← t 3) (← t 4) (← lv 5) (← t 6) (← t 7) (← t 8) (← t 9) (← t 10)
    | "cocon" => return .cocon (← t 1)
    | "ulift" => return .ulift (← lv 1) (← t 2)
    | "up" => return .up (← t 1)
    | "down" => return .down (← t 1)
    | "prf" => return .prf (← lv 1) (← t 2)
    | "scofix" => return .scofix (← lv 1) (← t 2) (← t 3) (← t 4) (← t 5) (← t 6) (← t 7) (← t 8)
    | "coit" => return .coit (← lv 1) (← t 2) (← t 3) (← t 4) (← t 5) (← t 6) (← t 7)
    | "nat" => return .natLit (← n 1)
    | "natOp" => return .natOp (← s 1) (← ts 2).toArray
    | _ => none
  | _ => none

/-! ## Command effects -/

/-- What a command added to the state. -/
structure Effect (R : Type) where
  decls : Array (Decl R) := #[]
  messages : Array Msg := #[]
  builtins : List (Name × Name) := []
  assumed : List (Name × Name) := []
  classes : List ClassInfo := []
  instances : Array InstanceInfo := #[]
  coinductives : List (Name × List (Name × Bool)) := []
  foreignTypes : List (Name × String) := []
  cCode : Array String := #[]
  infos : Array (Info R) := #[]
  sites : Array (Name × SourceInfo × String) := #[]
  /-- (11s) what the declarations are, and their doc comments -/
  docs : Array (Name × DeclDoc) := #[]
  /-- (13b) names made private, and structures made opaque, with their module -/
  privates : Array (Name × String) := #[]
  opaques : Array (Name × String) := #[]

/-- The command kinds whose effect is just the fields of `Effect`. -/
def cacheable : List Name :=
  ["command.def", "command.axiom", "command.defEqns", "command.inductive", "command.structure",
   "command.class", "command.instance", "command.coinductive", "command.builtin", "command.extern",
   "command.glue", "command.foreignType", "command.cStruct", "command.export", "command.check", "command.reduce", "command.eval",
   "command.erase", "command.run", "command.ir", "command.printAxioms", "command.private"]

def effectOf (s s' : CommandState R) : Effect R :=
  let newNames := s'.globals.order.extract s.globals.order.size s'.globals.order.size
  { decls := newNames.filterMap s'.globals.find?
    messages := s'.messages.extract s.messages.size s'.messages.size
    builtins := s'.builtins.take (s'.builtins.length - s.builtins.length)
    assumed := s'.globals.assumed.take (s'.globals.assumed.length - s.globals.assumed.length)
    classes := s'.classes.take (s'.classes.length - s.classes.length)
    instances := s'.instances.extract s.instances.size s'.instances.size
    coinductives := s'.coinductives.drop s.coinductives.length
    foreignTypes := s'.foreignTypes.take (s'.foreignTypes.length - s.foreignTypes.length)
    cCode := s'.cCode.extract s.cCode.size s'.cCode.size
    infos := s'.infos.extract s.infos.size s'.infos.size
    sites := newNames.filterMap fun n => (s'.declSites.get? n).map fun (i, m) => (n, i, m)
    docs := newNames.filterMap fun n => (s'.declDocs.get? n).map fun d => (n, d)
    privates := newEntries s.globals.privates s'.globals.privates
    opaques := newEntries s.globals.opaques s'.globals.opaques }
where
  newEntries (old new : Std.HashMap Name String) : Array (Name × String) :=
    if old.size == new.size then #[] else
    ((new.fold (init := #[]) fun acc n m => if old.contains n then acc else acc.push (n, m)).qsort
      (fun a b => a.1 < b.1))

/-- Who declared a name, for messages: a module, or the file being checked (`""`). -/
def Effect.whose : Option String → String
  | some "" => "this file"
  | some m => s!"module {m}"
  | none => "an earlier declaration"

/-- Replay an effect. -/
def Effect.apply (e : Effect R) (s : CommandState R) : CommandState R :=
  -- a builtin key is registered once (`command.builtin`); a replayed registration (a
  -- module that was elaborated on its own) must not get around that. (Other keys,
  -- `extern:…`, `repr:…`, `inline`, are per constant.)
  let once (k : Name) : Bool := k == "nat" || k.startsWith "nat." || k == "string" || k == "memo"
  let clash := e.builtins.filter fun (k, n) => once k && (s.globals.builtins.lookup k).any (· != n)
  if let (k, n) :: _ := clash then
    let was := (s.globals.builtins.lookup k).getD "?"
    let text := s!"builtin {k} := {n}: {k} is already registered (as {was}); a builtin can be registered only once"
    { s with messages := s.messages.push { info := {}, severity := .error, text }, pristine := false } else
  -- An effect's declarations were new where it was recorded (a module elaborated on its
  -- own, from its own imports). Replayed into an importer that already has one of the
  -- names, from another module or from the file itself, it would replace that
  -- declaration while keeping everything checked against it: the kernel identifies
  -- constants by name, so a theorem about the old one would hold of the new one
  -- (`wiz-notes/soundness-probes/is-import-shadowing`). The same declaration reached
  -- twice (a diamond) is never replayed twice: a module is imported once per file.
  match e.decls.find? (s.globals.contains ·.name) with
  | some d =>
    let site := e.sites.find? (·.1 == d.name)
    let text := s!"'{d.name}' is declared by both {Effect.whose (s.declSites.get? d.name |>.map (·.2))} and {Effect.whose (site.map (·.2.2))}"
    { s with messages := s.messages.push { info := (site.map (·.2.1)).getD {}, severity := .error, text,
                                           code := "duplicate-declaration" },
             pristine := false }
  | none =>
  -- (the declarations belong to the module being replayed: `Globals.declModule`)
  let globals := e.decls.foldl (·.insert ·) { s.globals with module := s.module }
  let globals := { globals with builtins := e.builtins ++ globals.builtins,
                                assumed := e.assumed ++ globals.assumed,
                                privates := e.privates.foldl (fun m (n, md) => m.insert n md) globals.privates,
                                opaques := e.opaques.foldl (fun m (n, md) => m.insert n md) globals.opaques }
  { s with globals, messages := s.messages ++ e.messages, builtins := e.builtins ++ s.builtins,
           classes := e.classes ++ s.classes, instances := s.instances ++ e.instances,
           coinductives := s.coinductives ++ e.coinductives, foreignTypes := e.foreignTypes ++ s.foreignTypes,
           cCode := s.cCode ++ e.cCode, infos := s.infos ++ e.infos,
           declSites := e.sites.foldl (fun m (n, i, md) => m.insert n (i, md)) s.declSites,
           declDocs := e.docs.foldl (fun m (n, d) => m.insert n d) s.declDocs,
           pristine := false }

def info (i : SourceInfo) : Sx := list [nat i.start, nat i.stop]
def dinfo (x : Sx) : Option SourceInfo := do
  let #[a, b] ← items? x | none
  pure { start := ← (← atom? a).toNat?, stop := ← (← atom? b).toNat? }

/-! ## The info tree -/

def optTerm : Option (Term R) → Sx
  | some t => list [term t]
  | none => list []

def dOptTerm (x : Sx) : Option (Option (Term R)) := do
  match ← items? x with
  | #[t] => some (some (← dterm t))
  | #[] => some none
  | _ => none

def names (ns : List Name) : Sx := list (ns.map str)
def dnames (x : Sx) : Option (List Name) := do (← items? x).toList.mapM atom?
def bool (b : Bool) : Sx := .a (toString b)
def dbool (x : Sx) : Option Bool := do pure ((← atom? x) == "true")

def goalSx (g : GoalView R) : Sx :=
  list [list (g.hyps.toList.map fun (n, t, v) => list [str n, term t, optTerm v]), term g.target,
        names g.userName.toList]

def dGoal (x : Sx) : Option (GoalView R) := do
  let #[hs, t, u] ← items? x | none
  let hyps ← (← items? hs).mapM fun h => do
    let #[n, ty, v] ← items? h | none
    pure (← atom? n, ← dterm ty, ← dOptTerm v)
  pure { hyps, target := ← dterm t, userName := (← dnames u).head? }

def infoSx : Info R → Sx
  | .ident i n l ns t => node "ident" [info i, str n, bool l, names ns, term t]
  | .term i g h => node "term" [info i, goalSx g, bool h]
  | .tactic i b gs gs' => node "tactic" [info i, bool b, list (gs.toList.map goalSx), list (gs'.toList.map goalSx)]
  | .matchCases i m => node "match" [info i, str m.type, names m.covered, bool m.catchAll, nat m.columns,
      info m.firstAlt, info m.lastAlt]
  | .decl i n ns t a at_ => node "decl" [info i, str n, names ns, term t, bool a, nat at_]
  | .unknownIdent i n ns => node "unknown" [info i, str n, names ns]
  | .warning i m => node "warning" [info i, str m]
  | .trace i t => node "trace" [info i, str t]
  | .syntaxRef i (.kind k) => node "syntaxKind" [info i, str k]
  | .syntaxRef i (.cat c) => node "syntaxCat" [info i, str c]
  -- (the expansion is kept as text: a hover only prints it)
  | .expansion i k h e =>
    let handler := match h with
      | .rule site m => list [.a "rule", info site, str m]
      | .fn what f => list [.a "fn", str what, str f]
    node "expansion" [info i, str k, handler, list (e.toList.map (str ·.reprint))]
  | .importMod i m => node "import" [info i, str m]
  | .inst i ns ty t => node "inst" [info i, names ns, term ty, term t]
  | .fix i c d => node "fix" [info i, str c, list (d.map fun (k, vs) => list [str k, names vs])]

def dInfo (x : Sx) : Option (Info R) := do
  let xs ← items? x
  let tag ← atom? (← xs[0]?)
  let a (k : Nat) : Option Sx := xs[k]?
  match tag with
  | "ident" => pure (.ident (← dinfo (← a 1)) (← atom? (← a 2)) (← dbool (← a 3)) (← dnames (← a 4)) (← dterm (← a 5)))
  | "term" => pure (.term (← dinfo (← a 1)) (← dGoal (← a 2)) (← dbool (← a 3)))
  | "tactic" => pure (.tactic (← dinfo (← a 1)) (← dbool (← a 2)) (← (← items? (← a 3)).mapM dGoal)
      (← (← items? (← a 4)).mapM dGoal))
  | "match" =>
    let m := MatchInfo.mk (← atom? (← a 2)) (← dnames (← a 3)) (← dbool (← a 4)) (← (← atom? (← a 5)).toNat?)
      (← dinfo (← a 6)) (← dinfo (← a 7))
    pure (.matchCases (← dinfo (← a 1)) m)
  | "decl" => pure (.decl (← dinfo (← a 1)) (← atom? (← a 2)) (← dnames (← a 3)) (← dterm (← a 4))
      (← dbool (← a 5)) (← (← atom? (← a 6)).toNat?))
  | "unknown" => pure (.unknownIdent (← dinfo (← a 1)) (← atom? (← a 2)) (← dnames (← a 3)))
  | "warning" => pure (.warning (← dinfo (← a 1)) (← atom? (← a 2)))
  | "trace" => pure (.trace (← dinfo (← a 1)) (← atom? (← a 2)))
  | "syntaxKind" => pure (.syntaxRef (← dinfo (← a 1)) (.kind (← atom? (← a 2))))
  | "syntaxCat" => pure (.syntaxRef (← dinfo (← a 1)) (.cat (← atom? (← a 2))))
  | "expansion" =>
    let hs ← items? (← a 3)
    let h ← match ← atom? (← hs[0]?) with
      | "rule" => pure (SyntaxHandler.rule (← dinfo (← hs[1]?)) (← atom? (← hs[2]?)))
      | "fn" => pure (.fn (← atom? (← hs[1]?)) (← atom? (← hs[2]?)))
      | _ => none
    let e ← (← items? (← a 4)).toList.mapM fun x => do pure (Syntax.atom {} (← atom? x))
    pure (.expansion (← dinfo (← a 1)) (← atom? (← a 2)) h e.head?)
  | "import" => pure (.importMod (← dinfo (← a 1)) (← atom? (← a 2)))
  | "inst" => pure (.inst (← dinfo (← a 1)) (← dnames (← a 2)) (← dterm (← a 3)) (← dterm (← a 4)))
  | "fix" =>
    let d ← (← items? (← a 3)).toList.mapM fun kv => do
      let #[k, vs] ← items? kv | none
      pure (← atom? k, ← dnames vs)
    pure (.fix (← dinfo (← a 1)) (← atom? (← a 2)) d)
  | _ => none

def Effect.toSx (e : Effect R) : Sx :=
  let decl (d : Decl R) : Sx := list [str d.name, list (d.levelParams.map str), term d.type,
    (match d.value with | some v => term v | none => .a "none"), .a (toString d.inline),
    (match d.impl with | some v => term v | none => .a "none"),
    (match d.witness with | some v => term v | none => .a "none")]
  let sev : Severity → Sx | .error => .a "error" | .warning => .a "warning" | .info => .a "info"
  let msg (m : Msg) : Sx := list [info m.info, sev m.severity, str m.text, str m.code]
  list [list (e.decls.toList.map decl), list (e.messages.toList.map msg),
    list (e.builtins.map fun (k, n) => list [str k, str n]),
    list (e.assumed.map fun (k, n) => list [str k, str n]),
    list (e.classes.map fun c => list [str c.name, list (c.outParams.map (.a ∘ toString)), list (c.fields.map str)]),
    list (e.instances.toList.map fun i => list [str i.name, str i.cls, nat i.priority]),
    list (e.coinductives.map fun (n, obs) => list [str n, list (obs.map fun (o, b) => list [str o, .a (toString b)])]),
    list (e.foreignTypes.map fun (n, f) => list [str n, str f]),
    list (e.cCode.toList.map str),
    list (e.infos.toList.map infoSx),
    list (e.sites.toList.map fun (n, i, m) => list [str n, info i, str m]),
    list (e.privates.toList.map fun (n, m) => list [str n, str m]),
    list (e.opaques.toList.map fun (n, m) => list [str n, str m]),
    list (e.docs.toList.map fun (n, d) => list [str n, str d.kind, list (d.doc.toList.map str), names d.parent.toList, nat d.start])]

def Effect.ofSx? (x : Sx) : Option (Effect R) := do
  let #[ds, ms, bs, as, cs, is, cos, fts, cc, hs, ss, ps, os, dcs] ← items? x | none
  let decl (x : Sx) : Option (Decl R) := do
    let #[n, ps, ty, v, inl, im, w] ← items? x | none
    pure { name := ← atom? n, levelParams := ← (← items? ps).toList.mapM atom?, type := ← dterm ty,
           value := ← (match v with | .a "none" => some none | v => (dterm v).map some),
           inline := (← atom? inl) == "true",
           impl := ← (match im with | .a "none" => some none | v => (dterm v).map some),
           witness := ← (match w with | .a "none" => some none | v => (dterm v).map some) }
  let msg (x : Sx) : Option Msg := do
    let #[i, sev, t, c] ← items? x | none
    let severity : Severity := match ← atom? sev with
      | "error" => .error | "warning" => .warning | _ => .info
    pure { info := ← dinfo i, severity, text := ← atom? t, code := ← atom? c }
  let pair (x : Sx) : Option (String × String) := do
    let #[a, b] ← items? x | none
    pure (← atom? a, ← atom? b)
  pure {
    decls := (← (← items? ds).mapM decl)
    messages := (← (← items? ms).mapM msg)
    builtins := (← (← items? bs).toList.mapM pair)
    assumed := (← (← items? as).toList.mapM pair)
    classes := (← (← items? cs).toList.mapM fun c => do
      let #[n, os, fs] ← items? c | none
      pure { name := ← atom? n, outParams := ← (← items? os).toList.mapM fun o => do pure ((← atom? o) == "true"),
             fields := ← (← items? fs).toList.mapM atom? })
    instances := (← (← items? is).mapM fun i => do
      let #[n, c, p] ← items? i | none
      pure { name := ← atom? n, cls := ← atom? c, priority := ← (← atom? p).toNat? })
    coinductives := (← (← items? cos).toList.mapM fun c => do
      let #[n, obs] ← items? c | none
      pure (← atom? n, ← (← items? obs).toList.mapM fun o => do
        let #[a, b] ← items? o | none
        pure (← atom? a, (← atom? b) == "true")))
    foreignTypes := (← (← items? fts).toList.mapM pair)
    cCode := (← (← items? cc).mapM atom?)
    infos := (← (← items? hs).mapM dInfo)
    sites := (← (← items? ss).mapM fun x => do
      let #[n, i, m] ← items? x | none
      pure (← atom? n, ← dinfo i, ← atom? m))
    privates := (← (← items? ps).mapM pair)
    opaques := (← (← items? os).mapM pair)
    docs := (← (← items? dcs).mapM fun x => do
      let #[n, k, d, p, st] ← items? x | none
      pure (← atom? n, { kind := ← atom? k, doc := (← (← items? d).toList.mapM atom?).head?,
                         parent := (← dnames p).head?, start := ← (← atom? st).toNat? })) }

/-- The cache's version: change it whenever the format or the elaborator's output changes.
(The directory store also mixes in the binary's own hash, `binaryId`, so two builds of
wiz never share entries; the salt is for invalidating by hand.) -/
def salt : UInt64 := hash "wiz-cache-30-mutual-ctor-names-error-codes-scase-qty-letUnit"  -- 30: a mutual block's constructors are named per type, error codes, `Info.fix`, `scase` quantity (K1), `letUnit`; 20: proof markers (P2: declarations are stored marked); 15: doc comments and declaration kinds (11s); 14: a builtin key is registered once; 13: witnesses, assumed registrations, warnings; 12: private constructors, observations, fields (13b); 11: 22i, marked structure tails; 9: private names (13b); 8: Q4

/-! ## Keys and atomic writes (stage 23c)

A **module's key** is computed from text alone, before anything is elaborated:

    key(M) = hash(salt, toolchain, name and text of M, the C headers M imports, key(N) for M's imports N)

so editing one module invalidates it and the modules that (transitively) import it, and
nothing else. A module is elaborated **in isolation** (from the empty state plus its own
imports), so what it elaborates to depends only on its key; the commands of `M` chain
from `key(M)`, and an importer's chain mixes in `key(M)` at the `import`. -/

/-- Write a file atomically: to a temporary name next to it, then rename (another
process sees the old file, or the whole new one). -/
def writeAtomic (file : System.FilePath) (content : String) : IO Unit := do
  let tmp := file.toString ++ s!".tmp{← IO.Process.getPID}-{← IO.monoNanosNow}"
  IO.FS.writeFile tmp content
  IO.FS.rename tmp file

/-- What identifies the running binary, and so its elaborator and kernel: the hash of the
executable. Hashing it takes a moment, so the result is remembered in `dir/bin/`, by the
executable's path, size and modification time. Without it, a cache directory shared by
several builds (worktrees on different branches, CI runs) would serve one kernel's
verdicts to another whenever a change forgot to bump `salt`. -/
def binaryId (dir : Option System.FilePath) : IO UInt64 := do
  let exe ← IO.appPath
  let md ← exe.metadata
  let stamp := s!"{exe} {md.byteSize} {md.modified.sec} {md.modified.nsec}"
  let file := dir.map (· / "bin" / s!"{hash stamp}")
  if let some f := file then
    if ← f.pathExists then
      match (← IO.FS.readFile f).splitOn "\n" with
      | [st, k] => if st == stamp then if let some n := k.toNat? then return n.toUInt64
      | _ => pure ()
  let h := hash (← IO.FS.readBinFile exe)
  if let some f := file then
    IO.FS.createDirAll (f.parent.getD ".")
    writeAtomic f s!"{stamp}\n{h.toNat}"
  pure h

/-- The key of every module reachable from `ms` (see above). `headers` gives the
preprocessed text of a C header. Import cycles get key 0 on the back edge (the frontend
reports them). A module's `include_str` files enter its key through `includes` (the
resolver `CommandState.includes`; by default every include is an error, which the frontend
reports), so editing an included file invalidates the module and its importers. A module's
trust (`CommandState.trustedModule`: its `builtin` registrations are axioms or not) is part
of its key, and so of its importers' keys: an effect elaborated with one trust status (its
messages, `#print axioms`) is never replayed under the other. -/
partial def moduleKeys (loader : Name → Option String) (headers : String → Option String) (toolchain : UInt64)
    (ms : List Name) (memo : Std.HashMap Name UInt64 := {}) (trusted : Name → Bool := fun _ => false)
    (includes : String → String → Except String String := fun _ rel => .error s!"include_str: no file {rel}") :
    Std.HashMap Name UInt64 :=
  ms.foldl (fun memo m => (go [] m memo).2) memo
where
  go (stack : List Name) (m : Name) (memo : Std.HashMap Name UInt64) : UInt64 × Std.HashMap Name UInt64 :=
    match memo.get? m with
    | some k => (k, memo)
    | none =>
      if stack.contains m then (0, memo) else
      match loader m with
      | none => (0, memo)
      | some src =>
        -- (the name too: what a module elaborates to records it, in the sites of its
        -- declarations and in its private names)
        let k₀ := mixHash (mixHash (mixHash salt toolchain) (hash src)) (hash m)
        let k₀ := if trusted m then mixHash k₀ (hash "trusted") else k₀
        let k₀ := (Module.headersOf src).foldl (fun k h => mixHash k (hash ((headers h).getD ""))) k₀
        -- (include-str) the contents of the files it includes
        let k₀ := mixHash k₀ (Module.includesKey includes m src)
        let (k, memo) := (Module.importsOf src).foldl (fun (k, memo) n =>
          let (kn, memo) := go (m :: stack) n memo
          (mixHash k kn, memo)) (k₀, memo)
        (k, memo.insert m k)

/-- The key of one module. -/
def moduleKey (loader : Name → Option String) (headers : String → Option String) (toolchain : UInt64) (m : Name)
    (trusted : Name → Bool := fun _ => false)
    (includes : String → String → Except String String := fun _ rel => .error s!"include_str: no file {rel}") : UInt64 :=
  ((moduleKeys loader headers toolchain [m] {} trusted includes).get? m).getD 0

/-- How a file's commands are being elaborated. -/
inductive Mode where
  /-- the main file, or a module in isolation: misses are elaborated and written -/
  | write
  /-- a module replayed into an importer's state: misses are elaborated, not written
  (their effect could depend on what the importer imported before) -/
  | replay

/-- Where command effects are kept: a directory (the shared cache), or memory (for one
run without the cache: modules are still elaborated in isolation, so the cache on or off
gives the same results). -/
structure Store (R : Type) where
  get : UInt64 → IO (Option (Effect R))
  put : UInt64 → Effect R → IO Unit
  /-- has module `k` been elaborated in isolation? -/
  seen : UInt64 → IO Bool
  markSeen : UInt64 → Name → IO Unit

/-- The store in directory `dir`, for the binary `binary` (`binaryId`): its files are
named by the key mixed with the binary, so another build of wiz finds none of them. -/
def Store.disk (dir : System.FilePath) (binary : UInt64) : IO (Store R) := do
  IO.FS.createDirAll dir
  let name (k : UInt64) := toString (mixHash binary k)
  pure {
    get := fun k => do
      let file := dir / s!"{name k}.wizc"
      if ← file.pathExists then pure ((Sx.parse (← IO.FS.readFile file)).bind Effect.ofSx?) else pure none
    put := fun k e => writeAtomic (dir / s!"{name k}.wizc") e.toSx.render
    seen := fun k => (dir / s!"{name k}.wizm").pathExists
    markSeen := fun k m => writeAtomic (dir / s!"{name k}.wizm") m }

def Store.memory : IO (Store R) := do
  let effects ← IO.mkRef ({} : Std.HashMap UInt64 (Effect R))
  let seen ← IO.mkRef ({} : Std.HashSet UInt64)
  pure {
    get := fun k => return (← effects.get)[k]?
    put := fun k e => effects.modify (·.insert k e)
    seen := fun k => return (← seen.get).contains k
    markSeen := fun k _ => seen.modify (·.insert k) }

/-- (28) The solver settings, as a key, when they are not the defaults (none: nothing to
mix in, so the keys of every run without them stay as they were). -/
def smtKey (c : Smt.Config) : Option UInt64 :=
  let c := { c with cacheDir := none }
  if c == {} then none else some (mixHash (hash "smt") (hash c))

/-- Elaborate `input` (like `Query.elaborate`), reading and writing `store`. Returns the
final state and how many commands came from the store. `key₀` identifies what the
file can see besides its imports (for example its C headers); `toolchain` is mixed into
every module's key. -/
partial def elaborateWith (store : Store R) (input : String) (init : CommandState R) (key₀ : UInt64)
    (toolchain : UInt64 := 0) : IO (CommandState R × Nat) := do
  let keys ← IO.mkRef ({} : Std.HashMap Name UInt64)
  -- recording every term's expected type changes the effects: a different chain
  let salt' := if init.termInfo then mixHash salt 1 else salt
  -- (27a) so does `--trust-native` (and its fuel): a `native_refl` accepted with it is
  -- never replayed without it, nor the error without it replayed with it. (What it ran is
  -- already in the key: the binary, and the text of the file and of everything imported.)
  let salt' := if init.trustNative then mixHash salt' (nativeKey init) else salt'
  -- (28) and the solver settings (`--sat-solver`, `--solver-timeout`)
  let salt' := match smtKey init.smt with | some k => mixHash salt' k | none => salt'
  -- (include-str) the main file's included files enter its chain before its first command
  let includes := init.includes.getD (fun _ rel => .error s!"include_str: no file {rel}")
  let key₀ := mixHash (Module.includesKey includes "" input) key₀
  go keys init [] input init (mixHash salt' (mixHash toolchain key₀)) .write
where
  nativeKey (s : CommandState R) : UInt64 := mixHash (hash "trust-native") (hash s.nativeFuel)
  keyOf (keys : IO.Ref (Std.HashMap Name UInt64)) (m : Name) : IO UInt64 := do
    -- (term info changes what a module elaborates to, like the main file's chain)
    let tc := if init.termInfo then mixHash toolchain 1 else toolchain
    let tc := if init.trustNative then mixHash tc (nativeKey init) else tc
    let tc := match smtKey init.smt with | some k => mixHash tc k | none => tc
    let includes := init.includes.getD (fun _ rel => .error s!"include_str: no file {rel}")
    let memo := moduleKeys init.loader init.cHeaders tc [m] (← keys.get) init.trustedModule includes
    keys.set memo
    pure ((memo.get? m).getD 0)
  /-- Bring module `m` into `s`: elaborate it in isolation first if the cache has not
  seen it, then replay it from the cache. -/
  importModule (keys : IO.Ref (Std.HashMap Name UInt64)) (base : CommandState R) (stack : List Name)
      (s : CommandState R) (m : Name) (src : String) : IO (CommandState R × Nat) := do
    let k ← keyOf keys m
    let fresh ← if ← store.seen k then pure none else do
      let (_, h) ← go keys base (m :: stack) src { base with imported := [m], messages := #[], module := m } k .write
      store.markSeen k m
      pure (some h)
    let (s', h) ← go keys base (m :: stack) src { s with imported := m :: s.imported, messages := #[], module := m } k .replay
    -- after a fresh isolated run, the hits are that run's (the replay reads what it wrote)
    pure (s', fresh.getD h)
  go (keys : IO.Ref (Std.HashMap Name UInt64)) (base : CommandState R) (stack : List Name) (input : String)
      (s₀ : CommandState R) (key₀ : UInt64) (mode : Mode) : IO (CommandState R × Nat) := do
    let chars := input.toList.toArray
    let mut pos := 0
    let mut s := s₀
    let mut key := key₀
    let _ : Inhabited (CommandState R) := ⟨init⟩
    let mut hits := 0
    while skipWs chars pos < chars.size do
      match parseCommand chars s.tables pos with
      | .error _ =>
        -- report the parse error (and everything after it) without the cache
        s := runFrontend.go input base chars pos s
        break
      | .ok (cmd, stop) =>
        let text := String.ofList (chars.extract pos stop).toList
        key := mixHash key (hash text)
        if cmd.isOfKind "command.import" then
          let m := ((cmd.getArg 1).getId?).getD "_"
          -- what the rest of the file sees depends on the module's text, through its key
          key := mixHash key (← keyOf keys m)
          if stack.contains m then
            s := { s with messages := s.messages.push { info := cmd.info, severity := .error, text := s!"import cycle through {m}", code := ErrorCode.importCycle } }
          else if !s.imported.contains m then
            match s.loader m with
            | none => s := { s with messages := s.messages.push { info := cmd.info, severity := .error, text := s!"unknown module {m}", code := ErrorCode.unknownModule } }
            | some src =>
              let (inner, h) ← importModule keys base stack s m src
              hits := hits + h
              let errs := inner.messages.filter (·.severity == .error)
              let msg : Msg := { info := cmd.info, severity := .error, code := ErrorCode.moduleErrors,
                                 text := importErrorsText m src errs }
              -- (a module's warnings, such as an unchecked `builtin`, are shown at the import)
              let warns := (inner.messages.filter (·.severity == .warning)).map fun w =>
                ({ info := cmd.info, severity := .warning, text := s!"module {m}: {w.render src}" } : Msg)
              -- (13m) the module's `local` notation stays in it
              let inner := inner.endModule s
              -- a module that would replace a declaration this file already has (from
              -- another module, or its own) is not brought in at all: the rest of its
              -- commands were checked against its own declaration, not this file's
              if errs.any (·.code == "duplicate-declaration") then
                -- (the code goes up with it: an importer of an importer is dropped too)
                let dup := (errs.find? (·.code == "duplicate-declaration")).map (·.text) |>.getD msg.text
                s := { s with messages := s.messages.push { msg with text := dup, code := "duplicate-declaration" } ++ warns,
                              imported := m :: s.imported, pristine := false }
                -- in a module, that is the end of it: its later commands were checked
                -- (and their effects cached) with `m` imported, and replayed without it
                -- they would refer to declarations that aren't there, or to the other
                -- module's (the macro interpreter then ran a deriver of lib/Deriving.wiz
                -- with lib/Text.wiz dropped, and panicked). The importer drops the module.
                unless stack.isEmpty do break
              else
              s := { inner with messages := (if errs.isEmpty then s.messages else s.messages.push msg) ++ warns,
                                module := s.module, infos := s.infos }
          pos := stop
          continue
        let cached : Option (Effect R) ←
          if cacheable.contains cmd.kind then store.get key else pure none
        match cached with
        | some e =>
          s := e.apply s
          hits := hits + 1
        | none =>
          let s' := Query.elaborate.elabOne input base chars pos stop s
          if cacheable.contains cmd.kind && mode matches .write then
            store.put key (effectOf s s')
          s := s'
        pos := stop
    pure (s, hits)

/-- `elaborateWith`, through the cache directory `dir`, as this binary (`binaryId`) unless
`binary` says otherwise (tests). -/
def elaborateCached (dir : System.FilePath) (input : String) (init : CommandState R) (key₀ : UInt64)
    (toolchain : UInt64 := 0) (binary : Option UInt64 := none) : IO (CommandState R × Nat) := do
  let binary ← match binary with | some b => pure b | none => binaryId (some dir)
  elaborateWith (← Store.disk dir binary) input init key₀ toolchain

/-- `elaborateWith`, without a cache: modules are elaborated in isolation all the same. -/
def elaborateUncached (input : String) (init : CommandState R) (toolchain : UInt64 := 0) : IO (CommandState R) := do
  pure (← elaborateWith (← Store.memory) input init 0 toolchain).1

end Wiz.Cache
