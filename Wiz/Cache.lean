import Lean.CompactedRegion
import Std.Time.DateTime.Timestamp
import Wiz.Query
import Wiz.Module
import Wiz.Smt.Sha256

/-!
# The shared cache

The query engine's memo table, on disk: a command's **effect** (the declarations it
adds, its messages, and its registrations) is stored in `<cache dir>/<key>.wizc` (`wiz --cache DIR`), where
the key is the chained content hash of the command and everything before it (and a
version salt). The 64-bit half is an index; a SHA-256 key (domain-separated and
length-framed) names regions and manifests, so a collision cannot select another input's
effect. Elaboration is deterministic, so a shared directory is a shared cache: two
machines elaborating the same text compute the same keys and the same effects.

Any number of directories may also be **read-only caches** (`wiz --cache-ro DIR`, in
order): misses are looked up there after the write cache, and they are never written. A
Nix package ships one in `$out/share/wiz/cache`; a run with only read caches
(`--no-cache --cache-ro DIR`, since the default write cache is on) still replays modules
and computes the binary's id on every run.

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
def nat (n : Nat) : Sx := .a (NatString.decimalString n)
def str (s : String) : Sx := .a s
def list (xs : List Sx) : Sx := .l xs.toArray

partial def level : Level → Sx
  | .zero => .a "0"
  | .succ l => node "S" [level l]
  | .max a b => node "max" [level a, level b]
  | .imax a b => node "imax" [level a, level b]
  | .param n => node "p" [str n]
  | .mvar m => node "m" [nat m]
  | .hole => .a "_"

def bi : BinderInfo → Sx
  | .default => .a "d" | .implicit => .a "i" | .instImplicit => .a "I"

partial def term : Term R → Sx
  | .var i => node "var" [nat i]
  | .const n us => node "const" [str n, list (us.map level)]
  | .sort l => node "sort" [level l]
  | .pi x b q A B s => node "pi" [str x, bi b, term q, term A, term B, level s.dom, level s.cod]
  | .lam x b => node "lam" [str x, term b]
  | .app f a => node "app" [term f, term a]
  | .letE x q t v b => node "let" [str x, term q, term t, term v, term b]
  | .ann t ty => node "ann" [term t, term ty]
  | .mvar m => node "mvar" [nat m]
  | .sigma x q a b s => node "sigma" [str x, term q, term a, term b, level s.dom, level s.cod]
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
  | .mu l I D i s h prop => node "mu" [level l, term I, term D, term i, term s, hint h, .a (toString prop)]
  | .con x => node "con" [term x]
  | .ind l I D v P m i x prop => node "ind" [level l, term I, term D, level v, term P, term m, term i, term x, .a (toString prop)]
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
  | .ulift k l A => node "ulift" [level k, level l, term A]
  | .up a => node "up" [term a]
  | .down t => node "down" [term t]
  | .prf l t => node "prf" [level l, term t]
where
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
  | .a "_" => some .hole
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
    let n (i : Nat) : Option Nat := (s i).bind NatString.ofDecimalDigits?
    let lv (i : Nat) : Option Level := dlevel (x i)
    let ts (i : Nat) : Option (List (Term R)) := do (← items? (x i)).toList.mapM dterm
    let ss (i : Nat) : Option (List String) := do (← items? (x i)).toList.mapM atom?
    let hint (i : Nat) : Option (Option (Name × List Level × List (Term R))) :=
      match x i with
      | .a "none" => some none
      | .l #[.a "hint", .a nm, us, as] => do
        some (some (nm, ← (← items? us).toList.mapM dlevel, ← (← items? as).toList.mapM dterm))
      | _ => none
    let sorts (i : Nat) : Option BinderSorts := return ⟨← lv i, ← lv (i + 1)⟩
    let b (i : Nat) : Option Bool := (s i).map (· == "true")
    match tag with
    | "var" => return .var (← n 1)
    | "const" => return .const (← s 1) (← (← items? (x 2)).toList.mapM dlevel)
    | "sort" => return .sort (← lv 1)
    | "pi" => return .pi (← s 1) (← dbi (x 2)) (← t 3) (← t 4) (← t 5) (← sorts 6)
    | "lam" => return .lam (← s 1) (← t 2)
    | "app" => return .app (← t 1) (← t 2)
    | "let" => return .letE (← s 1) (← t 2) (← t 3) (← t 4) (← t 5)
    | "ann" => return .ann (← t 1) (← t 2)
    | "mvar" => return .mvar (← n 1)
    | "sigma" => return .sigma (← s 1) (← t 2) (← t 3) (← t 4) (← sorts 5)
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
    | "mu" => return .mu (← lv 1) (← t 2) (← t 3) (← t 4) (← t 5) (← hint 6) (← b 7)
    | "con" => return .con (← t 1)
    | "ind" => return .ind (← lv 1) (← t 2) (← t 3) (← lv 4) (← t 5) (← t 6) (← t 7) (← t 8) (← b 9)
    | "nu" => return .nu (← lv 1) (← t 2) (← t 3) (← t 4) (← t 5) (← hint 6)
    | "out" => return .out (← t 1)
    | "szSuc" => return .szSuc (← t 1)
    | "sizeLt" => return .sizeLt (← t 1)
    | "sfix" => return .sfix (← lv 1) (← t 2) (← t 3) (← lv 4) (← t 5) (← t 6) (← t 7) (← t 8) (← t 9)
    | "scase" => return .scase (← lv 1) (← t 2) (← t 3) (← t 4) (← lv 5) (← t 6) (← t 7) (← t 8) (← t 9) (← t 10)
    | "cocon" => return .cocon (← t 1)
    | "ulift" => return .ulift (← lv 1) (← lv 2) (← t 3)
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
   "command.plot", "command.anim", "command.animate", "command.erase", "command.run", "command.ir", "command.printAxioms", "command.private"]

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
def salt : UInt64 := hash "wiz-cache-31-deterministic-macro-scopes"  -- 31: macro scopes start at the command's source position (a cache hit no longer shifts them); 30: mandatory component sorts (Π/Σ carry ⟨dom, cod⟩, ULift its content's sort), a mutual block's constructors named per type, error codes, `Info.fix`, `scase` quantity (K1), `letUnit`; 20: proof markers (P2: declarations are stored marked); 15: doc comments and declaration kinds (11s); 14: a builtin key is registered once; 13: witnesses, assumed registrations, warnings; 12: private constructors, observations, fields (13b); 11: 22i, marked structure tails; 9: private names (13b); 8: Q4

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

/-- Remove `file` if it exists, ignoring errors (a pure cache never fails a run). -/
def removeQuietly (file : System.FilePath) : IO Unit :=
  try IO.FS.removeFile file catch _ => pure ()

/-- What identifies the running binary, and so its elaborator and kernel: the hash of the
executable. Hashing it takes a moment, so the result is remembered in `dir/bin/`, by the
executable's path, size and modification time. Without it, a cache directory shared by
several builds (worktrees on different branches, CI runs) would serve one kernel's
verdicts to another whenever a change forgot to bump `salt`. `dir` is the **write** cache:
with none (read-only caches only), the executable is hashed on every run and nothing is
written. -/
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

/-- A cache key has a fast 64-bit index (for in-memory tables, file lookups and Lean's
`HashMap`) and a **strong** SHA-256 content key (for manifests, regions and anything that
crosses a trust boundary). The fast half is not a security digest; the strong half is
domain-separated and length-framed, so two differently-shaped inputs cannot share a
preimage. `toolchain` and `target` are the strong namespaces (`Toolchain.tag` and
`Toolchain.targetTag`); they are kept out of `fast`, which stays exactly the old key. -/
structure Key where
  fast : UInt64 := 0
  /-- the SHA-256 content key (empty: a legacy fast-only key) -/
  strong : String := ""
  /-- the strong toolchain namespace (`Toolchain.tag`) -/
  toolchain : String := ""
  /-- the strong target namespace (`Toolchain.targetTag`) -/
  target : String := ""
  /-- SHA-256 of the running executable (`toolchainTag`) -/
  binary : String := ""
  deriving Repr, Inhabited, BEq

namespace Key

def ofFast (k : UInt64) : Key := { fast := k }

/-- One key's identity in a set or map keyed by both halves. (The fast half alone is not
enough: two colliding inputs are different keys.) -/
def id (k : Key) : String :=
  if k.strong.isEmpty then toString k.fast else s!"{k.fast}:{k.strong}"

/-- Chain one command's text into a key. The fast half is the old `mixHash`; the strong
half hashes the previous strong key and the exact text under a command domain. -/
def mixText (k : Key) (text : String) : Key :=
  { k with fast := mixHash k.fast (hash text),
           strong := Smt.Sha256.hexFramed "wiz-cache/command-v1" [k.strong, text] }

/-- Chain an imported module's key into the importer's key. -/
def mixKey (a b : Key) : Key :=
  { a with fast := mixHash a.fast b.fast,
           strong := Smt.Sha256.hexFramed "wiz-cache/import-v1" [a.strong, b.strong] }

/-- Mix arbitrary extra inputs (a file's `link_c` table, solver settings) into a key with
an explicit domain. -/
def mixDomain (k : Key) (domain : String) (fields : List String) : Key :=
  { k with strong := Smt.Sha256.hexFramed domain (k.strong :: fields) }

end Key

instance : Coe UInt64 Key := ⟨Key.ofFast⟩

/-- The strong toolchain namespace with the elaboration options that change what a module
means (`--term-info`, `--trust-native`/fuel, solver settings). The fast module key already
mixes the same options; this is the SHA-256 version, so an option change cannot select a
manifest or region by a 64-bit collision. -/
def toolchainOptionsTag (strongToolchain : String) (termInfo trustNative : Bool)
    (nativeFuel : Nat) (smt : Option UInt64) : String :=
  Smt.Sha256.hexFramed "wiz-cache/toolchain-options-v1"
    [strongToolchain, toString termInfo, toString trustNative, toString nativeFuel,
     match smt with | some k => toString k | none => ""]

/-- The strong version of `Module.includesKey`: the contents (or error) of every
`include_str` file of `src` under the `wiz-cache/include-v1` domain. Editing an included
file changes this digest, and so the strong module key as well as the fast one. -/
def includesKeyStrong (includes : String → String → Except String String)
    (m : Name) (src : String) : String :=
  Smt.Sha256.hexFramed "wiz-cache/include-v1"
    ((Module.includesOf src).map fun rel =>
      let body := match includes m rel with
        | .ok text => "ok\x00" ++ text
        | .error e => "error\x00" ++ e
      s!"include:{rel}:" ++ body)

/-- The key of every module reachable from `ms`, alongside its fast key. `headers` gives
the preprocessed text of a C header. Import cycles get the fast key 0 on the back edge (the
frontend reports them). A module's `include_str` files enter its key through `includes`
(the resolver `CommandState.includes`; by default every include is an error, which the
frontend reports), so editing an included file invalidates the module and its importers. A
module's trust (`CommandState.trustedModule`) is part of both halves, and so of its
importers' keys. -/
partial def moduleKeysAll (loader : Name → Option String) (headers : String → Option String)
    (toolchain : UInt64) (strongToolchain : String := "") (targetTag : String := "")
    (ms : List Name) (memo : Std.HashMap Name Key := {}) (trusted : Name → Bool := fun _ => false)
    (includes : String → String → Except String String := fun _ rel => .error s!"include_str: no file {rel}") :
    Std.HashMap Name Key :=
  ms.foldl (fun memo m => (go [] m memo).2) memo
where
  go (stack : List Name) (m : Name) (memo : Std.HashMap Name Key) : Key × Std.HashMap Name Key :=
    match memo.get? m with
    | some k => (k, memo)
    | none =>
      if stack.contains m then (Key.ofFast 0, memo) else
      match loader m with
      | none => (Key.ofFast 0, memo)
      | some src =>
        -- (the name too: what a module elaborates to records it, in the sites of its
        -- declarations and in its private names)
        let k₀ := mixHash (mixHash (mixHash salt toolchain) (hash src)) (hash m)
        let k₀ := if trusted m then mixHash k₀ (hash "trusted") else k₀
        let k₀ := (Module.headersOf src).foldl (fun k h => mixHash k (hash ((headers h).getD ""))) k₀
        -- (include-str) the contents of the files it includes (fast half unchanged)
        let k₀ := mixHash k₀ (Module.includesKey includes m src)
        -- (the strong half hashes the exact fields, each length-framed: not the 64-bit
        -- hashes above, and not a concatenation that can be ambiguous)
        let headerFields := (Module.headersOf src).flatMap fun h => [s!"header:{h}", (headers h).getD ""]
        let k₀ : Key :=
          { fast := k₀
            strong := Smt.Sha256.hexFramed "wiz-cache/module-v1"
              ([s!"salt:{salt}", s!"toolchain:{toolchain}", s!"toolchain-tag:{strongToolchain}",
                s!"target-tag:{targetTag}", s!"module:{m}", s!"trusted:{trusted m}", "source", src,
                s!"includes:{includesKeyStrong includes m src}"] ++ headerFields)
            toolchain := strongToolchain, target := targetTag }
        let (k, memo) := (Module.importsOf src).foldl (fun (k, memo) n =>
          let (kn, memo) := go (m :: stack) n memo
          (k.mixKey kn, memo)) (k₀, memo)
        (k, memo.insert m k)

/-- The key of every module reachable from `ms` (see above), as the fast 64-bit map used by
in-memory tables and the old file names. -/
def moduleKeys (loader : Name → Option String) (headers : String → Option String) (toolchain : UInt64)
    (ms : List Name) (memo : Std.HashMap Name UInt64 := {}) (trusted : Name → Bool := fun _ => false)
    (includes : String → String → Except String String := fun _ rel => .error s!"include_str: no file {rel}") :
    Std.HashMap Name UInt64 :=
  let start := memo.toList.foldl (fun acc (n, k) => acc.insert n (Key.ofFast k)) {}
  (moduleKeysAll loader headers toolchain "" "" ms start trusted includes).toList.foldl
    (fun acc (n, k) => acc.insert n k.fast) {}

/-- The key of one module. -/
def moduleKey (loader : Name → Option String) (headers : String → Option String) (toolchain : UInt64) (m : Name)
    (trusted : Name → Bool := fun _ => false)
    (includes : String → String → Except String String := fun _ rel => .error s!"include_str: no file {rel}") : UInt64 :=
  ((moduleKeys loader headers toolchain [m] {} trusted includes).get? m).getD 0

/-- The SHA-256 key of one module (the content key in manifests and region names). -/
def moduleKeyStrong (loader : Name → Option String) (headers : String → Option String) (toolchain : UInt64)
    (m : Name) (trusted : Name → Bool := fun _ => false)
    (strongToolchain : String := "") (targetTag : String := "")
    (includes : String → String → Except String String := fun _ rel => .error s!"include_str: no file {rel}") : String :=
  ((moduleKeysAll loader headers toolchain strongToolchain targetTag [m] {} trusted includes).get? m)
    |>.map (·.strong) |>.getD ""

/-- How a file's commands are being elaborated. -/
inductive Mode where
  /-- the main file, or a module in isolation: misses are elaborated and written -/
  | write
  /-- a module replayed into an importer's state: misses are elaborated, not written
  (their effect could depend on what the importer imported before) -/
  | replay

/-! ## Module regions (`--region-cache`)

Lean's `.olean` files are *compacted regions*: a byte image of a module's terms, saved at a
base address derived from the module name, and read back with `mmap`
(`Lean.CompactedRegion`). A Wiz `.wizc` entry is S-expression text, decoded and reallocated
on every hit. A module's effects are plain data (no closures), so they can be saved as a
region too: **one artifact per module**, `<cache>/<fast key>.<SHA-256 key>.wizr`, holding
every cacheable command's `Effect` in command order. `--region-cache` serves those effects
from the mapped region; the text entries stay in place, are the authority, and are the
fallback.

`CompactedRegion.read` does not check the type it loads (`α` is erased at the boundary), so a
file is guarded by its name (this binary's hash, the module's fast key and its SHA-256 key),
Lean's `.olean` header (magic and version), the payload's `magic`, `format`, `binary`,
`binarySha`, `salt`, `rig`, `key`, `keySha`, `toolchainSha` and `targetSha`, and — format 3
— a **payload checksum**: a `.wizs` sidecar holds the 8-byte hash of the whole image
(`checksumFile`: one read, a 64-bit hash), checked before the image is mapped, so a
same-size bit flip (even one that would corrupt a pointer) is a miss and never reaches the
type-erased reader. The checksum catches corruption; the SHA-256 fields catch a name
collision and a cross-toolchain/target swap (the 64-bit name is only an index). The check is
one read and a `ByteArray.hash` pass, not a decode: a millisecond or two for a multi-MB
region. Never content-address a region by its bytes: they are pointers, and not canonical.
Bump `regionFormat` whenever `Effect`, `Decl`, `Term` or `Info` change shape, or the file
framing changes; the format is disposable, never migrated.

The artifact is a *projection*: `CommandState`/`Globals` carry closures (`loader`,
`trustedModule`, `pp.run`, `metaCode`, `Budget.ref`) that the compactor refuses. Loading
applies the effects to the live state with `Effect.apply`, so those fields stay live; the
regions themselves are kept for the process lifetime (mapped objects have no reference
counts: a state must not outlive the region it was built from). -/

/-- Format of a `.wizr` file: bump it when `Effect`, `Decl`, `Term` or `Info` change shape
(`salt` covers the same ground for the text entries), and when the file's framing changes.
1: a bare `Lean.CompactedRegion` image. 2: the image and, beside it, a `.wizs` sidecar
holding the image's 8-byte little-endian hash (`regionSumFile`). 3: the SHA-256 content,
toolchain and target keys, and the strong key in the file name. A file of the wrong format
(or without its sidecar) is a miss, never migrated (`RegionStore.layered`: the write cache
drops and rewrites it, a read-only cache keeps it). Old format-2 files are ignored by their
old names too, so an old cache is a clean miss and regenerates with the new key. -/
def regionFormat : Nat := 3

/-- `"wizreg03"` (format 3): checked after a region is read (Lean's header is the first
line). A format-2 file ("wizreg02") has no SHA-256 key fields and fails `fits`. -/
def regionMagic : UInt64 := 0x77697A7265673033

/-- What one module contributes to an importer, as pure data. -/
structure ModuleArtifact (R : Type) where
  /-- `regionMagic`, checked after the read -/
  magic : UInt64 := regionMagic
  /-- `regionFormat` -/
  format : Nat := regionFormat
  /-- the `wiz` binary that wrote it (`binaryId`; the file name has it too) -/
  binary : UInt64 := 0
  /-- SHA-256 of the executable (a strong binary identity) -/
  binarySha : String := ""
  /-- the text format's `salt`, in case the file name is reused -/
  textSalt : UInt64 := 0
  /-- the rig the effects were elaborated for (`RigTag.tag`) -/
  rig : String := ""
  /-- the module these effects belong to -/
  module : Name := ""
  /-- the module key (`moduleKey`: text, headers and imports) -/
  key : UInt64 := 0
  /-- the strong module key (`moduleKeyStrong`) -/
  keySha : String := ""
  /-- the strong toolchain namespace (`Toolchain.tag`) -/
  toolchainSha : String := ""
  /-- the strong target namespace (`Toolchain.targetTag`) -/
  targetSha : String := ""
  /-- every cacheable command's effect, in command order (`Effect.apply` in order) -/
  effects : Array (Effect R) := #[]
  /-- the chained key at each of those commands, in the same order: a replay checks its
  own parsed text's keys against these, so a command loop that parses differently (an
  importer's extra syntax) falls back to the text instead of taking the wrong effect -/
  keys : Array UInt64 := #[]
  /-- every command was cacheable: no `import`/`syntax`/`macro` needs rerunning, so a
  loader may skip the per-command loop (commit 3; the writer records it, the reader does
  not act on it yet) -/
  complete : Bool := false
  /-- the source ranges of the commands that are not cacheable, for the rerun path
  (commit 3) -/
  rerun : Array (Nat × Nat) := #[]

/-- Does this artifact belong to module `key` of `binary`, under `rig`, for this strong
toolchain/target namespace? The 64-bit `key` is only the index; the SHA-256 fields are the
identity. A legacy fast-only key (`strong = ""`) accepts the old tags, but new writers
always fill them. -/
def ModuleArtifact.fits (a : ModuleArtifact R) (binary : UInt64) (key : Key) (rig : String) : Bool :=
  a.magic == regionMagic && a.format == regionFormat && a.binary == binary &&
  a.textSalt == salt && a.rig == rig && a.key == key.fast &&
  (key.strong.isEmpty || a.keySha == key.strong) &&
  (key.toolchain.isEmpty || a.toolchainSha == key.toolchain) &&
  (key.target.isEmpty || a.targetSha == key.target) &&
  (key.binary.isEmpty || a.binarySha == key.binary)

/-- What `--region-stats` reports. -/
structure RegionCounts where
  -- (so `IO.mkRef {}` works)
  /-- module lookups that found a usable region -/
  hits : Nat := 0
  /-- module lookups that found none (cold, missing, corrupt or mistagged): the text cache
  answered, and a new region was written -/
  misses : Nat := 0
  /-- command effects that came from a region -/
  commands : Nat := 0
  deriving Inhabited, Repr

/-- `--region-cache`'s settings. -/
structure RegionOptions where
  /-- the rig the effects were elaborated for (`RigTag.tag (R := R)`) -/
  rig : String
  /-- where to count hits and misses, for `--region-stats` and tests -/
  stats : Option (IO.Ref RegionCounts) := none

/-- The `.wizr` file for module `key` as `binary`. The fast half keeps the old shape; a
key with a strong half adds it to the name, so two colliding fast keys never share a region
file (and an old fast-only file is a miss, never read under the new key). -/
def regionFileName (binary : UInt64) (key : Key) : String :=
  if key.strong.isEmpty then s!"{mixHash binary key.fast}.wizr"
  else s!"{mixHash binary key.fast}-{key.strong}.wizr"

/-! ## Output manifests (`--cache-verify`)

A cache key is an **input** hash; the bytes a cache entry returns are an **output**. Until
this stage nothing checked the output against the key: a cache could return any parseable
`Effect`, and a `.wizr` region is worse (its type is erased at the `mmap` boundary). The
first integrity step is a digest of the bytes that are served, plus a **manifest** that
binds a key to that digest. There is no signature yet: a manifest catches corruption, a
truncated/rewritten file and a mirror that swaps one entry for another; it does not stop a
writer who controls the manifest too (that needs P3's signatures and, eventually, the
append-only log).

The layout is deliberately the note's **P2** (per-module manifests) with a **P1**
per-layer generation index:

```
<cache>/manifest.d/<binary ⊕ module key>.wizmf   -- one module (or one root file)
<cache>/manifest.sexpr                            -- the layer's generation index
```

A module manifest lists every cacheable command entry of that module and its region, with
both the fast index and the SHA-256 input key:

```lisp
(module-manifest
  (format 2) (module "Data.Two") (key "1234") (key-sha "…") (binary "99")
  (toolchain "sha256:…") (toolchain-tag "…") (target-tag "…") (rig "zero-one-many")
  (region (entry (kind wizr) (key "1234") (key-sha "…") (file "5678-….wizr")
                 (size 123) (sha256 "…") (format 3)))
  (entries ((entry (kind wizc) (key "1235") (key-sha "…") (file "5679.wizc")
                   (size 77) (sha256 "…") (format 1)) …))
  (root "sha256:…"))
```

The `key` is a fast index; `key-sha` is the SHA-256 key of the exact inputs (command text
and its chain, or module text/headers/imports plus the toolchain/target namespaces). The
manifest file name includes `key-sha`, and a lookup requires both halves, so a 64-bit
collision is a miss, never another command's effect. A format-1 manifest (or a format-2
region) is a miss and is regenerated; it is never read under a strong key.

`root` is an RFC 6962-style Merkle root over the entries (`0x00` leaf, `0x01` node
separation), so P3 can sign one value instead of every entry. `.wizc` bytes are canonical
text, so their digest is the effect digest too; a `.wizr` is a pointer image and is **not**
canonical, so only its byte digest is recorded (never content-address a region by bytes).

The policy is `--cache-verify MODE`:

* `off` — no manifests are written or read; the cache is byte-identical to the old one.
* `warn` (the default) — if a manifest exists, every key it lists is served only after its
  bytes match; a mismatch is a miss (the text path/elaboration answers). A new key has a
  SHA-256 half, so a write-cache entry no manifest lists is a miss too: nothing else binds
  its bytes to the strong input key (an old fast-only key still falls through, and
  `--cache-verify off` restores the old unverified lookup). An old local cache is one cold
  pass, then it is rewritten with manifests.
* `strict` (alias `require`) — only manifested entries are used anywhere. Manifests are
  written to the write cache (never to a `--cache-ro` layer), so a cold run becomes
  strict-warm after one pass.

A bad manifest disables the entries it names (they miss); an absent manifest in `warn` is
the compatibility default. Verification runs at the file boundary (`Store.get`,
`RegionStore.get`) and costs one digest of the bytes being read anyway; it never scans the
whole cache, and never repairs a read-only layer. `regionFormat` 2's `.wizs` sidecar is
still checked first, so a corrupt region never reaches the type-erased reader even when a
manifest is absent. -/

/-- `--cache-verify`'s policy (`require` is accepted as a synonym of `strict`). -/
inductive VerifyMode where
  | off
  /-- verify when a manifest exists; an unlisted key keeps the old lookup (default) -/
  | warn
  /-- only manifested entries are used; an unlisted key is a miss -/
  | strict
  deriving Repr, Inhabited, BEq, DecidableEq

def VerifyMode.ofString? : String → Option VerifyMode
  | "off" => some .off
  | "warn" => some .warn
  | "strict" | "require" => some .strict
  | _ => none

def VerifyMode.render : VerifyMode → String
  | .off => "off" | .warn => "warn" | .strict => "strict"

/-- One manifest entry: the bytes of one artifact and where they live. -/
structure ManifestEntry where
  /-- `wizc` (a command's effect text) or `wizr` (a module's region) -/
  kind : String := "wizc"
  /-- the command key (`.wizc`) or module key (`.wizr`); a fast index -/
  key : UInt64 := 0
  /-- the SHA-256 key of what the entry answers (the strong half; never the file name) -/
  keySha : String := ""
  /-- the file name inside the layer (no path components) -/
  file : String := ""
  size : Nat := 0
  /-- SHA-256 of the file's bytes -/
  sha256 : String := ""
  /-- `salt` for a `.wizc`, `regionFormat` for a `.wizr` -/
  format : Nat := 0
  deriving Repr, Inhabited, BEq

def ManifestEntry.toSx (e : ManifestEntry) : Sx :=
  node "entry" [node "kind" [str e.kind], node "key" [str (toString e.key)],
    node "key-sha" [str e.keySha],
    node "file" [str e.file], node "size" [nat e.size],
    node "sha256" [str e.sha256], node "format" [nat e.format]]

/-- The field named `tag` in the S-expression `x`, if it is an S-expression. -/
def sxField? (tag : String) (x : Sx) : Option Sx := do
  let xs ← items? x
  let y ← xs.find? (fun y => match items? y with
    | some ys => match ys.toList with
      | .a t :: _ => t == tag
      | _ => false
    | none => false)
  let ys ← items? y
  match ys[1]? with
  | some a => pure a
  | none => none

def ManifestEntry.ofSx? (x : Sx) : Option ManifestEntry := do
  let kv ← sxField? "kind" x
  let kind ← atom? kv
  let kv ← sxField? "key" x
  let key ← (← atom? kv).toNat?
  let keySha ← match ← sxField? "key-sha" x with
    | .a s => pure s
    | _ => pure ""
  let fv ← sxField? "file" x
  let file ← atom? fv
  let sv ← sxField? "size" x
  let size ← (← atom? sv).toNat?
  let hv ← sxField? "sha256" x
  let sha256 ← atom? hv
  let fv ← sxField? "format" x
  let format ← (← atom? fv).toNat?
  pure { kind, key := key.toUInt64, keySha, file, size, sha256, format }

/-- The bytes an entry's digest covers: its canonical S-expression, with a newline. -/
def ManifestEntry.canonical (e : ManifestEntry) : ByteArray := (e.toSx.render ++ "\n").toUTF8

/-- The file an entry must name for `binary` (the same name the store uses). -/
def ManifestEntry.expectedFile (binary : UInt64) (e : ManifestEntry) : String :=
  let key : Key := { fast := e.key, strong := e.keySha }
  if e.kind == "wizr" then regionFileName binary key else s!"{mixHash binary e.key}.wizc"

/-- A file name that stays inside the layer. -/
def safeFileName (f : String) : Bool :=
  !f.isEmpty && !f.contains '/' && !f.contains '\\' && !f.contains ".."

/-- A single entry's self-consistency: its format, safe name, expected name, and both
digests (the output and the strong input key). -/
def ManifestEntry.valid (binary : UInt64) (e : ManifestEntry) : Bool :=
  let formatOk := if e.kind == "wizr" then e.format == regionFormat
    else e.kind == "wizc" && e.format == salt.toNat
  formatOk && safeFileName e.file && e.file == e.expectedFile binary &&
  e.sha256.length == 64 && e.keySha.length == 64

/-! Merkle roots (RFC 6962 shapes: `SHA-256(0x00 || leaf)`, `SHA-256(0x01 || l || r)`). -/

def leafHash (domain : String) (data : ByteArray) : ByteArray :=
  Smt.Sha256.bytes ((domain.toUTF8.push 0) ++ data)

def nodeHash (l r : ByteArray) : ByteArray :=
  Smt.Sha256.bytes (ByteArray.mk #[0x01] ++ l ++ r)

/-- The largest power of two strictly below `n` (n ≥ 2). -/
def largestPow2Lt (n : Nat) : Nat := Id.run do
  let mut k := 1
  while 2 * k < n do k := 2 * k
  k

partial def merkleRoot (hs : Array ByteArray) : ByteArray :=
  if hs.size == 0 then Smt.Sha256.bytes .empty
  else if hs.size == 1 then hs[0]!
  else
    let k := largestPow2Lt hs.size
    nodeHash (merkleRoot (hs.extract 0 k)) (merkleRoot (hs.extract k hs.size))

/-- One module's (or one root file's) manifest. It does not carry mtime, the cache path or
any display field: two seals of the same entries render identically. -/
structure ModuleManifest where
  format : Nat := 2
  /-- the module name; `""` for a root file -/
  module : Name := ""
  /-- the module key (or the root file's chain key); a fast index -/
  key : UInt64 := 0
  /-- the SHA-256 module key (or root chain key) -/
  keySha : String := ""
  /-- the `wiz` binary (`binaryId`) -/
  binary : UInt64 := 0
  /-- SHA-256 of the executable (a strong toolchain tag; P3 can sign it) -/
  toolchain : String := ""
  /-- the strong toolchain namespace (`Toolchain.tag`: target, compiler, flags) -/
  toolchainTag : String := ""
  /-- the strong target namespace (`Toolchain.targetTag`: triple and word width) -/
  targetTag : String := ""
  /-- the rig the region was saved for (`RigTag.tag`) -/
  rig : String := ""
  region : Option ManifestEntry := none
  entries : Array ManifestEntry := #[]
  /-- the root of this module's previous manifest (a local hash chain; `""` for the
  first). It is inside the root, so it cannot be edited without detection. -/
  prev : String := ""
  /-- Unix seconds after which the manifest must not be used (`0`: no expiry). An expired
  manifest is a miss, never a wrong result. -/
  validUntil : Nat := 0
  root : String := ""
  deriving Inhabited

/-- 1: fast-key-only manifests. 2: the SHA-256 input keys and target/toolchain namespace
(`key-sha`, `target-tag`); a format-1 manifest is a miss and is regenerated, never read
under a strong key. -/
def manifestFormat : Nat := 2

def ModuleManifest.allEntries (m : ModuleManifest) : Array ManifestEntry :=
  m.entries ++ m.region.toList.toArray

/-- What a manifest says about itself (not its entries): this leaf is part of the root. -/
def ModuleManifest.metaSx (m : ModuleManifest) : Sx :=
  node "manifest-meta" [node "format" [nat m.format], node "module" [str (toString m.module)],
    node "key" [str (toString m.key)], node "key-sha" [str m.keySha],
    node "binary" [str (toString m.binary)],
    node "toolchain" [str m.toolchain], node "toolchain-tag" [str m.toolchainTag],
    node "target-tag" [str m.targetTag], node "rig" [str m.rig],
    node "prev" [str m.prev], node "valid-until" [nat m.validUntil]]

/-- The RFC 6962 root over the metadata leaf and the entries (sorted by their canonical
text). Metadata (`prev`, `valid-until`) is bound too, so it is not free-floating. -/
def ModuleManifest.rootOf (m : ModuleManifest) : String :=
  let sorted := (m.allEntries.qsort fun a b => a.toSx.render < b.toSx.render)
  let metaLeaf := leafHash "wiz-manifest-v1" ((m.metaSx.render ++ "\n").toUTF8)
  Smt.Sha256.hexBytes (merkleRoot (#[metaLeaf] ++ sorted.map fun e => leafHash "wiz-entry-v1" e.canonical))

def ModuleManifest.toSx (m : ModuleManifest) : Sx :=
  let region := match m.region with
    | some e => node "region" [e.toSx]
    | none => node "region" [.a "none"]
  -- (canonical order: entries are a set, and the order they were written in depends on
  -- which commands were cache hits; the Merkle root already sorts them)
  let entries := (m.entries.qsort fun a b => a.toSx.render < b.toSx.render).toList
  node "module-manifest" [
    node "format" [nat m.format],
    node "module" [str (toString m.module)],
    node "key" [str (toString m.key)],
    node "key-sha" [str m.keySha],
    node "binary" [str (toString m.binary)],
    node "toolchain" [str m.toolchain],
    node "toolchain-tag" [str m.toolchainTag],
    node "target-tag" [str m.targetTag],
    node "rig" [str m.rig],
    node "prev" [str m.prev],
    node "valid-until" [nat m.validUntil],
    region,
    node "entries" [list (entries.map ManifestEntry.toSx)],
    node "root" [str m.root]]

def ModuleManifest.ofSx? (x : Sx) : Option ModuleManifest := do
  let v ← sxField? "format" x
  let format ← (← atom? v).toNat?
  let v ← sxField? "module" x
  let module ← atom? v
  let v ← sxField? "key" x
  let key ← (← atom? v).toNat?
  let keySha ← match ← sxField? "key-sha" x with
    | .a s => pure s
    | _ => pure ""
  let v ← sxField? "binary" x
  let binary ← (← atom? v).toNat?
  let v ← sxField? "toolchain" x
  let toolchain ← atom? v
  let toolchainTag ← match ← sxField? "toolchain-tag" x with
    | .a s => pure s
    | _ => pure ""
  let targetTag ← match ← sxField? "target-tag" x with
    | .a s => pure s
    | _ => pure ""
  let v ← sxField? "rig" x
  let rig ← atom? v
  let prev ← match ← sxField? "prev" x with
    | .a s => pure s
    | _ => pure ""
  let validUntil ← match ← sxField? "valid-until" x with
    | .a s => pure (s.toNat?.getD 0)
    | _ => pure 0
  let region ← match ← sxField? "region" x with
    | .a "none" => some none
    | e => (ManifestEntry.ofSx? e).map some
  let v ← sxField? "entries" x
  let entries ← (← items? v).mapM ManifestEntry.ofSx?
  let v ← sxField? "root" x
  let root ← atom? v
  pure { format, module, key := key.toUInt64, keySha, binary := binary.toUInt64, toolchain,
         toolchainTag, targetTag, rig, region, entries, prev, validUntil, root }

/-- Does this manifest belong to `key` of `binary`, under this toolchain and rig, and does
its own root cover its entries? The fast key is an index; when `key.strong` (or its
toolchain/target namespace) is known, it must match the manifest's SHA-256 fields, so a
64-bit collision selects no entry. -/
def ModuleManifest.valid (m : ModuleManifest) (key : Key) (binary : UInt64)
    (toolchain rig : String) : Bool :=
  m.format == manifestFormat && m.key == key.fast && m.keySha.length == 64 &&
  (key.strong.isEmpty || m.keySha == key.strong) &&
  (key.toolchain.isEmpty || m.toolchainTag == key.toolchain) &&
  (key.target.isEmpty || m.targetTag == key.target) &&
  m.binary == binary &&
  (toolchain == "" || m.toolchain == toolchain) &&
  (rig == "" || m.rig == rig) &&
  m.entries.all (fun e => e.kind == "wizc" && e.valid binary) &&
  (match m.region with
   | none => true
   | some e => e.kind == "wizr" && e.key == key.fast &&
      (key.strong.isEmpty || e.keySha == key.strong) && e.valid binary) &&
  m.root == m.rootOf

def parseManifest (text : String) : Option ModuleManifest :=
  (Sx.parse text).bind ModuleManifest.ofSx?

/-- A manifest entry for an effect text (`.wizc`). -/
def ManifestEntry.ofEffect (binary : UInt64) (key : Key) (e : Effect R) : ManifestEntry :=
  let text := e.toSx.render
  { kind := "wizc", key := key.fast, keySha := key.strong,
    file := s!"{mixHash binary key.fast}.wizc",
    size := text.toUTF8.size, sha256 := Smt.Sha256.hexBytes text.toUTF8, format := salt.toNat }

/-- A manifest entry for bytes read from `file` (a `.wizc` or `.wizr` a layer has). -/
def ManifestEntry.ofBytes (kind : String) (key : Key) (file : String) (bytes : ByteArray) : ManifestEntry :=
  { kind, key := key.fast, keySha := key.strong, file, size := bytes.size,
    sha256 := Smt.Sha256.hexBytes bytes,
    format := if kind == "wizr" then regionFormat else salt.toNat }

/-- The manifest file of module `key` in a layer. The strong half is in the name, so two
colliding fast keys never overwrite each other; a fast-only (old) name is never looked up
under a strong key, so an old cache is a clean miss and regenerates. -/
def manifestDirName : String := "manifest.d"

def manifestFileName (binary : UInt64) (key : Key) : String :=
  if key.strong.isEmpty then s!"{mixHash binary key.fast}.wizmf"
  else s!"{mixHash binary key.fast}-{key.strong}.wizmf"

def manifestFile (dir : System.FilePath) (binary : UInt64) (key : Key) : System.FilePath :=
  dir / manifestDirName / manifestFileName binary key

/-- The layer's generation index (P1): `manifest.sexpr`. -/
def generationFile (dir : System.FilePath) : System.FilePath := dir / "manifest.sexpr"

/-- One module record in a layer's generation index: fast key, SHA-256 key, name,
manifest file, and the manifest's own digest. -/
def moduleRecord (x : UInt64 × String × String × String × String) : Sx :=
  node "module" [node "key" [str (toString x.1)], node "key-sha" [str x.2.1],
    node "name" [str x.2.2.1], node "file" [str x.2.2.2.1], node "sha256" [str x.2.2.2.2]]

/-- The layer's `manifest.sexpr` (P1): a generation number, the previous index's root, an
optional expiry, and one record per module manifest. The root covers the metadata and the
records, so `prev` and `valid-until` are not free-floating. -/
structure Generation where
  generation : Nat := 0
  /-- the previous `manifest.sexpr` root (`""` for the first) -/
  prev : String := ""
  /-- Unix seconds after which this generation must not be used (`0`: no expiry) -/
  validUntil : Nat := 0
  /-- (fast module key, SHA-256 module key, module name, manifest file, manifest SHA-256) -/
  modules : Array (UInt64 × String × String × String × String) := #[]
  root : String := ""
  deriving Inhabited

def Generation.metaSx (g : Generation) : Sx :=
  node "generation-meta" [node "format" [nat 2], node "generation" [nat g.generation],
    node "prev" [str g.prev], node "valid-until" [nat g.validUntil]]

def Generation.rootOf (g : Generation) : String :=
  let metaLeaf := leafHash "wiz-generation-v1" ((g.metaSx.render ++ "\n").toUTF8)
  let mods := (g.modules.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1)).map fun x =>
    leafHash "wiz-module-v1" (moduleRecord x).render.toUTF8
  Smt.Sha256.hexBytes (merkleRoot (#[metaLeaf] ++ mods))

def Generation.toSx (g : Generation) : Sx :=
  node "cache-manifest" [node "format" [nat 2], node "generation" [nat g.generation],
    node "prev" [str g.prev], node "valid-until" [nat g.validUntil],
    node "modules" [list ((g.modules.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1)).toList.map moduleRecord)],
    node "root" [str g.root]]

def parseGeneration (text : String) : Option Generation := do
  let x ← Sx.parse text
  let v ← sxField? "format" x
  unless (← atom? v) == "2" do none
  let v ← sxField? "generation" x
  let generation ← (← atom? v).toNat?
  let prev ← match ← sxField? "prev" x with | .a s => pure s | _ => pure ""
  let validUntil ← match ← sxField? "valid-until" x with
    | .a s => pure (s.toNat?.getD 0) | _ => pure 0
  let mods ← match ← sxField? "modules" x with
    | .l xs => xs.filterMapM fun x => do
        let v ← sxField? "key" x; let key ← (← atom? v).toNat?
        let v ← sxField? "key-sha" x; let keySha ← atom? v
        let v ← sxField? "name" x; let name ← atom? v
        let v ← sxField? "file" x; let file ← atom? v
        let v ← sxField? "sha256" x; let sha ← atom? v
        pure (key.toUInt64, keySha, name, file, sha)
    | _ => none
  let v ← sxField? "root" x
  let root ← atom? v
  pure { generation, prev, validUntil, modules := mods, root }

def readGeneration (dir : System.FilePath) : IO (Option Generation) := do
  let f := generationFile dir
  if ← f.pathExists then
    try pure (parseGeneration (← IO.FS.readFile f)) catch _ => pure none
  else pure none

/-- The write cache's pointer from a root file's path to its last root manifest. A root
manifest is per **text** (so every root file does not share one manifest, which grew
without bound and lost concurrent writers' entries); this pointer is what lets an edit
reuse the unchanged prefix's entries: the previous text's manifest is loaded too, and the
new manifest records the entries that hit. A missing or stale pointer only costs a cold
root, never a wrong result. -/
def rootPointerFile (dir : System.FilePath) (path : String) : System.FilePath :=
  dir / "roots" / s!"{hash path}.rootp"

def readRootPointer (dir : System.FilePath) (path : String) : IO (Option Key) := do
  let f := rootPointerFile dir path
  if !(← f.pathExists) then return none
  let text ← try pure (← IO.FS.readFile f) catch _ => pure ""
  match text.splitOn "\n" with
  | k :: sha :: _ =>
    match k.toNat? with
    | some k =>
      if sha.length == 64 then
        pure (some ({ fast := k.toUInt64, strong := sha } : Key))
      else pure none
    | none => pure none
  | _ => pure none

def writeRootPointer (dir : System.FilePath) (path : String) (k : Key) : IO Unit := do
  let f := rootPointerFile dir path
  IO.FS.createDirAll (f.parent.getD dir)
  try writeAtomic f s!"{k.fast}\n{k.strong}\n" catch _ => pure ()

def unixNow : IO Nat := do
  pure (← Std.Time.Timestamp.now).val.toSeconds.toInt.toNat

/-- What verification did, for `--cache-verify-stats` and `wiz cache verify`. -/
structure VerifyCounts where
  /-- module manifests loaded and found valid -/
  manifests : Nat := 0
  /-- entries served after their bytes matched a manifest -/
  hits : Nat := 0
  /-- entries that a manifest listed but whose bytes did not match (a miss) -/
  mismatches : Nat := 0
  /-- entries used without a manifest (the `warn` compatibility path) -/
  unverified : Nat := 0
  /-- regions served after their bytes matched a manifest -/
  regions : Nat := 0
  deriving Inhabited, Repr

/-- The per-process manifest index: the manifests of every layer, by module key, and the
entries they name, by command key. Read-only layers are only ever read. -/
structure ManifestStore where
  write : Option System.FilePath
  reads : List System.FilePath
  binary : UInt64
  toolchain : String
  rig : String
  mode : VerifyMode
  /-- `Key.id`s whose manifests have been loaded -/
  loaded : IO.Ref (Std.HashSet String)
  /-- `Key.id` → (entry, layer), in layer order -/
  entries : IO.Ref (Std.HashMap String (Array (ManifestEntry × System.FilePath)))
  /-- module `Key.id` → (region entry, layer), in layer order -/
  regions : IO.Ref (Std.HashMap String (Array (ManifestEntry × System.FilePath)))
  /-- keys named by a manifest whose own root failed: always a miss -/
  poisoned : IO.Ref (Std.HashSet String)
  /-- module keys with a manifest file in some layer (valid or not) -/
  present : IO.Ref (Std.HashSet String)
  /-- module keys whose manifest validated in some layer -/
  valid : IO.Ref (Std.HashSet String)
  /-- a layer's generation expiry, cached per layer -/
  expiry : IO.Ref (Std.HashMap String Nat)
  /-- read-only layers already warned about, so a missing manifest is reported once -/
  warnedRo : IO.Ref (Std.HashSet String)
  /-- how many manifested entries failed their digest (drives one repair pass) -/
  broken : IO.Ref Nat
  stats : Option (IO.Ref VerifyCounts) := none

def ManifestStore.create (write : Option System.FilePath) (reads : List System.FilePath)
    (binary : UInt64) (toolchain rig : String) (mode : VerifyMode)
    (stats : Option (IO.Ref VerifyCounts) := none) : IO ManifestStore := do
  pure { write, reads, binary, toolchain, rig, mode,
         loaded := ← IO.mkRef ({} : Std.HashSet String),
         entries := ← IO.mkRef ({} : Std.HashMap String (Array (ManifestEntry × System.FilePath))),
         regions := ← IO.mkRef ({} : Std.HashMap String (Array (ManifestEntry × System.FilePath))),
         poisoned := ← IO.mkRef ({} : Std.HashSet String),
         present := ← IO.mkRef ({} : Std.HashSet String),
         valid := ← IO.mkRef ({} : Std.HashSet String),
         expiry := ← IO.mkRef ({} : Std.HashMap String Nat),
         warnedRo := ← IO.mkRef ({} : Std.HashSet String),
         broken := ← IO.mkRef 0, stats }

def ManifestStore.dirs (m : ManifestStore) : List System.FilePath := m.write.toList ++ m.reads

/-- Is `dir` one of the read-only layers (`--cache-ro`)? -/
def ManifestStore.isRead (m : ManifestStore) (dir : System.FilePath) : Bool :=
  m.reads.any (·.toString == dir.toString)

/-- A layer's generation expiry (Unix seconds, `0` for none), read once. -/
def ManifestStore.expiryOf (m : ManifestStore) (dir : System.FilePath) : IO Nat := do
  let key := dir.toString
  match (← m.expiry.get)[key]? with
  | some n => pure n
  | none =>
    let n ← match ← readGeneration dir with
      | some g => pure g.validUntil
      | none => pure 0
    m.expiry.modify (·.insert key n)
    pure n

/-- Warn once per read-only layer that has no manifest for a module: its entries are not
used (they would be unverified). -/
def ManifestStore.warnMissingRo (m : ManifestStore) (dir : System.FilePath) : IO Unit := do
  let key := dir.toString
  if (← m.warnedRo.get).contains key then return
  m.warnedRo.modify (·.insert key)
  IO.eprintln s!"cache verify: --cache-ro {dir}: no manifest for a module; its entries are not used (--cache-verify off restores the old lookup)"

def ManifestStore.bump (m : ManifestStore) (f : VerifyCounts → VerifyCounts) : IO Unit :=
  match m.stats with
  | some r => r.modify f
  | none => pure ()

def ManifestStore.inWrite (m : ManifestStore) (dir : System.FilePath) : Bool :=
  some dir.toString == m.write.map (·.toString)

/-- Load (once) every layer's manifest for module key `key` and index its entries. A layer
whose manifest exists but does not validate poisons the keys it names; it is never
silently treated as authoritative. -/
def ManifestStore.load (m : ManifestStore) (key : Key) : IO Unit := do
  let id := Key.id key
  if (← m.loaded.get).contains id then return
  m.loaded.modify (·.insert id)
  let now ← unixNow
  for dir in m.dirs do
    let f := manifestFile dir m.binary key
    if ← f.pathExists then
      m.present.modify (·.insert id)
      let text ← try pure ((String.fromUTF8? (← IO.FS.readBinFile f)).getD "") catch _ => pure ""
      match parseManifest text with
      | some man =>
        -- (a manifest, or its layer's generation index, may carry an expiry)
        let layerUntil ← m.expiryOf dir
        let expired := (man.validUntil != 0 && now > man.validUntil) ||
          (layerUntil != 0 && now > layerUntil)
        if !expired && man.valid key m.binary m.toolchain m.rig then
          m.valid.modify (·.insert id)
          m.bump fun c => { c with manifests := c.manifests + 1 }
          for e in man.entries do
            let eid := Key.id { fast := e.key, strong := e.keySha }
            m.entries.modify fun mp => mp.insert eid (((mp[eid]?).getD #[]).push (e, dir))
          if let some e := man.region then
            m.regions.modify fun mp => mp.insert id (((mp[id]?).getD #[]).push (e, dir))
        else
          -- (expired or not self-consistent: the entries it names are all misses, both
          -- under its strong keys and under the fast-only compatibility key)
          if expired then
            IO.eprintln s!"cache verify: {dir}: manifest for module {man.module} expired (valid-until {man.validUntil})"
          for e in man.allEntries do
            let eid := Key.id { fast := e.key, strong := e.keySha }
            m.poisoned.modify (·.insert eid)
            m.poisoned.modify (·.insert (Key.id (Key.ofFast e.key)))
      | none =>
        -- (unparsable: its keys are unknown; treat it as absent, as the old cache did)
        pure ()
    else if m.isRead dir then
      -- (warn only if this module was elaborated here; an empty layer or one that
      -- simply lacks the module is not a downgrade. The marker is named by the module
      -- key; the `.wizc` entries are named by command keys.)
      let oldMarker := s!"{mixHash m.binary key.fast}.wizm"
      let marker := if key.strong.isEmpty then oldMarker
        else s!"{mixHash m.binary key.fast}-{key.strong}.wizm"
      let oldRegion := s!"{mixHash m.binary key.fast}.wizr"
      let hasMarker ← (dir / marker).pathExists
      let hasOldMarker ← (dir / oldMarker).pathExists
      let hasRegion ← (dir / regionFileName m.binary key).pathExists
      let hasOldRegion ← (dir / oldRegion).pathExists
      if hasMarker || hasOldMarker || hasRegion || hasOldRegion then m.warnMissingRo dir

/-- The entries a manifest lists for command key `k` (none: unlisted). The strong half is
part of the index, so a 64-bit collision finds no entry for the other input. -/
def ManifestStore.entryFor (m : ManifestStore) (k : Key) : IO (Option (Array (ManifestEntry × System.FilePath))) := do
  pure ((← m.entries.get)[Key.id k]?)

def ManifestStore.regionFor (m : ManifestStore) (k : Key) : IO (Option (Array (ManifestEntry × System.FilePath))) := do
  pure ((← m.regions.get)[Key.id k]?)

def ManifestStore.poisonedFor (m : ManifestStore) (k : Key) : IO Bool := do
  pure ((← m.poisoned.get).contains (Key.id k))

def ManifestStore.presentFor (m : ManifestStore) (k : Key) : IO Bool := do
  pure ((← m.present.get).contains (Key.id k))

def ManifestStore.validFor (m : ManifestStore) (k : Key) : IO Bool := do
  pure ((← m.valid.get).contains (Key.id k))

/-- Write module `key`'s manifest to the write cache (a no-op without one). `merge` keeps
entries from an existing manifest (the root pseudo-module is shared by files with the same
headers). The entries are also indexed for this process, so a key written now verifies on
the next read. -/
def ManifestStore.writeManifest (m : ManifestStore) (key : Key) (module : Name)
    (entries : Array ManifestEntry) (region : Option ManifestEntry) (merge : Bool := false)
    (validUntil : Nat := 0) : IO Unit := do
  let some dir := m.write | return
  IO.FS.createDirAll (dir / manifestDirName)
  let f := manifestFile dir m.binary key
  let id := Key.id key
  let oldRaw ← if ← f.pathExists then
      try pure (parseManifest ((String.fromUTF8? (← IO.FS.readBinFile f)).getD ""))
      catch _ => pure none
    else pure none
  let old := oldRaw.filter fun x => x.valid key m.binary m.toolchain m.rig
  let entries := match old with
    | some o => if merge then
        entries.foldl (fun acc e =>
          if acc.any (fun a => a.key == e.key && a.keySha == e.keySha) then acc else acc.push e) o.entries
      else entries
    | none => entries
  let validUntil := if validUntil == 0 then (old.map (·.validUntil) |>.getD 0) else validUntil
  -- A refresh that adds nothing is a no-op: `prev` is the hash chain of the previous
  -- manifest, so rewriting an unchanged manifest (a module checked again in the same
  -- build, or in a later build) would make the cache bytes depend on how many times it
  -- was written. Compare entries as a set (the canonical order is in `toSx`).
  let unchanged := match old with
    | none => false
    | some o =>
      o.module == module && o.key == key.fast && o.keySha == key.strong &&
      o.binary == m.binary && o.toolchain == m.toolchain &&
      o.toolchainTag == key.toolchain && o.targetTag == key.target && o.rig == m.rig &&
      o.validUntil == validUntil && o.region == region &&
      o.entries.size == entries.size && o.entries.all (entries.contains ·)
  if unchanged then
    m.present.modify (·.insert id)
    m.valid.modify (·.insert id)
    return
  -- (a rewrite keeps the generation base the manifest started from: the number of
  -- rewrites depends on which commands were cache hits, not on the module's inputs.
  -- The layer's `manifest.sexpr` is a snapshot for the same reason.)
  let prev := old.map (·.prev) |>.getD ""
  let m0 : ModuleManifest := { module, key := key.fast, keySha := key.strong,
                               binary := m.binary, toolchain := m.toolchain,
                               toolchainTag := key.toolchain, targetTag := key.target,
                               rig := m.rig, region, entries, prev, validUntil }
  let m0 := { m0 with root := m0.rootOf }
  let text := m0.toSx.render ++ "\n"
  writeAtomic f text
  -- (this process may read the entry back before the manifest is reloaded)
  m.present.modify (·.insert id)
  m.valid.modify (·.insert id)
  for e in m0.entries do
    let eid := Key.id { fast := e.key, strong := e.keySha }
    m.entries.modify fun mp => mp.insert eid (((mp[eid]?).getD #[]).push (e, dir))
  if let some e := m0.region then do
    m.regions.modify fun mp => mp.insert id (((mp[id]?).getD #[]).push (e, dir))

/-- Verify the keyed files of one layer against its manifests (the full-scan tool). This
is what `wiz cache verify` reports; normal runs verify only what they read. -/
structure LayerVerify where
  /-- valid module manifests -/
  modules : Nat := 0
  /-- `.wizc` entries checked -/
  entries : Nat := 0
  /-- `.wizr` regions checked -/
  regions : Nat := 0
  /-- bytes that differ from their manifest (or a bad manifest) -/
  mismatches : Nat := 0
  /-- files a manifest lists that are missing -/
  missing : Nat := 0
  /-- keyed `.wizc`/`.wizr` files no manifest lists -/
  unmanifested : Nat := 0
  /-- manifests past their (or their layer's) `valid-until` -/
  expired : Nat := 0
  deriving Inhabited, Repr

partial def allFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out := #[]
  for e in ← dir.readDir do
    if ← e.path.isDir then out := out ++ (← allFiles e.path)
    else out := out.push e.path
  pure out

/-- Check every manifest in `dir` against the bytes beside it, and count keyed files that
no manifest lists. The layer is read only. -/
def verifyLayer (dir : System.FilePath) : IO LayerVerify := do
  let mut c : LayerVerify := {}
  let mut named : Std.HashSet String := {}
  let now ← unixNow
  let layerUntil ← match ← readGeneration dir with
    | some g => pure g.validUntil
    | none => pure 0
  let layerExpired := layerUntil != 0 && now > layerUntil
  let mdir := dir / manifestDirName
  let files ← if ← mdir.pathExists then mdir.readDir else pure #[]
  for e in files do
    if !e.fileName.endsWith ".wizmf" then continue
    let text ← try pure ((String.fromUTF8? (← IO.FS.readBinFile e.path)).getD "") catch _ => pure ""
    match parseManifest text with
    | some man =>
      let expired := layerExpired || (man.validUntil != 0 && now > man.validUntil)
      if expired then
        c := { c with expired := c.expired + 1 }
        for ent in man.allEntries do named := named.insert ent.file
      else if man.valid { fast := man.key, strong := man.keySha,
                           toolchain := man.toolchainTag, target := man.targetTag } man.binary "" "" then
        c := { c with modules := c.modules + 1 }
        for ent in man.allEntries do
          named := named.insert ent.file
          if ent.kind == "wizr" then c := { c with regions := c.regions + 1 }
          else c := { c with entries := c.entries + 1 }
          let f := dir / ent.file
          if ← f.pathExists then
            let bytes ← try pure (← IO.FS.readBinFile f) catch _ => pure ByteArray.empty
            unless bytes.size == ent.size && Smt.Sha256.hexBytes bytes == ent.sha256 do
              c := { c with mismatches := c.mismatches + 1 }
          else
            c := { c with missing := c.missing + 1 }
      else
        c := { c with mismatches := c.mismatches + 1 }
    | none => c := { c with mismatches := c.mismatches + 1 }
  for f in ← allFiles dir do
    let name := f.fileName.getD ""
    if (name.endsWith ".wizc" || name.endsWith ".wizr") && !named.contains name then
      c := { c with unmanifested := c.unmanifested + 1 }
  pure c

/-- `wiz cache manifest [DIR]`: rebuild a layer's `manifest.sexpr` from its per-module
manifests, and report the counts. With `write = false` it only reports (a read-only layer
is never written). -/
def sealLayer (dir : System.FilePath) (write : Bool) (validUntil : Nat := 0) : IO (Nat × Nat) := do
  let mut mods : Array (UInt64 × String × String × String × String) := #[]
  let mut entries := 0
  let mdir := dir / manifestDirName
  let files ← if ← mdir.pathExists then mdir.readDir else pure #[]
  for e in files do
    if !e.fileName.endsWith ".wizmf" then continue
    let text ← try pure ((String.fromUTF8? (← IO.FS.readBinFile e.path)).getD "") catch _ => pure ""
    match parseManifest text with
    | some man =>
      if man.valid { fast := man.key, strong := man.keySha,
                     toolchain := man.toolchainTag, target := man.targetTag } man.binary "" "" then
        entries := entries + man.allEntries.size
        mods := mods.push (man.key, man.keySha, (toString man.module), e.fileName,
          Smt.Sha256.hexBytes text.toUTF8)
    | none => pure ()
  if write then
    let old ← readGeneration dir
    let mergedMods := (old.map (·.modules) |>.getD #[]).foldl (fun acc x =>
      (acc.filter (fun y => y.1 != x.1 || y.2.1 != x.2.1)).push x) mods
    let g0 := Generation.mk (max 1 mergedMods.size) ""
      (if validUntil == 0 then (old.map (·.validUntil) |>.getD 0) else validUntil) mergedMods ""
    let g := { g0 with root := g0.rootOf }
    writeAtomic (generationFile dir) (g.toSx.render ++ "\n")
  pure (mods.size, entries)

/-- The toolchain tag: SHA-256 of the executable, memoised in the write cache's `bin/` by
the same stamp `binaryId` uses. Without a write cache it is recomputed (as `binaryId` is);
if the executable cannot be read, the (weaker) `binaryId` is used. -/
def toolchainTag (dir : Option System.FilePath) : IO String := do
  try
    let exe ← IO.appPath
    let md ← exe.metadata
    let stamp := s!"{exe} {md.byteSize} {md.modified.sec} {md.modified.nsec}"
    let file := dir.map (· / "bin" / s!"{hash stamp}.tag")
    if let some f := file then
      if ← f.pathExists then
        let s ← IO.FS.readFile f
        if s.startsWith (stamp ++ "\n") then return (s.drop (stamp.length + 1)).toString
    let tag := "sha256:" ++ Smt.Sha256.hexBytes (← IO.FS.readBinFile exe)
    if let some f := file then
      IO.FS.createDirAll (f.parent.getD ".")
      writeAtomic f s!"{stamp}\n{tag}"
    pure tag
  catch _ => do
    pure s!"binary:{← binaryId dir}"

/-- An effect read from the cache and the manifest entry (with its layer) that verified it.
`none` for the entry means the `warn` compatibility path (no manifest listed the key). -/
abbrev CacheHit (R : Type) := Effect R × Option (ManifestEntry × System.FilePath)

/-- Read `f`, check it against `e` (size and SHA-256), then decode it. Any read, size,
digest or parse failure is a miss. -/
def readVerifiedEffect (f : System.FilePath) (e : ManifestEntry) : IO (Option (Effect R)) := do
  try
    if !(← f.pathExists) then return none
    let bytes ← IO.FS.readBinFile f
    unless bytes.size == e.size && Smt.Sha256.hexBytes bytes == e.sha256 do return none
    let some text := String.fromUTF8? bytes | return none
    pure ((Sx.parse text).bind Effect.ofSx?)
  catch _ => pure none

/-- The module region cache: one artifact per module key, `get` treating any read error or
mismatched tag as a miss (and dropping the file). -/
structure RegionStore (R : Type) where
  get : Key → IO (Option (ModuleArtifact R))
  /-- write `a`; the store fills in `binary`, `salt` and `rig`, and returns the manifest
  entry (none without a write cache) -/
  put : ModuleArtifact R → IO (Option ManifestEntry)
  stats : Option (IO.Ref RegionCounts) := none
  /-- the output manifests (`--cache-verify`), shared with the text store -/
  manifests : Option ManifestStore := none

-- (`CompactedRegion.save`/`read` are `unsafe opaque`: `α` is erased at the boundary and the
-- caller must load with the type it saved. The `opaque` wrappers keep the loader safe, as
-- `Budget.tick` does; the type is checked by the tags above, never by Lean.)

private unsafe def regionSaveImpl {α : Type} (file : System.FilePath) (key : Lean.Name)
    (a : α) : IO Unit := do
  let _ ← Lean.CompactedRegion.save file key a #[] none
  pure ()

@[implemented_by regionSaveImpl]
private opaque regionSave {α : Type} (file : System.FilePath) (key : Lean.Name) (a : α) : IO Unit

private unsafe def regionReadImpl {α : Type} (file : System.FilePath) :
    IO (α × Lean.CompactedRegion) :=
  Lean.CompactedRegion.read (α := α) file #[]

@[implemented_by regionReadImpl]
private opaque regionRead {α : Type} (file : System.FilePath) : IO (α × Lean.CompactedRegion)

/-- Regions read in this process, kept until it exits: the objects in a mapped region are
not reference counted, so a state built from one must not outlive it (design §6.3 of
`wiz-notes/module-mmap.md`). One region per module name: re-reading the same module takes
Lean's copy path, which is correct, only slower. -/
initialize regionRoots : IO.Ref (Array Lean.CompactedRegion) ← IO.mkRef #[]

/-! ### The payload checksum

A region is a byte image, and `CompactedRegion.read` does no validation: a flipped byte is
not an error but a wrong term (or a crash). Format 2 therefore comes with a **sidecar**,
`<region>.wizs`: the 8-byte little-endian 64-bit hash of the `.wizr`'s bytes. It is checked
**before** the image is mapped, so a same-size bit flip — even one in a pointer the reader
would follow — is an ordinary miss, never UB.

Why a sidecar and not a trailer: Lean's compacted-region reader walks the image *backwards
from its end* (the root is written last), so appending 8 bytes shifts where it looks for the
root and the read fails ("unreachable code was reached"). Prepending is impossible (the
`.olean` header must be at offset 0), and patching a field inside the image would need its
offset, which is not stable. The sidecar keeps the `.wizr` byte-identical to what
`CompactedRegion.save` wrote, and lets the raw bytes be hashed before the mapping.

The check is cheap: one read of the region (the pages the `mmap` then uses) and the
runtime's 64-bit `ByteArray.hash` over the bytes — a millisecond or two for a multi-MB
region, never a decode. The hash is not content addressing (the image is not canonical): it
only guards the bytes this file on disk has. A missing sidecar, a wrong-size sidecar or a
mismatch is a miss; the write cache drops both files, a read-only cache keeps them. -/

/-- `n` as its eight little-endian bytes. -/
def u64Bytes (n : UInt64) : ByteArray :=
  ByteArray.mk #[ (n &&& 0xff).toUInt8, ((n >>> 8) &&& 0xff).toUInt8,
                  ((n >>> 16) &&& 0xff).toUInt8, ((n >>> 24) &&& 0xff).toUInt8,
                  ((n >>> 32) &&& 0xff).toUInt8, ((n >>> 40) &&& 0xff).toUInt8,
                  ((n >>> 48) &&& 0xff).toUInt8, ((n >>> 56) &&& 0xff).toUInt8 ]

/-- The little-endian `UInt64` in `b`'s first eight bytes. -/
def u64OfBytes (b : ByteArray) : UInt64 :=
  (b.get! 0).toUInt64 ||| ((b.get! 1).toUInt64 <<< 8) ||| ((b.get! 2).toUInt64 <<< 16) |||
  ((b.get! 3).toUInt64 <<< 24) ||| ((b.get! 4).toUInt64 <<< 32) ||| ((b.get! 5).toUInt64 <<< 40) |||
  ((b.get! 6).toUInt64 <<< 48) ||| ((b.get! 7).toUInt64 <<< 56)

/-- The checksum of every byte of `file`: the runtime's 64-bit `ByteArray.hash` over one
read of the whole image. (Chunked `Handle.read` calls were 80× slower here — about 0.8 ms
per 64 KiB — so the image is read once instead; a region is a few MB.) -/
def checksumFile (file : System.FilePath) : IO UInt64 := do
  pure (hash (← IO.FS.readBinFile file))

/-- A region's checksum file: the same stem as the `.wizr`, extension `.wizs`. -/
def regionSumFile (file : System.FilePath) : System.FilePath :=
  file.withExtension "wizs"

/-- `file`'s recorded checksum, if its sidecar holds the hash of the file's bytes. `none`
for a missing region or sidecar, a wrong-size sidecar, or corrupt bytes (any read error is
a miss). -/
def regionFileChecksum (file : System.FilePath) : IO (Option UInt64) := do
  try
    if !(← file.pathExists) then return none
    let side ← IO.FS.readBinFile (regionSumFile file)
    if side.size != 8 then return none
    let sum ← checksumFile file
    pure (if u64OfBytes side == sum then some sum else none)
  catch _ => pure none

/-- Read the artifact at `file`; `none` if it is missing, truncated, corrupt (the payload
checksum is checked first, so a bit flip never reaches the type-erased reader) or fails to
load. With `expected`, the bytes are also checked against a manifest's size and SHA-256
(one read of the image serves both checks). The region is kept alive for the process
(`regionRoots`). -/
def readRegionFile (file : System.FilePath) (expected : Option (Nat × String) := none) :
    IO (Option (ModuleArtifact R)) := do
  try
    if !(← file.pathExists) then return none
    let md ← file.metadata
    let side ← IO.FS.readBinFile (regionSumFile file)
    if side.size != 8 then return none
    let bytes ← IO.FS.readBinFile file
    if u64OfBytes side != hash bytes then return none
    if let some (size, sha) := expected then
      unless bytes.size == size && Smt.Sha256.hexBytes bytes == sha do return none
    let (a, r) ← regionRead (α := ModuleArtifact R) file
    -- (another process may have replaced the file between the check and the read: its
    -- bytes were not the ones we hashed, so do not trust them)
    let md' ← file.metadata
    if md'.byteSize != md.byteSize || md'.modified != md.modified then return none
    regionRoots.modify (·.push r)
    pure (some a)
  catch _ => pure none

/-- Delete a region and its checksum (both, so neither is left behind). -/
def removeRegionFiles (file : System.FilePath) : IO Unit := do
  removeQuietly file
  removeQuietly (regionSumFile file)

/-- Write an artifact to `file`: Lean writes a temporary image, its bytes are hashed into a
temporary `.wizs`, and both are renamed into place (image first: a reader that sees the new
image with the old checksum gets a clean miss, never a wrong term). Returns the manifest
entry for the bytes written (the SHA-256 is computed from the same read as the checksum). -/
def writeRegionFile (file : System.FilePath) (a : ModuleArtifact R) : IO (Option ManifestEntry) := do
  let stamp := s!".tmp{← IO.Process.getPID}-{← IO.monoNanosNow}"
  let tmp := file.toString ++ stamp
  let sumFile := regionSumFile file
  let sumTmp := sumFile.toString ++ stamp
  try
    regionSave tmp (Lean.Name.mkSimple a.module) a
    let bytes ← IO.FS.readBinFile tmp
    let sum := hash bytes
    IO.FS.writeBinFile sumTmp (u64Bytes sum)
    IO.FS.rename tmp file
    IO.FS.rename sumTmp sumFile
    pure (some { kind := "wizr", key := a.key, keySha := a.keySha, file := file.fileName.getD "",
                 size := bytes.size, sha256 := Smt.Sha256.hexBytes bytes, format := regionFormat })
  catch e =>
    removeQuietly tmp
    removeQuietly sumTmp
    throw e

/-- Module `key`'s artifact, if it exists and its tags match; a bad file is dropped (a pure
cache: the next run rewrites it). -/
def readModuleRegion (dir : System.FilePath) (binary : UInt64) (rig : String) (key : Key) :
    IO (Option (ModuleArtifact R)) := do
  let file := dir / regionFileName binary key
  match ← readRegionFile (R := R) file with
  | some a => if a.fits binary key rig then pure (some a) else
      removeRegionFiles file
      pure none
  | none =>
      if ← file.pathExists then removeRegionFiles file
      pure none

/-- Write module `key`'s artifact (the tags are filled in here). -/
def writeModuleRegion (dir : System.FilePath) (binary : UInt64) (rig : String) (key : Key)
    (module : Name) (effects : Array (Effect R)) (keys : Array UInt64) (complete := false)
    (rerun : Array (Nat × Nat) := #[]) : IO (Option ManifestEntry) :=
  writeRegionFile (dir / regionFileName binary key)
    { magic := regionMagic, format := regionFormat, binary, textSalt := salt, rig, module,
      key := key.fast, keySha := key.strong, toolchainSha := key.toolchain, targetSha := key.target,
      effects, keys, complete, rerun }

/-- Where command effects are kept: a write directory and read-only directories (the
layered shared cache), or memory (for one run without the cache: modules are still
elaborated in isolation, so the cache on or off gives the same results). A store may also
carry a module region cache (`--region-cache`): its regions live in the same directory
layers, the text entries remain the authority, and `--cache-verify`'s manifests gate both. -/
structure Store (R : Type) where
  get : Key → IO (Option (Effect R))
  /-- like `get`, with the manifest entry that verified the bytes (for writing manifests) -/
  getEntry : Key → IO (Option (CacheHit R))
  put : Key → Effect R → IO Unit
  /-- has module `k` been elaborated in isolation? -/
  seen : Key → IO Bool
  markSeen : Key → Name → IO Unit
  /-- the module region cache (`--region-cache`), when the store has one -/
  region : Option (RegionStore R) := none
  /-- the output manifests (`--cache-verify`) -/
  manifests : Option ManifestStore := none
  /-- the binary id the file names mix in -/
  binary : UInt64 := 0

/-- A layered store: entries are looked up in `write` first, then in each of `reads` in
order, and written only to `write` (none: `put` does nothing). A read cache is never
created or written: `get` just reports a missing or unparsable entry as a miss, so a
corrupt entry falls through to the next cache. `seen` is true when any cache has the
module's marker; `markSeen` writes the marker to `write`, or keeps it in memory when
there is none, so a `--cache-ro`-only run knows which modules it has already elaborated
in isolation. Its files are named by the key mixed with the binary, so another build of
wiz finds none of them. With `verify` on, a manifest-listed entry is served only after
its bytes match; a listed-but-bad entry is a miss, and an unlisted one falls back to the
old lookup in `warn` or misses in `strict`. -/
def Store.layeredCore (write : Option System.FilePath) (reads : List System.FilePath)
    (binary : UInt64) (manifests : Option ManifestStore) : IO (Store R) := do
  if let some dir := write then IO.FS.createDirAll dir
  -- (`.wizc` names keep the old fast shape: a text entry is still found by old caches;
  -- the manifest's SHA-256 key is what makes a colliding input a miss. A module marker
  -- includes the strong key: a colliding module must not be "seen" by name alone.)
  let entryName (k : Key) := toString (mixHash binary k.fast)
  let markerName (k : Key) :=
    if k.strong.isEmpty then entryName k else s!"{entryName k}-{k.strong}"
  let dirs := write.toList ++ reads
  let seenInMemory ← IO.mkRef ({} : Std.HashSet String)
  let getEntry : Key → IO (Option (CacheHit R)) := fun k => do
    let file := s!"{entryName k}.wizc"
    match manifests with
    | none =>
      for dir in dirs do
        let f := dir / file
        if ← f.pathExists then
          if let some e := (Sx.parse (← IO.FS.readFile f)).bind Effect.ofSx? then return some (e, none)
      pure none
    | some ms =>
      if ← ms.poisonedFor k then
        ms.bump fun c => { c with mismatches := c.mismatches + 1 }
        pure none
      else match ← ms.entryFor k with
      | some list =>
        for (ent, dir) in list do
          if let some eff ← readVerifiedEffect (R := R) (dir / ent.file) ent then
            ms.bump fun c => { c with hits := c.hits + 1 }
            return some (eff, some (ent, dir))
        ms.bump fun c => { c with mismatches := c.mismatches + 1 }
        ms.broken.modify (· + 1)
        pure none
      | none =>
        -- (A new key has a SHA-256 half: without a manifest entry there is nothing that
        -- binds the bytes to that input, so the write cache is a miss too. This is the
        -- old-cache migration: one cold pass rewrites its entries with manifests.
        -- `--cache-verify off` keeps the old unverified lookup; a fast-only legacy key
        -- reached through the API may also fall through.)
        if ms.mode == .strict || !k.strong.isEmpty then pure none
        else
          for dir in dirs do
            if ms.isRead dir then continue
            let f := dir / file
            if ← f.pathExists then
              let bytes ← try pure (← IO.FS.readBinFile f) catch _ => pure ByteArray.empty
              if let some text := String.fromUTF8? bytes then
                if let some e := (Sx.parse text).bind Effect.ofSx? then
                  ms.bump fun c => { c with unverified := c.unverified + 1 }
                  return some (e, some (ManifestEntry.ofBytes "wizc" k file bytes, dir))
          pure none
  pure {
    getEntry
    get := fun k => return (← getEntry k).map (·.1)
    put := fun k e => match write with
      | some dir => writeAtomic (dir / s!"{entryName k}.wizc") e.toSx.render
      | none => pure ()
    seen := fun k => do
      if (← seenInMemory.get).contains (Key.id k) then return true
      for dir in dirs do
        if ← (dir / s!"{markerName k}.wizm").pathExists then return true
      pure false
    markSeen := fun k m => match write with
      | some dir => writeAtomic (dir / s!"{markerName k}.wizm") m
      | none => seenInMemory.modify (·.insert (Key.id k))
    manifests
    binary }

/-- A layered store with the verification policy `verify` (default off: the old store). -/
def Store.layered (write : Option System.FilePath) (reads : List System.FilePath)
    (binary : UInt64) (verify : VerifyMode := .off) (rig : String := "")
    (stats : Option (IO.Ref VerifyCounts) := none) : IO (Store R) := do
  let manifests ← if verify == .off then pure none else
    pure (some (← ManifestStore.create write reads binary (← toolchainTag write) rig verify stats))
  Store.layeredCore write reads binary manifests

/-- The store in directory `dir`, for the binary `binary` (`binaryId`): a layered store
with one write directory and no read caches (the compatibility name for the old
single-directory store). -/
def Store.disk (dir : System.FilePath) (binary : UInt64) : IO (Store R) :=
  Store.layered (some dir) [] binary

def Store.memory : IO (Store R) := do
  let effects ← IO.mkRef ({} : Std.HashMap String (Effect R))
  let seen ← IO.mkRef ({} : Std.HashSet String)
  let getEntry : Key → IO (Option (CacheHit R)) := fun k =>
    return (← effects.get)[Key.id k]?.map fun e => (e, none)
  pure {
    getEntry
    get := fun k => return (← effects.get)[Key.id k]?
    put := fun k e => effects.modify (·.insert (Key.id k) e)
    seen := fun k => return (← seen.get).contains (Key.id k)
    markSeen := fun k _ => seen.modify (·.insert (Key.id k)) }

/-- A module's effects, collected while it is elaborated in isolation, to write its region
and its output manifest. -/
structure RegionSink (R : Type) where
  module : Name
  effects : IO.Ref (Array (Effect R))
  /-- the chained key at each collected effect, in the same order -/
  keys : IO.Ref (Array UInt64)
  /-- the source ranges of the commands that are not cacheable (commit 3's rerun path) -/
  rerun : IO.Ref (Array (Nat × Nat))
  /-- also write a module region (`false` for the root file, which has none) -/
  region : Bool := true
  /-- the `wizc` entries written into the write cache, for the module manifest -/
  entries : IO.Ref (Array ManifestEntry)

/-- The region store over the same layers as `Store.layered`: `get` searches the write
directory first, then each read-only directory in order, and `put` writes only to the write
directory (none: no writes). A read-only cache is never created, written or repaired, so a
missing, truncated or mistagged region there is just a miss; a bad file in the write
directory is dropped (the next run rewrites it). With `manifests`, a region must be listed
by the module's manifest and its bytes must match: a region is never served from a layer
whose manifest exists but does not list it (a corrupt or swapped `.wizr` is a miss), and a
manifest that does not validate makes it a miss. -/
def RegionStore.layered (write : Option System.FilePath) (reads : List System.FilePath)
    (binary : UInt64) (opts : RegionOptions) (manifests : Option ManifestStore := none) :
    IO (RegionStore R) := do
  let dirs := write.toList ++ reads
  let inWrite (dir : System.FilePath) : Bool :=
    some dir.toString == write.map (·.toString)
  let read (k : Key) : IO (Option (ModuleArtifact R)) := do
    match manifests with
    | none =>
      for dir in dirs do
        let file := dir / regionFileName binary k
        if ← file.pathExists then
          match ← readRegionFile (R := R) file with
          | some a =>
            if a.fits binary k opts.rig then return some a
            else if inWrite dir then removeRegionFiles file
          | none => if inWrite dir then removeRegionFiles file
      pure none
    | some ms =>
      ms.load k
      if ← ms.poisonedFor k then
        ms.bump fun c => { c with mismatches := c.mismatches + 1 }
        pure none
      else match ← ms.regionFor k with
        | some list =>
          for (ent, dir) in list do
            match ← readRegionFile (R := R) (dir / ent.file)
                (expected := some (ent.size, ent.sha256)) with
            | some a =>
              if a.fits binary k opts.rig then
                ms.bump fun c => { c with regions := c.regions + 1 }
                return some a
              else if inWrite dir then removeRegionFiles (dir / ent.file)
            | none => if inWrite dir then removeRegionFiles (dir / ent.file)
          ms.bump fun c => { c with mismatches := c.mismatches + 1 }
          pure none
        | none =>
          if ms.mode == .strict || (← ms.presentFor k) then
            if ms.mode == .strict then
              ms.bump fun c => { c with mismatches := c.mismatches + 1 }
            pure none
          else
            for dir in dirs do
              if ms.isRead dir then continue
              let file := dir / regionFileName binary k
              if ← file.pathExists then
                match ← readRegionFile (R := R) file with
                | some a =>
                  if a.fits binary k opts.rig then return some a
                  else if inWrite dir then removeRegionFiles file
                | none => if inWrite dir then removeRegionFiles file
            pure none
  pure {
    get := fun k => read k
    put := fun a => match write with
      | some dir => do
        -- (a pure cache: a region that cannot be written, say because `Effect` grew a
        -- closure, must not fail the run; the `.wizc` entries remain the authority)
        try
          let key : Key := { fast := a.key, strong := a.keySha, toolchain := a.toolchainSha,
                             target := a.targetSha, binary := a.binarySha }
          let e ← writeRegionFile (dir / regionFileName binary key)
            { a with binary := binary, textSalt := salt, rig := opts.rig }
          match manifests with
          | some ms =>
            for ent in e.toList do
              let id := Key.id key
              ms.regions.modify fun mp => mp.insert id (((mp[id]?).getD #[]).push (ent, dir))
          | none => pure ()
          pure e
        catch _ => pure none
      | none => pure none
    stats := opts.stats
    manifests }

/-- A layered store with module regions (`--region-cache`): the text entries and the
regions are searched in the same layer order, with one shared manifest index. -/
def Store.layeredRegion (write : Option System.FilePath) (reads : List System.FilePath)
    (binary : UInt64) (opts : RegionOptions) (verify : VerifyMode := .off) (rig : String := "")
    (stats : Option (IO.Ref VerifyCounts) := none) : IO (Store R) := do
  let manifests ← if verify == .off then pure none else
    pure (some (← ManifestStore.create write reads binary (← toolchainTag write) rig verify stats))
  let store ← Store.layeredCore write reads binary manifests
  let region ← RegionStore.layered write reads binary opts manifests
  pure { store with region := some region }

/-- The store in `dir` with module regions (`--region-cache`), for the rig `opts.rig`. -/
def Store.diskRegion (dir : System.FilePath) (binary : UInt64) (opts : RegionOptions) :
    IO (Store R) :=
  Store.layeredRegion (some dir) [] binary opts

/-! ## Pruning (`--cache-prune`, `wiz cache prune`)

Keyed entries are never invalidated by name: every edit, every binary and every option
change leaves last generation's `.wizc`/`.wizm`/`.wizr`/`.wizs` behind. Pruning is by **age**
(modification time) and only ever in the **write** cache — a `--cache-ro` layer is not
passed to `pruneCache` at all, so it cannot be touched. A pruned entry is an ordinary
miss: the next run elaborates and rewrites it. Pruning happens *before* a batch command
(`--cache-prune DAYS`) or as `wiz cache prune`, so the current process has not mapped any
region yet; only the three keyed extensions are considered (never a directory, the `bin/`
memo or anything else), and the CLI requires at least one day. -/

/-- What a prune removed (or would remove, with `dryRun`). -/
structure PruneCounts where
  /-- `.wizc` effect entries -/
  entries : Nat := 0
  /-- `.wizm` module markers -/
  markers : Nat := 0
  /-- `.wizr` module regions -/
  regions : Nat := 0
  /-- `.wizs` region checksums -/
  sums : Nat := 0
  /-- their total size in bytes -/
  bytes : Nat := 0
  deriving Inhabited, Repr

def PruneCounts.total (c : PruneCounts) : Nat := c.entries + c.markers + c.regions + c.sums

def PruneCounts.plus (a b : PruneCounts) : PruneCounts :=
  { entries := a.entries + b.entries, markers := a.markers + b.markers,
    regions := a.regions + b.regions, sums := a.sums + b.sums, bytes := a.bytes + b.bytes }

/-- A byte count in readable units. -/
def sizeText (n : Nat) : String :=
  if n < 1024 then s!"{n} B"
  else if n < 1024 * 1024 then s!"{n / 1024} KiB"
  else if n < 1024 * 1024 * 1024 then s!"{n / (1024 * 1024)} MiB"
  else s!"{n / (1024 * 1024 * 1024)} GiB"

/-- Delete the keyed cache files under `dir` older than `days` days (by modification time),
recursively; with `dryRun`, only count them. `now` (seconds since the Unix epoch) is for
tests and defaults to the wall clock. Only `.wizc`, `.wizm`, `.wizr` and `.wizs` are
considered: everything else — the `bin/` memo, a package's files, a subdirectory that is not
part of the cache — is left alone, and symlinks are not followed. Call it on the **write** cache: a
read-only layer is never pruned. -/
partial def pruneCache (dir : System.FilePath) (days : Nat) (dryRun : Bool := false)
    (now : Option Int := none) : IO PruneCounts := do
  let now ← match now with
    | some t => pure t
    | none => pure (← Std.Time.Timestamp.now).val.toSeconds.toInt
  let cutoff := now - (Int.ofNat days * 86400)
  let rec walk (d : System.FilePath) : IO PruneCounts := do
    let mut c : PruneCounts := {}
    for e in ← d.readDir do
      let link ← try pure (← e.path.symlinkMetadata).type catch _ => pure .other
      if link == .symlink then continue
      let md ← try pure (some (← e.path.metadata)) catch _ => pure none
      match md with
      | none => pure ()
      | some md =>
        if md.type == .dir then
          c := c.plus (← walk e.path)
        else if md.type == .file && md.modified.sec < cutoff then
          let entry := e.fileName.endsWith ".wizc"
          let marker := e.fileName.endsWith ".wizm"
          let region := e.fileName.endsWith ".wizr"
          let sum := e.fileName.endsWith ".wizs"
          if entry || marker || region || sum then
            unless dryRun do removeQuietly e.path
            c := c.plus { entries := if entry then 1 else 0, markers := if marker then 1 else 0,
                          regions := if region then 1 else 0, sums := if sum then 1 else 0,
                          bytes := md.byteSize.toNat }
    pure c
  walk dir

/-- One line, for `--cache-prune` or `wiz cache prune`. -/
def PruneCounts.render (c : PruneCounts) (days : Nat) (dryRun : Bool)
    (dir : System.FilePath) : String :=
  let what := if dryRun then "would remove" else "removed"
  s!"cache prune: {what} {c.total} files ({c.entries} .wizc, {c.markers} .wizm, " ++
  s!"{c.regions} .wizr, {c.sums} .wizs), {sizeText c.bytes} older than {days} days in {dir}"

/-- Prune `dir` and render the summary (`--cache-prune DAYS`, `wiz cache prune`). -/
def pruneSummary (dir : System.FilePath) (days : Nat) (dryRun : Bool := false)
    (now : Option Int := none) : IO String := do
  pure ((← pruneCache dir days dryRun now).render days dryRun dir)

/-- Module `key`'s artifact, if the region cache is on and the file matches. -/
def Store.getRegion (s : Store R) (k : Key) : IO (Option (ModuleArtifact R)) :=
  match s.region with
  | some r => r.get k
  | none => pure none

/-- Save a module artifact as its region (a no-op without `--region-cache`); returns the
manifest entry of the bytes written (none when nothing was written). -/
def Store.putRegion (s : Store R) (a : ModuleArtifact R) : IO (Option ManifestEntry) :=
  match s.region with
  | some r => r.put a
  | none => pure none

/-- Count a module that the region cache served (or did not; a no-op without stats). -/
def Store.countRegion (s : Store R) (hit : Bool) : IO Unit :=
  match s.region with
  | some r =>
    match r.stats with
    | some stats =>
      stats.modify fun c => if hit then { c with hits := c.hits + 1 } else { c with misses := c.misses + 1 }
    | none => pure ()
  | none => pure ()

/-- Count one command whose effect came from a region. -/
def Store.countRegionCommand (s : Store R) : IO Unit :=
  match s.region with
  | some r =>
    match r.stats with
    | some stats => stats.modify fun c => { c with commands := c.commands + 1 }
    | none => pure ()
  | none => pure ()

/-- (28) The solver settings, as a key, when they are not the defaults (none: nothing to
mix in, so the keys of every run without them stay as they were). -/
def smtKey (c : Smt.Config) : Option UInt64 :=
  let c := { c with cacheDir := none }
  if c == {} then none else some (mixHash (hash "smt") (hash c))

/-- Elaborate `input` (like `Query.elaborate`), reading and writing `store`. Returns the
final state and how many commands came from the store. `key₀` identifies what the
file can see besides its imports (for example its C headers); `toolchain` is mixed into
every module's key. `strongToolchain`/`targetTag`/`rootTag`/`binaryTag` are the SHA-256
namespaces a new manifest or region records; they do not change a fast key. `rootPath`
(the root file's path, when the caller has one) only names the pointer that lets an edit
reuse its unchanged prefix's manifest entries. -/
partial def elaborateWith (store : Store R) (input : String) (init : CommandState R) (key₀ : UInt64)
    (toolchain : UInt64 := 0) (strongToolchain : String := "") (targetTag : String := "")
    (rootTag : String := "") (binaryTag : String := "") (rootPath : String := "") :
    IO (CommandState R × Nat) := do
  let keys ← IO.mkRef ({} : Std.HashMap Name Key)
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
  let key₀Fast := mixHash (Module.includesKey includes "" input) key₀
  let key₀Strong := includesKeyStrong includes "" input
  -- (the strong namespace carries the same options, so a manifest/region from one
  -- option set is never accepted under another)
  let strongToolchain' := toolchainOptionsTag strongToolchain init.termInfo init.trustNative
    init.nativeFuel (smtKey init.smt)
  let chainKey : Key :=
    { fast := mixHash salt' (mixHash toolchain key₀Fast)
      strong := Smt.Sha256.hexFramed "wiz-cache/root-v1"
        [toString salt', toString toolchain, strongToolchain', targetTag, toString key₀Fast,
         rootTag, s!"includes:{key₀Strong}"]
      toolchain := strongToolchain', target := targetTag, binary := binaryTag }
  -- (a root file's manifest is keyed by the chain key **and its text**: the chain key does
  -- not contain the text (the commands chain it), so without this every root file with the
  -- same headers shared one manifest. That manifest grew with every file checked (12.7 MB
  -- in one cache here), was parsed and rewritten per root miss, and two concurrent checks
  -- of different files lost each other's entries -- a fresh file then missed on every run.
  -- The strong half alone separates the files; the fast half stays the old key.)
  let manifestKey : Key := chainKey.mixDomain "wiz-cache/root-manifest-v1" [input]
  -- (an edit keeps the unchanged prefix warm: the pointer names the previous text's
  -- manifest for this path, and loading it indexes the prefix's entries for this run)
  let prevKey ← match store.manifests with
    | some ms => match ms.write with
      | some dir => if rootPath.isEmpty then pure none else readRootPointer dir rootPath
      | none => pure none
    | none => pure none
  -- (a root file's manifest is keyed by the chain key and its text: the file is not an
  -- imported module)
  if let some ms := store.manifests then
    ms.load manifestKey
    if let some pk := prevKey then
      unless pk.strong == manifestKey.strong do ms.load pk
  let rootSink : Option (RegionSink R) ← match store.manifests with
    | some _ => pure (some { module := init.module, effects := ← IO.mkRef #[], keys := ← IO.mkRef #[],
                             rerun := ← IO.mkRef #[], region := false, entries := ← IO.mkRef #[] })
    | none => pure none
  let result ← go keys init [] input init chainKey .write manifestKey none rootSink
  match store.manifests with
  | some ms =>
    if !rootPath.isEmpty then
      if let some dir := ms.write then writeRootPointer dir rootPath manifestKey
  | none => pure ()
  pure result
where
  nativeKey (s : CommandState R) : UInt64 := mixHash (hash "trust-native") (hash s.nativeFuel)
  keyOf (keys : IO.Ref (Std.HashMap Name Key)) (m : Name) : IO Key := do
    -- (term info changes what a module elaborates to, like the main file's chain)
    let tc := if init.termInfo then mixHash toolchain 1 else toolchain
    let tc := if init.trustNative then mixHash tc (nativeKey init) else tc
    let tc := match smtKey init.smt with | some k => mixHash tc k | none => tc
    let stc := toolchainOptionsTag strongToolchain init.termInfo init.trustNative
      init.nativeFuel (smtKey init.smt)
    let includes := init.includes.getD (fun _ rel => .error s!"include_str: no file {rel}")
    let memo := moduleKeysAll init.loader init.cHeaders tc stc targetTag [m] (← keys.get)
      init.trustedModule includes
    keys.set memo
    pure ((memo.get? m).getD (Key.ofFast 0))
  /-- Bring module `m` into `s`: elaborate it in isolation first if the cache has not
  seen it, then replay it from the cache. -/
  importModule (keys : IO.Ref (Std.HashMap Name Key)) (base : CommandState R) (stack : List Name)
      (s : CommandState R) (m : Name) (src : String) : IO (CommandState R × Nat) := do
    let k ← keyOf keys m
    -- (the module's output manifest, if a layer has one: its entries gate the text and
    -- region lookups below)
    if let some ms := store.manifests then ms.load k
    -- (`--region-cache`) the module's artifact: one region for all its cacheable commands
    let region₀ ← store.getRegion k
    store.countRegion region₀.isSome
    -- with the region cache on, a warm module without an artifact is elaborated in
    -- isolation once more (from its `.wizc` entries) to write it: one extra pass, once
    -- (likewise a module with no valid manifest: one pass writes its manifest)
    let needManifest ← match store.manifests with
      | some ms => do pure (ms.write.isSome && !(← ms.validFor k))
      | none => pure false
    let rebuild := (store.region.isSome && region₀.isNone) || needManifest
    let fresh ← if (← store.seen k) && !rebuild then pure none else do
      let sink : Option (RegionSink R) ←
        if store.region.isSome || store.manifests.isSome then
          pure (some { module := m, effects := ← IO.mkRef #[], keys := ← IO.mkRef #[],
                       rerun := ← IO.mkRef #[], region := store.region.isSome,
                       entries := ← IO.mkRef #[] })
        else pure none
      let (_, h) ← go keys base (m :: stack) src { base with imported := [m], messages := #[], module := m } k .write k none sink
      store.markSeen k m
      pure (some h)
    -- (the isolated run above wrote the artifact if it was missing or unusable)
    let region ← if region₀.isSome then pure region₀ else if rebuild then store.getRegion k else pure none
    -- (a manifested entry that failed its digest is repaired by one more isolated pass,
    -- which can write; a replay must not write effects that could depend on the importer)
    let brokenBefore ← match store.manifests with
      | some ms => ms.broken.get
      | none => pure 0
    -- (the command loop still runs: imports, keys and duplicate checks are unchanged; the
    -- effects come from the region when it has them)
    let (s', h) ← go keys base (m :: stack) src { s with imported := m :: s.imported, messages := #[], module := m } k .replay k region
    let brokenAfter ← match store.manifests with
      | some ms => ms.broken.get
      | none => pure brokenBefore
    if brokenAfter > brokenBefore then
      match store.manifests with
      | some ms =>
        if ms.write.isSome then
          let sink : Option (RegionSink R) ←
            if store.region.isSome then
              pure (some { module := m, effects := ← IO.mkRef #[], keys := ← IO.mkRef #[],
                           rerun := ← IO.mkRef #[], region := true,
                           entries := ← IO.mkRef #[] })
            else pure none
          let _ ← go keys base (m :: stack) src { base with imported := [m], messages := #[], module := m } k .write k none sink
          pure ()
      | none => pure ()
    -- after a fresh isolated run, the hits are that run's (the replay reads what it wrote)
    pure (s', fresh.getD h)
  go (keys : IO.Ref (Std.HashMap Name Key)) (base : CommandState R) (stack : List Name) (input : String)
      (s₀ : CommandState R) (key₀ : Key) (mode : Mode) (mkey : Key)
      (region : Option (ModuleArtifact R) := none) (sink : Option (RegionSink R) := none) :
      IO (CommandState R × Nat) := do
    let chars := input.toList.toArray
    let mut pos := 0
    let mut s := s₀
    let mut key := key₀
    let _ : Inhabited (CommandState R) := ⟨init⟩
    let mut hits := 0
    -- (`complete` in the artifact: every command is cacheable, so the region could replace
    -- the loop; commit 3 uses it)
    let mut allCacheable := true
    -- (a parse error or an aborted module: no region is written for it)
    let mut aborted := false
    -- (which effect in the module's region is next; imports and non-cacheable commands
    -- don't consume one)
    let regionIdx ← IO.mkRef 0
    while skipWs chars pos < chars.size do
      match parseCommand chars s.tables pos with
      | .error _ =>
        aborted := true
        -- report the parse error (and everything after it) without the cache
        s := runFrontend.go input base chars pos s
        break
      | .ok (cmd, stop) =>
        let text := String.ofList (chars.extract pos stop).toList
        key := key.mixText text
        if cmd.isOfKind "command.import" then
          allCacheable := false
          if let some sink := sink then sink.rerun.modify (·.push (pos, stop))
          let m := ((cmd.getArg 1).getId?).getD "_"
          -- what the rest of the file sees depends on the module's text, through its key
          key := key.mixKey (← keyOf keys m)
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
                unless stack.isEmpty do
                  aborted := true
                  break
              else
              s := { inner with messages := (if errs.isEmpty then s.messages else s.messages.push msg) ++ warns,
                                module := s.module, infos := s.infos }
          pos := stop
          continue
        let cacheable? := cacheable.contains cmd.kind
        unless cacheable? do
          allCacheable := false
          if let some sink := sink then sink.rerun.modify (·.push (pos, stop))
        let cached : Option (CacheHit R) ←
          if !cacheable? then pure none
          else match region with
            -- (`--region-cache`: the module's region holds the effects in command order;
            -- the chained key at each command is checked, so a parse that diverges from
            -- the isolated run's — an importer's extra syntax — falls back to the text)
            | some a => do
              let i ← regionIdx.get
              regionIdx.set (i + 1)
              match a.keys[i]?, a.effects[i]? with
              | some k', some e =>
                if k' == key.fast then do
                  store.countRegionCommand
                  pure (some (e, none))
                else
                  store.getEntry key
              | _, _ => store.getEntry key
            | none => store.getEntry key
        match cached with
        | some (e, hit) =>
          if let some sink := sink then do
            sink.effects.modify (·.push e)
            sink.keys.modify (·.push key.fast)
            -- (a manifest entry from the write cache is local: the module manifest keeps it)
            if let some (ent, dir) := hit then
              match store.manifests with
              -- (a legacy fast-only hit has no SHA-256 key to put in a format-2 manifest)
              | some ms => if ms.inWrite dir && ent.keySha.length == 64 then
                  sink.entries.modify (·.push ent)
              | none => pure ()
          s := e.apply s
          hits := hits + 1
        | none =>
          let s' := Query.elaborate.elabOne input base chars pos stop s
          if cacheable? && mode matches .write then
            let e := effectOf s s'
            store.put key e
            if let some sink := sink then do
              sink.effects.modify (·.push e)
              sink.keys.modify (·.push key.fast)
              if store.manifests.isSome then
                sink.entries.modify (·.push (ManifestEntry.ofEffect store.binary key e))
          s := s'
        pos := stop
    -- (write the module's region after a complete isolated run; a manifest is written even
    -- for an aborted run: the entries before a parse error were elaborated and their bytes
    -- are valid, and without a manifest every run re-elaborated the file's whole prefix)
    if let some sink := sink then
      let regionEntry ←
        if sink.region && !aborted then
          store.putRegion { magic := regionMagic, format := regionFormat, module := sink.module,
                            key := key₀.fast, keySha := key₀.strong,
                            binarySha := key₀.binary, toolchainSha := key₀.toolchain,
                            targetSha := key₀.target,
                            effects := ← sink.effects.get, keys := ← sink.keys.get,
                            complete := allCacheable, rerun := ← sink.rerun.get }
        else pure none
      if let some ms := store.manifests then
        -- (the root pseudo-module's manifest is per root file: `mkey` has the file's text)
        ms.writeManifest mkey sink.module (← sink.entries.get) regionEntry
          (merge := (toString sink.module).isEmpty)
    pure (s, hits)

/-- `elaborateWith`, through the layered cache: `write` is the directory that is written
(none: no writes), `reads` are read-only directories searched after it, in order. As this
binary (`binaryId` of `write`) unless `binary` says otherwise (tests). With `region`, module
effects are also served from `<dir>/<fast key>.<SHA-256 key>.wizr` (`--region-cache`): the
regions live in the same layers, are read from the write cache first and then from the
read-only caches, and are only written to the write cache. With `verify`, output manifests
are written to the write cache and checked on load (`rig` is the rig's tag).
`strongToolchain`/`targetTag` are the SHA-256 namespaces (`Toolchain.tag`,
`Toolchain.targetTag`); `rootTag` is a strong version of `key₀` (the root file's headers),
so a root manifest is bound to its actual inputs too. `rootPath` is the root file's path,
used only for the manifest pointer an edit follows to keep its unchanged prefix warm. -/
def elaborateCached (write : Option System.FilePath) (reads : List System.FilePath)
    (input : String) (init : CommandState R) (key₀ : UInt64)
    (toolchain : UInt64 := 0) (binary : Option UInt64 := none)
    (region : Option RegionOptions := none) (verify : VerifyMode := .off) (rig : String := "")
    (stats : Option (IO.Ref VerifyCounts) := none)
    (strongToolchain : String := "") (targetTag : String := "") (rootTag : String := "")
    (rootPath : String := "") :
    IO (CommandState R × Nat) := do
  let binary ← match binary with | some b => pure b | none => binaryId write
  let binaryTag ← if region.isSome || verify != .off then toolchainTag write else pure ""
  -- (13b) `--trace-guess-fallback` reports from the elaborator: nothing may come from a cache
  let store ← if ← traceGuessesRef.get then Store.memory else match region with
    | some opts => Store.layeredRegion write reads binary opts verify rig stats
    | none => Store.layered write reads binary verify rig stats
  -- (the layer's `manifest.sexpr` is not refreshed here: rebuilding it reads and
  -- re-validates every manifest in the layer, which is O(cache) per run — about a minute
  -- on a shared cache of thousands of manifests. Nothing a run does reads its module
  -- list (only its expiry, which a run never changes); `wiz cache manifest` rebuilds it.
  -- `agent/cold-check` 7ecc48b2 made the same change; this branch keeps it while fixing
  -- the root manifest's key.)
  elaborateWith store input init key₀ toolchain strongToolchain targetTag rootTag binaryTag rootPath

/-- `elaborateWith`, without a cache: modules are elaborated in isolation all the same. -/
def elaborateUncached (input : String) (init : CommandState R) (toolchain : UInt64 := 0)
    (strongToolchain : String := "") (targetTag : String := "") (rootTag : String := "") :
    IO (CommandState R) := do
  pure (← elaborateWith (← Store.memory) input init 0 toolchain strongToolchain targetTag rootTag).1

end Wiz.Cache
