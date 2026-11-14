import Wiz
import Tests.Harness
import Tests.Elab
import Grail

/-!
# `native_refl` and `--trust-native` (stage 27a)

The group `native`: closed equations decided by running them, only with the flag, with
an axiom per use that `#print axioms` lists together with the native implementations
the run can reach; never in the library; and cache entries that never cross the flag.

The group also checks the **trust ledger** (`scripts/trust-ledger.sh`,
`.github/trust-baseline.tsv`): every declaration of `lib/` is run through
`#print axioms`, and a source of trust that is not in the checked-in baseline — an
axiom, `sorry`, `native_refl`, `implemented_by`/`repr:`, SMT or `builtin`
registration, or a `partial` definition — fails until it is reviewed and the baseline
is regenerated. The `hdl-verified` group checks the axiom-free example the same way.
-/

open Wiz

set_option compiler.extract_closed false

namespace Tests.Native

/-- Every message of `input` (`severity: text`), with `lib/`'s Prelude, Word, Logic, …
importable, with or without `--trust-native`. -/
def msgs (input : String) (trust : Bool := true) : IO (List String) := do
  let loader ← Elab.preludeLoader
  let s := runFrontend (R := ZeroOneMany) input { loader, trustedModule := Tests.libModule, trustNative := trust }
  pure (s.messages.toList.map fun m =>
    s!"{match m.severity with | .error => "error" | .warning => "warning" | .info => "info"}: {m.text}")

/-- `msgs` with every module of `lib/` importable (Hdl.Verified, …). -/
def msgsLibs (input : String) (trust : Bool := true) : IO (List String) := do
  let loader ← Elab.libLoader
  let s := runFrontend (R := ZeroOneMany) input { loader, trustedModule := Tests.libModule, trustNative := trust }
  pure (s.messages.toList.map fun m =>
    s!"{match m.severity with | .error => "error" | .warning => "warning" | .info => "info"}: {m.text}")

def has (ms : List String) (fragment : String) : Bool := ms.any fun m => (m.splitOn fragment).length > 1

def expect (ms : List String) (fragment : String) : IO Unit :=
  unless has ms fragment do throw (IO.userError s!"no message mentions '{fragment}':\n{"\n".intercalate ms}")

def noErrors (ms : List String) : IO Unit := do
  let errs := ms.filter (·.startsWith "error")
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs}")

def sumTo : String :=
  "import Prelude\ndef sumTo : Nat → Nat\n  | .zero => 0\n  | .succ n => Nat.add (Nat.succ n) (sumTo n)\n"

/-- A 16-bit linear congruential generator, iterated: `n` steps of word arithmetic. The
kernel takes seconds for this many steps (it unfolds `UIntN`'s model on every step);
the interpreter a fraction of one. -/
def lcg : String :=
  "import Prelude\nimport Word\n" ++
  "def step (x : UIntN 16) : UIntN 16 := UIntN.add (UIntN.mul x (UIntN.ofNat 16 25173)) (UIntN.ofNat 16 13849)\n" ++
  "def iter : Nat → UIntN 16 → UIntN 16\n  | .zero, x => x\n  | .succ k, x => iter k (step x)\n"

/-- The value `iter n 1` computes, by Lean's arithmetic. -/
def lcgValue (n : Nat) : Nat := Id.run do
  let mut x := 1
  for _ in [0:n] do x := (x * 25173 + 13849) % 65536
  pure x

/-- Elaborate `input` with `M` importable as `modSrc`, through `store`. -/
def viaStore (store : Cache.Store ZeroOneMany) (modSrc input : String) (trust : Bool) : IO (List String) := do
  let pre ← Elab.preludeLoader
  let loader (m : Name) := if m == "M" then some modSrc else pre m
  let (s, _) ← Cache.elaborateWith store input { loader, trustedModule := fun m => m != "" && m != "M", trustNative := trust } 0
  pure (s.messages.toList.map fun m =>
    s!"{match m.severity with | .error => "error" | .warning => "warning" | .info => "info"}: {m.text}")

/-- Every `.wiz` file under `dir`. -/
partial def wizFiles (dir : System.FilePath) : IO (List System.FilePath) := do
  let mut out := []
  for e in ← dir.readDir do
    if ← e.path.isDir then out := out ++ (← wizFiles e.path)
    else if e.path.extension == some "wiz" then out := e.path :: out
  pure out

/-! ## The trust ledger

A checked-in baseline of the **trusted base** of `lib/` (`.github/trust-baseline.tsv`):
every declaration the kernel does not check, and every registration that decides how a
definition computes. `#print axioms` is still run on every declaration (as the case
below always did), and every axiom it lists must be one of the ledger's sources; the
baseline then makes a *new* source — a new `axiom`, `native_refl`, SMT answer,
`implemented_by`, `builtin` or `partial` definition — a test failure that a reviewer must
approve by updating the file.

The ledger records sources, not every dependency edge: a new theorem that uses
`castRefl` doesn't add a line (the axiom was already trusted), while a new
`implemented_by` or a new use of `native_refl`/`smt` (each introduces a declaration of
its own) does. See `scripts/trust-ledger.sh` and the header of
`.github/trust-baseline.tsv`. -/

/-- A source of trust: the module (or example file) that declares it, the declaration it
belongs to, and the words `#print axioms` uses for it. -/
structure TrustSource where
  module : String
  name : String
  item : String
  deriving Repr, BEq, Inhabited

def TrustSource.line (t : TrustSource) : String :=
  s!"{t.module}\t{t.name}\t{t.item}"

/-- Is `n` the axiom a `native_refl` added (`f.native✝`)? -/
def isNativeReflAxiom (n : Name) : Bool := n.endsWith ".native✝"

/-- Is `n` an axiom an `smt` answer added (`f.smt✝k⟨solver⟩`)? -/
def isSmtAxiom (n : Name) : Bool := (n.splitOn ".smt✝").length > 1

/-- The module a declaration was made in, for the ledger's label. A `private`
declaration is re-inserted under `_private.M._0.name` after elaboration, and
`Globals.renamePrivate` does not rewrite `declModule`; read the module from the name
then. -/
def trustModuleOf (g : Globals ZeroOneMany) (n : Name) : String :=
  match g.declModule[n]? with
  | some m => m
  | none =>
    if n.startsWith "_private." then
      match (n.drop "_private.".length).toString.splitOn "._0." with
      | m :: _ => m
      | [] => "(no module)"
    else "(no module)"

/-- The trusted base of `g`: one entry per declaration that is an axiom (no value, no
witness), a `partial` definition (its body is compiled, not unfolded), a native
implementation (`implemented_by`, and a type's `repr:` representation), a `native_refl`
or `smt` axiom, and one per `builtin` registration. `only` restricts it to a scope (an
example's own declarations). -/
def trustSources (g : Globals ZeroOneMany) (labelOf : Name → String)
    (only : Name → Bool := fun _ => true) : List TrustSource := Id.run do
  let mut out : Array TrustSource := #[]
  for n in g.order do
    if !only n then continue
    let some d := g.find? n | continue
    let m := labelOf n
    if isNativeReflAxiom n then
      out := out.push { module := m, name := n, item := s!"native_refl {n}" }
    else if isSmtAxiom n then
      out := out.push { module := m, name := n, item := s!"smt {n}" }
    else if d.value.isNone && d.witness.isNone then
      -- `axiom`, `extern`, a `foreign` type, a seal (`T.seal✝`)
      out := out.push { module := m, name := n, item := s!"axiom {n}" }
    if d.witness.isSome then
      out := out.push { module := m, name := n, item := "partial" }
    if let some i := d.nativeImpl? then
      out := out.push { module := m, name := n, item := s!"native {n} := {i}" }
  -- every registration, including `repr:` (a type's native representation) and `seal:`;
  -- `inline` (a compiler hint) and `int` (only how values print) are not trust
  for (k, nm) in g.builtins do
    if k == "inline" || k == "int" then continue
    if !only nm then continue
    let m := labelOf nm
    let item := match k.splitOn ":" with
      | "repr" :: T :: mk :: get :: _ => s!"native {T} := {mk}/{get}"
      | _ => s!"builtin {k} := {nm}"
    out := out.push { module := m, name := nm, item }
  return out.toList

/-- Every trust `#print axioms` lists for the declarations in `only` is one of
`sources`: the walk over the whole environment is what makes the ledger a *ledger* and
not just a grep; a trust the source list misses is reported. -/
def checkCovered (g : Globals ZeroOneMany) (sources : List TrustSource)
    (only : Name → Bool := fun _ => true) : IO Unit := do
  let keys := sources.foldl (fun s t => s.insert t.item) ({} : Std.HashSet String)
  for n in g.order do
    if !only n then continue
    for a in g.axiomsOf n do
      -- `inline` and `int` registrations are not trust (see `trustSources`)
      if a.startsWith "builtin inline " || a.startsWith "builtin int " then continue
      let key :=
        if a.startsWith "builtin " || a.startsWith "native " then a
        else if isNativeReflAxiom a then s!"native_refl {a}"
        else if isSmtAxiom a then s!"smt {a}"
        else s!"axiom {a}"
      unless keys.contains key do
        throw (IO.userError s!"{n}: `#print axioms` lists '{a}', which is not a source in the trust ledger")

/-- Is the identifier `sorry` in `src`, outside comments and strings? Returns its
offsets. Wiz has no `sorry` keyword on this branch, so a use is a parse error anyway;
the check makes it a trust-ledger failure with a clear message (and covers an exercise
tree or a future keyword that would parse it). -/
partial def sorryOffsets (src : String) : List Nat :=
  let a := src.toList.toArray
  let n := a.size
  let rec strEnd (j : Nat) : Nat :=
    if j >= n then j
    else if a[j]! == '\\' then strEnd (j + 2)
    else if a[j]! == '"' then j + 1
    else strEnd (j + 1)
  let rec identEnd (j : Nat) : Nat := if j < n && isIdRest a[j]! then identEnd (j + 1) else j
  let isSorry (i j : Nat) : Bool :=
    j - i == 5 && a[i]! == 's' && a[i+1]? == some 'o' && a[i+2]? == some 'r' &&
      a[i+3]? == some 'r' && a[i+4]? == some 'y'
  let rec go (i : Nat) (acc : List Nat) : List Nat :=
    let i := skipWs a i
    if i >= n then acc.reverse
    else if a[i]! == '"' then go (strEnd (i + 1)) acc
    else if isIdStart a[i]! then
      let j := identEnd (i + 1)
      go j (if isSorry i j then i :: acc else acc)
    else go (i + 1) acc
  go 0 []

/-- The line (1-based) of character offset `off`. -/
def lineOf (src : String) (off : Nat) : Nat :=
  (String.ofList (src.toList.take off)).splitOn "\n" |>.length

/-- The examples that are meant to be axiom-free (kernel-checked, nothing trusted):
their own declarations must add no trust. `examples/hdl-verified.wiz` is checked by the
`hdl-verified` group too; `-native`/`-full` are deliberately trusted and are not here. -/
def trustLedgerExamples : List String := ["examples/hdl-verified.wiz"]

/-- The state of importing every module of `lib/`, as `wiz check` does (the toolchain's
library trusted). Both trust extensions are on so that a use is *recorded* by the
ledger rather than merely an error; `lib/` is not allowed to use either (the cases below
and `lib/ never uses native_refl` still fail on a use). -/
def libTrustState : IO (CommandState ZeroOneMany) := do
  let files ← wizFiles "lib"
  let mods := files.filterMap fun f => do
    let cs := (f.toString.toList.drop 4)
    pure ((String.ofList (cs.take (cs.length - 4))).replace "/" ".")
  let mods := mods.toArray.qsort (· ≤ ·) |>.toList
  let input := String.join (mods.map (s!"import {·}\n"))
  pure (runFrontend (R := ZeroOneMany) input
    { loader := ← Elab.libLoader, trustedModule := Tests.libModule
      trustNative := true, smt := { trust := true } })

/-- The state of elaborating `path` (an example) with every library module importable. -/
def exampleTrustState (path : String) : IO (CommandState ZeroOneMany) := do
  let input ← IO.FS.readFile path
  pure (runFrontend (R := ZeroOneMany) input
    { loader := ← Elab.libLoader, trustedModule := Tests.libModule
      trustNative := true, smt := { trust := true } })

def noTrustErrors (what : String) (s : CommandState ZeroOneMany) : IO Unit := do
  let errs := s.messages.filter (·.severity == .error)
  unless errs.isEmpty do
    throw (IO.userError s!"{what} has errors:\n{"\n".intercalate (errs.toList.map (·.text))}")

/-- Reject `sorry` anywhere in `files`. -/
def rejectSorry (files : List System.FilePath) : IO Unit := do
  for f in files do
    let src ← IO.FS.readFile f
    match sorryOffsets src with
    | [] => pure ()
    | off :: _ => throw (IO.userError s!"{f}:{lineOf src off}: `sorry` is not checked by the kernel; it is never allowed in the trusted base")

/-- The ledger's lines: `module<TAB>declaration<TAB>item`, sorted and deduplicated. With
`includeExamples`, the axiom-free examples' own declarations are included too. -/
def ledgerLines (includeExamples : Bool) : IO (List String) := do
  let libFiles ← wizFiles "lib"
  rejectSorry libFiles
  let s ← libTrustState
  noTrustErrors "the library" s
  check (s.globals.order.size > 1000) s!"only {s.globals.order.size} library declarations"
  let libLabel (n : Name) : String := trustModuleOf s.globals n
  let libSources := trustSources s.globals libLabel
  checkCovered s.globals libSources
  let mut sources := libSources
  if includeExamples then
    for path in trustLedgerExamples do
      rejectSorry [path]
      let es ← exampleTrustState path
      noTrustErrors path es
      let own (n : Name) : Bool := es.globals.declModule[n]?.isNone
      let labelOf (n : Name) : String := if own n then path else ""
      let ownSources := (trustSources es.globals labelOf own)
      -- an example's declarations may depend on the library's trusted base, so the
      -- walk checks against both; its own sources are what the baseline would gain
      checkCovered es.globals (libSources ++ ownSources) own
      sources := sources ++ ownSources
  let lines := (sources.map TrustSource.line).toArray.qsort (· ≤ ·) |>.toList.eraseDups
  pure lines

def trustBaseline : System.FilePath := ".github/trust-baseline.tsv"

def trustBaselineHeader : String :=
  "# The Wiz trust ledger: the trusted base of lib/ (and the axiom-free examples).\n" ++
  "# One line per source of trust: module<TAB>declaration<TAB>item.  `item` is the wording\n" ++
  "# of `#print axioms` (`axiom X`, `native f := g` for implemented_by, `native T := mk/get`\n" ++
  "# for a repr registration, `native_refl X.native✝`, `smt X.smt✝…`, `builtin k := n`), or\n" ++
  "# `partial` for a partial definition (its body is compiled, not unfolded).\n" ++
  "# `builtin inline` (a compiler hint) and `builtin int` (how values print) are not\n" ++
  "# trust and are not listed. A new line fails the `native` group (and\n" ++
  "# scripts/trust-ledger.sh): review it, then regenerate this file with\n" ++
  "# `scripts/trust-ledger.sh --update`.\n"

def readTrustBaseline : IO (List String) := do
  unless ← trustBaseline.pathExists do
    throw (IO.userError s!"no {trustBaseline}: run scripts/trust-ledger.sh --update")
  let text ← IO.FS.readFile trustBaseline
  pure (text.splitOn "\n" |>.map (·.trimAsciiEnd.toString) |>.filter fun l => !l.isEmpty && !l.startsWith "#")

/-- The baseline lines in the scope of `includeExamples`: without examples, the lines
labelled with an example path are left out (the `native` group checks `lib/` alone; the
`hdl-verified` group checks the example in its own heavy case). -/
def baselineFor (lines : List String) (includeExamples : Bool) : List String :=
  if includeExamples then lines
  else lines.filter fun l => !(((l.splitOn "\t").headD "").startsWith "examples/")

/-- Compare `actual` with `baseline`, failing on either a new trust (the security
relevant direction) or a stale baseline entry. -/
def compareTrust (what : String) (actual baseline : List String) : IO Nat := do
  let added := actual.filter fun l => !baseline.contains l
  let removed := baseline.filter fun l => !actual.contains l
  if !added.isEmpty || !removed.isEmpty then
    let fmt (sign : String) (ls : List String) : String :=
      "\n" ++ "\n".intercalate (ls.map fun l => s!"  {sign} {l.replace "\t" " | "}")
    let parts :=
      (if added.isEmpty then "" else s!"\nnew trust ({added.length}):{fmt "+" added}") ++
      (if removed.isEmpty then "" else s!"\nstale baseline ({removed.length}; regenerate the file):{fmt "-" removed}")
    throw (IO.userError s!"{what} changed ({actual.length} items, baseline {baseline.length}):{parts}\n\nreview each new trust, then run scripts/trust-ledger.sh --update")
  pure baseline.length

/-- Check the ledger against `.github/trust-baseline.tsv`; returns its item count. -/
def checkTrustLedger (includeExamples : Bool := true) : IO Nat := do
  let actual ← ledgerLines includeExamples
  compareTrust "the trust ledger" actual (baselineFor (← readTrustBaseline) includeExamples)

/-- Check one axiom-free example's own declarations against its part of the baseline,
from the state a case already elaborated (no second elaboration). -/
def checkExampleTrustLedger (path : String) (g : Globals ZeroOneMany) : IO Nat := do
  let own (n : Name) : Bool := g.declModule[n]?.isNone
  let libLabel (n : Name) : String := trustModuleOf g n
  let libSources := trustSources g libLabel (fun n => !own n)
  let labelOf (n : Name) : String := if own n then path else ""
  let ownSources := trustSources g labelOf own
  checkCovered g (libSources ++ ownSources) own
  let actual := (ownSources.map TrustSource.line).toArray.qsort (· ≤ ·) |>.toList.eraseDups
  let baseline := (← readTrustBaseline).filter fun l => ((l.splitOn "\t").headD "") == path
  compareTrust path actual baseline

def updateTrustLedger (includeExamples : Bool) : IO Unit := do
  let lines ← ledgerLines includeExamples
  IO.FS.writeFile trustBaseline (trustBaselineHeader ++ "\n".intercalate lines ++ "\n")
  IO.println s!"wrote {trustBaseline} ({lines.length} items)"

/-- `tests --trust-ledger [--check|--update|--print] [--lib-only]` (`scripts/trust-ledger.sh`). -/
def trustLedgerMain (args : List String) : IO UInt32 := do
  let known := ["--check", "--update", "--print", "--lib-only"]
  let bad := args.filter fun a => !known.contains a
  unless bad.isEmpty do
    IO.eprintln s!"usage: tests --trust-ledger [--check|--update|--print] [--lib-only] (unknown: {" ".intercalate bad})"
    return 2
  let includeExamples := !args.contains "--lib-only"
  if args.contains "--update" then
    if !includeExamples then
      IO.eprintln "trust-ledger: --update always includes the examples (they are part of the ledger)"
      return 2
    updateTrustLedger true
    return 0
  if args.contains "--print" then
    for l in ← ledgerLines includeExamples do IO.println l
    return 0
  try
    let n ← checkTrustLedger includeExamples
    IO.println s!"trust ledger: OK ({n} sources in the checked scope)"
    return 0
  catch e =>
    IO.eprintln e
    return 1

def group : Group where
  name := "native"
  parallel := true
  exercise := "—"
  cases := [
    { name := "accepted with --trust-native: numbers, lists, a declaration that uses it", run := fun _ => do
        let ms ← msgs (sumTo ++
          "def s100 : sumTo 100 = 5050 := native_refl\n" ++
          "def l : List.cons (sumTo 3) List.nil = List.cons 6 List.nil := native_refl\n" ++
          "def both : sumTo 20 = Nat.add (sumTo 19) 20 := native_refl\n" ++
          "def use : sumTo 100 = 5050 := s100\n")
        noErrors ms
        expect ms "s100 is accepted on the strength of native evaluation" },
    { name := "word arithmetic, many steps (slow for the kernel, fast natively)", run := fun _ => do
        let ms ← msgs (lcg ++ s!"def it : iter 20000 (UIntN.ofNat 16 1) = UIntN.ofNat 16 {lcgValue 20000} := native_refl\n#print axioms it\n")
        noErrors ms
        expect ms "'it' depends on axioms: [it.native✝" },
    { name := "a word read back with its range proof, marked (#145 × #128)", run := fun _ => do
        -- a word carries an erased proof `toNat < 2^w`: the read-back builds it, and the
        -- marking pass marks it (`prf`) before the kernel checks the value
        let ms ← msgs ("import Prelude\nimport Word\n" ++
          "def w : UIntN.add (UIntN.ofNat 8 200) (UIntN.ofNat 8 100) = UIntN.ofNat 8 44 := native_refl\n" ++
          "def p : (UIntN.mul (UIntN.ofNat 8 16) (UIntN.ofNat 8 16), UIntN.ofNat 4 15) = (UIntN.ofNat 8 0, UIntN.max 4) := native_refl\n" ++
          "#print axioms w\n")
        noErrors ms
        expect ms "'w' depends on axioms: [w.native✝"
        let ms ← msgs ("import Prelude\nimport Word\n" ++
          "def w : UIntN.add (UIntN.ofNat 8 200) (UIntN.ofNat 8 100) = UIntN.ofNat 8 45 := native_refl\n")
        expect ms "native evaluation refutes it" },
    { name := "rejected without --trust-native", run := fun _ => do
        let ms ← msgs (sumTo ++ "def s : sumTo 4 = 10 := native_refl\n") (trust := false)
        expect ms "error: native evaluation is not enabled"
        expect ms "--trust-native" },
    { name := "a false equation is refuted", run := fun _ => do
        let ms ← msgs (sumTo ++ "def bad : sumTo 10 = 54 := native_refl\n")
        expect ms "error: native_refl: native evaluation refutes it: the left-hand side is 55, the right-hand side 54"
        let ms ← msgs (lcg ++ s!"def bad : iter 1000 (UIntN.ofNat 16 1) = UIntN.ofNat 16 {lcgValue 1000 + 1} := native_refl\n")
        expect ms "error: native_refl: native evaluation refutes it" },
    { name := "only first-order data: functions and types are refused", run := fun _ => do
        let ms ← msgs (sumTo ++ "def f : (fun (x : Nat) => x) = (fun (x : Nat) => sumTo x) := native_refl\n")
        expect ms "error: native_refl: native_refl compares first-order data; Nat → Nat is not"
        let ms ← msgs (sumTo ++ "def t : Nat = Nat := native_refl\n")
        expect ms "is not (a function, codata or a type)"
        -- a field of quantity 0 is not there at run time: it can't be compared
        let ms ← msgs (sumTo ++ "inductive E where\n  | mk (0 n : Nat)\ndef e : E.mk 1 = E.mk 1 := native_refl\n")
        expect ms "quantity 0" },
    { name := "only as the whole body of a closed definition", run := fun _ => do
        expect (← msgs (sumTo ++ "def p (n : Nat) : sumTo n = sumTo n := native_refl\n")) "native_refl proves a closed equation"
        expect (← msgs (sumTo ++ "def q : sumTo 3 = 6 := (native_refl : sumTo 3 = 6)\n")) "native_refl can only be the whole body of a definition"
        expect (← msgs (sumTo ++ "def r : Nat := native_refl\n")) "native_refl proves an equation `a = b`" },
    { name := "#print axioms: the native axiom, also of what uses it", run := fun _ => do
        let ms ← msgs (sumTo ++ "def s100 : sumTo 100 = 5050 := native_refl\ndef use : sumTo 100 = 5050 := s100\n" ++
          "#print axioms s100\n#print axioms use\n#print axioms sumTo\n")
        noErrors ms
        expect ms "info: 's100' depends on axioms: [s100.native✝]"
        expect ms "info: 'use' depends on axioms: [s100.native✝]"
        expect ms "native_refl, --trust-native"
        expect ms "info: 'sumTo' does not depend on any axioms" },
    { name := "a wrong implemented_by proves a false equation, and #print axioms names it", run := fun _ => do
        -- the adversary: `f`'s compiled code is `g`, which disagrees with it. The kernel
        -- refutes `f 1 = 3` (`refl` fails); native evaluation runs `g` and accepts it.
        -- That is what `--trust-native` trusts, and `#print axioms` says so.
        let src := sumTo ++ "def f (n : Nat) : Nat := Nat.succ n\ndef g (n : Nat) : Nat := Nat.add n 2\n" ++
          "attribute [implemented_by g] f\n" ++
          "def lie : f 1 = 3 := native_refl\n#print axioms lie\n"
        let ms ← msgs src
        noErrors ms
        expect ms "info: 'lie' depends on axioms: [lie.native✝, native f := g]"
        -- the kernel alone refutes it
        let ms ← msgs (sumTo ++ "def f (n : Nat) : Nat := Nat.succ n\ndef g (n : Nat) : Nat := Nat.add n 2\n" ++
          "attribute [implemented_by g] f\ndef lie : f 1 = 3 := refl 3\n")
        check (has ms "error") s!"the kernel accepted f 1 = 3: {ms}"
        -- and what the implementation's code reaches is listed too: here `g` is itself
        -- implemented by `h` (the run executes `h`)
        let ms ← msgs (sumTo ++ "def f (n : Nat) : Nat := Nat.succ n\ndef g (n : Nat) : Nat := Nat.succ n\n" ++
          "def h (n : Nat) : Nat := Nat.add n 2\nattribute [implemented_by h] g\nattribute [implemented_by g] f\n" ++
          "def lie : f 1 = 3 := native_refl\n#print axioms lie\n")
        noErrors ms
        expect ms "native g := h"
        -- (t1-review L2) a three-link chain a1 → a2 → a3 → a4, and what the last one uses
        let ms ← msgs (sumTo ++ "axiom k : Nat\ndef a1 (n : Nat) : Nat := n\ndef a2 (n : Nat) : Nat := n\n" ++
          "def a3 (n : Nat) : Nat := n\ndef a4 (n : Nat) : Nat := Nat.add n k\n" ++
          "attribute [implemented_by a4] a3\nattribute [implemented_by a3] a2\nattribute [implemented_by a2] a1\n" ++
          "def u : Nat := a1 2\n#print axioms u\n")
        noErrors ms
        expect ms "native a1 := a2"
        expect ms "native a2 := a3"
        expect ms "native a3 := a4"
        check (has ms ", k]" || has ms ", k," || has ms "[k,") s!"the last link's axiom k is not listed: {ms}" },
    { name := "a foreign constant has no value here (trust-review N1)", run := fun _ => do
        -- `getpid` is not 0: reading a foreign constant as 0 would prove `pid = 0`
        let ms ← msgs (sumTo ++ "extern \"getpid\" pid : Nat\ndef pidIsZero : pid = 0 := native_refl\n")
        expect ms "error: native_refl: native evaluation failed: pid is a foreign constant"
        let ms ← msgs (sumTo ++ "extern \"wiz_flag\" flag : Bool\ndef f : flag = Bool.false := native_refl\n")
        expect ms "is a foreign constant" },
    { name := "a huge power is an error, not a panic (trust-review N2)", run := fun _ => do
        let ms ← msgs (sumTo ++ "def huge : Nat.beq (Nat.pow 2 (Nat.pow 2 40)) 0 = Bool.false := native_refl\n")
        expect ms "nat.pow: the result would have more than" },
    { name := "an erased proof field is built and checked; an erased data field is refused (AB1)", run := fun _ => do
        -- the shape of a word with its range proof (PR #145)
        let small := sumTo ++ "inductive Small where\n  | mk (n : Nat) (0 h : Nat.lt n 10 = .true)\n" ++
          "def three : Small := Small.mk 3 (refl Bool.true)\n"
        let ms ← msgs (small ++ "def s : three = Small.mk (sumTo 2) (refl Bool.true) := native_refl\n" ++
          "def l : List.cons three List.nil = List.cons three List.nil := native_refl\n")
        noErrors ms
        let ms ← msgs (small ++ "def s : three = Small.mk 4 (refl Bool.true) := native_refl\n")
        expect ms "native evaluation refutes it"
        -- an erased field that is data: the two sides could differ there
        let ms ← msgs (sumTo ++ "inductive E where\n  | mk (m : Nat) (0 n : Nat)\ndef e : E.mk 1 2 = E.mk 1 3 := native_refl\n")
        expect ms "quantity 0" },
    { name := "a partial definition's implementation is not run", run := fun _ => do
        let ms ← msgs (sumTo ++ "partial def loop (n : Nat) : Nat := loop n\ndef l : loop 0 = 0 := native_refl\n")
        expect ms "reaches the partial definition loop" },
    { name := "the step limit (--native-fuel) ends a long run with a message", run := fun _ => do
        let loader ← Elab.preludeLoader
        let s := runFrontend (R := ZeroOneMany) (sumTo ++ "def s : sumTo 100000 = 5000050000 := native_refl\n")
          { loader, trustedModule := Tests.libModule, trustNative := true, nativeFuel := 1000 }
        let ms := s.messages.toList.map (·.text)
        expect ms "native evaluation did not finish within 1000 steps (raise the limit with --native-fuel N)" },
    { name := "the flags: wiz's and grail's toolchain take and pass on --trust-native", run := fun _ => do
        let (t, rest) := ({} : Toolchain).parseFlags ["--trust-native", "--native-fuel", "77", "check", "f.wiz"]
        check t.trustNative "--trust-native not taken"
        checkEq (some 77) t.nativeFuel
        checkEq ["check", "f.wiz"] rest
        check (t.toFlags.contains "--trust-native") "toFlags drops --trust-native"
        let (t', _) := ({} : Toolchain).parseFlags t.toFlags
        check (t'.trustNative && t'.nativeFuel == some 77) "toFlags does not round-trip"
        let (u, _) := ({} : Toolchain).parseFlags ["check", "f.wiz"]
        check (!u.trustNative && !(u.toFlags.contains "--trust-native")) "--trust-native is on by default"
        -- grail: a check with the flag is another job than one without
        let src := sumTo ++ "def s : sumTo 4 = 10 := native_refl\n"
        let a ← Grail.load {} ["lib"] 0 src
        let b ← Grail.load { trustNative := true } ["lib"] 0 src
        check (a.key != b.key) "grail's check key ignores --trust-native"
        check (b.init.trustNative && !a.init.trustNative) "grail does not pass --trust-native to the elaborator" },
    { name := "the cache: never replayed across the flag, re-decided when what it ran changes", run := fun _ => do
        let store ← Cache.Store.memory (R := ZeroOneMany)
        let modOk := "import Prelude\ndef f (n : Nat) : Nat := Nat.add n n\n"
        let modBad := "import Prelude\ndef f (n : Nat) : Nat := Nat.add n 1\n"
        let main := "import M\ndef x : f 2 = 4 := native_refl\n#print axioms x\n"
        noErrors (← viaStore store modOk main true)
        -- the same text without the flag: the acceptance is not replayed
        expect (← viaStore store modOk main false) "error: native evaluation is not enabled"
        -- and with it again: the error is not replayed either
        noErrors (← viaStore store modOk main true)
        -- the imported definition changed (so the code that ran): decided again
        expect (← viaStore store modBad main true) "native evaluation refutes it" },
    { name := "lib/ never uses native_refl", run := fun _ => do
        -- (lib/ is checked without --trust-native everywhere, so a use would be an error;
        -- the grep also catches a macro or deriver that would build one)
        for f in ← wizFiles "lib" do
          let src ← IO.FS.readFile f
          check ((src.splitOn "native_refl").length == 1 && (src.splitOn "nativeRefl").length == 1)
            s!"{f} mentions native_refl" },
    { name := "no library declaration depends on a native axiom", run := fun _ => do
        -- The trust ledger: every declaration of lib/ is run through `#print axioms`;
        -- each axiom listed must be a source in .github/trust-baseline.tsv, and a new
        -- source (axiom, `sorry`, native_refl, implemented_by, SMT, builtin, partial)
        -- fails. The examples that must be axiom-free are checked in `hdl-verified`.
        let _ ← checkTrustLedger (includeExamples := false)
        pure () }
  ]

/-- H14 V1 (docs/libraries.md): the OLED demo's arithmetic units, against their Nat
definitions. Slow (minutes: kernel evaluation over every input of each unit's domain,
and native_refl), so a group of its own, in a heavy shard. The 2^20-input checks,
examples/hdl-verified-full.wiz, are run on demand only. -/
def hdlVerifiedGroup : Group where
  name := "hdl-verified"
  exercise := "—"
  cases := [
    { name := "V1: kernel-checked on the units' domains, nothing trusted (examples/hdl-verified.wiz)", run := fun _ => do
        let path := "examples/hdl-verified.wiz"
        let s := runFrontend (R := ZeroOneMany) (← IO.FS.readFile path)
          { loader := ← Elab.libLoader, trustedModule := Tests.libModule }
        let ms := s.messages.toList.map fun m =>
          s!"{match m.severity with | .error => "error" | .warning => "warning" | .info => "info"}: {m.text}"
        noErrors ms
        expect ms "info: (20, 19)"
        if has ms "native" then throw (IO.userError s!"the kernel-checked file mentions native evaluation:\n{"\n".intercalate ms}")
        -- the trust ledger's part for this file: it must add no source of trust
        let _ ← checkExampleTrustLedger path s.globals
        pure () },
    { name := "V1: full widths by native_refl, each an axiom #print axioms names (examples/hdl-verified-native.wiz)", run := fun _ => do
        let ms ← msgsLibs (← IO.FS.readFile "examples/hdl-verified-native.wiz")
        noErrors ms
        expect ms "root_full is accepted on the strength of native evaluation"
        expect ms "norm_256 is accepted on the strength of native evaluation"
        expect ms "smin_256 is accepted on the strength of native evaluation"
        expect ms "'smin_256' depends on axioms: [smin_256.native✝" } ]

def groups : List Group := [group, hdlVerifiedGroup]

end Tests.Native
