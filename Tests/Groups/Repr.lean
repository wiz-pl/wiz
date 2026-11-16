import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-! ### Representations are a function of the type up to conversion (R3)

`wiz-notes/repr-shape.md`. A value keeps its bits when it is converted to an equal type,
or passed to generic code, so erasure may choose a representation only by what conversion
(and substitution) can see: never by a binder name, an `Enum` label or the display name
on a `μ`. -/

/-- `#eval main`, `#run main` (the IR interpreter), and `main` compiled by the C and the
LLVM backends all give `expected`. `unbox`: with `--unbox-structs`. -/
def reprAll (src expected : String) (unbox : Bool := false) (libs : Bool := false)
    (extra : Name → Option String := fun _ => none) : IO Unit := do
  let full := src ++ "\n#eval main\n#run main\n"
  let loader ← if libs then libLoader else preludeLoader
  let loader := fun m => extra m <|> loader m
  let s := runFrontend (R := ZeroOneMany) full
    { trustedModule := Tests.libModule, loader, globals := { unboxStructs := unbox } }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render full
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  checkEq [expected, expected] (s.messages.toList.map (·.text))
  for llvm in [false, true] do
    let dir ← IO.FS.createTempDir
    match ← Build.runGlobal (← toolchain) s "main" dir llvm with
    | .ok v => checkEq expected v
    | .error e =>
      let missing := noToolchain e
      if missing then skip "no toolchain" else throw (IO.userError e)

/-- The audit's probe: a hand-written Σ of a structure's shape, converted both ways. -/
def r3Marker : String := "import Prelude
structure S where
  val : Nat
def toS (p : (val : Nat) × ((0 f : Enum [x]) → Unit)) : S := p
def ofS (s : S) : (val : Nat) × ((0 f : Enum [x]) → Unit) := s
def main : Nat := (toS (5, fun _ => ())).val + 10 * (ofS (S.mk 7)).1
"

/-- A structure's phantom tail, at a type that calls it a function, applied. -/
def r3PhantomTail : String := "import Prelude
structure P (n : Nat) where
  val : Nat
def tailOf (p : P 3) : (0 d : (0 x : Nat) × (x = 3)) → (0 f : Enum [q]) → Unit := p.2
def useT (t : (0 d : (0 x : Nat) × (x = 3)) → (0 f : Enum [q]) → Unit) : Unit := t (3, rfl) 'q
def keep (u : Unit) : Nat := 9
def main : Nat := keep (useT (tailOf (P.mk 4)))
"

/-- … and applied by generic code, which knows nothing of the tail. -/
def r3PhantomGeneric : String := "import Prelude
structure P (n : Nat) where
  val : Nat
def app0 {D A : Type} (0 d : D) (f : (0 _ : D) → A) : A := f d
def tailU (p : P 3) : (0 f : Enum [q]) → Unit := app0 (D := (0 x : Nat) × (x = 3)) (3, rfl) p.2
def keep (u : Unit) : Nat := 9
def main : Nat := keep (tailU (P.mk 4) 'q)
"

/-- Generic code over pairs, used at a structure: unification puts the structure's tail
in the type variable `B`. -/
def r3Generic : String := "import Prelude
structure S where
  val : Nat
def first {A : Type} {B : Type} (p : A × B) : A := p.1
def mk2 {A : Type} {B : Type} (a : A) (b : B) : A × B := (a, b)
def s2 : S := mk2 7 (S.mk 1).2
def main : Nat := first (S.mk 5) + 10 * s2.val
"

/-- A Σ whose second component is a function into `Unit` only for some first components. -/
def r3Dependent : String := "import Prelude
def T (b : Bool) : Type := match b with
  | .true => (0 f : Enum [x]) → Unit
  | .false => Nat
def p : (b : Bool) × T b := (.true, fun _ => ())
def q : (b : Bool) × T b := (.false, 7)
def isT (q : (b : Bool) × T b) : Nat := match q.1 with
  | .true => 1
  | .false => 0
def main : Nat := isT p + 10 * isT q
"

/-- A copy of `Nat`'s declaration is convertible to `Nat`. -/
def r3NatCopy : String := "import Prelude
inductive MyNat where
  | zero
  | succ (n : MyNat)
def ofNat (n : Nat) : MyNat := n
def toNat (n : MyNat) : Nat := n
def count : MyNat → Nat
  | .zero => 0
  | .succ n => count n + 1
def main : Nat := count (ofNat 3) + 10 * (toNat (.succ (.succ .zero)) + 1)
"

/-- A proof-valued function applied by code that is generic in the sort. -/
def r3SortPoly : String := "import Prelude
def app.{u} {A : Sort u} (f : Nat → A) : A := f 0
def keep.{u} {A : Sort u} (f : Nat → A) : Nat := let x := app f; 4
def main : Nat := keep (A := 0 = 0) (fun _ => rfl)
"

/-- A description built by a function that abstracts its first field's type, used at an
`Enum`: code at the known type takes the tag from the object, the generic eliminator
would follow the description's run-time mark, which says there is none. -/
def r3DescMark : String := "import Prelude
def mkD (S : Type) (F : S → Desc Unit) : Desc Unit := Desc.arg 1 S F
def B2 : Type := μ (mkD (Enum [a, b]) (fun _ => Desc.ret ())) ()
def tb : B2 := con ('b, (), ())
def isB2 (x : B2) : Nat := ind (fun _ _ => Nat) (fun i xs ih => let h := ih; ecase xs.1 [0, 1]) x
def main : Nat := isB2 tb
"

/-- A pair of proofs projected by code that is generic in the sorts of its components. -/
def r3SortPolyPair : String := "import Prelude
def sndP.{u, v} {A : Sort u} {B : Sort v} (p : A × B) : B := p.2
def keep.{u, v} {A : Sort u} {B : Sort v} (p : A × B) : Nat := let x := sndP p; 4
def main : Nat := keep (A := 0 = 0) (B := 1 = 1) (rfl, rfl)
"

/-- Structures of 1 to 3 fields, with and without a phantom parameter, each with the Σ of
its shape written by hand: values converted back and forth, read through the structure's
projections and through the raw ones. Returns the program and the value of `main`. -/
def r3RoundTrips : String × Nat := Id.run do
  let mut src := "import Prelude\ndef lsum : List Nat → Nat\n  | .nil => 0\n  | .cons x xs => x + lsum xs\n"
  let mut total := 0
  let mut terms : List String := []
  let mut k := 0
  for nf in [1, 2, 3] do
    for phantom in [false, true] do
      k := k + 1
      -- field `i` is a `Nat` (even `i`) or a `List Nat` (odd `i`), with the value `v i`
      let v (i : Nat) : Nat := 3 * k + 5 * i + 1
      let isList (i : Nat) : Bool := i % 2 == 1
      let fty (i : Nat) : String := if isList i then "List Nat" else "Nat"
      let lit (i : Nat) : String := if isList i then s!"(List.cons {v i} (List.cons 1 List.nil))" else s!"{v i}"
      let rd (i : Nat) (e : String) : String := if isList i then s!"lsum ({e})" else e
      let (ps, arg) := if phantom then (" (w : Nat)", " 3") else ("", "")
      let tail := if phantom then "((0 d : (0 x : Nat) × (x = 3)) → (0 f : Enum [q]) → Unit)" else "((0 f : Enum [q]) → Unit)"
      let tailV := if phantom then "(fun _ _ => ())" else "(fun _ => ())"
      let fields := List.range nf
      src := src ++ s!"structure S{k}{ps} where\n" ++ String.join (fields.map fun i => s!"  f{i} : {fty i}\n")
      src := src ++ s!"def H{k} : Type := " ++ String.join (fields.map fun i => s!"(f{i} : {fty i}) × ") ++ tail ++ "\n"
      src := src ++ s!"def to{k} (h : H{k}) : S{k}{arg} := h\ndef of{k} (s : S{k}{arg}) : H{k} := s\n"
      -- the weighted sum of the fields, through the structure's projections and the raw ones
      let viaS := " + ".intercalate (fields.map fun i => s!"{i + 1} * {rd i s!"s.f{i}"}")
      let raw (i : Nat) : String := "h" ++ String.join (List.replicate i ".2") ++ ".1"
      let viaH := " + ".intercalate (fields.map fun i => s!"{i + 1} * {rd i (raw i)}")
      src := src ++ s!"def sumS{k} (s : S{k}{arg}) : Nat := {viaS}\ndef sumH{k} (h : H{k}) : Nat := {viaH}\n"
      src := src ++ s!"def s{k} : S{k}{arg} := S{k}.mk {" ".intercalate (fields.map lit)}\n"
      src := src ++ s!"def h{k} : H{k} := ({", ".intercalate (fields.map lit)}, {tailV})\n"
      let w := fields.foldl (fun acc i => acc + (i + 1) * (v i + (if isList i then 1 else 0))) 0
      let checks := [s!"sumS{k} (to{k} h{k})", s!"sumH{k} (of{k} s{k})", s!"sumS{k} (to{k} (of{k} (to{k} (of{k} s{k}))))",
        s!"sumH{k} (of{k} (to{k} h{k}))", s!"sumS{k} s{k}", s!"sumH{k} h{k}"]
      for c in checks, j in [0:checks.length] do
        terms := terms ++ [s!"{j + 1} * {c}"]
        total := total + (j + 1) * w
  src := src ++ "def main : Nat := " ++ " + ".intercalate terms ++ "\n"
  pure (src, total)

/-- (22k) A type with a native representation, sealed, with a private constructor, in a
module of its own: `W` is a byte, compiled as its bits. -/
def sealNat8 : String := "import Word
sealed inductive W where
  | private mk (toNat : Nat)
extern \"wiz_word_of_bits\" W.ofBits : NatObj → W
extern \"wiz_word_to_bits\" W.toBits : W → NatObj
attribute [implemented_by W.ofBits W.toBits] W.mk
def W.of (n : Nat) : W := .mk (Nat.mod n 256)
def W.get : W → Nat
  | .mk n => n
def W.succ (a : W) : W := W.of (a.get + 1)
"

def sealLoader (m : Name) : Option String := if m == "Nat8" then some sealNat8 else none

/-- `input` with `Nat8` importable: its error messages. -/
def sealErrors (input : String) : IO (Array String) := do
  let loader ← preludeLoader
  let s := runFrontend (R := ZeroOneMany) input { trustedModule := Tests.libModule, loader := fun m => sealLoader m <|> loader m }
  pure ((s.messages.filter (·.severity == .error)).map fun m => m.render input)

def sealFails (input fragment : String) : IO Unit := do
  let errs ← sealErrors input
  unless errs.size == 1 do throw (IO.userError s!"expected one error, got {errs.size}: {errs}")
  unless (errs[0]!.splitOn fragment).length > 1 do
    throw (IO.userError s!"error does not mention '{fragment}':\n{errs[0]!}")

/-- (22k, layer 3) What erasure refuses, on kernel terms no surface program produces: the
elaborated program `import Nat8` plus a hand-made declaration `bad` (outside `W`'s module).
`fragment`: the refusal expected (`none`: it compiles). -/
def sealLayer3 (bad : Decl ZeroOneMany) (fragment : Option String) : IO Unit := do
  let loader ← preludeLoader
  let src := "import Nat8\ndef ok : Nat := W.get (W.succ (W.of 7))\n"
  let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := fun m => sealLoader m <|> loader m }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  let s := { s with globals := s.globals.insert bad }
  match Build.irProgram s bad.name, fragment with
  | .ok _, none => pure ()
  | .ok _, some f => throw (IO.userError s!"{bad.name} compiled; expected a refusal mentioning '{f}'")
  | .error e, some f => check ((e.splitOn f).length > 1) e
  | .error e, none => throw (IO.userError s!"{bad.name} was refused: {e}")

/-- A state with every library module and `Nat8` importable, from `src`, no errors. -/
def reprState (src : String) : IO (CommandState ZeroOneMany) := do
  let loader ← libLoader
  let s := runFrontend (R := ZeroOneMany) src
    { trustedModule := Tests.libModule, loader := fun m => sealLoader m <|> loader m }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  pure s

/-- Replace every `repr:` key with a wrong tag (a stale or hand-made registration). -/
def staleReprs (s : CommandState ZeroOneMany) : CommandState ZeroOneMany :=
  let bump (k : Name) (v : Name) : Name × Name :=
    match ReprInfo.parse? k with
    | some (T, ri) => (ReprInfo.key T { ri with tag := ri.tag + 7 }, v)
    | none => (k, v)
  { s with builtins := s.builtins.map (fun (k, v) => bump k v),
           globals := { s.globals with builtins := s.globals.builtins.map (fun (k, v) => bump k v) } }

/-- Drop every seal registration (an environment a `sealed` marker never reached). -/
def unsealed (s : CommandState ZeroOneMany) : CommandState ZeroOneMany :=
  { s with builtins := s.builtins.filter fun (k, _) => !k.startsWith "seal:",
           globals := { s.globals with builtins := s.globals.builtins.filter fun (k, _) => !k.startsWith "seal:" } }

def cStructSrc : String := "import Nat8
import IO
c_struct \"struct pair\" Pair where
  a : Nat
  b : UInt64
extern \"nop\" nop : Pair → Nat
def main : Nat := nop (Pair.mk 1 2)
"

def reprGroup : Group where
  name := "repr"
  exercise := "Representations and conversion (R3)"
  cases := [
    { name := "R3: a hand-written Σ of a structure's shape converts to the structure and back", run := fun _ =>
        reprAll r3Marker "75" },
    { name := "… and with --unbox-structs", run := fun _ => reprAll r3Marker "75" (unbox := true) },
    { name := "R3: a phantom tail at a type that calls it a function is applied (compiled too)", run := fun _ =>
        reprAll r3PhantomTail "9" },
    { name := "… and applied by generic code: ◾ applied is ◾", run := fun _ => do
        reprAll r3PhantomGeneric "9"
        reprAll r3PhantomGeneric "9" (unbox := true) },
    { name := "generic code over pairs, used at a structure (substitution)", run := fun _ =>
        reprAll r3Generic "75" },
    { name := "a Σ whose second component depends on the first is always a pair", run := fun _ => do
        reprAll r3Dependent "1"
        reprAll r3Dependent "1" (unbox := true) },
    { name := "a copy of Nat's declaration is convertible to Nat, and is a number too", run := fun _ =>
        reprAll r3NatCopy "33" },
    { name := "a proof-valued function applied by code generic in the sort", run := fun _ =>
        reprAll r3SortPoly "4" },
    { name := "a pair of proofs projected by code generic in the sorts: a projection of ◾ is ◾", run := fun _ =>
        reprAll r3SortPolyPair "4" },
    { name := "a description whose first field has an abstract type is refused, not miscompiled", run := fun _ => do
        failsLib (r3DescMark ++ "#eval main\n") "cannot compile a description"
        let s := runFrontend (R := ZeroOneMany) r3DescMark { trustedModule := Tests.libModule, loader := ← preludeLoader }
        match Build.cProgram s "main" with
        | .ok _ => throw (IO.userError "it compiled")
        | .error e => check ((e.splitOn "cannot compile a description").length > 1) e
        -- a parameterised type's own fields are not first fields: `List A` compiles
        reprAll "import Prelude\ndef len {A : Type} : List A → Nat\n  | .nil => 0\n  | .cons _ xs => len xs + 1\ndef main : Nat := len (List.cons 'a (List.cons 'b List.nil) : List (Enum [a, b]))\n" "2" },
    { name := "two runs in one process with different options don't share a module's state", run := fun _ => do
        let loader ← preludeLoader
        let run (g : Globals ZeroOneMany) : Globals ZeroOneMany :=
          (runFrontend (R := ZeroOneMany) "import Prelude\n" { trustedModule := Tests.libModule, loader, globals := g }).globals
        check (!(run {}).unboxStructs) "the default unboxes"
        check (run { unboxStructs := true }).unboxStructs "unboxStructs was lost"
        check (!(run {}).unboxStructs) "unboxStructs leaked"
        check ((run { inertReg := .ground }).inertReg == .ground) "inertReg := ground was lost"
        check ((run {}).inertReg == .conv) "inertReg leaked"
        check ((run { predicativeProp := true }).predicativeProp) "predicativeProp was lost"
        check (!(run {}).predicativeProp) "predicativeProp leaked"
        check (!(run { lazyProofs := false }).lazyProofs) "lazyProofs := false was lost"
        check ((run {}).lazyProofs) "lazyProofs leaked" },
    { name := "structures and the Σ of their shape: values converted back and forth", run := fun _ => do
        let (src, total) := r3RoundTrips
        reprAll src (toString total)
        reprAll src (toString total) (unbox := true) },
    { name := "22k: a sealed type: a look-alike, another sealed type, another width are other types", run := fun _ => do
        let hdr := "import Prelude\n" ++ sealHeader
        okLib (hdr ++ "def same (x : W 8) : W 8 := x\ndef get {w : Nat} : W w → Nat\n  | .mk n => n\n#eval get (W.mk 5 : W 8)\n#print axioms same\n")
          ["5", "'same' depends on axioms: [W.seal✝]"]
        for d in ["def bad (x : L 8) : W 8 := x", "def bad (x : W 8) : L 8 := x", "def bad (x : V 8) : W 8 := x",
            "def bad (x : W 8) : W 16 := x"] do
          failsLib (hdr ++ d ++ "\n") "type mismatch"
        failsLib (hdr ++ "def bad : W 8 = L 8 := rfl\n") "not definitionally equal"
        failsLib (hdr ++ "def bad : W 8 = V 8 := rfl\n") "not definitionally equal"
        failsLib "import Prelude\nsealed structure P where\n  x : Nat\n" "`sealed` applies to an `inductive` declaration"
        -- the seal can't be named
        check (!(← sealErrors "import Nat8\ndef s : Type := W.seal✝\n").isEmpty) "W.seal✝ was named" },
    { name := "22k: a native sealed type in its own module: its functions, generic code and lists of it, interpreted and compiled", run := fun _ =>
        reprAll ("import Nat8\ndef keep {A : Type} (x : A) : A := x\ndef sum : List W → Nat\n  | .nil => 0\n  | .cons x xs => x.get + sum xs\n" ++
          "def main : Nat := W.get (keep (W.succ (W.of 299))) + sum (.cons (W.of 1) (.cons (W.of 256) .nil))\n") "45" (extra := sealLoader) },
    { name := "22k: outside its module a native type is not built, taken apart or matched by a look-alike (R5, layer 1)", run := fun _ => do
        sealFails "import Nat8\ndef big (n : Nat) : W := .mk (n + 300)\n" "private to module Nat8"
        sealFails "import Nat8\ndef get (x : W) : Nat := match x with\n  | .mk n => n\n" "Nat8"
        sealFails "import Nat8\ninductive Box (A : Type) where\n  | mk (n : Nat)\ndef toBox (x : W) : Box _ := x\n" "type mismatch"
        sealFails "import Nat8\ndef d := W.desc\n" "private" },
    { name := "22k: the words are sealed: UIntN 8 is not IntN 8 or a look-alike, and out-of-range words can't be built (R5)", run := fun _ => do
        -- audit 2's R5 probe (`wiz-notes/soundness-probes/a2-r5-word-out-of-range.wiz`)
        let errs ← sealErrors ("import Word\ndef big (n : Nat) : UIntN 8 := .mk (n + 300)\n" ++
          "def main : Nat := (big 0).toNat + (UIntN.not (big 0)).toNat\n")
        check (errs.size > 0 && (errs[0]!.splitOn "'UIntN.mk' is private to module Word").length > 1) s!"{errs}"
        for d in ["def f (x : IntN 8) : UIntN 8 := x", "def f (x : UIntN 8) : IntN 8 := x",
            "inductive MyU (w : Nat) where\n  | mk (toNat : Nat)\ndef f (x : MyU 8) : UIntN 8 := x"] do
          sealFails ("import Word\n" ++ d ++ "\n") "type mismatch"
        sealFails "import Word\ndef e : UIntN 8 = IntN 8 := rfl\n" "not definitionally equal"
        -- the conversions are the identity on the bits
        okLib "import Word\n#eval (UIntN.toIntN (UIntN.ofNat 8 200)).toNat\n#eval (IntN.toUIntN (IntN.ofNeg 8 1)).toNat\n" ["200", "255"] },
    { name := "22k: a native representation needs a sealed type and a private constructor", run := fun _ => do
        let natives := "extern \"wiz_word_of_bits\" W.ofBits : NatObj → W\nextern \"wiz_word_to_bits\" W.toBits : W → NatObj\n" ++
          "attribute [implemented_by W.ofBits W.toBits] W.mk\n"
        sealFails ("import Word\ninductive W where\n  | private mk (toNat : Nat)\n" ++ natives) "needs `sealed inductive W`"
        sealFails ("import Word\nsealed inductive W where\n  | mk (toNat : Nat)\n" ++ natives) "needs a private constructor" },
    { name := "22k: erasure refuses a native value built outside its module, and the seal outside its type (layer 3)", run := fun _ => do
        -- a `W` built by `con` (the elaborator refuses `W.mk`; a kernel term need not)
        sealLayer3 { name := "forged", type := .const "W" [], value := some (.con .tt) } (some nativeHomeMsg)
        -- the seal as a term outside a `μ`
        sealLayer3 { name := "leak", type := .sort (.succ .zero), value := some (.const (sealName "W") []) } (some "has a native representation (it is a sealed type)")
        -- and the module's own functions are fine
        sealLayer3 { name := "fine", type := .const "Nat" [], value := some (.app (.const "W.get" []) (.app (.const "W.of" []) (.const "ok" []))) } none },
    { name := "22m: wiz repr prints the target, the natives and the C struct layouts", run := fun _ => do
        let s ← reprState cStructSrc
        let tc : Toolchain := { target := "aarch64-unknown-linux-gnu", ptrBits := 64, endian := "little" }
        let r := Build.reprReport tc s
        for line in ["target: aarch64-unknown-linux-gnu (64-bit pointers, little-endian)",
            "native representations (3):",
            "W: W.ofBits / W.toBits on W.mk, tag 0, 1 fields, runtime field 0 (one word)",
            "UIntN: UIntN.ofBits / UIntN.toBits on UIntN.mk, tag 0, 2 fields, runtime field 0 (one word)",
            "struct pair (generated): 2 fields, size 16, align 8",
            "a: Nat, 8 bytes, offset 0", "b: UInt64, 8 bytes, offset 8"] do
          check ((r.splitOn line).length > 1) s!"no '{line}' in:\n{r}"
        -- the default target is the host's, named
        check (((Build.reprReport {} s).splitOn "target: (the host) (64-bit pointers, little-endian)").length > 1)
          "the default target is not the host"
        -- and the CLI prints it, if the binary is built
        let wiz := ((← IO.appPath).parent.getD ".") / "wiz"
        unless ← wiz.pathExists do
          skip "no wiz binary"
          return
        let dir ← IO.FS.createTempDir
        -- (the CLI sees `lib/` only: `Nat8` is this suite's module)
        IO.FS.writeFile (dir / "main.wiz") "import Word\nimport IO\nc_struct \"struct pair\" Pair where\n  a : Nat\n  b : UInt64\ndef main : Nat := UIntN.toNat (UIntN.ofNat 8 1)\n"
        let out ← IO.Process.output { cmd := wiz.toString, args := #["repr", (dir / "main.wiz").toString] }
        checkEq 0 out.exitCode
        for line in ["native representations (2):", "UIntN: UIntN.ofBits / UIntN.toBits", "struct pair (generated): 2 fields, size 16, align 8"] do
          check ((out.stdout.splitOn line).length > 1) s!"no '{line}' in:\n{out.stdout}{out.stderr}" },
    { name := "22m: the build's _Static_asserts check the target and the struct layout", run := fun _ => do
        let s ← reprState cStructSrc
        let some c := (Build.cProgram s "main").toOption.map (·.1) | throw (IO.userError "the program did not compile")
        for line in ["_Static_assert(sizeof(uint64_t) == 8", "_Static_assert(_Alignof(uint64_t) == 8",
            "_Static_assert(sizeof(void *) * 8 == 64", "__ORDER_LITTLE_ENDIAN__",
            "_Static_assert(sizeof(struct pair) == 16", "_Static_assert(_Alignof(struct pair) == 8",
            "offsetof(struct pair, a) == 0", "offsetof(struct pair, b) == 8",
            "/* native W: W.ofBits / W.toBits, tag 0, 1 fields, runtime field 0 (one word) */"] do
          check ((c.splitOn line).length > 1) s!"no '{line}' in the generated C:\n{c.take 4000}"
        -- a 32-bit or big-endian target asserts what it was told
        let c32 := (Build.cProgram s "main" ({ ptrBits := 32, endian := "big" } : Toolchain)).toOption.map (·.1)
        match c32 with
        | none => throw (IO.userError "the 32-bit build did not compile")
        | some c32 =>
          check ((c32.splitOn "sizeof(void *) * 8 == 32").length > 1) "no 32-bit pointer assert"
          check ((c32.splitOn "__ORDER_BIG_ENDIAN__").length > 1) "no big-endian assert"
        -- a generated struct nested in another: the model's offsets and size, checked
        let nested ← reprState ("import IO\nc_struct \"struct inner\" Inner where\n  x : UInt64\n" ++
          "c_struct \"struct outer\" Outer where\n  a : Nat\n  b : Inner\n  c : UInt64\n" ++
          "extern \"nop\" nop : Outer → Nat\ndef main : Nat := nop (Outer.mk 1 (Inner.mk 2) 3)\n")
        let some nc := (Build.cProgram nested "main").toOption.map (·.1) | throw (IO.userError "the nested program did not compile")
        for line in ["_Static_assert(sizeof(struct inner) == 8", "_Static_assert(sizeof(struct outer) == 24",
            "offsetof(struct outer, b) == 8", "offsetof(struct outer, c) == 16"] do
          check ((nc.splitOn line).length > 1) s!"no '{line}' in:\n{nc.take 4000}" },
    { name := "22m: a repr: without a seal, or one whose shape changed, is refused by the build (coherence)", run := fun _ => do
        let src := "import Word\ndef main : Nat := UIntN.toNat (UIntN.ofNat 8 3)\n"
        let s ← reprState src
        checkEq #[] (Build.reprCoherence s).toArray
        -- the seal is what the registration is found by: without it, no build
        let s' := unsealed s
        check ((Build.reprCoherence s').any fun e => (e.splitOn "not `sealed`").length > 1)
          s!"no seal error: {Build.reprCoherence s'}"
        match Build.irProgram s' "main" with
        | .error e => check ((e.splitOn "not `sealed`").length > 1) s!"the build error: {e}"
        | .ok _ => throw (IO.userError "an unsealed representation compiled")
        -- a registration that disagrees with the constructor is refused, not compiled
        let sBad := staleReprs s
        check ((Build.reprCoherence sBad).any fun e => (e.splitOn "disagrees with UIntN.mk's erased shape").length > 1)
          s!"no shape error: {Build.reprCoherence sBad}"
        match Build.irProgram sBad "main" with
        | .error e => check ((e.splitOn "disagrees with").length > 1) s!"the build error: {e}"
        | .ok _ => throw (IO.userError "a stale representation compiled") },
    { name := "22m: a c_struct program is compiled with its layout asserts (C, LLVM)", run := fun _ => do
        -- `div_t` is the header's struct: the asserts check the fields exist in it, and the
        -- target's ABI (both backends compile the program, so the C compiler runs them)
        let src := "import IO\nc_struct \"div_t\" (header := \"stdlib.h\") DivT where\n  quot : Nat\n  rem : Nat\n" ++
          "extern \"div\" (header := \"stdlib.h\") cdiv : Nat → Nat → DivT\n" ++
          "def main : Nat := (cdiv 47 5).quot + 10 * (cdiv 47 5).rem\n"
        cRunLibs src "29"
        cRunLibs src "29" (llvm := true) }
  ]

builtin_initialize registerGroup reprGroup

end Tests.Elab
