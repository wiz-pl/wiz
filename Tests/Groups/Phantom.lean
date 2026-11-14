import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-! ### Phantom parameters

A parameter that no field mentions gets an erased phantom tail (`phantomTail`,
`Elab/Inductive.lean`), so it counts in conversion and unification and costs nothing at
run time. -/

/-- The same program with a phantom parameter (`B`/`Q` are `Box 8`/`Pt 8`) or with a
proof parameter instead, which gets no phantom (`Box (refl 0)`): the only difference is
the phantom tail. -/
def phantomPair (phantom : Bool) : String :=
  let (ps, args) := if phantom then (" (w : Nat)", " 8") else (" (h : 0 = 0)", " (refl 0)")
  s!"import Prelude\ninductive Box{ps} where\n  | mk (n : Nat)\nstructure Pt{ps} where\n  x : Nat\n  y : Nat\n" ++
  s!"def B : Type := Box{args}\ndef Q : Type := Pt{args}\n" ++
  "def get : B → Nat\n  | .mk n => n\ndef sum (p : Q) : Nat := p.x + p.y\n" ++
  "def main : Nat := get (.mk 3) + sum (Pt.mk 1 2)\n#ir get\n#ir sum\n#ir main\n"

/-- Rename the variables `x<n>` of IR or C in order of first occurrence (an erased
argument still takes a variable number). -/
def renumberVars (s : String) : String := Id.run do
  let cs := s.toList.toArray
  let mut out : String := ""
  let mut seen : Array String := #[]
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    let prevOk := i == 0 || !(cs[i-1]!.isAlphanum || cs[i-1]! == '_')
    if c == 'x' && prevOk && i + 1 < cs.size && cs[i+1]!.isDigit then
      let mut j := i + 1
      let mut num := ""
      while j < cs.size && cs[j]!.isDigit do
        num := num.push cs[j]!
        j := j + 1
      if j < cs.size && (cs[j]!.isAlphanum || cs[j]! == '_') then
        out := out.push c
        i := i + 1
      else
        let k := match seen.findIdx? (· == num) with
          | some k => k
          | none => seen.size
        if k == seen.size then seen := seen.push num
        out := out ++ s!"x{k}"
        i := j
    else
      out := out.push c
      i := i + 1
  return out

def phantomGroup : Group where
  name := "phantom"
  exercise := "Phantom parameters"
  cases := [
    { name := "UIntN 8 and UIntN 16 are different types", run := fun _ =>
        failsLib "import Prelude\ninductive UIntN (w : Nat) where\n  | mk (toNat : Nat)\ndef f (x : UIntN 8) : UIntN 16 := x" "mismatch" },
    { name := "so rfl can't prove UIntN 8 = UIntN 16", run := fun _ =>
        failsLib "import Prelude\ninductive UIntN (w : Nat) where\n  | mk (toNat : Nat)\ndef e : UIntN 8 = UIntN 16 := rfl" "not definitionally equal" },
    { name := "μ equality: UIntN 8 = UIntN 8 holds, UIntN 8 = UIntN 16 is refutable (4g)", run := fun _ => do
        -- equality of μ types compares the codes (4g): the phantom is in the index type,
        -- whose equation is `e.1`, and at the phantom it is `(x = 16) ↔ (x = 8)`
        let ty := "import Prelude\ninductive UIntN (w : Nat) where\n  | mk (toNat : Nat)\n"
        okLib (ty ++ "def same : UIntN 8 = UIntN 8 := refl (UIntN 8)")
        okLib (ty ++ "def ne (e : UIntN 8 = UIntN 16) : Empty := absurd ((e.1.1.2 16).1 (refl 16))")
        failsLib (ty ++ "def bad : UIntN 8 = UIntN 16 := refl (UIntN 8)") "mismatch" },
    { name := "the width is inferred from the type", run := fun _ =>
        okLib ("import Prelude\ninductive UIntN (w : Nat) where\n  | mk (toNat : Nat)\nstructure S (w : Nat) where\n  x : Nat\n" ++
          "def width {ω w : Nat} (a : UIntN w) : Nat := w\ndef swidth {ω w : Nat} (a : S w) : Nat := w\n" ++
          "#eval width (UIntN.mk 3 : UIntN 8)\n#eval swidth (S.mk 1 : S 16)") ["8", "16"] },
    { name := "structures: S 8 and S 16 are different types", run := fun _ =>
        failsLib "import Prelude\nstructure S (w : Nat) where\n  x : Nat\ndef f (x : S 8) : S 16 := x" "mismatch" },
    { name := "structures: S 8 = S 16 is refutable", run := fun _ =>
        okLib ("import Prelude\nstructure S (w : Nat) where\n  x : Nat\n" ++
          "def ne (e : S 8 = S 16) : Empty := absurd (((e.2 0).1.2 16).1 (refl 16))") },
    { name := "structures: tuples end in (), and η still holds", run := fun _ =>
        okLib ("import Prelude\nstructure P (w : Nat) where\n  x : Nat\n  y : Nat\n" ++
          "def p : P 4 := (1, 2, ())\n#eval p.y\ndef eta {w : Nat} (q : P w) : q = P.mk q.x q.y := refl q") ["2"] },
    { name := "type parameters: Proxy Nat and Proxy Bool are different types", run := fun _ =>
        failsLib "import Prelude\ninductive Proxy (A : Type) where\n  | mk\ndef f (x : Proxy Nat) : Proxy Bool := x" "mismatch" },
    { name := "coinductive: signals in different clock domains are different types", run := fun _ => do
        let sig := "import Prelude\nstructure Domain where\n  period : Nat\ndef System : Domain := Domain.mk 10\ndef Fast : Domain := Domain.mk 1\n" ++
          "coinductive Signal (d : Domain) (A : Type) where\n  head : A\n  tail : Signal d A\n" ++
          "def konst {d : Domain} {A : Type} (a : A) : Signal d A\n  | .head => a\n  | .tail => konst a\n" ++
          "def reg {d : Domain} {A : Type} (init : A) (s : Signal d A) : Signal d A\n  | .head => init\n  | .tail => s\n"
        okLib (sig ++ "def sys : Signal System Nat := reg 1 (konst 2)\n#eval sys.tail.head") ["2"]
        failsLib (sig ++ "def crossDomain (s : Signal System Nat) : Signal Fast Nat := s") "mismatch" },
    { name := "indexed families: matching with index unification, and recursion", run := fun _ =>
        okLib ("import Prelude\ninductive V (w : Nat) (A : Type) : Nat → Type where\n  | nil : V w A .zero\n" ++
          "  | cons {0 n : Nat} (x : A) (xs : V w A n) : V w A (.succ n)\n" ++
          "def V.len {w : Nat} {A : Type} {0 n : Nat} : V w A n → Nat\n  | .nil => 0\n  | .cons _ xs => Nat.succ (V.len xs)\n" ++
          "def V.head {w : Nat} {A : Type} {0 n : Nat} : V w A (.succ n) → A\n  | .cons x _ => x\n" ++
          "def v : V 7 Nat 2 := .cons 5 (.cons 6 .nil)\n#eval V.len v\n#eval V.head v\n#run V.head v") ["2", "5", "5"] },
    { name := "sized recursion on a parameterised (and a phantom) type", run := fun _ =>
        okLib ("import Prelude\ninductive L (A : Type) where\n  | nil\n  | cons (a : A) (t : L A)\n" ++
          "def L.app {A : Type} {i : Size} : (L A)^i → L A → L A\n  | .nil, m => m\n  | .cons a t, m => .cons a (L.app t m)\n" ++
          "inductive N (w : Nat) where\n  | z\n  | s (n : N w)\n" ++
          "def N.add {i : Size} {w : Nat} : (N w)^i → N w → N w\n  | .z, m => m\n  | .s n, m => .s (N.add n m)\n" ++
          "#eval N.add (.s .z : N 3) (.s .z)\n#eval L.app (.cons 1 .nil) (.cons 2 .nil)")
          [".s (.s .z)", ".cons 1 (.cons 2 .nil)"] },
    { name := "deriving still works", run := fun _ =>
        okDeriving ("import Deriving\ninductive Tagged (w : Nat) where\n  | none\n  | some (n : Nat)\n  deriving Repr, BEq, Inhabited\n" ++
          "#eval Repr.repr (Tagged.some 3 : Tagged 8)\n#eval BEq.beq (Tagged.some 3 : Tagged 8) (Tagged.some 3)\n" ++
          "structure P (w : Nat) where\n  x : Nat\n  y : Nat\nderiving instance Repr, BEq for P\n#eval Repr.repr (P.mk 1 2 : P 5)")
          ["\"Tagged.some 3\"", ".true", "\"P.mk 1 2\""] },
    { name := "regions: Mut ρ A and Mut ρ' A are different types", run := fun _ =>
        failsLib ("import Prelude\naxiom Region : Type\nstructure Mut (ρ : Region) (A : Type) where\n  get : A\n" ++
          "def reborrow {ρ : Region} {A : Type} (m : Mut ρ A) : Mut ρ A := m\n" ++
          "def bad {ρ ρ' : Region} {A : Type} (m : Mut ρ A) : Mut ρ' A := m") "mismatch" },
    { name := "erased: the IR and the C don't change", run := fun _ => do
        let loader ← preludeLoader
        let run (phantom : Bool) : IO (List String × String) := do
          let src := phantomPair phantom
          let s := runFrontend (R := ZeroOneMany) src { loader, trustedModule := Tests.libModule }
          let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
          unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
          match Build.cProgram s "main" with
          | .ok (c, _) => pure (s.messages.toList.map (renumberVars ·.text), renumberVars c)
          | .error e => throw (IO.userError e)
        let (ir1, c1) ← run true
        let (ir0, c0) ← run false
        checkEq (repr ir0).pretty (repr ir1).pretty
        let l0 := c0.splitOn "\n"
        let l1 := c1.splitOn "\n"
        match (l0.zip l1).find? (fun (a, b) => a != b) with
        | some (a, b) => throw (IO.userError s!"the C differs:\n  without: {a}\n  with:    {b}")
        | none => check (l0.length == l1.length) "the C differs in length" },
    { name := "and it runs", run := fun _ => cRun (phantomPair true) "6" },
    { name := "structures: every pair is a pair; with --unbox-structs the last field is unboxed (22i)", run := fun _ => do
        let src := "import Prelude\nstructure W where\n  val : List Nat\nstructure P (w : Nat) where\n  x : Nat\n  y : List Nat\n" ++
          "def w : W := W.mk (List.cons 1 List.nil)\ndef l : List Nat := List.cons 1 List.nil\n" ++
          "def p : P 3 := P.mk 2 (List.cons 1 List.nil)\ndef q : Nat × List Nat × Unit := (2, List.cons 1 List.nil, ())\n" ++
          "def unW (v : W) : List Nat := v.val\ndef swap (v : P 3) : P 3 := (v.x, v.y, ())\n" ++
          "#eval w\n#run w\n#run p\n#eval swap p\n#run swap p\n" ++
          "def wl : List W := List.cons w List.nil\n#run wl\n"
        for unbox in [false, true] do
          let s := runFrontend (R := ZeroOneMany) src
            { trustedModule := Tests.libModule, loader := ← preludeLoader, globals := { unboxStructs := unbox } }
          let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
          unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
          -- the values read back the same in both layouts
          checkEq ["(.cons 1 .nil, ())", "(.cons 1 .nil, ())", "(2, .cons 1 .nil, ())",
            "(2, .cons 1 .nil, ())", "(2, .cons 1 .nil, ())", ".cons (.cons 1 .nil, ()) .nil"]
            (s.messages.toList.map (·.text))
          let allocs (n : Name) : IO Nat := match (do
              let code ← (compileReachable s.globals s.builtins [n]).mapError toString
              let decls ← IR.lowerProgram code (.global n)
              let (_, a) ← IR.runProgram (decls.map (·.optimize))
              pure a : Except String Nat) with
            | .ok a => pure a
            | .error e => throw (IO.userError e)
          let l ← allocs "l"
          -- unboxed: `W` is its list, and `P` is one pair, as a raw `Nat × List Nat × Unit`
          -- is two; else one cell per field
          let k := if unbox then 0 else 1
          checkEq (unbox, l + k, l + 1 + k, l + 2) (unbox, ← allocs "w", ← allocs "p", ← allocs "q") }
  ]

builtin_initialize registerGroup phantomGroup

end Tests.Elab
