import Wiz
import Tests.Harness

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

/-! The helpers of the elaboration tests that several groups use. Each group is a
module of its own, `Tests/Groups/<Name>.lean` (see `Tests/Harness.lean`,
`registerGroup`). -/

namespace Tests.Elab

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

def run (input : String) : Array String :=
  let s := runFrontend (R := ZeroOneMany) input
  s.messages.map fun m => m.render input

def errors (input : String) : Array String :=
  let s := runFrontend (R := ZeroOneMany) input
  (s.messages.filter (·.severity == .error)).map fun m => m.render input

/-- No errors, and the info messages (from `#check`/`#reduce`) are exactly `infos`,
without their positions. -/
def ok (input : String) (infos : List String := []) : IO Unit := do
  let errs := errors input
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  let got := (runFrontend (R := ZeroOneMany) input).messages.toList.map (·.text)
  checkEq (repr infos).pretty (repr got).pretty

/-- Exactly one error, mentioning `fragment`. -/
def fails (input : String) (fragment : String) : IO Unit := do
  let errs := errors input
  unless errs.size == 1 do
    throw (IO.userError s!"expected one error, got {errs.size}: {errs}")
  unless (errs[0]!.splitOn fragment).length > 1 do
    throw (IO.userError s!"error does not mention '{fragment}':\n{errs[0]!}")

def prelude : String := "
def id {A : Type} (x : A) : A := x
def const {A B : Type} (x : A) (y : B) : A := x
def comp {A B C : Type} (g : B → C) (f : A → B) (x : A) : C := g (f x)
"

def church : String := "
def Nat : Type 1 := (A : Type) → (A → A) → A → A
def zero : Nat := fun A s z => z
def succ (n : Nat) : Nat := fun A s z => s (n A s z)
def add (m n : Nat) : Nat := fun A s z => m A s (n A s z)
def two : Nat := succ (succ zero)
def four : Nat := add two two
def Leibniz {A : Type 1} (x y : A) : Type 2 := (P : A → Type 1) → P x → P y
def lrefl {A : Type 1} (x : A) : Leibniz x x := fun P px => px
"

/-- (D1) Abel–Coquand's counterexample to normalisation (LMCS 2020, the propext version),
in Wiz. Their `cast` is between propositions, where Wiz applies the equivalence instead of
regularity, so it goes through a box type: a `μ` type, where `cast` falls back to
regularity (`vCast`: equal types ⇒ `t`). `Omega` has no normal form, and the cast
between Σ types in `loopy` projects its proof, so checking `loopy` evaluates it. See
`wiz-notes/d1-experiment.md`.

`loopy` writes `Omega` out inline (`acOmega`: `δ ω` as lambdas, `unbox` as `ind`), not as
the global: a projection of a glued global stays glued until it is needed (`vFst`), and
the proof is never needed (the cast at `B2` doesn't look at it), so `(Omega …).1` would
never be unfolded. Inline, evaluating the proof is β-reduction and `ind` on the cast,
which loops with regularity. -/
def acDelta : String := "(fun (z : Top) => z T2 id2 z)"

/-- `ω`'s body inline (for `A : Prop`, `a : A`): `unbox (cast … (mk δ))`. The cast is
ascribed on both sides: since 4g `Box T2 = Box A` computes (to the equation of the codes),
so the elaborator can't read the two types off the proof's type. The target is `Box A`;
the source must be written `Box T2`, with the *name* `T2`: the inferred type of `mk δ` is
`Box (Top → Top)`, and the D1 regularity modes used to compare the two types
syntactically, so with the inferred type regularity did not fire at `A := T2` and the
program terminated for a reason that had nothing to do with the loop. (Since Part 2
regularity is decided by conversion, and both spellings behave alike.) -/
def acOmegaBody : String :=
  s!"ind (fun _ _ => A) (fun i xs ih => xs.1.2) (cast (apTy Prop Box T2 A (tautext T2 A id2 a)) (mk {acDelta} : Box T2) : Box A)"

/-- `Ω = δ ω`, inline -/
def acOmega (body : String := acOmegaBody) : String :=
  s!"({acDelta} (fun (A : Prop) (a : A) => {body}))"

def abelCoquand (omega : String := "Omega") (body : String := acOmegaBody) : String :=
  let omegaTm := if omega == "Omega" then acOmega body else omega
  "def Top : Prop := (A : Prop) → A → A\n" ++
  "def T2 : Prop := Top → Top\n" ++
  "def id2 : T2 := fun x => x\n" ++
  "def delta : T2 := fun z => z T2 id2 z\n" ++
  "def BoxD (P : Prop) : Desc Unit := Desc.arg 1 ((_ : Enum [u]) × P) (fun _ => Desc.ret ())\n" ++
  "def Box (P : Prop) : Type := μ (BoxD P) ()\n" ++
  "def mk {P : Prop} (p : P) : Box P := con (('u, p), (), ())\n" ++
  "def unbox {P : Prop} (b : Box P) : P := ind (fun _ _ => P) (fun i xs ih => xs.1.2) b\n" ++
  "def tautext (A B : Prop) (a : A) (b : B) : A = B := ((fun _ => b), (fun _ => a))\n" ++
  "def apTy (A : Type) (F : A → Type) (a b : A) (e : a = b) : F a = F b :=\n" ++
  "  transp (fun b _ => F a = F b) (refl (F a)) e\n" ++
  "def omega : Top := fun A a => unbox (cast (apTy Prop Box T2 A (tautext T2 A id2 a)) (mk delta))\n" ++
  "def Omega : Top := delta omega\n" ++
  "def B2 : Type := Enum [a, b]\n" ++
  "def P2 : Type := B2 × B2\n" ++
  "def ab : P2 := ('a, 'b)\n" ++
  "def a0 : B2 := 'a\n" ++
  s!"def loopy : (cast ({omegaTm} (P2 = P2) (refl P2)) ab : P2).1 = a0 := refl a0\n"

/-- `--regularity` modes, as on the command line. -/
def regularityMode : String → Regularity
  | "off" => .off
  | _ => .full

/-- No errors under the given regularity mode. -/
def okWith (r : Regularity) (input : String) : IO Unit := do
  let s := runFrontend (R := ZeroOneMany) input { globals := { regularity := r } }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render input
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")

/-- Checking `input` (with the Lean kernel, in a child process: `tests --check`) doesn't
finish within `secs` seconds. Memory is capped, as the loop allocates. -/
def checkDiverges (input mode : String) (secs : Nat := 3) : IO Unit := do
  let dir ← IO.FS.createTempDir
  IO.FS.writeFile (dir / "input.wiz") input
  let self ← IO.appPath
  let out ← IO.Process.output { cmd := "sh", cwd := dir, args := #["-c",
    s!"ulimit -v 8000000; exec timeout {secs} \"$0\" --check {mode} input.wiz", self.toString] }
  unless out.exitCode == 124 do
    throw (IO.userError s!"expected a timeout, got exit code {out.exitCode}: {out.stderr.take 1000}")

def matchPrelude : String := "inductive Nat where\n  | zero\n  | succ (n : Nat)\n\ninductive Vec (A : Type) : Nat → Type where\n  | nil : Vec A .zero\n  | cons {0 n : Nat} (x : A) (xs : Vec A n) : Vec A (.succ n)\n\ndef pred (n : Nat) : Nat := match n with\n  | .zero => .zero\n  | .succ m => m\n\ndef add : Nat → Nat → Nat\n  | .zero, n => n\n  | .succ m, n => .succ (add m n)\n\ndef head {A : Type} {n : Nat} : Vec A (.succ n) → A\n  | .cons x _ => x\n\ndef map {A B : Type} (f : A → B) {n : Nat} : Vec A n → Vec B n\n  | .nil => .nil\n  | .cons x xs => .cons (f x) (map xs)\n\n"

def streamPrelude : String := "inductive Nat where\n  | zero\n  | succ (n : Nat)\n\ncoinductive Stream (A : Type) where\n  head : A\n  tail : Stream A\n\ndef nats (n : Nat) : Stream Nat\n  | .head => n\n  | .tail => nats (.succ n)\n\n\ndef repeat {A : Type} (a : A) : Stream A\n  | .head => a\n  | .tail => repeat a\n\n"

/-- `register` (no corecursive observation: `cocon`) and `mealy` (corecursive: `coit`). -/
def registerSrc : String :=
  "def register {A : Type} (init : A) (s : Stream A) : Stream A\n  | .head => init\n  | .tail => s\n" ++
  "def mealy {S I O : Type} (f : S → I → S × O) (st : S) (i : Stream I) : Stream O\n" ++
  "  | .head => (f st i.head).2\n  | .tail => mealy f (f st i.head).1 i.tail\n"

def runPrelude : String := "inductive Nat where\n  | zero\n  | succ (n : Nat)\ndef add : Nat → Nat → Nat\n  | .zero, n => n\n  | .succ m, n => .succ (add m n)\ndef fib {i : Size} : Nat^i → Nat\n  | .zero => .succ .zero\n  | .succ .zero => .succ .zero\n  | .succ (.succ n) => add (fib n) (fib (.succ n))\ncoinductive Stream (A : Type) where\n  head : A\n  tail : Stream A\ndef nats (n : Nat) : Stream Nat\n  | .head => n\n  | .tail => nats (.succ n)\ndef swap {A B : Type} (p : A × B) : B × A := (p.2, p.1)\n\n"

/-- Exactly one error (with `lib/` importable), mentioning `fragment`. -/
def failsLib (input : String) (fragment : String) : IO Unit := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let s := runFrontend (R := ZeroOneMany) input { trustedModule := Tests.libModule, loader := fun m => if m == "Prelude" then some prelude else none }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render input
  unless errs.size == 1 do throw (IO.userError s!"expected one error, got {errs.size}: {errs}")
  unless (errs[0]!.splitOn fragment).length > 1 do
    throw (IO.userError s!"error does not mention '{fragment}':\n{errs[0]!}")

def treePrelude : String := "import Prelude
inductive Tree where
  | leaf
  | node (k : Nat → Tree)
def Tree.depthAt : Tree → Nat → Nat
  | .leaf, _ => 1
  | .node k, n => Tree.depthAt (k n) n + 1
"

/-- `import Prelude`, `import Word`, `import Functor` and `import Logic`. -/
def preludeLoader : IO (Name → Option String) := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let word ← IO.FS.readFile "lib/Word.wiz"
  let functor ← IO.FS.readFile "lib/Functor.wiz"
  let logic ← IO.FS.readFile "lib/Logic.wiz"
  let text ← IO.FS.readFile "lib/Text.wiz"
  pure fun m => if m == "Prelude" then some prelude else if m == "Word" then some word
    else if m == "Functor" then some functor else if m == "Logic" then some logic
    else if m == "Text" then some text else none

/-- `ok`, with `lib/` available to `import` (the tests run from the package root). -/

def okLib (input : String) (infos : List String := []) : IO Unit := do
  let loader ← preludeLoader
  let s := runFrontend (R := ZeroOneMany) input { loader, trustedModule := Tests.libModule }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render input
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  checkEq (repr infos).pretty (repr (s.messages.toList.map (·.text))).pretty

/-- `failsLib`, with `lib/`'s Prelude, Word, Text, Functor and Logic importable. -/
def failsLibW (input : String) (fragment : String) : IO Unit := do
  let loader ← preludeLoader
  let s := runFrontend (R := ZeroOneMany) input { loader, trustedModule := Tests.libModule }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render input
  unless errs.size == 1 do throw (IO.userError s!"expected one error, got {errs.size}: {errs}")
  unless (errs[0]!.splitOn fragment).length > 1 do
    throw (IO.userError s!"error does not mention '{fragment}':\n{errs[0]!}")

/-- Every message of `input` (with `lib/` importable), as `severity: text`, in order. -/
def msgsLib (input : String) : IO (List String) := do
  let loader ← preludeLoader
  let s := runFrontend (R := ZeroOneMany) input { loader, trustedModule := Tests.libModule }
  pure (s.messages.toList.map fun m =>
    s!"{match m.severity with | .error => "error" | .warning => "warning" | .info => "info"}: {m.text}")

def classPrelude : String := "import Prelude
class Inhabited (A : Type) where
  default : A
instance : Inhabited Nat := Inhabited.mk 0
instance : Inhabited Bool where
  default := Bool.true
instance {A : Type} [Inhabited A] : Inhabited (List A) where
  default := List.cons Inhabited.default List.nil
"

/-- Memoised streams, observed twice and dropped part-way (no leaks, `#run` and native). -/
def memoStreamSrc : String :=
  "import Prelude\ncoinductive Stream (A : Type) where\n  head : A\n  tail : Stream A\n" ++
  "def nats (n : Nat) : Stream Nat\n  | .head => n\n  | .tail => nats (n + 1)\n" ++
  "def sumN : Nat → Stream Nat → Nat\n  | .zero, _ => 0\n  | .succ k, s => s.head + sumN k s.tail\n" ++
  "def twice (s : Stream Nat) : Nat := sumN 100 s + sumN 100 s\n" ++
  "def partly (s : Stream Nat) : Nat := sumN 100 s + sumN 10 s + s.tail.head\n" ++
  "def walk : Nat → Stream Nat → Stream Nat\n  | .zero, s => s\n  | .succ k, s => walk k s.tail\n" ++
  "def main : Nat := twice (nats 0) + partly (nats 0) + (walk 50 (nats 0)).head\n"

/-- (15c) Folded at compile time: arithmetic on literals (truncated subtraction, `n / 0 = 0`,
a power past 64 bits), a match on a constructor built in place, a test on a known number,
a second match on the same list. -/
def foldSrc : String := "import Prelude
def known (b : Bool) : Nat := match (List.cons 5 List.nil : List Nat) with
  | .nil => 0
  | .cons x _ => x + 1
def isTen (n : Nat) : Nat := match Nat.beq n 10 with
  | .true => n + 1
  | .false => 0
def again (xs : List Nat) : Nat := match xs with
  | .nil => 0
  | .cons x _ => match xs with
    | .nil => 7
    | .cons _ _ => x
def main : List Nat := .cons (3 * 4 + 10 - 20) (.cons (Nat.div 7 0) (.cons (Nat.sub 3 5) (.cons (known .true)
  (.cons (isTen 10) (.cons (isTen 3) (.cons (again (.cons 4 .nil)) (.cons (Nat.pow 2 70) (.cons (Nat.mod 7 0) .nil))))))))
"

def foldExpected : String :=
  ".cons 2 (.cons 0 (.cons 0 (.cons 6 (.cons 11 (.cons 0 (.cons 4 (.cons 1180591620717411303424 (.cons 7 .nil))))))))"

/-- (15g) Numerals around the boundaries of the representation: small numbers are 62-bit
immediates, bigger ones GMP objects (`2^62` is the first), and a few operations on them. -/
def bigLitSrc : String := "import Prelude
def a : Nat := 2147483648
def b : Nat := 4294967296
def c : Nat := 4611686018427387904
def d : Nat := 9223372036854775808
def e : Nat := 18446744073709551616
def f : Nat := 18446744073709551617
def g : Nat := 1000000000000000000000000000000
def h : Nat := 4611686018427387903
def main : List Nat := .cons a (.cons b (.cons c (.cons d (.cons e (.cons f (.cons g (.cons h (.cons (f - e)
  (.cons (Nat.div g 1000000000) (.cons (c + c) (.cons (Nat.mod (d + d) 1000) (.cons (h + 1) .nil))))))))))))
"

def bigLitExpected : String :=
  ".cons 2147483648 (.cons 4294967296 (.cons 4611686018427387904 (.cons 9223372036854775808 " ++
  "(.cons 18446744073709551616 (.cons 18446744073709551617 (.cons 1000000000000000000000000000000 " ++
  "(.cons 4611686018427387903 (.cons 1 (.cons 1000000000000000000000 (.cons 9223372036854775808 (.cons 616 " ++
  "(.cons 4611686018427387904 .nil))))))))))))"

/-- (15h) Calls of case-shaped definitions: a search that stops (`Bool.or`), a test of
every element (`Bool.and`), a second argument that never returns, a breadth-first
search whose next level is only built if the test fails, and a user function of that
shape (`orElse`). -/
def caseShapeSrc : String := "import Prelude
def range : Nat → List Nat → List Nat
  | .zero, acc => acc
  | .succ n, acc => range n (.cons n acc)
def mem (n : Nat) : List Nat → Bool
  | .nil => .false
  | .cons x xs => Bool.or (Nat.beq x n) (mem n xs)
def allLt (n : Nat) : List Nat → Bool
  | .nil => .true
  | .cons x xs => Bool.and (Nat.lt x n) (allLt n xs)
def double : List Nat → List Nat
  | .nil => .nil
  | .cons x xs => .cons (x + x) (double xs)
def reach (n : Nat) : Nat → List Nat → Bool
  | .zero, _ => .false
  | .succ fuel, xs => Bool.or (mem n xs) (reach n fuel (.cons 1 (double xs)))
partial def loop (n : Nat) : Bool := loop (n + 1)
partial def upFrom (n i : Nat) : Bool := Bool.or (Nat.beq i n) (upFrom n (i + 1))
def orElse (o : Option Nat) (d : Nat) : Nat := match o with
  | .some x => x
  | .none => d
def pick (o : Option Nat) (xs : List Nat) : Nat := orElse o (List.length (range 50 xs))
def s1 : Bool := mem 3 (range 1000 .nil)
def s2 : Bool := reach 8 100 (.cons 1 .nil)
def s3 : Bool := Bool.and (mem 2000 (range 1000 .nil)) (mem 5 (range 1000 .nil))
def s4 : Nat := pick (.some 4) (range 100 .nil)
def b2n : Bool → Nat
  | .true => 1
  | .false => 0
def foldB (f : Bool → Bool → Bool) : List Bool → Bool
  | .nil => .true
  | .cons b bs => f b (foldB f bs)
def rest : List Nat := .cons (b2n (Bool.and (mem 7 (range 5 .nil)) (loop 0))) (.cons (b2n (Bool.or (mem 3 (range 5 .nil)) (loop 0)))
  (.cons (b2n s1) (.cons (b2n s2) (.cons (b2n s3) (.cons s4 (.cons (b2n (allLt 5 (range 1000 .nil)))
  (.cons (pick .none (range 3 .nil)) (.cons (b2n (foldB Bool.and (.cons .true (.cons .false .nil)))) .nil))))))))
def main : List Nat := .cons (b2n (upFrom 10000000 0)) rest
"

def caseShapeRest : String :=
  ".cons 0 (.cons 1 (.cons 1 (.cons 1 (.cons 0 (.cons 4 (.cons 0 (.cons 53 (.cons 0 .nil))))))))"

def caseShapeExpected : String := s!".cons 1 ({caseShapeRest})"

/-- (15i) Closed top-level definitions (CAFs): a table read in a loop, a definition that
diverges but is used only in a branch never taken, a memoised suspension, a big number, a
proof and a type (erased), one whose evaluation fails (an axiom) in the same branch, a function value, an alias of another constant, and codata
that refers to itself. -/
def cafSrc : String := "import Prelude
def range : Nat → List Nat → List Nat
  | .zero, acc => acc
  | .succ n, acc => range n (.cons n acc)
def sum : List Nat → Nat
  | .nil => 0
  | .cons x xs => x + sum xs
def table : List Nat := range 1000 .nil
partial def forever (n : Nat) : Nat := forever (n + 1)
def diverge : Nat := forever 0
axiom bad : Nat
def failing : Nat := bad + 1
def pick : Bool → Nat
  | .true => diverge + failing
  | .false => 1
def addTen : Nat → Nat := Nat.add 10
def lazySum : Unit → Nat := memo (fun _ => sum table)
def big : Nat := Nat.pow 3 100
def four : 2 + 2 = 4 := refl 4
def Tab : Type := List Nat
def len : List Nat → Nat
  | .nil => 0
  | .cons _ ys => len ys + 1
def tab : Tab := table
coinductive Stream (A : Type) where
  head : A
  tail : Stream A
def ones : Stream Nat
  | .head => 1
  | .tail => ones
def loop : Nat → Nat → Nat
  | .zero, acc => acc
  | .succ n, acc => loop n (acc + sum table + lazySum () + addTen 0 + pick .false + ones.tail.tail.head)
def main : List Nat := .cons (loop 2000 (Nat.mod big 7)) (.cons (len tab) (.cons big .nil))
"

def cafExpected : String :=
  ".cons 1998024004 (.cons 1000 (.cons 515377520732011331036461129765621272702107522001 .nil))"

/-- (15i) An `IO` action as a closed definition: a description, run at each use. -/
def cafIOSrc : String := "import IO
def hello : IO Unit := IO.println \"hello\"
def twice : IO Unit := IO.bind hello (fun _ => hello)
def main : IO Unit := IO.bind twice (fun _ => twice)
"

/-- Build `main` with the C backend and compare its printed value. Skipped (passes) if
the C toolchain can't find GMP: give the suite a toolchain (`Tests/Main.lean`) to run these. -/
def cRun (src : String) (expected : String) (llvm : Bool := false) (split : Nat := 0) : IO Unit := do
  let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := ← preludeLoader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  let dir ← IO.FS.createTempDir
  match ← Build.runGlobal (← toolchain) s "main" dir llvm (split := split) with
  | .ok v => checkEq expected v
  | .error e =>
    let missing := ["gmp.h", "llc:", "No such file"].any fun m => (e.splitOn m).length > 1
    if missing then skip "no toolchain" else throw (IO.userError e)

/-- (15f) Build `main` with the C compiler's optimiser off (`-O0`: it does no tail calls of
its own) and run it on a 1 MB stack (`WIZ_STACK_MB`): deep recursion overflows it, a loop
doesn't. -/
def cRunSmallStack (src : String) (expected : String) (llvm : Bool := false) : IO Unit := do
  let s := runFrontend (R := ZeroOneMany) src { loader := ← preludeLoader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  let tc ← toolchain
  let tc := { tc with cflags := tc.cflags ++ ["-O0"] }
  let dir ← IO.FS.createTempDir
  let exe := dir / "wiz_main"
  let (decls, ty) ← match Build.irProgram s "main" with
    | .ok r => pure r
    | .error e => throw (IO.userError e)
  let built ← if llvm then Build.compileLLVM tc (LLVM.program decls false) exe (Build.extraC s ++ "\n" ++ C.glue (C.externs decls))
    else Build.compileC tc (C.program decls false (Build.extraC s)) exe
  match built with
  | .error e =>
    let missing := ["gmp.h", "llc:", "No such file"].any fun m => (e.splitOn m).length > 1
    if missing then skip "no toolchain" else throw (IO.userError e)
  | .ok () =>
    let out ← IO.Process.output { cmd := exe.toString, env := #[("WIZ_STACK_MB", some "1")] }
    unless out.exitCode == 0 do throw (IO.userError s!"the program failed ({out.exitCode}): {out.stderr.take 500}")
    match Build.parseValue out.stdout with
    | none => throw (IO.userError s!"could not read the result: {out.stdout}")
    | some v => checkEq expected (readback s.globals s.builtins (eval s.globals [] ty) v).pretty

/-- (L-1) Diverging terms in 0 positions the kernel checks erased: a constructor field at
0 (`Tagged.mk`, and the implicit one of `L.cons`), and a 0 field of a structure, with other fields
(`S`) and alone (`S1`; whatever the structure's layout, boxed or not). -/
def zeroFieldDecls : String :=
  "partial def loop (u : Unit) : Nat := loop u\n" ++
  "inductive L where\n  | nil\n  | cons {0 ghost : Nat} (x : Nat) (xs : L)\n" ++
  "def len : L → Nat\n  | .nil => 0\n  | .cons x xs => len xs + 1\n" ++
  "inductive Tagged where\n  | mk (0 ghost : Nat) (val : Nat)\ndef Tagged.get : Tagged → Nat\n  | .mk _ v => v\n" ++
  "structure S where\n  0 ghost : Nat\n  val : Nat\nstructure S1 where\n  0 ghost : Nat\n" ++
  "def e1 : Nat := Tagged.get (Tagged.mk (loop ()) 7)\ndef e2 : Nat := (S.mk (loop ()) 8).val\n" ++
  "def e3 : Nat := match S1.mk (loop ()) with\n  | _ => 9\n" ++
  "def e4 : Nat := len (L.cons (ghost := loop ()) 1 (L.cons (ghost := loop ()) 2 L.nil))\n"

/-- Build `main : IO _` with the C backend (and the `IO` library), run it, and hand its
output to `k`. -/
def ioRunWith (src : String) (k : String → IO Unit) (args : Array String := #[]) (llvm : Bool := false)
    (cflags : List String := []) : IO Unit := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let ioLib ← IO.FS.readFile "lib/IO.wiz"
  let effLib ← IO.FS.readFile "lib/Eff.wiz"
  let stdLib ← IO.FS.readFile "lib/Std.wiz"
  let functorLib ← IO.FS.readFile "lib/Functor.wiz"
  let sysLib ← IO.FS.readFile "lib/Sys.wiz"
  let textLib ← IO.FS.readFile "lib/Text.wiz"
  let derivingLib ← IO.FS.readFile "lib/Deriving.wiz"
  let loader : Name → Option String := fun m =>
    if m == "Prelude" then some prelude else if m == "IO" then some ioLib else if m == "Eff" then some effLib
    else if m == "Std" then some stdLib else if m == "Sys" then some sysLib else if m == "Functor" then some functorLib
    else if m == "Text" then some textLib else if m == "Deriving" then some derivingLib else none
  let headers ← Build.preprocessHeaders (← toolchain) src
  let s := runFrontend (R := ZeroOneMany) src { loader, trustedModule := Tests.libModule, cHeaders := (headers[·]?) }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  let dir ← IO.FS.createTempDir
  let tc ← toolchain
  match ← Build.runGlobal { tc with cflags := tc.cflags ++ cflags } s "main" dir llvm (timeout := some 120) (args := args) with
  | .ok v => k v
  | .error e =>
    let missing := ["gmp.h", "llc:", "No such file"].any fun m => (e.splitOn m).length > 1
    if missing then skip "no toolchain" else throw (IO.userError e)

/-- Build `main : IO _` with the C backend (and the `IO` library) and compare its output. -/
def ioRun (src : String) (expected : String) (args : Array String := #[]) (llvm : Bool := false)
    (cflags : List String := []) : IO Unit :=
  ioRunWith src (checkEq expected ·) args llvm cflags

def ioFails (src : String) (fragment : String) : IO Unit := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let ioLib ← IO.FS.readFile "lib/IO.wiz"
  let effLib ← IO.FS.readFile "lib/Eff.wiz"
  let loader : Name → Option String := fun m =>
    if m == "Prelude" then some prelude else if m == "IO" then some ioLib else if m == "Eff" then some effLib else none
  let s := runFrontend (R := ZeroOneMany) src { loader, trustedModule := Tests.libModule }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.size == 1 do throw (IO.userError s!"expected one error, got {errs.size}: {errs}")
  unless (errs[0]!.splitOn fragment).length > 1 do throw (IO.userError s!"error does not mention '{fragment}':\n{errs[0]!}")

/-- (9f) Elaborate `main.wiz` in a fresh directory holding `files` (modules under it are
importable), resolving `link_c` files as `wiz` does, relative to each file. -/
def elabTree (files : List (String × String)) : IO (CommandState ZeroOneMany × String × System.FilePath) := do
  let dir ← IO.FS.createTempDir
  for (p, text) in files do
    let f := dir / p
    if let some d := f.parent then IO.FS.createDirAll d
    IO.FS.writeFile f text
  let src ← IO.FS.readFile (dir / "main.wiz")
  let mods ← Module.loadClosure ["lib", dir] src
  let sources ← Module.cSourceTable dir src mods
  let s := runFrontend (R := ZeroOneMany) src
    { loader := fun m => (mods[m]?).map (·.2), cSources := some (Module.cSourceResolver sources) }
  pure (s, src, dir)

/-- `elabTree`, then build and run `main` (through C, or LLVM) and compare its output. -/
def linkRun (files : List (String × String)) (expected : String) (llvm : Bool := false) : IO Unit := do
  let (s, src, dir) ← elabTree files
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  match ← Build.runGlobal (← toolchain) s "main" dir llvm (timeout := some 120) with
  | .ok v => checkEq expected v
  | .error e =>
    let missing := ["gmp.h", "llc:"].any fun m => (e.splitOn m).length > 1
    if missing then skip "no toolchain" else throw (IO.userError e)

/-- A program that links a C file (with a static helper and a header the FFI can't bind)
and the maths library. -/
def linkFiles : List (String × String) :=
  [("main.wiz", "import IO\nlink_c \"c/twice.c\"\nlink_lib \"m\"\n" ++
      "extern \"twice\" twice : Nat → Nat\nextern \"root_of\" rootOf : Nat → IO Nat\n" ++
      "def main : IO Unit := do\n  IO.println (Nat.toString (twice 21));\n  r ← rootOf 1764;\n  IO.println (Nat.toString r)\n"),
   ("c/twice.c", "#include <stdint.h>\n#include <math.h>\nstruct box { uint64_t v; };\n" ++
      "static uint64_t unbox(struct box *b) { return b->v; }\n" ++
      "uint64_t twice(uint64_t n) { struct box b = { 2 * n }; return unbox(&b); }\n" ++
      "uint64_t root_of(uint64_t n) { volatile double d = (double)n; return (uint64_t)sqrt(d); }\n")]

def sysShow : String :=
  "def showList : List String → String\n  | .nil => \"\"\n  | .cons x xs => String.append x (String.append \";\" (showList xs))\n" ++
  "def say (s : String) : EIO Unit := EIO.lift (IO.println s)\n" ++
  "def yesNo : Bool → String\n  | .true => \"yes\"\n  | .false => \"no\"\n" ++
  "def orUnset : Option String → String\n  | .some s => s\n  | .none => \"(unset)\"\n"

/-! Byte I/O, descriptors with time limits, spawn options (sys-bytes; docs/stages/09-ffi.md, 9k). -/

def sysBytesShow : String := sysShow ++ r#"def showR : List Readiness → String
  | .nil => ""
  | .cons r rs => String.append (Nat.toString r.index) (String.append (yesNo r.readable) (String.append (yesNo r.hangup) (String.append ";" (showR rs))))
def utf8 (b : Bytes) : String := match Bytes.toUtf8 b with
  | .ok s => s
  | .error e => e
def gotShow {t : Bool} (all : Bytes) (g : Got t) : String := match g with
  | .all b => String.append "all " (yesNo (Bytes.eq b all))
  | .eof b => String.append "eof after " (Nat.toString (Bytes.size b))
  | .timeout b => String.append "timeout after " (Nat.toString (Bytes.size b))
"#

/-! ### Stage 9g: callbacks and exported functions -/

/-- The frontend's state for a test program (with the libraries `ioRun` has). -/
def ffiState (src : String) : IO (CommandState ZeroOneMany) := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let ioLib ← IO.FS.readFile "lib/IO.wiz"
  let loader : Name → Option String := fun m =>
    if m == "Prelude" then some prelude else if m == "IO" then some ioLib else none
  let s := runFrontend (R := ZeroOneMany) src { loader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  pure s

/-- Run `main` linked with a C file `csrc`, through both backends. -/
def ioRunC (src csrc expected : String) (fails : Option String := none) : IO Unit := do
  let s ← ffiState src
  for llvm in [false, true] do
    let dir ← IO.FS.createTempDir
    IO.FS.writeFile (dir / "helper.c") csrc
    let tc ← toolchain
    let tc := { tc with libs := tc.libs ++ [(dir / "helper.c").toString] }
    match ← Build.runGlobal tc s "main" dir llvm (timeout := some 120) with
    | .ok v => if fails.isSome then throw (IO.userError s!"expected a failure, got {v}") else checkEq expected v
    | .error e =>
      if ["gmp.h", "llc:", "No such file"].any fun m => (e.splitOn m).length > 1 then
        skip "no toolchain"
      else match fails with
        | some frag => unless (e.splitOn frag).length > 1 do throw (IO.userError s!"error does not mention '{frag}':\n{e}")
        | none => throw (IO.userError s!"{if llvm then "(llvm) " else ""}{e}")

/-- Build the exports of `src` as a library (`wiz build --lib`), link it with the C
program `csrc` (which includes `lib.h`), run it. Both backends. -/
def libRunC (src csrc expected : String) : IO Unit := do
  let s ← ffiState src
  for llvm in [false, true] do
    let dir ← IO.FS.createTempDir
    let tc ← toolchain
    match ← Build.build tc s "main" (dir / "lib.o") llvm true with
    | .error e =>
      if ["gmp.h", "llc:", "No such file"].any fun m => (e.splitOn m).length > 1 then
        skip "no toolchain"
      else throw (IO.userError s!"{if llvm then "(llvm) " else ""}{e}")
    | .ok _ =>
      IO.FS.writeFile (dir / "main.c") csrc
      let exe := (dir / "prog").toString
      let out ← IO.Process.output { cmd := tc.cc, args := #["-w", "-I", dir.toString, "-o", exe, (dir / "main.c").toString,
        (dir / "lib.o").toString] ++ tc.cflags.toArray ++ tc.gmp.toArray ++ tc.ldflags.toArray ++ tc.libs.toArray }
      unless out.exitCode == 0 do throw (IO.userError s!"cc failed: {out.stderr}")
      let r ← IO.Process.output { cmd := exe }
      unless r.exitCode == 0 do throw (IO.userError s!"the program failed ({r.exitCode}): {r.stderr}")
      checkEq expected r.stdout

def sortHelper : String := "#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef int (*cmp_fn)(void *, uint64_t, uint64_t);
static cmp_fn g_fn; static void *g_ctx;
static int cmp(const void *a, const void *b) {
  uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
  return g_fn(g_ctx, x, y) ? -1 : g_fn(g_ctx, y, x) ? 1 : 0;
}
/* sort some numbers with qsort and a Wiz comparator; the result as text */
const char *sort_some(cmp_fn lt, void *ctx) {
  static char buf[64];
  uint64_t a[] = {5, 3, 9, 1, 7, 4};
  g_fn = lt; g_ctx = ctx;
  qsort(a, 6, sizeof a[0], cmp);
  buf[0] = 0;
  for (int i = 0; i < 6; i++) sprintf(buf + strlen(buf), i ? \" %llu\" : \"%llu\", (unsigned long long)a[i]);
  return buf;
}
"

def tickHelper : String := "#include <stdint.h>
void wiz_release(void *v);
typedef void (*tick_fn)(void *, uint64_t);
static tick_fn s_fn; static void *s_ctx;
/* keep a callback (and its reference) for later */
void on_tick(tick_fn f, void *ctx) { if (s_ctx) wiz_release(s_ctx); s_fn = f; s_ctx = ctx; }
void tick(uint64_t n) { for (uint64_t i = 0; i < n; i++) if (s_ctx) s_fn(s_ctx, i); }
void forget(void) { if (s_ctx) wiz_release(s_ctx); s_ctx = 0; }
"

-- the generators of Wiz source moved to `Wiz/Selfhost.lean` (grail builds the
-- self-hosted toolchain too); the names stay here for the scripts that use them
export Wiz.Selfhost (wizLit wizPD wizList wizTables)

/-- Level expressions over parameters, for the declaration test. -/
inductive MLvl where
  | num (n : Nat)
  | param (u : String)
  | succ (l : MLvl)
  | max (a b : MLvl)
  | imax (a b : MLvl)
  deriving Inhabited

def MLvl.toWiz : MLvl → String
  | num n => s!"(.lnum {n})"
  | param u => s!"(.lparam \"{u}\")"
  | succ l => s!"(.lsucc {l.toWiz})"
  | max a b => s!"(.lmax {a.toWiz} {b.toWiz})"
  | imax a b => s!"(.limax {a.toWiz} {b.toWiz})"

def MLvl.toLevel : MLvl → Level
  | num n => Level.ofNat n
  | param u => .param u
  | succ l => .succ l.toLevel
  | max a b => .max a.toLevel b.toLevel
  | imax a b => .imax a.toLevel b.toLevel

def MLvl.pretty : MLvl → String
  | num n => toString n
  | param u => u
  | succ l => s!"({l.pretty})+1"
  | max a b => s!"max({a.pretty}, {b.pretty})"
  | imax a b => s!"imax({a.pretty}, {b.pretty})"

/-- A random level over `u` and `v`. -/
partial def MLvl.gen (s : Nat) (depth : Nat) : MLvl × Nat :=
  let s := (s * 1103515245 + 12345) % 2147483648
  if depth == 0 then
    match s / 7 % 4 with
    | 0 => (num (s / 11 % 3), s)
    | 1 => (param "u", s)
    | 2 => (param "v", s)
    | _ => (num 0, s)
  else match s / 7 % 5 with
    | 0 => let (l, s) := gen s (depth - 1); (succ l, s)
    | 1 => let (a, s) := gen s (depth - 1); let (b, s) := gen s (depth - 1); (max a b, s)
    | 2 => let (a, s) := gen s (depth - 1); let (b, s) := gen s (depth - 1); (imax a b, s)
    | _ => gen s 0

/-- An equivalent level, by rewriting with identities that hold at every level. -/
partial def MLvl.rewrite (s : Nat) : MLvl → MLvl × Nat
  | l =>
    let s := (s * 1103515245 + 12345) % 2147483648
    match l, s / 7 % 6 with
    | max a b, 0 => let (b, s) := rewrite s b; let (a, s) := rewrite s a; (max b a, s)
    | max a b, 1 => let (a, s) := rewrite s a; (max a (max b a), s)
    | succ (max a b), 2 => (max (succ a) (succ b), s)
    | imax a (succ b), 3 => (max a (succ b), s)
    | imax a b, 4 => let (a, s) := rewrite s a; (imax (max a b) b, s)
    | succ l, _ => let (l, s) := rewrite s l; (succ l, s)
    | max a b, _ => let (a, s) := rewrite s a; let (b, s) := rewrite s b; (max a b, s)
    | imax a b, _ => let (a, s) := rewrite s a; let (b, s) := rewrite s b; (imax a b, s)
    | l, 5 => (max l (num 0), s)
    | l, _ => (l, s)

/-- The core calculus of `selfhost/Kernel.wiz`, for differential tests against the
Lean kernel. -/
inductive MTm where
  | var (i : Nat)
  | univ (n : Nat)
  | pi (a b : MTm)
  | lam (b : MTm)
  | app (f a : MTm)
  | letE (ty v b : MTm)
  | ann (t ty : MTm)
  | sigma (a b : MTm)
  | pair (a b : MTm)
  | fst (p : MTm)
  | snd (p : MTm)
  | unit (n : Nat)
  | star
  | empty (n : Nat)
  | exfalso (m t : MTm)
  /-- `let () := u; b`, the unit eliminator (linear-case stage 2) -/
  | letUnit (u b : MTm)
  | enum (k : Nat)
  | tag (k i : Nat)
  | ecase (m s : MTm) (bs : List MTm)
  | prop
  | ptrue
  | pfalse
  | eq (A a b : MTm)
  | eqTy (A B : MTm)
  | refl (A a : MTm)
  | reflTy (X : MTm)
  | cast (A B e t : MTm)
  | transp (A a P p b e : MTm)
  | desc (l : Nat) (I : MTm)
  | dret (i : MTm)
  /-- (21x) a field's quantity, last (ω by default) -/
  | darg (S E : MTm) (q : ZeroOneMany := .many)
  | drec (j E : MTm) (q : ZeroOneMany := .many)
  | dhrec (H j E : MTm) (q : ZeroOneMany := .many)
  | delim (v : Nat) (P a b c h D : MTm)
  | mu (l : Nat) (I D i : MTm)
  | con (x : MTm)
  | ind (l : Nat) (I D : MTm) (v : Nat) (P m i x : MTm)
  /-- a global, from `globalDefs`, at some universe levels -/
  | const (name : String) (levels : List Nat := [])
  /-- `Sort u` for a level parameter (inside universe-polymorphic globals) -/
  | sortParam (u : String)
  /-- `Sort l` for any level expression -/
  | sortLv (l : MLvl)
  /-- binders with a quantity other than ω: `0` or `1` -/
  | piq (q : ZeroOneMany) (a b : MTm)
  | sigmaq (q : ZeroOneMany) (a b : MTm)
  | letq (q : ZeroOneMany) (ty v b : MTm)
  | size
  | szInf
  | szSuc (s : MTm)
  | sizeLt (s : MTm)
  | mus (l : Nat) (I D i s : MTm)
  | sfix (l : Nat) (I D : MTm) (v : Nat) (P f s i x : MTm)
  | nu (l : Nat) (I D i s : MTm)
  | out (x : MTm)
  | cocon (x : MTm)
  | scofix (l : Nat) (I D A f s i a : MTm)
  | coit (l : Nat) (I D S st i s : MTm)
  | scase (l : Nat) (I D : MTm) (v : Nat) (P m s i x : MTm)
  /-- `scase` at a quantity (K1); `scase` is the one at ω -/
  | scaseq (q : ZeroOneMany) (l : Nat) (I D : MTm) (v : Nat) (P m s i x : MTm)
  /-- a `Π`/`Σ` with its components' sorts written (`i`, `j`; mandatory sorts). The others
  (`pi`, `sigma`, …) are written with holes, which each side's sorts pass fills -/
  | sorted (i j : Nat) (t : MTm)
  /-- `ULift A` in `Sort l` for `A : Sort k` (Q4), its constructor and eliminator -/
  | ulift (k l : Nat) (A : MTm)
  | up (a : MTm)
  | down (t : MTm)
  /-- (P2) the proof marker, at a level -/
  | prf (l : MLvl) (t : MTm)
  deriving Inhabited

namespace MTm

/-- The global definitions (or axioms, without a value) the differential test uses, in
order. -/
def natD0 : MTm := darg (enum 2) (lam (ecase (desc 0 (unit 0)) (var 0) [dret star, drec star (dret star)]))
def globalDefs : List (String × List String × Option MTm × MTm) :=
  [("idU", [], some (lam (var 0)), pi (univ 0) (univ 0)),
   ("Nat", [], some (mu 0 (unit 0) natD0 star), univ 0),
   ("zero", [], some (ann (con (pair (tag 2 0) (pair star star))) (const "Nat")), const "Nat"),
   ("one", [], some (ann (con (pair (tag 2 1) (pair (const "zero") (pair star star)))) (const "Nat")), const "Nat"),
   ("twice", [], some (lam (lam (app (var 1) (app (var 1) (var 0))))), pi (pi (univ 0) (univ 0)) (pi (univ 0) (univ 0))),
   ("A", [], none, univ 0),
   ("a", [], none, const "A"),
   -- universe-polymorphic
   ("idP", ["u"], some (lam (lam (var 0))), pi (sortParam "u") (pi (var 0) (var 1))),
   ("constP", ["u", "v"], some (lam (lam (lam (lam (var 1))))),
     pi (sortParam "u") (pi (sortParam "v") (pi (var 1) (pi (var 1) (var 3))))),
   -- a proposition whose value depends on its level and whose type does not: `polyK.{0}`
   -- is `Prop → True`, `polyK.{1}` is `Type → True` (two instances of one constant must
   -- not be identified by their name: the property harness compares them, `Tests/Prop.lean`)
   ("polyK", ["u"], some (pi (sortParam "u") ptrue), prop),
   -- (W1, `wiz-notes/kernel-lint.md`) a proposition that is a theorem at level 0 and false
   -- at level 1, and a case that is stuck on its scrutinee with `A` in its environment
   -- (its propositional Π's carry their sort, `0`: unannotated, a cast between two of
   -- them computes where their equation is stuck, the known U5 class of the property
   -- harness, `Tests/Prop.lean`; `A → Prop` has a sort that depends on `u` and stays bare)
   ("dLv", ["u"], some (pi (sortParam "u") (pi (var 0) (pi (var 1)
     (pi (pi (var 2) prop) (pi (app (var 0) (var 2)) (app (var 1) (var 2))))))), prop),
   ("caseF", [], some (lam (lam (ecase prop (var 0) [var 1]))), pi prop (pi (enum 1) prop))]

/-- (W1) `fun x p => p : (x : Enum 1) → caseF dLv.{l} x → caseF dLv.{l'} x`: the two types
are stuck cases with the same motive and branch terms, whose environments hold `dLv` at
the two levels. Well typed only when `l = l'`. -/
def levelInEnv (l l' : Nat) : MTm :=
  ann (lam (lam (var 0))) (pi (enum 1)
    (pi (app (app (const "caseF") (const "dLv" [l])) (var 0)) (app (app (const "caseF") (const "dLv" [l'])) (var 1))))

def qWiz : ZeroOneMany → String
  | .zero => ".qz"
  | .one => ".qo"
  | .many => ".qw"

def labels (k : Nat) : List Name := (List.range k).map (s!"a{·}")

partial def toWiz : MTm → String
  | var i => s!"(.var {i})"
  | univ n => s!"(.univ {n})"
  | pi a b => s!"(.pi .qw .lhole .lhole {a.toWiz} {b.toWiz})"
  | lam b => s!"(.lam {b.toWiz})"
  | app f a => s!"(.app {f.toWiz} {a.toWiz})"
  | letE t v b => s!"(.letE {t.toWiz} {v.toWiz} {b.toWiz})"
  | ann t ty => s!"(.ann {t.toWiz} {ty.toWiz})"
  | sigma a b => s!"(.sigma .qw .lhole .lhole {a.toWiz} {b.toWiz})"
  | pair a b => s!"(.pair {a.toWiz} {b.toWiz})"
  | fst p => s!"(.fst {p.toWiz})"
  | snd p => s!"(.snd {p.toWiz})"
  | unit n => s!"(.unit {n})"
  | star => ".star"
  | empty n => s!"(.empty {n})"
  | exfalso m t => s!"(.exfalso {m.toWiz} {t.toWiz})"
  | letUnit u b => s!"(.letUnit {u.toWiz} {b.toWiz})"
  | enum k => s!"(.enum {k})"
  | tag k i => s!"(.tag {k} {i})"
  | ecase m s bs => s!"(.ecase {m.toWiz} {s.toWiz} {bs.foldr (fun b acc => s!"(.tcons {b.toWiz} {acc})") ".tnil"})"
  | prop => ".prop"
  | ptrue => ".ptrue"
  | pfalse => ".pfalse"
  | eq A a b => s!"(.eq {A.toWiz} {a.toWiz} {b.toWiz})"
  | eqTy A B => s!"(.eqTy {A.toWiz} {B.toWiz})"
  | refl A a => s!"(.eqRefl {A.toWiz} {a.toWiz})"
  | reflTy X => s!"(.tyRefl {X.toWiz})"
  | sorted i j t => match t with
    | pi a b => s!"(.pi .qw (.lnum {i}) (.lnum {j}) {a.toWiz} {b.toWiz})"
    | piq q a b => s!"(.pi {qWiz q} (.lnum {i}) (.lnum {j}) {a.toWiz} {b.toWiz})"
    | sigma a b => s!"(.sigma .qw (.lnum {i}) (.lnum {j}) {a.toWiz} {b.toWiz})"
    | sigmaq q a b => s!"(.sigma {qWiz q} (.lnum {i}) (.lnum {j}) {a.toWiz} {b.toWiz})"
    | t => t.toWiz
  | cast A B e t => s!"(.coe {A.toWiz} {B.toWiz} {e.toWiz} {t.toWiz})"
  | transp A a P p b e => s!"(.subst {A.toWiz} {a.toWiz} {P.toWiz} {p.toWiz} {b.toWiz} {e.toWiz})"
  | desc l I => s!"(.descr {l} {I.toWiz})"
  | dret i => s!"(.dret {i.toWiz})"
  | darg S E q => s!"(.darg (.qlit {qWiz q}) {S.toWiz} {E.toWiz})"
  | drec j E q => s!"(.drec (.qlit {qWiz q}) {j.toWiz} {E.toWiz})"
  | dhrec H j E q => s!"(.dhrec (.qlit {qWiz q}) {H.toWiz} {j.toWiz} {E.toWiz})"
  | delim v P a b c h D => s!"(.delim {v} {P.toWiz} {a.toWiz} {b.toWiz} {c.toWiz} {h.toWiz} {D.toWiz})"
  | mu l I D i => s!"(.mu {l} {I.toWiz} {D.toWiz} {i.toWiz})"
  | con x => s!"(.con {x.toWiz})"
  | ind l I D v P m i x => s!"(.ind {l} {I.toWiz} {D.toWiz} {v} {P.toWiz} {m.toWiz} {i.toWiz} {x.toWiz})"
  | const n ls => match globalDefs.find? (·.1 == n) with
    | some (_, ps, some v, ty) =>
      let psW := ps.foldr (fun p acc => s!"(.cons \"{p}\" {acc})") ".nil"
      let lsW := ls.foldr (fun l acc => s!"(.cons (.lnum {l}) {acc})") ".nil"
      -- (the value with its proof markers and sorts, as the frontend stores it)
      s!"(.const \"{n}\" {psW} {lsW} (markClosed {v.toWiz} (sortsTy {ty.toWiz})) (sortsTy {ty.toWiz}))"
    | some (_, _, none, ty) => s!"(.axiomC \"{n}\" (sortsTy {ty.toWiz}))"
    | none => "(.var 999)"
  | sortParam u => s!"(.sortL (.lparam \"{u}\"))"
  | sortLv l => s!"(.sortL {l.toWiz})"
  | piq q a b => s!"(.pi {qWiz q} .lhole .lhole {a.toWiz} {b.toWiz})"
  | sigmaq q a b => s!"(.sigma {qWiz q} .lhole .lhole {a.toWiz} {b.toWiz})"
  | letq q t v b => s!"(.letq {qWiz q} {t.toWiz} {v.toWiz} {b.toWiz})"
  | size => ".size"
  | szInf => ".szInf"
  | szSuc s => s!"(.szSuc {s.toWiz})"
  | sizeLt s => s!"(.sizeLt {s.toWiz})"
  | mus l I D i s => s!"(.mus {l} {I.toWiz} {D.toWiz} {i.toWiz} {s.toWiz})"
  | sfix l I D v P f s i x => s!"(.sfix {l} {I.toWiz} {D.toWiz} {v} {P.toWiz} {f.toWiz} {s.toWiz} {i.toWiz} {x.toWiz})"
  | nu l I D i s => s!"(.nu {l} {I.toWiz} {D.toWiz} {i.toWiz} {s.toWiz})"
  | out x => s!"(.out {x.toWiz})"
  | cocon x => s!"(.cocon {x.toWiz})"
  | scofix l I D A f s i a => s!"(.scofix {l} {I.toWiz} {D.toWiz} {A.toWiz} {f.toWiz} {s.toWiz} {i.toWiz} {a.toWiz})"
  | coit l I D S st i s => s!"(.coit {l} {I.toWiz} {D.toWiz} {S.toWiz} {st.toWiz} {i.toWiz} {s.toWiz})"
  | scaseq q l I D v P m s i x => s!"(.scase {l} {qWiz q} {I.toWiz} {D.toWiz} {v} {P.toWiz} {m.toWiz} {s.toWiz} {i.toWiz} {x.toWiz})"
  | scase l I D v P m s i x => s!"(.scase {l} .qw {I.toWiz} {D.toWiz} {v} {P.toWiz} {m.toWiz} {s.toWiz} {i.toWiz} {x.toWiz})"
  | ulift k l A => s!"(.ulift {k} {l} {A.toWiz})"
  | up a => s!"(.up {a.toWiz})"
  | down t => s!"(.down {t.toWiz})"
  | prf l t => s!"(.prf {l.toWiz} {t.toWiz})"

partial def toTerm : MTm → Term ZeroOneMany
  | var i => .var i
  | univ n => .sort (Level.ofNat (n + 1))
  | pi a b => .pi "x" .default (.qlit .many) a.toTerm b.toTerm .hole
  | lam b => .lam "x" b.toTerm
  | app f a => .app f.toTerm a.toTerm
  | letE t v b => .letE "x" (.qlit .many) t.toTerm v.toTerm b.toTerm
  | ann t ty => .ann t.toTerm ty.toTerm
  | sigma a b => .sigma "x" (.qlit .many) a.toTerm b.toTerm .hole
  | pair a b => .pair a.toTerm b.toTerm
  | fst p => .fst p.toTerm
  | snd p => .snd p.toTerm
  | unit n => .unit (Level.ofNat (n + 1))
  | star => .tt
  | empty n => .empty (Level.ofNat (n + 1))
  | exfalso m t => .absurd m.toTerm t.toTerm
  | letUnit u b => .letUnit u.toTerm b.toTerm
  | enum k => .enum (labels k)
  | tag k i => .tag (labels k) i
  | ecase m s bs => .ecase "z" m.toTerm s.toTerm (bs.map toTerm)
  | prop => .sort .zero
  | ptrue => .unit .zero
  | pfalse => .empty .zero
  | eq A a b => .eq A.toTerm a.toTerm b.toTerm
  | eqTy A B => .eqTy A.toTerm B.toTerm
  | refl A a => .refl A.toTerm a.toTerm
  | reflTy X => .reflTy X.toTerm
  | sorted i j t => match t.toTerm with
    | .pi x bi q a b _ => .pi x bi q a b ⟨Level.ofNat i, Level.ofNat j⟩
    | .sigma x q a b _ => .sigma x q a b ⟨Level.ofNat i, Level.ofNat j⟩
    | u => u
  | cast A B e t => .cast A.toTerm B.toTerm e.toTerm t.toTerm
  | transp A a P p b e => .transp A.toTerm a.toTerm P.toTerm p.toTerm b.toTerm e.toTerm
  | desc l I => .desc (Level.ofNat l) I.toTerm
  | dret i => .dret i.toTerm
  | darg S E q => .darg (.qlit q) S.toTerm E.toTerm
  | drec j E q => .drec (.qlit q) j.toTerm E.toTerm
  | dhrec H j E q => .dhrec (.qlit q) H.toTerm j.toTerm E.toTerm
  | delim v P a b c h D => .delim (Level.ofNat v) P.toTerm a.toTerm b.toTerm c.toTerm h.toTerm D.toTerm
  | mu l I D i => .mu (Level.ofNat l) I.toTerm D.toTerm i.toTerm .szInf none
  | con x => .con x.toTerm
  | ind l I D v P m i x => .ind (Level.ofNat l) I.toTerm D.toTerm (Level.ofNat v) P.toTerm m.toTerm i.toTerm x.toTerm
  | const n ls => .const n (ls.map Level.ofNat)
  | sortParam u => .sort (.param u)
  | sortLv l => .sort l.toLevel
  | piq q a b => .pi "x" .default (.qlit q) a.toTerm b.toTerm .hole
  | sigmaq q a b => .sigma "x" (.qlit q) a.toTerm b.toTerm .hole
  | letq q t v b => .letE "x" (.qlit q) t.toTerm v.toTerm b.toTerm
  | size => .size
  | szInf => .szInf
  | szSuc s => .szSuc s.toTerm
  | sizeLt s => .sizeLt s.toTerm
  | mus l I D i s => .mu (Level.ofNat l) I.toTerm D.toTerm i.toTerm s.toTerm none
  | sfix l I D v P f s i x => .sfix (Level.ofNat l) I.toTerm D.toTerm (Level.ofNat v) P.toTerm f.toTerm s.toTerm i.toTerm x.toTerm
  | nu l I D i s => .nu (Level.ofNat l) I.toTerm D.toTerm i.toTerm s.toTerm none
  | out x => .out x.toTerm
  | cocon x => .cocon x.toTerm
  | scofix l I D A f s i a => .scofix (Level.ofNat l) I.toTerm D.toTerm A.toTerm f.toTerm s.toTerm i.toTerm a.toTerm
  | coit l I D S st i s => .coit (Level.ofNat l) I.toTerm D.toTerm S.toTerm st.toTerm i.toTerm s.toTerm
  | scaseq q l I D v P m s i x => .scase (Level.ofNat l) (.qlit q) I.toTerm D.toTerm (Level.ofNat v) P.toTerm m.toTerm s.toTerm i.toTerm x.toTerm
  | scase l I D v P m s i x => .scase (Level.ofNat l) (.qlit .many) I.toTerm D.toTerm (Level.ofNat v) P.toTerm m.toTerm s.toTerm i.toTerm x.toTerm
  | ulift k l A => .ulift (Level.ofNat k) (Level.ofNat l) A.toTerm
  | up a => .up a.toTerm
  | down t => .down t.toTerm
  | prf l t => .prf l.toLevel t.toTerm

/-- A `Π`/`Σ` read back with its sorts, when they are closed numbers. -/
def sortedOf (σ : BinderSorts) (t : MTm) : MTm :=
  match σ.dom.toNat?, σ.cod.toNat? with
  | some i, some j => sorted i j t
  | _, _ => t

partial def ofTerm : Term ZeroOneMany → Option MTm
  | .var i => some (var i)
  | .sort l => match l.toNat? with
    | some (n + 1) => some (univ n)
    | some 0 => some prop
    | _ => none
  | .pi _ _ (.qlit .many) a b σ => return sortedOf σ (pi (← ofTerm a) (← ofTerm b))
  | .pi _ _ (.qlit q) a b σ => return sortedOf σ (piq q (← ofTerm a) (← ofTerm b))
  | .lam _ b => return lam (← ofTerm b)
  | .app f a => return app (← ofTerm f) (← ofTerm a)
  | .sigma _ (.qlit .many) a b σ => return sortedOf σ (sigma (← ofTerm a) (← ofTerm b))
  | .sigma _ (.qlit q) a b σ => return sortedOf σ (sigmaq q (← ofTerm a) (← ofTerm b))
  | .pair a b => return pair (← ofTerm a) (← ofTerm b)
  | .fst p => return fst (← ofTerm p)
  | .snd p => return snd (← ofTerm p)
  | .unit l => match l.toNat? with
    | some (n + 1) => some (unit n)
    | some 0 => some ptrue
    | _ => none
  | .tt => some star
  | .empty l => match l.toNat? with
    | some (n + 1) => some (empty n)
    | some 0 => some pfalse
    | _ => none
  | .absurd m t => return exfalso (← ofTerm m) (← ofTerm t)
  | .letUnit u b => return letUnit (← ofTerm u) (← ofTerm b)
  | .enum ls => some (enum ls.length)
  | .tag ls i => some (tag ls.length i)
  | .ecase _ m s bs => return ecase (← ofTerm m) (← ofTerm s) (← bs.mapM ofTerm)
  | .eq A a b => return eq (← ofTerm A) (← ofTerm a) (← ofTerm b)
  | .eqTy A B => return eqTy (← ofTerm A) (← ofTerm B)
  | .refl A a => return refl (← ofTerm A) (← ofTerm a)
  | .reflTy X => return reflTy (← ofTerm X)
  | .cast A B e t => return cast (← ofTerm A) (← ofTerm B) (← ofTerm e) (← ofTerm t)
  | .transp A a P p b e => return transp (← ofTerm A) (← ofTerm a) (← ofTerm P) (← ofTerm p) (← ofTerm b) (← ofTerm e)
  | .desc l I => return desc (← l.toNat?) (← ofTerm I)
  | .dret i => return dret (← ofTerm i)
  | .darg (.qlit q) S E => return darg (← ofTerm S) (← ofTerm E) q
  | .drec (.qlit q) j E => return drec (← ofTerm j) (← ofTerm E) q
  | .dhrec (.qlit q) H j E => return dhrec (← ofTerm H) (← ofTerm j) (← ofTerm E) q
  | .delim v P a b c h D => return delim (← v.toNat?) (← ofTerm P) (← ofTerm a) (← ofTerm b) (← ofTerm c) (← ofTerm h) (← ofTerm D)
  | .mu l I D i .szInf _ => return mu (← l.toNat?) (← ofTerm I) (← ofTerm D) (← ofTerm i)
  | .mu l I D i s _ => return mus (← l.toNat?) (← ofTerm I) (← ofTerm D) (← ofTerm i) (← ofTerm s)
  | .nu l I D i s _ => return nu (← l.toNat?) (← ofTerm I) (← ofTerm D) (← ofTerm i) (← ofTerm s)
  | .out x => return out (← ofTerm x)
  | .cocon x => return cocon (← ofTerm x)
  | .scofix l I D A f s i a => return scofix (← l.toNat?) (← ofTerm I) (← ofTerm D) (← ofTerm A) (← ofTerm f) (← ofTerm s) (← ofTerm i) (← ofTerm a)
  | .coit l I D S st i s => return coit (← l.toNat?) (← ofTerm I) (← ofTerm D) (← ofTerm S) (← ofTerm st) (← ofTerm i) (← ofTerm s)
  | .sfix l I D v P f s i x => return sfix (← l.toNat?) (← ofTerm I) (← ofTerm D) (← v.toNat?) (← ofTerm P) (← ofTerm f) (← ofTerm s) (← ofTerm i) (← ofTerm x)
  | .scase l (.qlit .many) I D v P m s i x => return scase (← l.toNat?) (← ofTerm I) (← ofTerm D) (← v.toNat?) (← ofTerm P) (← ofTerm m) (← ofTerm s) (← ofTerm i) (← ofTerm x)
  | .scase l (.qlit q) I D v P m s i x => return scaseq q (← l.toNat?) (← ofTerm I) (← ofTerm D) (← v.toNat?) (← ofTerm P) (← ofTerm m) (← ofTerm s) (← ofTerm i) (← ofTerm x)
  | .size => some size
  | .szInf => some szInf
  | .szSuc s => return szSuc (← ofTerm s)
  | .sizeLt s => return sizeLt (← ofTerm s)
  | .con x => return con (← ofTerm x)
  | .ind l I D v P m i x => return ind (← l.toNat?) (← ofTerm I) (← ofTerm D) (← v.toNat?) (← ofTerm P) (← ofTerm m) (← ofTerm i) (← ofTerm x)
  | .const n us => return const n (← us.mapM Level.toNat?)
  | .ulift k l A => return ulift (← k.toNat?) (← l.toNat?) (← ofTerm A)
  | .up a => return up (← ofTerm a)
  | .down t => return down (← ofTerm t)
  -- (the marker is not printed)
  | .prf _ t => ofTerm t
  | _ => none

/-- (21x) a description field's quantity, as `Kernel.wiz`'s `show` prints it: nothing at ω -/
def fieldQPre : ZeroOneMany → String
  | .zero => "0 "
  | .one => "1 "
  | .many => ""

/-- Printed like `show .nil` in `Kernel.wiz`. -/
partial def pretty (l : Nat) : MTm → String
  | var i => s!"x{l - i - 1}"
  | univ n => s!"U{n}"
  | pi a b => s!"(x{l} : {pretty l a}) → {pretty (l + 1) b}"
  | lam b => s!"λx{l}. {pretty (l + 1) b}"
  | app f a => s!"({pretty l f} {pretty l a})"
  | letE _ v b => s!"let x{l} := {pretty l v}; {pretty (l + 1) b}"
  | ann t ty => s!"({pretty l t} : {pretty l ty})"
  | sigma a b => s!"(x{l} : {pretty l a}) × {pretty (l + 1) b}"
  | pair a b => s!"({pretty l a}, {pretty l b})"
  | fst p => s!"{pretty l p}.1"
  | snd p => s!"{pretty l p}.2"
  | unit n => s!"Unit{n}"
  | star => "tt"
  | empty n => s!"Empty{n}"
  | exfalso m t => s!"absurd({pretty l m}, {pretty l t})"
  | letUnit u b => s!"let () := {pretty l u}; {pretty l b}"
  | enum k => s!"Enum{k}"
  | tag _ i => s!"#{i}"
  | ecase m s bs => s!"case({pretty (l + 1) m}, {pretty l s}{String.join (bs.map fun b => ", " ++ pretty l b)})"
  | prop => "Prop"
  | ptrue => "True"
  | pfalse => "False"
  | eq A a b => s!"Eq({pretty l A}, {pretty l a}, {pretty l b})"
  | eqTy A B => s!"EqTy({pretty l A}, {pretty l B})"
  | refl A a => s!"refl({pretty l A}, {pretty l a})"
  | reflTy X => s!"reflTy({pretty l X})"
  | sorted _ _ t => pretty l t
  | cast A B e t => s!"cast({pretty l A}, {pretty l B}, {pretty l e}, {pretty l t})"
  | transp A a P p b e => s!"transp({pretty l A}, {pretty l a}, {pretty l P}, {pretty l p}, {pretty l b}, {pretty l e})"
  | desc k I => s!"Desc{k}({pretty l I})"
  | dret i => s!"ret({pretty l i})"
  | darg S E q => s!"arg({fieldQPre q}{pretty l S}, {pretty l E})"
  | drec j E q => s!"rec({fieldQPre q}{pretty l j}, {pretty l E})"
  | dhrec H j E q => s!"hrec({fieldQPre q}{pretty l H}, {pretty l j}, {pretty l E})"
  | delim _ P a b c h D => s!"elim({pretty l P}, {pretty l a}, {pretty l b}, {pretty l c}, {pretty l h}, {pretty l D})"
  | mu k I D i => s!"μ{k}({pretty l I}, {pretty l D}, {pretty l i})"
  | con x => s!"con({pretty l x})"
  | ind _ _ _ _ P m i x => s!"ind({pretty l P}, {pretty l m}, {pretty l i}, {pretty l x})"
  | const n ls => if ls.isEmpty then n else n ++ ".{" ++ ", ".intercalate (ls.map toString) ++ "}"
  | sortParam u => s!"Sort {u}"
  | sortLv l => s!"Sort({l.pretty})"
  | piq q a b => s!"(x{l} :{q} {pretty l a}) → {pretty (l + 1) b}"
  | sigmaq q a b => s!"(x{l} :{q} {pretty l a}) × {pretty (l + 1) b}"
  | letq _ _ v b => s!"let x{l} := {pretty l v}; {pretty (l + 1) b}"
  | nu k I D i s => s!"ν{k}({pretty l I}, {pretty l D}, {pretty l i}, {pretty l s})"
  | out x => s!"out({pretty l x})"
  | cocon x => s!"cocon({pretty l x})"
  | scofix _ _ _ A f s i a => s!"scofix({pretty l A}, {pretty l f}, {pretty l s}, {pretty l i}, {pretty l a})"
  | coit _ _ _ S st i s => s!"coit({pretty l S}, {pretty l st}, {pretty l i}, {pretty l s})"
  | sfix _ _ _ _ P f s i x => s!"sfix({pretty l P}, {pretty l f}, {pretty l s}, {pretty l i}, {pretty l x})"
  | scaseq q _ _ _ _ P m s i x => s!"scase{q}({pretty l P}, {pretty l m}, {pretty l s}, {pretty l i}, {pretty l x})"
  | scase _ _ _ _ P m s i x => s!"scase({pretty l P}, {pretty l m}, {pretty l s}, {pretty l i}, {pretty l x})"
  | size => "Size"
  | szInf => "∞"
  | szSuc s => s!"↑({pretty l s})"
  | sizeLt s => s!"Size<({pretty l s})"
  | mus k I D i s => s!"μ{k}({pretty l I}, {pretty l D}, {pretty l i}, {pretty l s})"
  | ulift _ k A => s!"ULift{k}({pretty l A})"
  | up a => pretty l a
  | down t => pretty l t
  | prf _ t => pretty l t

/-- A well-typed pair (at random levels), for the generator: `(U k, U k)`, or the
dependent `(U k, λx. x) : (A : U (k+1)) × (A → A)`. -/
def wellTypedPair (s : Nat) : MTm :=
  let k := s / 5 % 2
  if s / 3 % 2 == 0 then ann (pair (univ k) (univ k)) (sigma (univ (k + 1)) (univ (k + 1)))
  else ann (pair (univ k) (lam (var 0))) (sigma (univ (k + 1)) (pi (var 0) (var 1)))

def lams : Nat → MTm → MTm
  | 0, b => b
  | k + 1, b => lam (lams k b)

/-- The natural numbers as a description, `arg Enum2 (fun t => case t [ret tt, rec tt (ret tt)])`. -/
def natD : MTm := darg (enum 2) (lam (ecase (desc 0 (unit 0)) (var 0) [dret star, drec star (dret star)]))
def natTy : MTm := mu 0 (unit 0) natD star
def natAt (s : MTm) : MTm := mus 0 (unit 0) natD star s
/-- streams of bits, the stream that alternates (by coiteration), and zeros (by corecursion) -/
def streamD : MTm := darg (enum 2) (lam (drec star (dret star)))
def streamAt (s : MTm) : MTm := nu 0 (unit 0) streamD star s
def streamTy : MTm := streamAt szInf
def alt : MTm := coit 0 (unit 0) streamD (lam (enum 2))
  (lams 2 (pair (var 0) (pair (ecase (enum 2) (var 0) [tag 2 1, tag 2 0]) (pair star star)))) star (tag 2 0)
def zeros : MTm := scofix 0 (unit 0) streamD (lam (unit 0))
  (lams 4 (cocon (pair (tag 2 0) (pair (app (app (var 2) (var 1)) (var 0)) (pair star star))))) szInf star star
def shead (x : MTm) : MTm := fst (out x)
def stail (x : MTm) : MTm := fst (snd (out x))
def natZero : MTm := ann (con (pair (tag 2 0) (pair star star))) natTy
def natSucc (n : MTm) : MTm := ann (con (pair (tag 2 1) (pair n (pair star star)))) natTy

def eqRefl' (A a : MTm) : MTm := refl A a

/-- The proof of `False` from equivalent propositions of different shapes: `True = (True
→ True)` at `Prop`, carried by `transp` to `(True → Unit) = ((True → True) → Unit)`, whose
first component (the domains' equation) was `False` when domains were compared by shape. -/
def propShapes : List MTm :=
  let T1 := sorted 0 0 (pi ptrue ptrue)
  let G (X : MTm) := sorted 0 1 (pi X (unit 0))
  let e := ann (pair (lam (lam (var 0))) (lam star)) (eq prop ptrue T1)
  let bad := transp prop ptrue (lam (lam (eqTy (G ptrue) (G (var 1))))) (reflTy (G ptrue)) T1 e
  let erasedArg (A : MTm) := app (ann (lam star) (piq .zero A (unit 0))) (fst bad)
  [erasedArg pfalse, erasedArg (eqTy T1 ptrue)]

/-- Finding O1: `Size = Size` is not `False`. The self-hosted kernel counted `Size` and
`Size< s` as type formers, so equations between them (even `Size = Size`) fell through
to "different formers ⇒ False", and `absurd(Empty, reflTy Size) : Empty` checked. In the
Lean kernel these equations stay stuck: the three `absurd`s are rejected, and `reflTy`
has the type `Size = Size` (resp. `Size< ∞ = Size< ∞`). -/
def sizeEq : List MTm :=
  [exfalso (empty 0) (reflTy size), exfalso (empty 0) (reflTy (sizeLt szInf)),
   ann (lam (exfalso (empty 0) (var 0))) (pi (eqTy size (sizeLt szInf)) (empty 0)),
   reflTy size, reflTy (sizeLt szInf)]

/-- Decision D2: `∞` is not below itself (`↑∞ = ∞` makes `↑s ≤ ∞` true of every `s`).
The first five are rejected: `∞` (or `↑∞`) as a `Size< ∞`, a variable of type `Size` (it
may be `∞`), and the loop `sfix (fun s rec i x => rec ∞ i x) ∞ tt 0 : Empty` (its `rec`
takes sizes below the generic `s`, so it was already rejected). The rest are accepted:
a bounded variable and its successors are below `∞`. -/
def sizeInf : List MTm :=
  let sizeArg (A s : MTm) := app (ann (lam star) (piq .zero A (unit 0))) s
  [ann szInf (sizeLt szInf), ann (szSuc szInf) (sizeLt szInf), sizeArg (sizeLt szInf) szInf,
   ann (lam (var 0)) (pi size (sizeLt szInf)),
   sfix 0 (unit 0) natD 1 (lams 2 (empty 0)) (lams 4 (app (app (app (var 2) szInf) (var 1)) (var 0))) szInf star natZero,
   ann (lam (var 0)) (pi (sizeLt szInf) (sizeLt szInf)),
   ann (lam (szSuc (szSuc (var 0)))) (pi (sizeLt szInf) (sizeLt szInf)),
   ann (lam (lam (var 0))) (pi size (pi (sizeLt (var 0)) (sizeLt szInf))),
   ann (lam (lam (szSuc (var 0)))) (pi size (pi (sizeLt (var 0)) (sizeLt (szSuc (var 1))))),
   ann (lam (lam (sizeArg (sizeLt szInf) (var 0)))) (pi size (pi (sizeLt (var 0)) (unit 0)))]

/-- K3: the size of `μ^s`/`ν^s` must be a size. The first two (`tt`, `Enum 2` as sizes) are
rejected, the rest accepted. -/
def sizeArgs : List MTm :=
  [mus 0 (unit 0) natD star star, streamAt (enum 2),
   natAt szInf, ann (lam (natAt (var 0))) (pi size (univ 0)), ann (lam (streamAt (szSuc (var 0)))) (pi size (univ 0))]

/-- Q4 (fixed): a description field must live exactly in `Sort (l+1)`, the universe
`Desc.elim`'s `marg` takes it from. It used to be enough for it to fit (`Sort k`,
`k ≤ l+1`), and universes aren't cumulative, so `Desc.elim` could reduce to a term of the
wrong type: `getS D : Type` was accepted and reduced to `True`, while `True : Type` is
rejected. Now that `D` is rejected (the first four are errors, and so is the last), and the field is lifted
instead: `getS D' : Type` reduces to `ULift True`, which is in `Type`. The rest: the rules
of `ULift` (a boxed proof, `down`, equality and casts, η, the level check). -/
def smallField : List MTm :=
  let getS (D : MTm) := delim 2 (lam (univ 0)) (lam (unit 0)) (lams 4 (var 2)) (lams 4 (unit 0)) (lams 5 (unit 0)) D
  let D := ann (darg ptrue (lam (dret star))) (desc 0 (unit 0))
  -- (`k`: the content's sort, `True : Sort 0`, `Enum 2 : Sort 1`, `Type : Sort 2`)
  let L (A : MTm) := match A with
    | ptrue => ulift 0 1 A
    | univ _ => ulift 2 1 A
    | _ => ulift 1 1 A
  let D' := ann (darg (L ptrue) (lam (dret star))) (desc 0 (unit 0))
  let boxed := ann (up star) (L ptrue)
  let liftedTag (i : Nat) := ann (up (tag 2 i)) (L (enum 2))
  [-- rejected: the small field, `getS` on it, `True : Type`, and `ULift.{1} Type`
   D, ann (getS D) (univ 0), ann ptrue (univ 0), L (univ 0),
   -- accepted: the lifted field; `getS D'` is `ULift True` (by `reflTy`), a type
   D', ann (getS D') (univ 0), ann (reflTy (getS D')) (eqTy (getS D') (L ptrue)),
   ann (con (pair (up star) (pair star star))) (mu 0 (unit 0) D' star),
   -- a boxed proof, its contents, and equality of boxed proofs (`True`)
   boxed, down boxed, ann star (eq (L ptrue) boxed boxed),
   ann (lam (lam star)) (pi (L ptrue) (pi (L ptrue) (eq (L ptrue) (var 1) (var 0)))),
   -- η: a variable of type `ULift A` is `up (down x)`
   ann (lam (refl (L (enum 2)) (var 0))) (pi (L (enum 2)) (eq (L (enum 2)) (var 0) (up (down (var 0))))),
   ann (lam (up (var 0))) (pi (enum 2) (ulift 1 2 (enum 2))),
   -- type equality: `ULift A = ULift B` is `A = B`; `ULift A = A` is `False`
   reflTy (L ptrue), reflTy (L (enum 2)),
   ann (lam (exfalso (empty 0) (var 0))) (pi (eqTy (L (enum 2)) (enum 2)) (empty 0)),
   -- casts go through `down`
   ann star (eq (L (enum 2)) (cast (L (enum 2)) (L (enum 2)) star (liftedTag 1)) (liftedTag 1)),
   -- rejected: boxed different tags are different
   ann star (eq (L (enum 2)) (liftedTag 0) (liftedTag 1))]

/-- F6: two types whose binder quantities are different literals are unequal (`False`, so
the `absurd` checks), and equal literals give the Σ rule. (`MTm` has no quantity variables,
the case F6 was about: its Lean test is in the group *quantity polymorphism*.) -/
def qtyApart : List MTm :=
  let F (q : ZeroOneMany) := sorted 1 1 (piq q (enum 2) (enum 2))
  [ann (lam (exfalso (empty 0) (var 0))) (pi (eqTy (F .zero) (F .one)) (empty 0)),
   ann (lam (exfalso (empty 0) (var 0))) (pi (eqTy (sorted 1 1 (sigmaq .one (enum 2) (enum 2))) (sorted 1 1 (sigma (enum 2) (enum 2)))) (empty 0)),
   ann (lam (exfalso (empty 0) (var 0))) (pi (eqTy (F .one) (F .one)) (empty 0)),
   reflTy (F .one)]

/-- (R1) Projections are available only on unrestricted pairs, and positions at 0 are
erased positions: each term with whether the kernels accept it. -/
def projRule : List (MTm × Bool) := [
   -- (R1) projections need an unrestricted pair, whatever the fields' quantities:
   -- a linear pair is rejected (the last one has a bare second component: the audit's
   -- probe), an unrestricted one and a closed one are accepted
   (ann (lam (snd (var 0))) (piq .one (sigmaq .one (univ 0) (univ 0)) (univ 0)), false),
   (ann (lam (snd (var 0))) (piq .one (sigmaq .many (univ 0) (univ 0)) (univ 0)), false),
   (ann (lam (snd (var 0))) (piq .many (sigmaq .one (univ 0) (univ 0)) (univ 0)), true),
   (snd (ann (pair (enum 2) (enum 2)) (sigmaq .one (univ 0) (univ 0))), true),
   (ann (lam (fst (var 0))) (piq .one (sigma (univ 0) (sigmaq .one (univ 0) (univ 0))) (univ 0)), false),
   (ann (lam (fst (var 0))) (piq .many (sigma (univ 0) (sigmaq .one (univ 0) (univ 0))) (univ 0)), true),
   (ann (lam (fst (var 0))) (piq .one (sigma (univ 0) (sigma (univ 0) (univ 0))) (univ 0)), false),
   (ann (lam (fst (var 0))) (piq .one (sigmaq .one (univ 0) (univ 0)) (univ 0)), false),
   (ann (lam (fst (snd (var 0)))) (piq .one (sigma (univ 0) (sigma (univ 0) (univ 0))) (univ 0)), false),
   (ann (lam (fst (snd (var 0)))) (piq .many (sigma (univ 0) (sigma (univ 0) (univ 0))) (univ 0)), true),
   -- a projection of an expression uses the expression ω times: `(f x).1` with `x` at 1
   -- is rejected, with `x` at ω accepted
   (ann (lam (lam (fst (app (var 1) (var 0))))) (pi (piq .one (univ 0) (sigma (univ 0) (univ 0))) (piq .one (univ 0) (univ 0))), false),
   (ann (lam (lam (fst (app (var 1) (var 0))))) (pi (piq .one (univ 0) (sigma (univ 0) (univ 0))) (piq .many (univ 0) (univ 0))), true),
   -- positions at 0 are erased positions, where a projection is free: the value of a
   -- `let` at 0, the first part of a pair at a 0 field, an argument to a 0 binder
   -- (accepted: the linear pair is then used once, by the body)
   (ann (lam (letq .zero (univ 0) (fst (var 0)) (var 1))) (piq .one (sigma (univ 0) (univ 0)) (sigma (univ 0) (univ 0))), true),
   (ann (lam (pair (fst (var 0)) (var 0))) (piq .one (sigma (univ 0) (univ 0)) (sigmaq .zero (univ 0) (sigma (univ 0) (univ 0)))), true),
   (ann (lam (lam (app (app (var 1) (fst (var 0))) (var 0))))
     (pi (piq .zero (univ 0) (piq .one (sigma (univ 0) (univ 0)) (univ 0))) (piq .one (sigma (univ 0) (univ 0)) (univ 0))), true),
   -- an erased field can be read there (accepted), and not in a `let` at 1 or ω (rejected)
   (ann (lam (letq .zero (univ 0) (fst (var 0)) (snd (var 1)))) (piq .many (sigmaq .zero (univ 0) (univ 0)) (univ 0)), true),
   (ann (lam (letq .one (univ 0) (fst (var 0)) (var 0))) (piq .many (sigmaq .zero (univ 0) (univ 0)) (univ 0)), false),
   -- what a `let` at 0 binds can't be used (rejected), nor can the linear pair go unused
   (ann (lam (letq .zero (univ 0) (fst (var 0)) (var 0))) (piq .many (sigma (univ 0) (univ 0)) (univ 0)), false),
   (ann (lam (letq .zero (univ 0) (fst (var 0)) (enum 2))) (piq .one (sigma (univ 0) (univ 0)) (univ 0)), false)]

/-- The eliminators bind what they take apart at ω, so the scrutinee (the seed) counts ω
times: at 1 it is rejected (the method below ignores it: a linear value would be
dropped), at ω accepted. `ind`, `scase`, `sfix`, `coit`, `scofix`. -/
def elimRule : List (MTm × Bool) :=
  let step := lams 2 (pair (var 0) (pair (ecase (enum 2) (var 0) [tag 2 1, tag 2 0]) (pair star star)))
  let zerosF := lams 4 (cocon (pair (tag 2 0) (pair (app (app (var 2) (var 1)) (var 0)) (pair star star))))
  [ZeroOneMany.one, ZeroOneMany.many].flatMap fun q =>
    let ok := q == ZeroOneMany.many
    [(ann (lam (ind 0 (unit 0) natD 1 (lams 2 (enum 2)) (lams 3 (tag 2 0)) star (var 0))) (piq q natTy (enum 2)), ok),
     (ann (lam (scase 0 (unit 0) natD 1 (lams 2 (enum 2)) (lams 3 (tag 2 0)) szInf star (var 0))) (piq q natTy (enum 2)), ok),
     (ann (lam (sfix 0 (unit 0) natD 1 (lams 2 (enum 2)) (lams 4 (tag 2 0)) szInf star (var 0))) (piq q natTy (enum 2)), ok),
     (ann (lam (coit 0 (unit 0) streamD (lam (enum 2)) step star (var 0))) (piq q (enum 2) streamTy), ok),
     (ann (lam (scofix 0 (unit 0) streamD (lam (unit 0)) zerosF szInf star (var 0))) (piq q (unit 0) streamTy), ok)]

/-- Usage checking at the edges (kernel-lint's findings in Kernel.wiz, whose usage lists
drop trailing zeros): a variable that is never used has usage 0, which a binder at 1 does
not allow; and branches that disagree about a linear variable join to ω, also when one of
them uses no variable at all. -/
def usageRule : List (MTm × Bool) :=
  let caseOn (q : ZeroOneMany) (bs : List MTm) :=
    ann (lam (lam (ecase (enum 2) (var 1) bs))) (pi (enum 2) (piq q (enum 2) (enum 2)))
  [(ann (lam (tag 2 0)) (piq .one (enum 2) (enum 2)), false),
   (ann (lam star) (piq .many (unit 0) (unit 0)), true),
   (ann (lam star) (piq .zero (unit 0) (unit 0)), true),
   (ann (lam (lam (var 1))) (pi (enum 2) (piq .one (enum 2) (enum 2))), false),
   (letq .one (enum 2) (tag 2 0) (tag 2 1), false),
   (letq .many (enum 2) (tag 2 0) (tag 2 1), true),
   (caseOn .one [var 0, tag 2 0], false),
   (caseOn .one [tag 2 0, var 0], false),
   (caseOn .one [var 0, var 0], true),
   (caseOn .one [tag 2 0, tag 2 1], false),
   (caseOn .many [var 0, tag 2 0], true)]

/-- Linear-case stage 2, both kernels. **K1**: `scase` at a quantity `q` binds the payload
at `q` and uses the scrutinee `q` times. At 1, `fun x => scase₁ … (fun j i xs => con xs) x`
rebuilds a linear `Nat` (accepted, also for `x` at ω), a method that drops the payload or
copies it (into a pair: an ω position) is rejected, and so is a linear `x` taken by the
case at ω (the existing rule) or at 0 (unused). At 0 the scrutinee is erased: a method that
ignores the payload is accepted for `x` at 0, one that reads it at run time (`xs.1`, the
tag) is rejected. **No unused linear unit** (K2a was withdrawn): a linear `Unit`, or an erased
function into `Unit`, left unused is rejected; `let () := u; b` consumes a `Unit` (once),
and only a `Unit`: applied to a closure into `Unit` (linear-review's `stash`, which hides a
linear `t` in `(0 e : A = Unit) → Unit`) it is rejected, as is dropping that closure. -/
def linearCaseRule : List (MTm × Bool) :=
  let rebuild := lams 3 (ann (con (var 0)) (mus 0 (unit 0) natD (var 1) (szSuc (var 2))))
  let cs (q : ZeroOneMany) (P m : MTm) := scaseq q 0 (unit 0) natD 1 P m szInf star (var 0)
  let natPair := sigma natTy natTy
  [-- K1 at 1
   (ann (lam (cs .one (lams 2 natTy) rebuild)) (piq .one natTy natTy), true),
   (ann (lam (cs .one (lams 2 natTy) rebuild)) (piq .many natTy natTy), true),
   (ann (lam (cs .one (lams 2 (enum 2)) (lams 3 (tag 2 0)))) (piq .one natTy (enum 2)), false),
   (ann (lam (cs .one (lams 2 natPair)
      (lams 3 (pair (ann (con (var 0)) natTy) (ann (con (var 0)) natTy))))) (piq .one natTy natPair), false),
   (ann (lam (cs .one (lams 2 (enum 2)) (lams 3 (fst (var 0))))) (piq .one natTy (enum 2)), false),
   (ann (lam (cs .many (lams 2 natTy) rebuild)) (piq .one natTy natTy), false),
   (ann (lam (cs .zero (lams 2 (enum 2)) (lams 3 (tag 2 0)))) (piq .one natTy (enum 2)), false),
   -- K1 at 0
   (ann (lam (cs .zero (lams 2 (enum 2)) (lams 3 (tag 2 0)))) (piq .zero natTy (enum 2)), true),
   (ann (lam (cs .zero (lams 2 (enum 2)) (lams 3 (fst (var 0))))) (piq .zero natTy (enum 2)), false),
   (ann (lam (cs .zero (lams 2 (enum 2)) (lams 3 (fst (var 0))))) (piq .many natTy (enum 2)), false),
   -- K1 at ω, as `scase`
   (ann (lam (cs .many (lams 2 (enum 2)) (lams 3 (fst (var 0))))) (piq .many natTy (enum 2)), true),
   -- no unit-shaped binder may go unused (K2a was withdrawn: linear-review's
   -- counterexamples); a linear `Unit` is consumed by `let () := u; b`
   (ann (lam star) (piq .one (unit 0) (unit 0)), false),
   (ann (lam (tag 2 0)) (piq .one (unit 0) (enum 2)), false),
   (letq .one (unit 0) star (tag 2 0), false),
   (ann (lam (tag 2 0)) (piq .one (piq .zero (enum 2) (unit 0)) (enum 2)), false),
   (ann (lam (letUnit (var 0) (tag 2 0))) (piq .one (unit 0) (enum 2)), true),
   (ann (lam (letUnit (var 0) (letUnit (var 0) (tag 2 0)))) (piq .one (unit 0) (enum 2)), false),
   (ann (lam (letUnit (var 0) (tag 2 0))) (piq .zero (unit 0) (enum 2)), false),
   (letUnit star (tag 2 0), true),
   -- the eliminator takes `Unit` only, never a function into it (a closure may hold a resource)
   (ann (lam (letUnit (var 0) (tag 2 0))) (piq .one (piq .zero (enum 2) (unit 0)) (enum 2)), false),
   (ann (lam (letUnit (var 0) (tag 2 0))) (piq .one (enum 1) (enum 2)), false),
   -- linear-review's stash: `(1 t : A)` captured by a closure `(0 e : A = Unit) → Unit`, then
   -- the closure dropped (rejected), or "eliminated" (rejected: not a `Unit`)
   (ann (lam (lam (letq .one (piq .zero (eqTy (var 1) (unit 0)) (unit 0)) (lam (cast (var 2) (unit 0) (var 0) (var 1))) (tag 2 0))))
     (pi (univ 0) (piq .one (var 0) (enum 2))), false),
   (ann (lam (lam (letq .one (piq .zero (eqTy (var 1) (unit 0)) (unit 0)) (lam (cast (var 2) (unit 0) (var 0) (var 1)))
       (letUnit (var 0) (tag 2 0)))))
     (pi (univ 0) (piq .one (var 0) (enum 2))), false),
   -- … and the closure passed to a binder that ignores it (leak4)
   (ann (lam (lam (app (ann (lam (tag 2 0)) (piq .one (piq .zero (eqTy (var 1) (unit 0)) (unit 0)) (enum 2)))
       (lam (cast (var 2) (unit 0) (var 0) (var 1))))))
     (pi (univ 0) (piq .one (var 0) (enum 2))), false)]

/-- The five eliminators that name the index type `I`, at level `l`, on the smallest
descriptions (`ret i`, and `rec i (ret i)` for `ν`), in this order: `ind`, `sfix`,
`scase`, `coit`, `scofix`. All five are well typed when `I` is in `Sort (l+1)`. -/
def elimsAt (l : Nat) (I i : MTm) : List MTm :=
  let uD := dret i
  let sD := drec i (dret i)
  let x := con (pair star star)
  let P := lams 2 (enum 2)
  [ind l I uD 1 P (lams 3 (tag 2 0)) i x,
   sfix l I uD 1 P (lams 4 (tag 2 0)) szInf i x,
   scase l I uD 1 P (lams 3 (tag 2 0)) szInf i x,
   coit l I sD (lam (unit l)) (lams 2 (pair star (pair star star))) i star,
   scofix l I sD (lam (unit l)) (lams 4 (cocon (pair (app (app (var 2) (var 1)) (var 0)) (pair star star)))) szInf i star]

/-- Audit F3 (fixed): an eliminator checks that its index type is in `Sort (l+1)`, as the
type formers `μ`/`ν` do. The eliminators check the scrutinee against `μ.{l} I D i` (or
return `ν.{l} I D i`) without the type former, so they used to accept an index type at
any level: a term could have a type that is not a type. In order: the five eliminators
with the index type one level too high (rejected), one level too low (rejected), then at
level 0 and at level 1 (accepted); last, the result of an ill-levelled `ind` used in an
equation, and the type of an ill-levelled `coit` observed (both rejected). -/
def elimLevels : List MTm :=
  elimsAt 0 (unit 1) star ++ elimsAt 1 (unit 0) star ++ elimsAt 0 (unit 0) star ++ elimsAt 1 (unit 1) star ++
  [ann star (eq (enum 2) (ind 0 (unit 1) (dret star) 1 (lams 2 (enum 2)) (lams 3 (tag 2 0)) star (con (pair star star))) (tag 2 0)),
   fst (out (coit 0 (unit 1) (drec star (dret star)) (lam (unit 0)) (lams 2 (pair star (pair star star))) star star))]

/-- `transp` is for types in `Type u`, like `eq` and `refl` (audit-2): its motive's type
`(0 b : A) → (0 _ : a = b) → Prop` and the type of its proof are equations at `A`, which
the `eq` rule rejects at a proposition. Rejected: `transp` at `True` and at an equation;
accepted: the same at `Unit` and at `Enum2`. -/
def transpProp : List MTm :=
  let e2 := eq (enum 2) (tag 2 0) (tag 2 0)
  [transp ptrue star (lams 2 ptrue) star star star,
   transp e2 star (lams 2 ptrue) star star star,
   transp (unit 0) star (lams 2 ptrue) star star star,
   transp (enum 2) (tag 2 0) (lams 2 ptrue) star (tag 2 0) (refl (enum 2) (tag 2 0))]

/-- Terms the differential test always checks (well-typed ones the generator rarely
builds whole), before the random ones. -/
def samples : List MTm :=
  propShapes ++ qtyApart ++ elimLevels ++ transpProp ++ sizeInf ++ sizeEq ++ sizeArgs ++ smallField ++ projRule.map (·.1) ++ elimRule.map (·.1) ++ usageRule.map (·.1) ++ linearCaseRule.map (·.1) ++ [levelInEnv 0 0, levelInEnv 1 1, levelInEnv 0 1, levelInEnv 1 0,
   natTy, natZero, natSucc natZero, natSucc (natSucc natZero), ann natD (desc 0 (unit 0)),
   eq natTy natZero (natSucc natZero), eq natTy (natSucc natZero) (natSucc natZero), refl natTy (natSucc natZero),
   delim 1 (lam (unit 0)) (lam star) (lams 4 star) (lams 4 star) (lams 5 star) (ann natD (desc 0 (unit 0))),
   ann (con (pair (tag 2 1) (pair star (pair star star)))) natTy,
   ann (con (pair (tag 2 0) star)) natTy,
   -- induction: a constant method, and one that returns the constructor's tag
   ind 0 (unit 0) natD 1 (lams 2 (enum 2)) (lams 3 (tag 2 0)) star natZero,
   ind 0 (unit 0) natD 1 (lams 2 (enum 2)) (lams 3 (fst (var 1))) star (natSucc natZero),
   -- it computes: `tt : ind … 1 = #1` checks, `tt : ind … 1 = #0` doesn't
   ann star (eq (enum 2) (ind 0 (unit 0) natD 1 (lams 2 (enum 2)) (lams 3 (fst (var 1))) star (natSucc natZero)) (tag 2 1)),
   ann star (eq (enum 2) (ind 0 (unit 0) natD 1 (lams 2 (enum 2)) (lams 3 (fst (var 1))) star (natSucc natZero)) (tag 2 0)),
   -- stuck on a variable
   ann (lam (ind 0 (unit 0) natD 1 (lams 2 (enum 2)) (lams 3 (fst (var 1))) star (var 0))) (pi natTy (enum 2)),
   -- an ill-typed method
   ind 0 (unit 0) natD 1 (lams 2 (enum 2)) (lams 3 (var 1)) star natZero,
   -- globals: kept folded in types, unfolded when needed
   const "idU", app (const "idU") (enum 2), ann star (eq (univ 0) (app (const "idU") (enum 2)) (enum 2)),
   const "one", ann (const "zero") (const "Nat"), app (app (const "twice") (const "idU")) (const "A"),
   eq (const "Nat") (const "zero") (const "one"), const "a", app (const "idU") (const "a"),
   ann (lam (var 0)) (pi (const "A") (const "A")),
   ann star (eq (enum 2) (ind 0 (unit 0) natD 1 (lams 2 (enum 2)) (lams 3 (fst (var 1))) star (const "one")) (tag 2 1)),
   ann (eqRefl' (pi (univ 0) (univ 0)) (app (const "twice") (const "idU")))
     (eq (pi (univ 0) (univ 0)) (app (const "twice") (const "idU")) (lam (var 0))),
   -- universe polymorphism: instances at different levels
   const "idP" [1], const "idP" [0], const "idP" [2], app (app (const "idP" [1]) (enum 2)) (tag 2 1),
   app (app (const "idP" [1]) (univ 0)) (enum 2), app (app (const "idP" [2]) (univ 0)) (enum 2),
   app (app (app (app (const "constP" [1, 2]) (enum 2)) (univ 0)) (tag 2 0)) (enum 3),
   ann (const "idP" [1]) (pi (univ 0) (pi (var 0) (var 1))),
   ann (lam (app (app (const "idP" [1]) (enum 2)) (var 0))) (pi (enum 2) (enum 2)),
   eq (pi (enum 2) (enum 2)) (app (const "idP" [1]) (enum 2)) (lam (var 0)),
   -- quantities: linear and erased binders
   ann (lam (var 0)) (piq .one (univ 0) (univ 0)),
   ann (lam (pair (var 0) (var 0))) (piq .one (univ 0) (sigma (univ 0) (univ 0))),
   ann (lam (var 0)) (piq .zero (univ 0) (univ 0)),
   ann (lam (ann star (unit 0))) (piq .zero (univ 0) (unit 0)),
   ann (lam (lam (var 0))) (piq .zero (univ 0) (pi (var 0) (var 1))),
   app (ann (lam (lam (var 0))) (piq .zero (univ 0) (pi (var 0) (var 1)))) (enum 2),
   letq .one (univ 0) (enum 2) (var 0), letq .zero (univ 0) (enum 2) (var 0),
   letq .zero (univ 0) (enum 2) (ann (lam (var 0)) (pi (var 0) (var 1))),
   fst (ann (pair (univ 0) star) (sigmaq .zero (univ 1) (unit 0))),
   snd (ann (pair (univ 0) star) (sigmaq .zero (univ 1) (unit 0))),
   ann (lam (lam (ecase (univ 0) (var 1) [var 0, var 0]))) (pi (enum 2) (piq .one (univ 0) (univ 0))),
   ann (lam (lam (ecase (univ 0) (var 1) [var 0, univ 0]))) (pi (enum 2) (piq .one (univ 0) (univ 0))),
   -- sizes and subtyping
   size, szInf, sizeLt szInf, szSuc szInf,
   ann (lam (ann (con (pair (tag 2 0) (pair star star))) (natAt (szSuc (var 0))))) (pi size (natAt (szSuc (var 0)))),
   ann (lam (lam (ann (con (pair (tag 2 1) (pair (var 0) (pair star star)))) (natAt (szSuc (var 1))))))
     (pi size (pi (natAt (var 0)) (natAt (szSuc (var 1))))),
   ann (lam (lam (var 0))) (pi size (pi (natAt (var 0)) natTy)),
   ann (lam (lam (var 0))) (pi size (pi natTy (natAt (var 0)))),
   ann (lam (lam (var 0))) (pi size (pi (sizeLt (var 0)) size)),
   ann (lam (lam (var 0))) (pi size (pi (sizeLt (var 0)) (sizeLt (szSuc (var 1))))),
   ann (lam (lam (var 0))) (pi size (pi (sizeLt (szSuc (var 0))) (sizeLt (var 1)))),
   ann (lam (ann (con (pair (tag 2 0) (pair star star))) (natAt (var 0)))) (pi size (natAt (var 0))),
   -- sized case analysis and recursion: they compute (the method / function gets ∞)
   scase 0 (unit 0) natD 1 (lams 2 (enum 2)) (lams 3 (fst (var 0))) szInf star (natSucc natZero),
   ann star (eq (enum 2) (scase 0 (unit 0) natD 1 (lams 2 (enum 2)) (lams 3 (fst (var 0))) szInf star (natSucc natZero)) (tag 2 1)),
   ann star (eq (enum 2) (scase 0 (unit 0) natD 1 (lams 2 (enum 2)) (lams 3 (fst (var 0))) szInf star (natSucc natZero)) (tag 2 0)),
   sfix 0 (unit 0) natD 1 (lams 2 (enum 2)) (lams 4 (tag 2 0)) szInf star natZero,
   ann star (eq (enum 2) (sfix 0 (unit 0) natD 1 (lams 2 (enum 2)) (lams 4 (tag 2 1)) szInf star natZero) (tag 2 1)),
   ann (lam (lam (sfix 0 (unit 0) natD 1 (lams 2 (enum 2)) (lams 4 (tag 2 0)) (var 1) star (var 0))))
     (pi size (pi (natAt (var 0)) (enum 2))),
   -- an ill-typed method (the index is erased: it can't be returned)
   scase 0 (unit 0) natD 1 (lams 2 (unit 0)) (lams 3 (var 1)) szInf star natZero,
   -- coinduction: unfoldings compute when observed
   alt, zeros,
   ann star (eq (enum 2) (shead alt) (tag 2 0)),
   ann star (eq (enum 2) (shead (stail alt)) (tag 2 1)),
   ann star (eq (enum 2) (shead (stail alt)) (tag 2 0)),
   ann star (eq (enum 2) (shead (stail (stail zeros))) (tag 2 0)),
   ann (cocon (pair (tag 2 1) (pair alt (pair star star)))) streamTy,
   ann star (eq (enum 2) (shead (ann (cocon (pair (tag 2 1) (pair alt (pair star star)))) streamTy)) (tag 2 1)),
   coit 0 (unit 0) streamD (lam (enum 2)) (lams 2 (pair (var 0) star)) star (tag 2 0),
   -- only a value of size ↑s (or ∞) can be observed; ν is contravariant in its size
   ann (lam (lam (shead (var 0)))) (pi size (pi (streamAt (var 0)) (enum 2))),
   ann (lam (lam (shead (var 0)))) (pi size (pi (streamAt (szSuc (var 0))) (enum 2))),
   ann (lam (lam (var 0))) (pi size (pi streamTy (streamAt (var 1)))),
   ann (lam (lam (var 0))) (pi size (pi (streamAt (var 0)) streamTy)),
   -- stuck observations compare by their spines
   ann (lam (lam (var 0))) (pi streamTy (pi (eq (enum 2) (shead (var 0)) (tag 2 0)) (eq (enum 2) (shead (var 1)) (tag 2 0)))),
   ann (lam (lam (var 0))) (pi streamTy (pi (eq (enum 2) (shead (var 0)) (tag 2 0)) (eq (enum 2) (shead (stail (var 1))) (tag 2 0))))]

/-- Random terms over `n` variables (a linear congruential generator), biased towards
well-typed ones: annotated λs, applications of them, universes. -/
partial def gen (seed : Nat) (depth n : Nat) : MTm × Nat :=
  let next (s : Nat) := (s * 1103515245 + 12345) % 2147483648
  let s := next seed
  let pick := s / 65536 % 24
  if depth == 0 then
    if n > 0 && pick < 5 then (var (s / 7 % n), s) else (univ (s / 7 % 2), s)
  else match pick with
    | 0 | 1 => let (a, s) := gen s (depth - 1) n; let (b, s) := gen s (depth - 1) (n + 1); (pi a b, s)
    | 2 | 3 =>
      let (a, s) := gen s (depth - 1) n
      let (b, s) := gen s (depth - 1) (n + 1)
      let (body, s) := gen s (depth - 1) (n + 1)
      let ty := match s / 29 % 4 with
        | 0 => piq .zero a b
        | 1 => piq .one a b
        | _ => pi a b
      (ann (lam body) ty, s)
    | 4 | 5 => let (f, s) := gen s (depth - 1) n; let (a, s) := gen s (depth - 1) n; (app f a, s)
    | 6 =>
      let (t, s) := gen s (depth - 1) n
      let (v, s) := gen s (depth - 1) n
      let (b, s) := gen s (depth - 1) (n + 1)
      (letE t v b, s)
    | 7 => let (t, s) := gen s (depth - 1) n; let (ty, s) := gen s (depth - 1) n; (ann t ty, s)
    | 8 => let (a, s) := gen s (depth - 1) n; let (b, s) := gen s (depth - 1) (n + 1); (sigma a b, s)
    | 9 =>
      let (ta, s) := gen s (depth - 1) n
      let (tb, s) := gen s (depth - 1) (n + 1)
      let (a, s) := gen s (depth - 1) n
      let (b, s) := gen s (depth - 1) n
      (ann (pair a b) (sigma ta tb), s)
    | 10 =>
      let (p, s) := if s / 11 % 2 == 0 then gen s (depth - 1) n else (wellTypedPair s, (s * 7 + 3) % 2147483648)
      (if s / 3 % 2 == 0 then fst p else snd p, s)
    | 11 => (wellTypedPair s, s)
    | 12 => let k := s / 5 % 2; (if s / 3 % 2 == 0 then unit k else ann star (unit k), s)
    | 13 => let k := s / 5 % 3 + 1; (tag k (s / 7 % (k + 1)), s)
    | 14 =>
      -- a case on a tag (or a variable), returning tags of another enumeration
      let k := s / 5 % 2 + 1
      let k' := s / 11 % 2 + 1
      let (sc, s) := if n > 0 && s / 13 % 3 == 0 then (var (s / 17 % n), s) else (tag k (s / 7 % k), s)
      let bs := (List.range k).map fun j => tag k' ((s / (j + 19)) % k')
      (ecase (enum k') sc bs, s)
    | 15 => let (t, s) := gen s (depth - 1) n; (exfalso (univ 0) t, s)
    | 16 =>
      -- propositions: `Prop`, `True`, `False`, `(P : Prop) → P → P`, `A → True`
      match s / 5 % 6 with
      | 0 => (prop, s)
      | 1 => (ptrue, s)
      | 2 => (pfalse, s)
      | 3 => (pi prop (pi (var 0) (var 1)), s)
      | 4 => let (a, s) := gen s (depth - 1) n; (pi a ptrue, s)
      | _ => (ann star ptrue, s)
    | 17 =>
      -- a proof term: `λP p. p : (P : Prop) → P → P`, applied or not
      let idP := ann (lam (lam (var 0))) (pi prop (pi (var 0) (var 1)))
      (if s / 5 % 2 == 0 then idP else app (app idP ptrue) (ann star ptrue), s)
    | 18 =>
      -- equalities and their proofs, often well-typed
      let k := s / 5 % 2 + 1
      let i := s / 7 % k
      let j := s / 11 % k
      let fnTy := pi (univ 0) (univ 0)
      let idU := ann (lam (var 0)) fnTy
      match s / 13 % 8 with
      | 0 => (refl (enum k) (tag k i), s)
      | 1 => (ann star (eq (enum k) (tag k i) (tag k j)), s)
      | 2 => (eq (enum k) (tag k i) (tag k j), s)
      | 3 => (cast (univ 0) (univ 0) (reflTy (univ 0)) (enum k), s)
      | 4 => (eqTy (univ 0) (univ (s / 17 % 2)), s)
      | 5 => (cast fnTy fnTy (reflTy fnTy) idU, s)
      | 6 => (eq fnTy idU idU, s)
      | _ => (refl (univ 0) (enum k), s)
    | 19 =>
      let (a, s) := gen s (depth - 1) n
      let (b, s) := gen s (depth - 1) n
      let (A, s) := gen s (depth - 1) n
      (if s / 3 % 2 == 0 then eq A a b else cast A A (reflTy A) a, s)
    | 20 =>
      -- data: the natural numbers
      match s / 5 % 7 with
      | 0 => (natTy, s)
      | 1 => (natZero, s)
      | 2 => (natSucc natZero, s)
      | 3 => (ann natD (desc 0 (unit 0)), s)
      | 4 => (eq natTy natZero (natSucc natZero), s)
      | 5 => (refl natTy (natSucc natZero), s)
      | _ =>
        -- `Desc.elim` into `Unit`: every method gives `tt`
        (delim 1 (lam (unit 0)) (lam star) (lams 4 star) (lams 4 star) (lams 5 star) (ann natD (desc 0 (unit 0))), s)
    | 22 =>
      -- a global, applied or not
      let names := ["idU", "Nat", "zero", "one", "twice", "A", "a", "idP", "constP"]
      let nm := names[s / 5 % names.length]!
      let lv := (List.range (if nm == "idP" then 1 else if nm == "constP" then 2 else 0)).map fun j => s / (j + 23) % 3
      let c := const nm lv
      let (a, s) := gen s (depth - 1) n
      (if s / 3 % 2 == 0 then c else app c a, s)
    | 21 =>
      -- ill-typed or random data
      let (x, s) := gen s (depth - 1) n
      (if s / 3 % 2 == 0 then ann (con x) natTy else ann (dret x) (desc 0 (unit 0)), s)
    | _ => if n > 0 then (var (s / 7 % n), s) else (univ (s / 7 % 3), s)

/-- Declarations `(level params, value, type)` for the declaration test: they are
checked with their parameters symbolic. -/
def declSamples : List (List String × Option MTm × MTm) :=
  let u := MLvl.param "u"
  let v := MLvl.param "v"
  [(["u"], some (lam (lam (var 0))), pi (sortParam "u") (pi (var 0) (var 1))),
   (["u"], some (lam (var 0)), pi (sortParam "u") (sortParam "u")),
   (["u"], some (lam (sortParam "u")), pi (sortParam "u") (sortLv (.succ u))),
   (["u"], some (lam (var 0)), pi (sortParam "u") (sortLv (.succ u))),
   (["u"], some (lam (pi (var 0) (var 1))), pi (sortParam "u") (sortParam "u")),
   (["u", "v"], some (pi (sortParam "u") (sortParam "v")), sortLv (.max (.succ u) (.succ v))),
   (["u", "v"], some (pi (sortParam "u") (sortParam "v")), sortLv (.succ (.max u v))),
   (["u", "v"], some (pi (sortParam "u") (sortParam "v")), sortLv (.max u v)),
   (["u", "v"], some (pi (sortParam "u") (sortParam "v")), sortLv (.imax (.succ u) v)),
   -- a type in `Sort (imax u v)`: `Prop` when `v` is
   (["u", "v"], some (lam (lam (pi (var 1) (var 1)))), pi (sortParam "u") (pi (sortParam "v") (sortLv (.imax u v)))),
   (["u", "v"], some (lam (lam (pi (var 1) (var 1)))), pi (sortParam "u") (pi (sortParam "v") (sortLv (.max u v)))),
   (["u"], some (pi (sortParam "u") prop), sortLv (.succ u)),
   (["u"], none, pi (sortParam "u") (var 0)),
   -- polymorphic globals at symbolic levels
   (["u"], some (app (const "idP" [0]) (univ 0)), pi (univ 0) (univ 0)),
   -- equality needs a level that is never zero
   (["u"], some (lam (lam (eq (var 1) (var 0) (var 0)))), pi (sortLv (.succ u)) (pi (var 0) prop)),
   (["u"], some (lam (lam (eq (var 1) (var 0) (var 0)))), pi (sortParam "u") (pi (var 0) prop))]

/-- Random level puzzles: `Sort a : Sort b`, about half of them with `b` a rewriting of
`a + 1` (so they hold), and `Π`s of sorts. -/
def levelPuzzles (n : Nat) : List (List String × Option MTm × MTm) := Id.run do
  let mut out := []
  let mut s := 7
  for i in [0:n] do
    let (a, s1) := MLvl.gen s 2
    let (b, s2) := MLvl.gen s1 2
    if i % 2 == 0 then
      let (a', s3) := MLvl.rewrite s2 (.succ a)
      out := out ++ [(["u", "v"], some (sortLv a), sortLv a')]
      s := s3
    else if i % 4 == 1 then
      out := out ++ [(["u", "v"], some (sortLv a), sortLv (.succ b))]
      s := s2
    else
      let (c, s3) := MLvl.rewrite s2 (.imax (.succ a) (.succ b))
      let c := if i % 8 == 3 then c else (MLvl.gen s3 2).1
      out := out ++ [(["u", "v"], some (pi (sortLv a) (sortLv b)), sortLv c)]
      s := s3
  return out

/-- (D1) `abelCoquand` as one core term (lets instead of definitions), for the self-hosted
kernel. `selfApp`: `Omega := delta omega` (no normal form); otherwise `Omega := omega`, the
control. -/
def abelCoquand (selfApp : Bool) : MTm :=
  let top := sorted 1 0 (pi prop (sorted 0 0 (pi (var 0) (var 1))))
  -- Box P := μ (Desc.arg ((_ : Enum [u]) × P) (fun _ => Desc.ret ())) (); `boxD n` with P at index n
  let boxD (n : Nat) := darg (sorted 1 0 (sigma (enum 1) (var (n + 1)))) (lam (dret star))
  let p2 := sorted 1 1 (sigma (enum 2) (enum 2))
  letE prop top <|                                                 -- Top
  letE prop (sorted 0 0 (pi (var 0) (var 1))) <|                   -- T2 := Top → Top
  letE (var 0) (lam (var 0)) <|                                    -- id2 : T2
  letE (var 1) (lam (app (app (app (var 0) (var 2)) (var 1)) (var 0))) <|  -- delta z := z T2 id2 z
  letE (pi prop (univ 0)) (lam (mu 0 (unit 0) (boxD 0) star)) <|  -- Box
  letE (pi prop (pi (var 0) (app (var 2) (var 1))))                -- mk (P : Prop) (p : P) : Box P
    (lam (lam (con (pair (pair (tag 1 0) (var 0)) (pair star star))))) <|
  letE (pi prop (pi (app (var 2) (var 0)) (var 1)))                -- unbox (P : Prop) (b : Box P) : P
    (lam (lam (ind 0 (unit 0) (boxD 1) 0 (lams 2 (var 3)) (lams 3 (snd (fst (var 1)))) star (var 0)))) <|
  letE (pi prop (pi prop (pi (var 1) (pi (var 1) (eq prop (var 3) (var 2))))))  -- tautext
    (lams 4 (pair (lam (var 1)) (lam (var 2)))) <|
  -- omega A a := unbox A (cast (Box T2) (Box A) (transp … (reflTy (Box T2)) (tautext T2 A id2 a)) (mk T2 delta))
  letE (var 7) (lam (lam (app (app (var 3) (var 1))
    (cast (app (var 5) (var 8)) (app (var 5) (var 1))
      (transp prop (var 8) (lam (lam (eqTy (app (var 7) (var 10)) (app (var 7) (var 1)))))
        (reflTy (app (var 5) (var 8))) (var 1) (app (app (app (app (var 2) (var 8)) (var 1)) (var 7)) (var 0)))
      (app (app (var 4) (var 8)) (var 6)))))) <|
  letE (var 8) (if selfApp then app (var 5) (var 0) else var 0) <|  -- Omega
  ann (refl (enum 2) (tag 2 0))
    (eq (enum 2) (fst (cast p2 p2 (app (app (var 0) (eqTy p2 p2)) (reflTy p2)) (pair (tag 2 0) (tag 2 1)))) (tag 2 0))

/-- (I-1, audit-2's probe) A proof that takes a tower of exponentials of β-steps to
normalise, inside a marked proof: `let two : (A : Prop) → (A → A) → A → A := fun A f x =>
f (f x); let h : True := two A_k (two A_{k-1}) … (two True) (fun x => x) (); ()`, all in
`Prop`. The checker must not run it: inside a proof it binds a proof suspended. -/
def proofTower (k : Nat) : MTm :=
  let A : Nat → MTm := fun n => (List.range n).foldl (fun a _ => sorted 0 0 (pi a a)) ptrue
  let twoTy := sorted 1 0 (pi prop (sorted 0 0 (pi (sorted 0 0 (pi (var 0) (var 1))) (sorted 0 0 (pi (var 1) (var 2))))))
  let twoVal := lams 3 (app (var 1) (app (var 1) (var 0)))
  let head := (List.range k).foldl (fun acc i => app acc (app (var 0) (A (k - 1 - i)))) (app (var 0) (A k))
  ann (prf (.num 0) (letE twoTy twoVal (letE ptrue (app (app head (lam (var 0))) star) star))) ptrue

/-- (review F7, Q2.9 of `wiz-notes/prf-review.md`) The same tower, unmarked, as a proof of
`False` under a hypothesis `h : False`: `fun h => refl (absurd h) : (h : False) → absurd h
= absurd (prf (let two := …; let _ : True := tower; h))` at `Enum 2`. The kernel never runs
the proof; reading the type back does (it is evaluated, to be a normal form), and must stop
at the step budget. -/
def proofTowerAbsurd (k : Nat) : MTm :=
  let A : Nat → MTm := fun n => (List.range n).foldl (fun a _ => sorted 0 0 (pi a a)) ptrue
  let twoTy := sorted 1 0 (pi prop (sorted 0 0 (pi (sorted 0 0 (pi (var 0) (var 1))) (sorted 0 0 (pi (var 1) (var 2))))))
  let twoVal := lams 3 (app (var 1) (app (var 1) (var 0)))
  let head := (List.range k).foldl (fun acc i => app acc (app (var 0) (A (k - 1 - i)))) (app (var 0) (A k))
  let tower := letE twoTy twoVal (letE ptrue (app (app head (lam (var 0))) star) (var 2))
  ann (prf (.num 0) (lam (refl (enum 2) (exfalso (enum 2) (var 0)))))
    (sorted 0 0 (pi pfalse (eq (enum 2) (exfalso (enum 2) (var 0)) (exfalso (enum 2) (prf (.num 0) tower)))))

/-- (P2) The proof marker, on terms that are *not* run through the marking pass: is the
term accepted? `T2` is `True → True`, a proposition. -/
def markerSamples : List (MTm × Bool) :=
  let T2 := pi ptrue ptrue
  let z : MLvl := .num 0
  -- `refl #0 : #0 = #0` at `Enum 2`, its type, a `transp` proving `True`, and a Σ with a proof field
  let rE := refl (enum 2) (tag 2 0)
  let TE := eq (enum 2) (tag 2 0) (tag 2 0)
  let tr (p e : MTm) := transp (enum 2) (tag 2 0) (lam (lam ptrue)) p (tag 2 0) e
  let SP := sorted 1 0 (sigma (enum 2) ptrue)
  [ -- a λ at a proposition must be marked
    (ann (lam (var 0)) T2, false),
    (ann (prf z (lam (var 0))) T2, true),
    -- a `let`-bound proof, and a proof in a pair
    (letE T2 (lam (var 0)) (univ 0), false),
    (letE T2 (prf z (lam (var 0))) (univ 0), true),
    (ann (pair (tag 2 0) (lam (var 0))) (sigma (enum 2) T2), false),
    (ann (pair (tag 2 0) (prf z (lam (var 0)))) (sigma (enum 2) T2), true),
    -- the kernel verifies the marker: not at a data type, and at the right level
    (ann (prf z (tag 2 0)) (enum 2), false),
    (ann (prf (.num 1) (tag 2 0)) (enum 2), true),
    (ann (prf (.num 1) (lam (var 0))) T2, false),
    -- a neutral-shaped proof (a variable, here applied) needs no marker; `tt` neither
    (ann (lam (pair (tag 2 0) (var 0))) (pi ptrue (sigma (enum 2) ptrue)), true),
    (ann (lam (lam (pair (tag 2 0) (app (var 1) (var 0))))) (pi T2 (pi ptrue (sigma (enum 2) ptrue))), true),
    (ann (pair (tag 2 0) star) (sigma (enum 2) ptrue), true),
    -- a marker inside a marked proof is allowed
    (ann (prf z (lam (prf z (var 0)))) T2, true),
    -- The stuck proof formers need no marker, in any position: evaluating one evaluates
    -- its relevant parts and gives a neutral. `refl`:
    (ann rE TE, true),
    (letE TE rE (univ 0), true),
    (ann (pair (tag 2 0) rE) (sigma (enum 2) TE), true),
    (app (ann (lam (tag 2 0)) (pi TE (enum 2))) rE, true),
    (ann (lam (exfalso (enum 2) (var 0))) (pi pfalse (enum 2)), true),
    -- `reflTy`:
    (ann (reflTy (enum 2)) (eqTy (enum 2) (enum 2)), true),
    (letE (eqTy (enum 2) (enum 2)) (reflTy (enum 2)) (univ 0), true),
    (ann (pair (tag 2 0) (reflTy (enum 2))) (sigma (enum 2) (eqTy (enum 2) (enum 2))), true),
    -- `transp` (its motive is a family of propositions, a relevant term; its base and its
    -- equation are never evaluated, so they may be any proof, unmarked):
    (ann (tr star rE) ptrue, true),
    (letE ptrue (tr star rE) (univ 0), true),
    (ann (pair (tag 2 0) (tr star rE)) (sigma (enum 2) ptrue), true),
    (app (ann (lam (tag 2 0)) (pi ptrue (enum 2))) (tr star rE), true),
    (letE ptrue (tr (letE ptrue star (var 0)) (letE TE rE (var 0))) (univ 0), true),
    -- under `absurd`: a `transp` that proves `False` from a hypothesis
    (ann (lam (exfalso (enum 2) (transp (enum 2) (tag 2 0) (lam (lam pfalse)) (var 0) (tag 2 0) rE))) (pi pfalse (enum 2)), true),
    -- but the relevant parts of a `refl` are checked like any term: a proof in them that is
    -- not neutral-shaped needs its marker
    (ann (refl SP (pair (tag 2 0) (letE ptrue star (var 0)))) (eq SP (pair (tag 2 0) star) (pair (tag 2 0) star)), false),
    (ann (refl SP (pair (tag 2 0) (prf z (letE ptrue star (var 0))))) (eq SP (pair (tag 2 0) star) (pair (tag 2 0) star)), true),
    -- (I-1) inside a proof, a subterm that is not a proof is a relevant term again (it can be
    -- evaluated, as the argument of a type), so a proof in it needs its marker
    (ann (prf z (app (ann (lam star) (pi (enum 2) ptrue)) (app (ann (lam (tag 2 0)) (pi T2 (enum 2))) (lam (var 0))))) ptrue, false),
    (ann (prf z (app (ann (lam star) (pi (enum 2) ptrue)) (app (ann (lam (tag 2 0)) (pi T2 (enum 2))) (prf z (lam (var 0)))))) ptrue, true),
    -- while a proof directly inside a proof needs none
    (ann (prf z (app (ann (lam star) (pi T2 ptrue)) (lam (var 0)))) ptrue, true),
    -- a `refl` whose term holds a proof variable, which a marked proof is then substituted for
    (app (ann (lam (pair (tag 2 0) (refl SP (pair (tag 2 0) (var 0)))))
        (pi ptrue (sigma (enum 2) (eq SP (pair (tag 2 0) (var 1)) (pair (tag 2 0) (var 1))))))
      (prf z (letE ptrue star (var 0))), true),
    -- `absurd` on a proof that is not neutral-shaped: marked
    (ann (lam (exfalso (enum 2) (letE pfalse (var 0) (var 0)))) (pi pfalse (enum 2)), false),
    (ann (lam (exfalso (enum 2) (prf z (letE pfalse (var 0) (var 0))))) (pi pfalse (enum 2)), true),
    -- conversion: a marked proof against a hypothesis, under `absurd` (a proof is not compared)
    (ann (prf z (lam (refl (enum 2) (exfalso (enum 2) (var 0)))))
      (pi pfalse (eq (enum 2) (exfalso (enum 2) (var 0)) (exfalso (enum 2) (prf z (letE pfalse (var 0) (var 0)))))), true),
    -- but the motives are
    (ann (prf z (lam (refl (univ 0) (exfalso (univ 0) (var 0)))))
      (pi pfalse (eq (univ 0) (exfalso (univ 0) (var 0)) (app (exfalso (pi (enum 2) (univ 0)) (var 0)) (tag 2 0)))), false),
    -- and so is what follows the `absurd`
    (ann (prf z (lam (refl (univ 0) (app (exfalso (pi (enum 2) (univ 0)) (var 0)) (tag 2 0)))))
      (pi pfalse (eq (univ 0) (app (exfalso (pi (enum 2) (univ 0)) (var 0)) (tag 2 0))
        (app (exfalso (pi (enum 2) (univ 0)) (prf z (letE pfalse (var 0) (var 0)))) (tag 2 1)))), false),
    (ann (prf z (lam (refl (univ 0) (app (exfalso (pi (enum 2) (univ 0)) (var 0)) (tag 2 0)))))
      (pi pfalse (eq (univ 0) (app (exfalso (pi (enum 2) (univ 0)) (var 0)) (tag 2 0))
        (app (exfalso (pi (enum 2) (univ 0)) (prf z (letE pfalse (var 0) (var 0)))) (tag 2 0)))), true) ]

/-- (P1) Regularity at inert types, decided by conversion (InReg_conv): the probes of
`wiz-notes/p1-stable.md` as core terms, for both kernels. `F i` is an inert family over
`Enum 2` (one constructor, at index `#0`), so `F i` for a variable `i` has an open index.
Each term is `fun … => refl k` at a type that states an equation; `true`: accepted. -/
def convSamples : List (String × MTm × Bool) :=
  let F (i : MTm) : MTm := mu 0 (enum 2) (dret (tag 2 0)) i
  -- a type computed by induction: `T i x : U0`, stuck on `x`
  let T (i x : MTm) : MTm := ind 0 (enum 2) (dret (tag 2 0)) 2 (lams 2 (univ 0)) (lams 3 (enum 2)) i x
  [ -- t1: a stuck cast between the same types at an open index is its argument
    ("t1", ann (lams 3 (refl (F (var 2)) (var 1)))
      (pi (enum 2) (pi (F (var 0)) (pi (eqTy (F (var 1)) (F (var 1)))
        (eq (F (var 2)) (cast (F (var 2)) (F (var 2)) (var 0) (var 1)) (var 1))))), true),
    -- t2: the two types convertible, not syntactically equal (`F (f p)`, `F (f q)`, two proofs)
    ("t2", ann (lams 6 (refl (F (app (var 4) (var 2))) (var 1)))
      (pi prop (pi (pi (var 0) (enum 2)) (pi (var 1) (pi (var 2) (pi (F (app (var 2) (var 1)))
        (pi (eqTy (F (app (var 3) (var 2))) (F (app (var 3) (var 1))))
          (eq (F (app (var 4) (var 2))) (cast (F (app (var 4) (var 3))) (F (app (var 4) (var 2))) (var 0) (var 1)) (var 1)))))))), true),
    -- h2: two casts of one value, at `F (f p) ≡ F (f p)` and at `F (f p) ≡ F (f q)`
    ("h2", ann (lams 7 (refl (F (app (var 5) (var 3))) (var 2)))
      (pi prop (pi (pi (var 0) (enum 2)) (pi (var 1) (pi (var 2) (pi (F (app (var 2) (var 1)))
        (pi (eqTy (F (app (var 3) (var 2))) (F (app (var 3) (var 2))))
          (pi (eqTy (F (app (var 4) (var 3))) (F (app (var 4) (var 2))))
            (eq (F (app (var 5) (var 3)))
              (cast (F (app (var 5) (var 4))) (F (app (var 5) (var 4))) (var 1) (var 2))
              (cast (F (app (var 5) (var 4))) (F (app (var 5) (var 3))) (var 0) (var 2)))))))))), true),
    -- a *type* stuck on such a cast (`convTy`): `x : T i (cast e k)` is a `T i k`
    ("ty", ann (lams 4 (var 0))
      (pi (enum 2) (pi (F (var 0)) (pi (eqTy (F (var 1)) (F (var 1)))
        (pi (T (var 2) (cast (F (var 2)) (F (var 2)) (var 0) (var 1))) (T (var 3) (var 2)))))), true),
    -- a cast between types that are not convertible stays: `F #0`, `F #1`
    ("ne", ann (lams 2 (refl (F (tag 2 1)) (cast (F (tag 2 0)) (F (tag 2 1)) (var 0) (var 1))))
      (pi (F (tag 2 0)) (pi (eqTy (F (tag 2 0)) (F (tag 2 1)))
        (eq (F (tag 2 1)) (cast (F (tag 2 0)) (F (tag 2 1)) (var 0) (var 1)) (cast (F (tag 2 0)) (F (tag 2 1)) (var 0) (var 1))))), true),
    -- t5, the control: no regularity at a type variable
    ("t5", ann (lams 3 (refl (var 2) (var 1)))
      (pi (univ 0) (pi (var 0) (pi (eqTy (var 1) (var 1)) (eq (var 2) (cast (var 2) (var 2) (var 0) (var 1)) (var 1))))), false) ]

end MTm

/-- The globals of the differential test, in the Lean kernel. (A function, so that it
is computed in the test, not when the module starts.) -/
def leanGlobals (_ : Unit := ()) : Globals ZeroOneMany :=
  MTm.globalDefs.foldl (fun g (n, ps, v, ty) => match addDecl g (Decl.withMarks g { name := n, levelParams := ps, type := ty.toTerm, value := v.map MTm.toTerm }) with
    | .ok g' => g'
    | .error _ => g) {}

/-- What the Lean kernel says about a closed term: its type (printed like the Wiz
kernel prints) or `error`. -/
def leanVerdict (t : MTm) (mark : Bool := true) : String :=
  let g := leanGlobals ()
  -- The proof markers the kernel requires come from the marking pass (`mark := false`: the
  -- term as it is). The pass evaluates the term as it goes and checks nothing, like the
  -- elaborator whose output it is made for; a random term can be ill-typed, so it is
  -- marked only if it is well typed (checked first without the marker's requirement).
  -- (the pre-check requires no markers at all, also inside proofs, so that a term whose
  -- proofs hold relevant subterms reaches the pass: review F2)
  -- (mandatory sorts: the holes `MTm` writes for the `Π`/`Σ` sorts are filled first, by the
  -- sorts pass, in every case)
  -- (the pre-check, holes allowed, comes first: the sorts pass evaluates the term)
  -- (`mark := false`: hand-written terms, given to the pass as they are)
  if mark && !(infer (R := ZeroOneMany) { globals := { g with lazyProofs := false, sortHolesOk := true } } t.toTerm).toBool then "error" else
  let t0 := (Mark.infer (R := ZeroOneMany) { globals := g, sortsOnly := true } t.toTerm).1
  let tm := if mark then (Mark.infer (R := ZeroOneMany) { globals := g } t0).1 else t0
  match infer (R := ZeroOneMany) { globals := g } tm with
  | .ok (ty, _) => match MTm.ofTerm (quote g 0 ty) with
    | some m => m.pretty 0
    | none => "?"
  | .error _ => "error"

/-- The Wiz kernel's verdict on a closed term, as a Wiz definition: the term gets its proof
markers from the Wiz marking pass first (`rawVerdict`: the term as it is). -/
def wizVerdict : String :=
  -- (mandatory sorts: the holes `MTm` writes are filled by the sorts pass first, always)
  "def rawVerdict (t0 : Tm) : String := match infer empty (sortsInfer t0) with\n  | .ok ty _ => show .nil 0 (quote 0 ty)\n  | .err _ => \"error\"\n" ++
  "def markedVerdict (t : Tm) : String := rawVerdict (MR.tm (markInfer empty (sortsInfer t)))\n" ++
  -- (a random term is marked only if it is well typed: the pass checks nothing)
  "def verdict (t : Tm) : String := match infer (TCtx.noMarkers empty) (sortsInfer t) with\n  | .err _ => \"error\"\n  | .ok _ _ => markedVerdict t\n"

/-- What the Lean kernel says about a declaration: `ok` or `error`. -/
def leanDeclVerdict (d : List String × Option MTm × MTm) : String :=
  let (ps, v, ty) := d
  let g := leanGlobals ()
  -- (marked only if well typed, as in `leanVerdict`; holes allowed in the pre-check, the
  -- sorts pass after it)
  let pre : TCM Unit := do
    let ctx : Ctx ZeroOneMany := { globals := { g with lazyProofs := false, sortHolesOk := true } }
    let _ ← Wiz.checkType ctx ty.toTerm
    if let some v := v then
      let _ ← Wiz.check ctx v.toTerm (ctx.eval ty.toTerm)
  if !pre.toBool then "error" else
  let d0 := Decl.withSorts g { name := "test", levelParams := ps, type := ty.toTerm, value := v.map MTm.toTerm }
  match addDecl (R := ZeroOneMany) g (Decl.withMarks g d0) with
  | .ok _ => "ok"
  | .error _ => "error"

/-- The whole self-hosted pipeline as a compiled program that checks the file `input.wiz`
in its working directory. It is built once and kept (under `/tmp`, keyed by its source
and this test binary), since every test that uses it would otherwise compile it again. -/
def selfhostChecker : IO (Except String System.FilePath) := do
  let src ← Selfhost.checkerFiles.mapM (fun (f : String) => IO.FS.readFile f)
  let prog := Selfhost.checkerSource src
  let stamp := toString (← (← IO.appPath).metadata).modified.sec
  let dir : System.FilePath := s!"/tmp/wiz-selfhost-{hash (prog ++ stamp)}"
  let exe := dir / "checker"
  note "uses checker"
  if ← exe.pathExists then return .ok exe
  let start ← IO.monoMsNow
  IO.FS.createDirAll dir
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let ioLib ← IO.FS.readFile "lib/IO.wiz"
  let stdLib ← IO.FS.readFile "lib/Std.wiz"
  let loader : Name → Option String := fun m =>
    if m == "Prelude" then some prelude else if m == "IO" then some ioLib else if m == "Std" then some stdLib else none
  let s := runFrontend (R := ZeroOneMany) prog { loader, trustedModule := Tests.libModule }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render prog
  unless errs.isEmpty do return .error s!"unexpected errors:\n{"\n".intercalate errs.toList}"
  match Build.irProgram s "main" with
  | .error e => return .error e
  | .ok (decls, _) =>
    -- built under another name and renamed: tests may run at the same time
    let tmp := dir / s!"checker-{← IO.monoNanosNow}"
    match ← Build.compileC (← toolchain) (C.program decls true (Build.extraC s)) tmp with
    | .error e => return .error e
    | .ok () =>
      IO.FS.rename tmp exe
      note s!"built checker {showMs ((← IO.monoMsNow) - start)}"
      return .ok exe

/-- The self-hosted compiler (stage 21): the frontend and `Backend.wiz`, printing the C
program for `input.wiz` (the frontend's own output as comments). -/
def selfhostCompiler : IO (Except String System.FilePath) := do
  let src ← Selfhost.compilerFiles.mapM (fun (f : String) => IO.FS.readFile f)
  let prog := Selfhost.compilerSource src
  let stamp := toString (← (← IO.appPath).metadata).modified.sec
  let dir : System.FilePath := s!"/tmp/wiz-selfhost-{hash (prog ++ stamp)}"
  let exe := dir / "compiler"
  note "uses compiler"
  if ← exe.pathExists then return .ok exe
  let start ← IO.monoMsNow
  IO.FS.createDirAll dir
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let ioLib ← IO.FS.readFile "lib/IO.wiz"
  let stdLib ← IO.FS.readFile "lib/Std.wiz"
  -- (the driver ends with `Process.exit` on a frontend error)
  let sysLib ← IO.FS.readFile "lib/Sys.wiz"
  let loader : Name → Option String := fun m =>
    if m == "Prelude" then some prelude else if m == "IO" then some ioLib else if m == "Std" then some stdLib
    else if m == "Sys" then some sysLib else none
  let s := runFrontend (R := ZeroOneMany) prog { loader, trustedModule := Tests.libModule }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render prog
  unless errs.isEmpty do return .error s!"unexpected errors:\n{"\n".intercalate errs.toList}"
  match Build.irProgram s "main" with
  | .error e => return .error e
  | .ok (decls, _) =>
    let tmp := dir / s!"compiler-{← IO.monoNanosNow}"
    match ← Build.compileC (← toolchain) (C.program decls true (Build.extraC s)) tmp with
    | .error e => return .error e
    | .ok () =>
      IO.FS.rename tmp exe
      note s!"built compiler {showMs ((← IO.monoMsNow) - start)}"
      return .ok exe

/-- Check a file of commands with the whole self-hosted pipeline (compiled), and compare
its output. -/
def selfhostCheckFile (file expected : String) : IO Unit := do
  match ← selfhostChecker with
  | .error e =>
    if (e.splitOn "gmp.h").length > 1 then skip "no toolchain" else throw (IO.userError e)
  | .ok exe =>
    let dir ← IO.FS.createTempDir
    IO.FS.writeFile (dir / "input.wiz") file
    let out ← IO.Process.output { cmd := "timeout", args := #["120", exe.toString], cwd := dir }
    unless out.exitCode == 0 do throw (IO.userError s!"the checker failed ({out.exitCode}): {out.stderr}")
    checkEq expected out.stdout

-- the self-hosted checker's output for a file
def selfhostOutput (file : String) : IO (Option String) := do
  match ← selfhostChecker with
  | .error e =>
    if (e.splitOn "gmp.h").length > 1 then
      skip "no toolchain"
      pure none
    else throw (IO.userError e)
  | .ok exe =>
    let dir ← IO.FS.createTempDir
    IO.FS.writeFile (dir / "input.wiz") file
    let out ← IO.Process.output { cmd := "timeout", args := #["900", exe.toString], cwd := dir }
    unless out.exitCode == 0 do throw (IO.userError s!"the checker failed ({out.exitCode}): {out.stderr}")
    pure (some out.stdout)

/-- (A14) The self-hosted checker's output for a set of module files: `input.wiz` is the
root module, the others are modules (written beside it, subdirectories included). `args`
go to the checker (`-I DIR`, `--key`). -/
def selfhostModuleOutput (files : List (String × String)) (args : Array String := #[]) :
    IO (Option String) := do
  match ← selfhostChecker with
  | .error e =>
    if (e.splitOn "gmp.h").length > 1 then
      skip "no toolchain"
      pure none
    else throw (IO.userError e)
  | .ok exe =>
    let dir ← IO.FS.createTempDir
    for (name, text) in files do
      if let some parent := (dir / name).parent then IO.FS.createDirAll parent
      IO.FS.writeFile (dir / name) text
    let out ← IO.Process.output { cmd := "timeout", args := #["120", exe.toString] ++ args, cwd := dir }
    unless out.exitCode == 0 do throw (IO.userError s!"the checker failed ({out.exitCode}): {out.stderr}")
    pure (some out.stdout)

/-- (A14) Check a set of module files with the self-hosted checker and compare its output. -/
def selfhostCheckModules (files : List (String × String)) (expected : String)
    (args : Array String := #[]) : IO Unit := do
  let some out ← selfhostModuleOutput files args | return
  checkEq expected out

/-- (D1) The compiled program `main` of `src` doesn't finish within `secs` seconds
(memory capped: a loop in the kernel allocates). -/
def ioDiverges (src : String) (secs : Nat := 5) : IO Unit := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let ioLib ← IO.FS.readFile "lib/IO.wiz"
  let loader : Name → Option String := fun m =>
    if m == "Prelude" then some prelude else if m == "IO" then some ioLib else none
  let s := runFrontend (R := ZeroOneMany) src { loader, trustedModule := Tests.libModule }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  match Build.irProgram s "main" with
  | .error e => throw (IO.userError e)
  | .ok (decls, _) =>
    let dir ← IO.FS.createTempDir
    let exe := dir / "wiz_main"
    match ← Build.compileC (← toolchain) (C.program decls true (Build.extraC s)) exe with
    | .error e =>
      if (e.splitOn "gmp.h").length > 1 then skip "no toolchain" else throw (IO.userError e)
    | .ok () =>
      let out ← IO.Process.output { cmd := "sh", args := #["-c",
        s!"ulimit -v 8000000; exec timeout {secs} \"$0\"", exe.toString] }
      unless out.exitCode == 124 do
        throw (IO.userError s!"expected a timeout, got exit code {out.exitCode}: {(out.stdout ++ out.stderr).take 1500}")

/-- (22k) A sealed type, a look-alike, and another sealed type of the same shape. -/
def sealHeader : String :=
  "sealed inductive W (w : Nat) where\n  | mk (toNat : Nat)\ninductive L (w : Nat) where\n  | mk (toNat : Nat)\n" ++
  "sealed inductive V (w : Nat) where\n  | mk (toNat : Nat)\n"

/-- Every `lib/*.wiz` and `lib/D/*.wiz` (as `D.X`), by module name. -/
def libLoader : IO (Name → Option String) := do
  let mut m : List (Name × String) := []
  for e in ← System.FilePath.readDir "lib" do
    if e.path.extension == some "wiz" then
      m := (e.path.fileStem.getD "", ← IO.FS.readFile e.path) :: m
    else if ← e.path.isDir then
      for f in ← System.FilePath.readDir e.path do
        if f.path.extension == some "wiz" then
          m := (e.fileName ++ "." ++ f.path.fileStem.getD "", ← IO.FS.readFile f.path) :: m
  pure fun n => m.lookup n

/-- No errors, and these messages, with every library importable. -/
def okLibs (input : String) (infos : List String := []) : IO Unit := do
  let s := runFrontend (R := ZeroOneMany) input { trustedModule := Tests.libModule, loader := ← libLoader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render input
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  checkEq (repr infos).pretty (repr (s.messages.toList.map (·.text))).pretty

/-- Exactly one error, mentioning `fragment`, with every library importable. -/
def failsLibs (input : String) (fragment : String) : IO Unit := do
  let s := runFrontend (R := ZeroOneMany) input { trustedModule := Tests.libModule, loader := ← libLoader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render input
  unless errs.size == 1 do throw (IO.userError s!"expected one error, got {errs.size}: {errs}")
  unless (errs[0]!.splitOn fragment).length > 1 do
    throw (IO.userError s!"error does not mention '{fragment}':\n{errs[0]!}")

/-- Build `main` with the C backend (or LLVM), with every library importable. -/
def cRunLibs (src : String) (expected : String) (llvm : Bool := false) : IO Unit := do
  let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := ← libLoader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  let dir ← IO.FS.createTempDir
  match ← Build.runGlobal (← toolchain) s "main" dir llvm (timeout := some 120) with
  | .ok v => checkEq expected v
  | .error e =>
    if ["gmp.h", "llc:", "No such file"].any fun m => (e.splitOn m).length > 1 then skip "no toolchain"
    else throw (IO.userError e)

/-- Build and run `main` with the whole library (`IO` …), through C or LLVM. -/
def cRunIO (src : String) (expected : String) (llvm : Bool := false) : IO Unit := do
  let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := ← libLoader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  let dir ← IO.FS.createTempDir
  match ← Build.runGlobal (← toolchain) s "main" dir llvm with
  | .ok v => checkEq expected v
  | .error e =>
    let missing := ["gmp.h", "llc:", "No such file"].any fun m => (e.splitOn m).length > 1
    if missing then skip "no toolchain" else throw (IO.userError e)

/-- Reads of a wide structure's fields through shared projection prefixes (15j), where
reference counting could go wrong: the root consumed (`keepW`) before the last read
through a prefix (`early`), the root's cell reused by an update while fields read through
the prefix are still to be used (`upd`), reads before and after a join point (`joinW`),
and fields of codata between observations, which overwrite lazy cells (`obs`). -/
def projShareSrc : String := "import Prelude\n" ++
  "structure W where\n" ++
  "  a : Nat\n" ++
  "  b : Nat\n" ++
  "  c : Nat\n" ++
  "  d : Nat\n" ++
  "  e : Nat\n" ++
  "  f : Nat\n" ++
  "def mkW (n : Nat) : W := W.mk n (n + 1) (n + 2) (n + 3) (n + 4) (n + 5)\n" ++
  "def sumW (w : W) : Nat := w.a + w.b + w.c + w.d + w.e + w.f\n" ++
  "def keepW (w : W) : List W := .cons w .nil\n" ++
  "def lenL {A : Type} : List A → Nat\n" ++
  "  | .nil => 0\n" ++
  "  | .cons _ r => lenL r + 1\n" ++
  "-- the root's last direct use (consumed) before the shared prefix's last use\n" ++
  "def early (w : W) : Nat := w.b + lenL (keepW w) + w.e + w.f\n" ++
  "-- an in-place update of the root's cell while a field read through the prefix is live\n" ++
  "def upd (w : W) : W × Nat := ({ w with c := w.d + w.e }, w.f)\n" ++
  "-- branches, then a join point after them\n" ++
  "def joinW (w : W) (k : Nat) : Nat := (match k with\n" ++
  "  | .zero => w.d\n" ++
  "  | .succ _ => w.e) + w.f + w.c\n" ++
  "coinductive Str where\n" ++
  "  hd : W\n" ++
  "  tl : Str\n" ++
  "def from (n : Nat) : Str\n" ++
  "  | .hd => mkW n\n" ++
  "  | .tl => from (n + 10)\n" ++
  "-- observing a lazy cell (lazySet) between reads of its fields\n" ++
  "def obs (s : Str) : Nat := s.hd.e + s.tl.hd.f + s.hd.f + s.tl.tl.hd.b\n" ++
  "def main : List Nat := .cons (sumW (mkW 1)) (.cons (early (mkW 2)) (.cons (sumW (upd (mkW 3)).1) (.cons (upd (mkW 3)).2\n" ++
  "  (.cons (joinW (mkW 4) 0) (.cons (joinW (mkW 4) 5) (.cons (obs (from 0)) .nil))))))\n" ++
  ""

def projShareExpected : String := ".cons 21 (.cons 17 (.cons 41 (.cons 8 (.cons 22 (.cons 23 (.cons 45 .nil))))))"

/-- Programs for the native backends (C, or LLVM). -/
def nativeCases (llvm : Bool) : List Case :=
[
    { name := "closed definitions (CAFs, 15i): computed once, on first use (a diverging one never), no leaks", run := fun _ =>
        cRun (llvm := llvm) cafSrc cafExpected },
    { name := "a closed IO action is a description: cached, run at each use (15i)", run := fun _ =>
        cRunIO (llvm := llvm) cafIOSrc "hello\nhello\nhello\nhello\n" },
    { name := "memoised codata: no leaks, also when dropped part-way", run := fun _ =>
        cRun (llvm := llvm) memoStreamSrc "14946" },
    { name := "numbers, with GMP for big ones", run := fun _ =>
        cRun (llvm := llvm) "import Prelude\ndef fact : Nat → Nat\n  | .zero => 1\n  | .succ n => (.succ n) * fact n\ndef main : Nat := fact 25"
          "15511210043330985984000000" },
    { name := "strings", run := fun _ =>
        cRun (llvm := llvm) "import Prelude\ndef main : String := String.append \"hello, \" \"world\"" "\"hello, world\"" },
    { name := "closures", run := fun _ =>
        cRun (llvm := llvm) "import Prelude\ndef adder (n : Nat) : Nat → Nat := fun x => x + n\ndef twice (f : Nat → Nat) (x : Nat) : Nat := f (f x)\ndef main : Nat := twice (adder 10) 1" "21" },
    { name := "codata", run := fun _ =>
        cRun (llvm := llvm) (streamPrelude ++ "def main : Nat := (nats .zero).tail.tail.head") ".succ (.succ .zero)" },
    { name := "codata by copatterns: register (cocon) and mealy (coit)", run := fun _ =>
        cRun (llvm := llvm) ("import Prelude\ncoinductive Stream (A : Type) where\n  head : A\n  tail : Stream A\n" ++
          "def nats (n : Nat) : Stream Nat\n  | .head => n\n  | .tail => nats (n + 1)\n" ++
          "def register {A : Type} (init : A) (s : Stream A) : Stream A\n  | .head => init\n  | .tail => s\n" ++
          "def mealy {S I O : Type} (f : S → I → S × O) (st : S) (i : Stream I) : Stream O\n" ++
          "  | .head => (f st i.head).2\n  | .tail => mealy f (f st i.head).1 i.tail\n" ++
          "def take {A : Type} : Nat → Stream A → List A\n  | .zero, _ => .nil\n  | .succ n, s => .cons s.head (take n s.tail)\n" ++
          "def main : List Nat := take 6 (register 100 (mealy (fun acc x => (acc + x, acc + x)) 0 (Stream.mk 1 (nats 1))))")
          ".cons 100 (.cons 1 (.cons 2 (.cons 4 (.cons 7 (.cons 11 .nil)))))" },
    { name := "infinitary data", run := fun _ =>
        cRun (llvm := llvm) (treePrelude ++ "def main : Nat := Tree.depthAt (.node (fun i => .node (fun j => .leaf))) 3") "3" },
    { name := "deep recursion (direct recursion, big stack)", run := fun _ =>
        cRun (llvm := llvm) "import Prelude\ndef sumTo : Nat → Nat\n  | .zero => 0\n  | .succ n => (.succ n) + sumTo n\ndef main : Nat := sumTo 100000"
          "5000050000" },
    { name := "type classes and do", run := fun _ =>
        cRun (llvm := llvm) ("import Prelude\ninstance : Monad Option where\n  pure := fun a => Option.some a\n" ++
          "  bind := fun x f => match x with\n    | .none => Option.none\n    | .some a => f a\n" ++
          "def main : Option Nat := do\n  a ← Option.some 1;\n  b ← Option.some 2;\n  Monad.pure (a + b)") ".some 3" },
    { name := "division, powers and bits (small and GMP numbers)", run := fun _ =>
        cRun (llvm := llvm) ("import Prelude\ndef big : Nat := Nat.pow 3 50\n" ++
          "def main : List Nat := .cons (Nat.div big 1000007) (.cons (Nat.mod big 1000007) (.cons (Nat.div 100 7) " ++
          "(.cons (Nat.mod 100 0) (.cons (Nat.land big (Nat.pow 2 70 - 1)) (.cons (Nat.lor 12 10) (.cons (Nat.xor big big) " ++
          "(.cons (Nat.shiftLeft 3 70) (.cons (Nat.shiftRight big 40) (.cons (Nat.log2 big) (.cons (Nat.log2 0) " ++
          "(.cons (Nat.pow 0 0) (.cons (Nat.shiftLeft 1 61) (.cons (Nat.shiftLeft 1 62) .nil)))))))))))))")
          ".cons 717892962441115500 (.cons 961749 (.cons 14 (.cons 100 (.cons 98282295666516288457 (.cons 14 (.cons 0 (.cons 3541774862152233910272 (.cons 652924416219 (.cons 79 (.cons 0 (.cons 1 (.cons 2305843009213693952 (.cons 4611686018427387904 .nil)))))))))))))" },
    { name := "self tail calls are loops: 10M iterations on a 1 MB stack, at -O0 (15f)", run := fun _ =>
        cRunSmallStack (llvm := llvm) ("import Prelude\npartial def count (n acc : Nat) : Nat := match n with\n  | .zero => acc\n" ++
          "  | .succ m => match Nat.beq (Nat.mod m 3) 0 with\n    | .true => count m (acc + 2)\n    | .false => count m acc\n" ++
          "def main : Nat := count 10000000 0") "6666668" },
    { name := "constant folding and known constructors behave as before (15c)", run := fun _ =>
        cRun (llvm := llvm) foldSrc foldExpected },
    { name := "numerals at 2^31 … 2^64+1 and 10^30 are constants (15g)", run := fun _ =>
        cRun (llvm := llvm) bigLitSrc bigLitExpected },
    { name := "Bool.and/Bool.or don't compute an argument they don't need: one that never returns, 10M steps on a 1 MB stack at -O0 (15h)", run := fun _ =>
        cRunSmallStack (llvm := llvm) caseShapeSrc caseShapeExpected },
    { name := "shared projection prefixes: a root consumed before the last read through its prefix, an in-place update, a join point, codata (15j)", run := fun _ => do
        -- (the IR interpreter checks every reference: no use after free, no leak)
        unless llvm do okLib (projShareSrc ++ "#run main") [projShareExpected]
        cRun (llvm := llvm) projShareSrc projShareExpected },
    { name := "memoised suspensions (memo)", run := fun _ =>
        cRun (llvm := llvm) ("import Prelude\ndef twice (t : Unit → Nat) : Nat := t () + t ()\n" ++
          "def lazyAdd (m n : Nat) : Unit → Nat := memo (fun _ => m + n)\n" ++
          "def main : Nat := twice (lazyAdd 20 1) + twice (memo (fun _ => 0))") "42" }
  ]

/-- `okLib` with `lib/Optic.wiz` importable too. -/
def okOptic (input : String) (infos : List String := []) : IO Unit := do
  let loader ← libLoader
  let s := runFrontend (R := ZeroOneMany) input { loader, trustedModule := Tests.libModule }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render input
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  checkEq (repr infos).pretty (repr (s.messages.toList.map (·.text))).pretty

/-! ## HD8: command macros, reflection, `deriving` -/

/-- Elaborate with `Prelude` and `Deriving` importable; no errors, and these infos. -/
def derivingRun (input : String) : IO (CommandState ZeroOneMany) := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let derivingLib ← IO.FS.readFile "lib/Deriving.wiz"
  let textLib ← IO.FS.readFile "lib/Text.wiz"
  let loader : Name → Option String := fun m =>
    if m == "Prelude" then some prelude else if m == "Deriving" then some derivingLib
    else if m == "Text" then some textLib else none
  pure (runFrontend (R := ZeroOneMany) input { loader, trustedModule := Tests.libModule })

def okDeriving (input : String) (infos : List String := []) : IO Unit := do
  let s ← derivingRun input
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render input
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  checkEq (repr infos).pretty (repr (s.messages.toList.map (·.text))).pretty

/-- Rejected within `secs` seconds, with an error mentioning `fragment`, with every library
importable: checked in a child process (`tests --check-libs`) that a regression times out
instead of hanging the suite (address space capped at 8 GB, like `Scaling.checksWithin`). -/
def failsLibsWithin (secs : Nat) (input : String) (fragment : String) : IO Unit := do
  let dir ← IO.FS.createTempDir
  let file := dir / "input.wiz"
  IO.FS.writeFile file input
  let self ← IO.appPath
  let out ← IO.Process.output { cmd := "sh", args := #["-c",
    s!"ulimit -v 8000000; exec timeout {secs} \"$0\" --check-libs \"$1\"", self.toString, file.toString] }
  IO.FS.removeDirAll dir
  if out.exitCode == 124 then throw (IO.userError s!"not rejected within {secs} s")
  unless out.exitCode == 1 do
    throw (IO.userError s!"expected an error; exit code {out.exitCode}: {(out.stdout ++ out.stderr).take 1500}")
  unless (out.stderr.splitOn fragment).length > 1 do
    throw (IO.userError s!"error does not mention '{fragment}':\n{out.stderr.take 1500}")

end Tests.Elab
