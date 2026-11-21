import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- (15g) Numerals for the self-hosted compiler, whose numbers are 63-bit words: up to
`2^63 - 1` (and the compiler does not overflow its stack halving 1000000000); arithmetic
wraps, also when the backend folds it at compile time. -/
def selfhostBigLits : String := "import Prelude
def printAll (ns : List Nat) : IO Unit := match ns with
  | .nil => IO.pure ()
  | .cons n rest => do
    IO.println (Nat.toString n);
    printAll rest
def main : IO Unit := printAll (.cons 1000000000 (.cons 2147483648 (.cons 4294967296 (.cons 4611686018427387904
  (.cons 9223372036854775807 (.cons (4611686018427387904 + 4611686018427387904) (.cons (4294967296 * 4294967297) .nil)))))))
"

def selfhostBigLitsExpected : String :=
  "1000000000\n2147483648\n4294967296\n4611686018427387904\n9223372036854775807\n0\n4294967296\n"

/-- Tokens as the Lean lexer reads them, as `kind:text` lines. -/
partial def leanTokens (tokens : Array String) (input : String) : List String :=
  let chars := input.toList.toArray
  let rec go (i : Nat) (acc : List String) : List String :=
    let i := skipWs chars i
    if i ≥ chars.size then acc.reverse else
    match readToken tokens chars i with
    | .ok t =>
      let line := match t.tok with
        | .atom a => "atom:" ++ a | .ident n => "ident:" ++ n | .num d => "num:" ++ d | .str s => "str:" ++ s
      go t.stop (line :: acc)
    | .error e => (("error:" ++ e) :: acc).reverse
  go 0 []

/-- What the Lean parser makes of `input`, printed like `parse` in `Parse.wiz`. -/
def leanParse (t : ParserTables) (cat : Name) (input : String) : String :=
  let chars := input.toList.toArray
  let p : P Syntax := do
    let stx ← categoryParser cat 0
    let i ← P.nextPos
    if i < chars.size then P.failAt i "end of input" else pure stx
  match p.run chars t with
  | .ok (stx, _) => stx.toSExpr (atoms := true)
  | .error e => s!"error {e.pos}: expected {", ".intercalate e.expected.toList}"

/-- (audit S1, audit-2 P-1) The name of a term's constructor. **No wildcard**: a new
constructor of `Term` does not compile here until it is given a name, and then the test
"every constructor of Term is covered by the traversals" fails until it has a sample in
`termSamples`. A constructor missing from `Term.mapChildrenM` proved `False` once. -/
def termCtor : Term ZeroOneMany → String
  | .var _ => "var" | .const .. => "const" | .sort _ => "sort" | .pi .. => "pi" | .lam .. => "lam"
  | .app .. => "app" | .letE .. => "letE" | .ann .. => "ann" | .mvar _ => "mvar" | .sigma .. => "sigma"
  | .pair .. => "pair" | .fst _ => "fst" | .snd _ => "snd" | .split .. => "split" | .unit _ => "unit"
  | .tt => "tt" | .empty _ => "empty" | .absurd .. => "absurd" | .eq .. => "eq" | .eqTy .. => "eqTy"
  | .refl .. => "refl" | .reflTy _ => "reflTy" | .cast .. => "cast" | .transp .. => "transp"
  | .qty => "qty" | .qlit _ => "qlit" | .enum _ => "enum" | .tag .. => "tag" | .ecase .. => "ecase"
  | .desc .. => "desc" | .dret _ => "dret" | .darg .. => "darg" | .drec .. => "drec" | .dhrec .. => "dhrec"
  | .delim .. => "delim" | .mu .. => "mu" | .con _ => "con" | .ind .. => "ind" | .nu .. => "nu"
  | .out _ => "out" | .size => "size" | .szInf => "szInf" | .szSuc _ => "szSuc" | .sizeLt _ => "sizeLt"
  | .sfix .. => "sfix" | .scase .. => "scase" | .cocon _ => "cocon" | .scofix .. => "scofix"
  | .coit .. => "coit" | .natLit _ => "natLit" | .natOp .. => "natOp" | .ulift .. => "ulift"
  | .up _ => "up" | .down _ => "down" | .prf .. => "prf" | .letUnit .. => "letUnit"

/-- How many constructors `Term` has (the arms of `termCtor`). -/
def termCtorCount : Nat := 56

/-- One term per constructor of `Term`, with `c` in every term position and `w` in every
level position, and how many of each there are. -/
def termSamples (c : Term ZeroOneMany) (w : Level) : List (Term ZeroOneMany × Nat × Nat) :=
  [(.var 3, 0, 0), (.const "k" [w], 0, 1), (.sort w, 0, 1), (.pi "x" .default c c c ⟨w, w⟩, 3, 2),
   (.lam "x" c, 1, 0), (.app c c, 2, 0), (.letE "x" c c c c, 4, 0), (.ann c c, 2, 0), (.mvar 0, 0, 0),
   (.sigma "x" c c c ⟨w, w⟩, 3, 2), (.pair c c, 2, 0), (.fst c, 1, 0), (.snd c, 1, 0),
   (.split c c "z" c "x" "y" c, 4, 0), (.unit w, 0, 1), (.tt, 0, 0), (.empty w, 0, 1), (.absurd c c, 2, 0),
   (.eq c c c, 3, 0), (.eqTy c c, 2, 0), (.refl c c, 2, 0), (.reflTy c, 1, 0), (.cast c c c c, 4, 0),
   (.transp c c c c c c, 6, 0), (.qty, 0, 0), (.qlit .one, 0, 0), (.enum ["a"], 0, 0), (.tag ["a"] 0, 0, 0),
   (.ecase "z" c c [c, c], 4, 0), (.desc w c, 1, 1), (.dret c, 1, 0), (.darg c c c, 3, 0), (.drec c c c, 3, 0),
   (.dhrec c c c c, 4, 0), (.delim w c c c c c c, 6, 1), (.mu w c c c c (some ("h", [w], [c])) false, 5, 2),
   (.con c, 1, 0), (.ind w c c w c c c c false, 6, 2), (.nu w c c c c (some ("h", [w], [c])), 5, 2), (.out c, 1, 0),
   (.size, 0, 0), (.szInf, 0, 0), (.szSuc c, 1, 0), (.sizeLt c, 1, 0), (.sfix w c c w c c c c c, 7, 2),
   (.scase w c c c w c c c c c, 8, 2), (.cocon c, 1, 0), (.scofix w c c c c c c c, 7, 1), (.coit w c c c c c c, 6, 1),
   (.natLit 3, 0, 0), (.natOp "nat.add" #[c, c], 2, 0), (.ulift w w c, 1, 2), (.up c, 1, 0), (.down c, 1, 0),
   (.prf w c, 1, 1), (.letUnit c c, 2, 0)]

/-- A program for the self-hosted backend (recursion, lists, arrays, maps, strings, mutual
types), printing `6765 5050 1989 2 yes, ünïcode 2 5`. -/
def selfhostProgram1 : String :=
  "import Prelude\npartial def fib : Nat → Nat\n  | 0 => 0\n  | 1 => 1\n  | n + 2 => fib n + fib (n + 1)\npartial def countdown (n : Nat) (acc : List Nat) : List Nat := match n with\n  | 0 => acc\n  | .succ k => countdown k (List.cons n acc)\ndef sum : List Nat → Nat\n  | .nil => 0\n  | .cons x xs => x + sum xs\ndef fill (a : Array Nat) : Nat → Array Nat\n  | 0 => a\n  | .succ k => fill (Array.push a k) k\nmutual\ninductive Tree where\n  | leaf (n : Nat)\n  | node (ts : Forest)\ninductive Forest where\n  | nil\n  | cons (t : Tree) (ts : Forest)\nend\nmutual\ndef sizeT (t : Tree) : Nat := match t with\n  | .leaf _ => 1\n  | .node ts => sizeF ts\ndef sizeF (f : Forest) : Nat := match f with\n  | .nil => 0\n  | .cons t ts => sizeT t + sizeF ts\nend\ndef main : IO Unit := do\n  IO.println (Nat.toString (fib 20));\n  IO.println (Nat.toString (sum (countdown 100 .nil)));\n  let a := fill Array.empty 1000;\n  IO.println (Nat.toString (Array.size a + Array.getD a 10 0));\n  let m := StrMap.insert (StrMap.insert StrMap.empty (Str.ofString \"a\") 1) (Str.ofString \"b\") 2;\n  IO.println (Nat.toString (StrMap.findD m (Str.ofString \"b\") 0));\n  IO.println (if Nat.lt 3 4 then String.append \"yes, \" \"ünïcode\" else \"no\");\n  IO.println (Nat.toString (sizeT (Tree.node (Forest.cons (Tree.leaf 1) (Forest.cons (Tree.leaf 2) Forest.nil)))));\n  IO.println (Nat.toString (String.length \"hello\"))\n"

/-- A program for the reference counting mode: a list a million long (built, walked by
`ind`, freed without deep recursion), a hypothesis never read, a shared array updated
(copied), closures applied twice, a parameter never used, a key inserted twice. -/
def selfhostProgram2 : String :=
  "import Prelude\ndef len : List Nat → Nat\n  | .nil => 0\n  | .cons _ t => len t + 1\npartial def build (n : Nat) (acc : List Nat) : List Nat := match n with\n  | 0 => acc\n  | .succ k => build k (List.cons k acc)\ndef firstOr (d : Nat) : List Nat → Nat\n  | .nil => d\n  | .cons x _ => x\ndef twice (f : Nat → Nat) (x : Nat) : Nat := f (f x)\ndef adder (n : Nat) : Nat → Nat := fun x => x + n\ndef pick (b : Bool) (x y : List Nat) : List Nat := if b then x else y\ndef ignore (x : List Nat) (y : Nat) : Nat := y\ndef main : IO Unit := do\n  let big := build 1000000 .nil;\n  IO.println (Nat.toString (len big));\n  IO.println (Nat.toString (firstOr 7 big));\n  let a := Array.push (Array.push Array.empty 1) 2;\n  let b := Array.set a 0 5;\n  IO.println (Nat.toString (Array.getD a 0 0 + Array.getD b 0 0));\n  let add3 := adder 3;\n  IO.println (Nat.toString (twice add3 1 + twice add3 2));\n  IO.println (Nat.toString (len (pick .false big (List.cons 1 .nil)) + ignore big 4));\n  let m := StrMap.insert (StrMap.insert StrMap.empty (Str.ofString \"k\") 1) (Str.ofString \"k\") 2;\n  IO.println (Nat.toString (StrMap.findD m (Str.ofString \"k\") 0 + StrMap.size m))\n"

/-- A program for reuse under reference counting: a list mapped while shared (copied)
and unique (its cells reused), a tree rebuilt twice, a pair taken apart and rebuilt;
prints `1000000 9900 18 4`. -/
def selfhostProgram3 : String :=
  "import Prelude\ndef mapL (f : Nat → Nat) : List Nat → List Nat\n  | .nil => .nil\n  | .cons x xs => .cons (f x) (mapL f xs)\ndef sumL : List Nat → Nat\n  | .nil => 0\n  | .cons x xs => x + sumL xs\npartial def build (n : Nat) (acc : List Nat) : List Nat := match n with\n  | 0 => acc\n  | .succ k => build k (List.cons k acc)\ninductive T where\n  | leaf (n : Nat)\n  | node (l : T) (r : T)\ndef incT : T → T\n  | .leaf n => .leaf (n + 1)\n  | .node l r => .node (incT l) (incT r)\ndef sumT : T → Nat\n  | .leaf n => n\n  | .node l r => sumT l + sumT r\ndef t0 : T := T.node (T.node (T.leaf 1) (T.leaf 2)) (T.leaf 3)\ndef swapP (p : Prod Nat (List Nat)) : Prod (List Nat) Nat := .mk p.snd p.fst\ndef main : IO Unit := do\n  let xs := build 1000 .nil;\n  let ys := mapL (fun x => x + 1) xs;\n  IO.println (Nat.toString (sumL xs + sumL ys));\n  IO.println (Nat.toString (sumL (mapL (fun x => x * 2) (build 100 .nil))));\n  IO.println (Nat.toString (sumT (incT (incT t0)) + sumT t0));\n  IO.println (Nat.toString (Prod.snd (swapP (.mk 4 xs))))\n"

/-- A program for the demand analysis of `let`s under reference counting: a `let` used
in one branch only (moved into it), a dead one (dropped), one under a `λ` (suspended),
one used on every path (strict); prints `110 0 7 23 13`. -/
def selfhostProgram4 : String :=
  "import Prelude\ndef sumTo : Nat → Nat\n  | .zero => 0\n  | .succ k => sumTo k + k + 1\ndef onlyIf (b : Bool) (n : Nat) : Nat :=\n  let s := sumTo n;\n  match b with\n  | .true => s + s\n  | .false => 0\ndef dead (n : Nat) : Nat :=\n  let unused := sumTo n;\n  n\ndef later (n : Nat) : Nat → Nat :=\n  let s := sumTo n;\n  fun x => x + s\ndef both (b : Bool) (n : Nat) : Nat :=\n  let s := sumTo n;\n  match b with\n  | .true => s\n  | .false => s + 1\ndef main : IO Unit := do\n  IO.println (Nat.toString (onlyIf .true 10));\n  IO.println (Nat.toString (onlyIf .false 10));\n  IO.println (Nat.toString (dead 7));\n  let f := later 4;\n  IO.println (Nat.toString (f 1 + f 2));\n  IO.println (Nat.toString (both .false 3 + both .true 3))\n"

/-- A program for unmemoised hypotheses under reference counting: a function-valued
recursion (`nth`) partially applied and called 3000 times, a hypothesis read once
(`lenL`), one read twice (`twice`: memoised, else exponential), a tree with two
hypotheses read once each; prints `4498500 3000 1099511627775 65536`. -/
def selfhostProgram5 : String :=
  "import Prelude\npartial def build (n : Nat) (acc : List Nat) : List Nat := match n with\n  | 0 => acc\n  | .succ k => build k (List.cons k acc)\ndef nth : List Nat → Nat → Nat\n  | .nil, _ => 0\n  | .cons x xs, i => match i with\n    | .zero => x\n    | .succ j => nth xs j\ndef sumF (f : Nat → Nat) : Nat → Nat\n  | .zero => 0\n  | .succ k => f k + sumF f k\ndef lenL : List Nat → Nat\n  | .nil => 0\n  | .cons _ t => lenL t + 1\ndef twice : List Nat → Nat\n  | .nil => 0\n  | .cons _ t => twice t + twice t + 1\ninductive T where\n  | leaf (n : Nat)\n  | node (l : T) (r : T)\ndef mk : Nat → T\n  | .zero => T.leaf 1\n  | .succ k => T.node (mk k) (mk k)\ndef sumT : T → Nat\n  | .leaf n => n\n  | .node l r => sumT l + sumT r\ndef main : IO Unit := do\n  let xs := build 3000 .nil;\n  let f := nth xs;\n  IO.println (Nat.toString (sumF f 3000));\n  IO.println (Nat.toString (lenL xs));\n  IO.println (Nat.toString (twice (build 40 .nil)));\n  IO.println (Nat.toString (sumT (mk 16)))\n"

/-- Compile a program with the self-hosted compiler, then the C it prints with the
self-hosted runtime (`selfhost/rt.c`, with the garbage collector given by the
toolchain's `gcCflags`/`gcLdflags`), run it, and hand its output to `k`. -/
def selfhostRunWith (file : String) (k : String → IO Unit) (flags : Array String := #[])
    (progArgs : Array String := #[]) (opt : String := "-O2") (smallStack : Bool := false) : IO Unit := do
  let tc ← toolchain
  if tc.gcCflags.isEmpty then skip "no garbage collector, --gc-cflags"; return
  match ← selfhostCompiler with
  | .error e =>
    if (e.splitOn "gmp.h").length > 1 then skip "no toolchain" else throw (IO.userError e)
  | .ok exe =>
    let dir ← IO.FS.createTempDir
    IO.FS.writeFile (dir / "input.wiz") file
    let out ← IO.Process.output { cmd := "timeout", args := #["300", exe.toString] ++ flags, cwd := dir }
    unless out.exitCode == 0 do throw (IO.userError s!"the compiler failed ({out.exitCode}): {out.stderr}")
    IO.FS.writeFile (dir / "out.c") out.stdout
    let rt := (← IO.currentDir) / "selfhost"
    let args := #[opt, "-w", s!"-I{rt}"] ++ tc.gcCflags.toArray ++ #["out.c", "-o", "prog"] ++ tc.gcLdflags.toArray
    let cc ← IO.Process.output { cmd := tc.cc, args, cwd := dir }
    unless cc.exitCode == 0 do throw (IO.userError s!"cc failed: {cc.stderr.take 2000}")
    -- (a small stack: 1 MB, and the runtime told not to raise it)
    let run ← if smallStack then
        let env : Array (String × Option String) := #[("WIZ_STACK_SET", some "1")]
        IO.Process.output { cmd := "sh", args := #["-c", "ulimit -s 1024; exec timeout 60 ./prog \"$@\"", "sh"] ++ progArgs, cwd := dir, env }
      else IO.Process.output { cmd := "timeout", args := #["60", (dir / "prog").toString] ++ progArgs, cwd := dir }
    unless run.exitCode == 0 do throw (IO.userError s!"the program failed ({run.exitCode}): {run.stderr}")
    k run.stdout

/-- Compile a program with the self-hosted compiler, then the C it prints with the
self-hosted runtime, run it, and compare its output. -/
def selfhostCompileRun (file expected : String) (flags : Array String := #[]) (progArgs : Array String := #[])
    (opt : String := "-O2") (smallStack : Bool := false) : IO Unit :=
  selfhostRunWith file (checkEq expected) flags progArgs opt smallStack

/-- (A17/A18) A program compiled and run by the Lean host and by the self-hosted compiler:
their outputs must agree (the expected output is the host's, not a literal). The C is
built at `-O0`: these are output differentials, and the program (with the prelude) is
large enough that `-O2` only slows them down. -/
def selfhostAgreesHost (file : String) : IO Unit := do
  let cell ← IO.mkRef (none : Option String)
  ioRunWith file fun out => cell.set (some out)
  let some expected ← cell.get | return
  selfhostCompileRun file expected (opt := "-O0")

/-- (15j) Reads of a wide structure's fields for the self-hosted backend: every field
(`sumW`), the root consumed before the last read through a prefix (`early`), the root's
cell reused by a rebuild while fields read through the prefix are live (`upd`), reads in
branches and after them (`br`); prints `21 17 43 22 23`. -/
def selfhostProjShare : String :=
  "import Prelude\nstructure W where\n  a : Nat\n  b : Nat\n  c : Nat\n  d : Nat\n  e : Nat\n  f : Nat\n" ++
  "def mkW (n : Nat) : W := W.mk n (n + 1) (n + 2) (n + 3) (n + 4) (n + 5)\n" ++
  "def sumW (w : W) : Nat := match w with\n  | .mk a b c d e f => a + b + c + d + e + f\n" ++
  "def keepW (w : W) : List W := .cons w .nil\n" ++
  "def lenL : List W → Nat\n  | .nil => 0\n  | .cons _ r => lenL r + 1\n" ++
  "def early (w : W) : Nat := match w with\n  | .mk _ b _ _ e f => b + lenL (keepW w) + e + f\n" ++
  "def upd (w : W) : W := match w with\n  | .mk _ b c d e f => W.mk (d + e) b c d e f\n" ++
  "def br (w : W) (k : Nat) : Nat := match w with\n  | .mk _ _ c d e f => (match k with\n    | .zero => d\n    | .succ _ => e) + f + c\n" ++
  "def main : IO Unit := do\n  IO.println (Nat.toString (sumW (mkW 1)));\n  IO.println (Nat.toString (early (mkW 2)));\n" ++
  "  IO.println (Nat.toString (sumW (upd (mkW 3))));\n  IO.println (Nat.toString (br (mkW 4) 0));\n  IO.println (Nat.toString (br (mkW 4) 5))\n"

/-- (15j) The C the self-hosted compiler prints for a program (`none`: no toolchain). -/
def selfhostC (file : String) (flags : Array String := #[]) : IO (Option String) := do
  match ← selfhostCompiler with
  | .error e =>
    if (e.splitOn "gmp.h").length > 1 then
      skip "no toolchain"
      return none
    else throw (IO.userError e)
  | .ok exe =>
    let dir ← IO.FS.createTempDir
    IO.FS.writeFile (dir / "input.wiz") file
    let out ← IO.Process.output { cmd := "timeout", args := #["300", exe.toString] ++ flags, cwd := dir }
    unless out.exitCode == 0 do throw (IO.userError s!"the compiler failed ({out.exitCode}): {out.stderr}")
    return some out.stdout

/-- (A14) The C the self-hosted compiler's driver writes for a set of module files
(`build input.wiz -o out.c`): `input.wiz` is the root module, the others are written
beside it (subdirectories included); `args` go to the driver after the command (`-I DIR`,
`--rc`, …). Without a command the compiler is the one-shot mode, which takes no roots: its
flags alone are the host's usage (`SelfhostCliDiff`). -/
def selfhostModuleC (files : List (String × String)) (args : Array String := #[]) :
    IO (Option String) := do
  match ← selfhostCompiler with
  | .error e =>
    if (e.splitOn "gmp.h").length > 1 then
      skip "no toolchain"
      return none
    else throw (IO.userError e)
  | .ok exe =>
    let dir ← IO.FS.createTempDir
    for (name, text) in files do
      if let some parent := (dir / name).parent then IO.FS.createDirAll parent
      IO.FS.writeFile (dir / name) text
    let cmdArgs := #["300", exe.toString, "build", "input.wiz", "-o", "out.c", "--no-cache"] ++ args
    let out ← IO.Process.output { cmd := "timeout", args := cmdArgs, cwd := dir }
    unless out.exitCode == 0 do
      throw (IO.userError s!"the compiler failed ({out.exitCode}): {out.stderr}{out.stdout}")
    return some (← IO.FS.readFile (dir / "out.c"))

/-- The self-hosted compiler rejects a program: exit code 1, the errors on standard
error, and no C (15g). -/
def selfhostCompileFails (file : String) (errors : String) : IO Unit := do
  match ← selfhostCompiler with
  | .error e =>
    if (e.splitOn "gmp.h").length > 1 then skip "no toolchain" else throw (IO.userError e)
  | .ok exe =>
    let dir ← IO.FS.createTempDir
    IO.FS.writeFile (dir / "input.wiz") file
    let out ← IO.Process.output { cmd := "timeout", args := #["300", exe.toString], cwd := dir }
    checkEq (1 : UInt32) out.exitCode
    checkEq errors out.stderr
    checkEq "" out.stdout

/-- (D6, A11) The self-hosted CLI's `check` subcommand reports a frontend error with the
command's `file:line:col`, and prints no C. -/
def selfhostCheckFails (file expected : String) : IO Unit := do
  match ← selfhostCompiler with
  | .error e =>
    if (e.splitOn "gmp.h").length > 1 then skip "no toolchain" else throw (IO.userError e)
  | .ok exe =>
    let dir ← IO.FS.createTempDir
    IO.FS.writeFile (dir / "input.wiz") file
    let out ← IO.Process.output { cmd := "timeout", args := #["300", exe.toString, "check", "input.wiz"], cwd := dir }
    checkEq (1 : UInt32) out.exitCode
    checkEq expected out.stderr
    checkEq "" out.stdout

/-- The checker's output for a file of declarations must be the declarations it printed,
not the program it read: an echoing stub (the case that checks this group is not vacuous)
would otherwise pass every "is accepted" case. -/
def checkChecked (src out : String) : IO Unit := do
  if out.splitOn "\n" == src.splitOn "\n" then
    throw (IO.userError s!"the checker's output is its input, not declarations:\n{out.take 500}")
  for l in out.splitOn "\n" do
    if l.startsWith "import " then
      throw (IO.userError s!"the checker's output is its input, not declarations:\n{out.take 500}")

/-- (A11) `lib/Deriving.wiz` and the modules it imports, for the `deriving` differential:
the tests' prelude loader does not include it. -/
def derivingLoader : IO (Name → Option String) := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let text ← IO.FS.readFile "lib/Text.wiz"
  let deriv ← IO.FS.readFile "lib/Deriving.wiz"
  pure fun m =>
    if m == "Prelude" then some prelude else if m == "Text" then some text
    else if m == "Deriving" then some deriv else none

/-- (A11) `deriving` differential, per form: the Lean host (which registers the five
derivers on `import Deriving`) and the self-hosted frontend (whose prelude has no
classes, so `selfHeader` declares them) accept or reject each declaration as `expected`
says. -/
def derivingAgrees (selfHeader : String) (decls : List (String × Bool)) : IO Unit := do
  let loader ← derivingLoader
  for (d, ok) in decls do
    let hostSrc := "import Deriving\n" ++ d
    let hs := runFrontend (R := ZeroOneMany) hostSrc { loader, trustedModule := Tests.libModule }
    let leanOk := (hs.messages.filter (·.severity == .error)).isEmpty
    unless leanOk == ok do
      let es := (hs.messages.filter (·.severity == .error)).map (·.text)
      throw (IO.userError s!"the Lean frontend {if leanOk then "accepts" else "rejects"}:\n{d}\n{es}")
    let selfSrc := "import Prelude\n" ++ selfHeader ++ d
    let some out ← selfhostOutput selfSrc | return
    let errs := (out.splitOn "\n").filter (·.startsWith "error")
    if errs.isEmpty then checkChecked selfSrc out
    unless errs.isEmpty == ok do
      throw (IO.userError s!"the self-hosted frontend {if errs.isEmpty then "accepts" else "rejects"}:\n{d}\n{out}")

/-- (21l) A program with foreign functions gives the same output compiled by the Lean
compiler and by the self-hosted one (with the collector unless `gc := false`, and with
reference counting, which also checks that every object was freed). -/
def ffiAgrees (src expected : String) (gc : Bool := true) : IO Unit := do
  ioRun src expected
  if gc then selfhostCompileRun src expected
  selfhostCompileRun src expected (flags := #["--rc"])

/-- (25a, D1) The concurrency natives (`runtime/rt_con.inc`) on the self-hosted runtime:
the same program forks a thread per element, sends its number over the channel (the
parent closes its end once every child has finished), bumps a counter under a lock, and
rendezvouses on an MVar; the Lean and the self-hosted runtimes print the same sum and
count. The program declares the natives with `lib/MVar.wiz`'s and `lib/Session.wiz`'s
types, minus the phantom indices and linear holes the self-hosted frontend cannot express
yet (a type family `{A : Type} → MVar A → Type`); `MVar.take acc` passes no type argument
(its implicit `A` is written in the extern's type, which the frontend now inserts at the
use). It does not `recv` from the channel: a `do` bind whose value is a pair needs the
self-hosted frontend to solve a metavariable applied to the local context, which it
cannot yet (a P1 frontend gap). -/
def concNatives : String :=
  "import IO\n" ++
  "axiom MVar : Type → Type\naxiom Lock : Type\naxiom Guard : Type\naxiom Chan : Type\n" ++
  "extern \"wiz_mvar_new\" MVar.new : {0 A : Type} → IO (MVar A)\n" ++
  "extern \"wiz_mvar_new_full\" MVar.newFull : {0 A : Type} → (a : A) → IO (MVar A)\n" ++
  "extern \"wiz_mvar_take\" MVar.take : {0 A : Type} → (m : MVar A) → IO A\n" ++
  "extern \"wiz_mvar_put\" MVar.put : {0 A : Type} → (m : MVar A) → (a : A) → IO Unit\n" ++
  "extern \"wiz_mvar_read\" MVar.read : {0 A : Type} → (m : MVar A) → IO A\n" ++
  "extern \"wiz_lock_new\" Lock.new : IO Lock\n" ++
  "extern \"wiz_lock_acquire\" Lock.acquire : (l : Lock) → IO Guard\n" ++
  "extern \"wiz_lock_release\" Lock.release : (l : Lock) → (g : Guard) → IO Unit\n" ++
  "extern \"wiz_chan_fork\" Chan.fork : (child : (c : Chan) → IO Unit) → IO Chan\n" ++
  "extern \"wiz_chan_send\" Chan.send : {0 A : Type} → (c : Chan) → (a : A) → IO Chan\n" ++
  "extern \"wiz_chan_close\" Chan.close : (c : Chan) → IO Unit\n" ++
  "def child (n : Nat) (acc : MVar Nat) (l : Lock) (done : MVar Nat) : (c : Chan) → IO Unit :=\n" ++
  "  fun c => do\n" ++
  "    g ← Lock.acquire l;\n" ++
  "    x ← MVar.take acc;\n" ++
  "    MVar.put (A := Nat) acc (x + 1);\n" ++
  "    Lock.release l g;\n" ++
  "    c' ← Chan.send (A := Nat) c n;\n" ++
  "    Chan.close c';\n" ++
  "    MVar.put (A := Nat) done n\n" ++
  "def main : IO Unit := do\n" ++
  "  acc ← MVar.newFull (A := Nat) 0;\n" ++
  "  l ← Lock.new;\n" ++
  "  done ← MVar.new (A := Nat);\n" ++
  "  c1 ← Chan.fork (child 1 acc l done);\n" ++
  "  c2 ← Chan.fork (child 2 acc l done);\n" ++
  "  c3 ← Chan.fork (child 3 acc l done);\n" ++
  "  c4 ← Chan.fork (child 4 acc l done);\n" ++
  "  c5 ← Chan.fork (child 5 acc l done);\n" ++
  "  c6 ← Chan.fork (child 6 acc l done);\n" ++
  "  c7 ← Chan.fork (child 7 acc l done);\n" ++
  "  c8 ← Chan.fork (child 8 acc l done);\n" ++
  "  v1 ← MVar.take (A := Nat) done;\n" ++
  "  v2 ← MVar.take (A := Nat) done;\n" ++
  "  v3 ← MVar.take (A := Nat) done;\n" ++
  "  v4 ← MVar.take (A := Nat) done;\n" ++
  "  v5 ← MVar.take (A := Nat) done;\n" ++
  "  v6 ← MVar.take (A := Nat) done;\n" ++
  "  v7 ← MVar.take (A := Nat) done;\n" ++
  "  v8 ← MVar.take (A := Nat) done;\n" ++
  "  Chan.close c1;\n  Chan.close c2;\n  Chan.close c3;\n  Chan.close c4;\n" ++
  "  Chan.close c5;\n  Chan.close c6;\n  Chan.close c7;\n  Chan.close c8;\n" ++
  "  n ← MVar.take (A := Nat) acc;\n" ++
  "  IO.println (Nat.toString (v1 + v2 + v3 + v4 + v5 + v6 + v7 + v8));\n" ++
  "  IO.println (Nat.toString n)\n"

/-- The same program gives the same output in the Lean compiler and in the self-hosted
one, in both memory modes (the `--rc` run also checks that every object was freed). -/
def bothRuntimes (src expected : String) : IO Unit := do
  ioRun src expected
  selfhostCompileRun src expected
  selfhostCompileRun src expected (flags := #["--rc"])

/-- (21l) Foreign functions: headers, prototypes, numbers, strings, `Bool`, `Unit`, `IO`. -/
def ffiProgram1 : String :=
  "import IO\nextern \"strlen\" (header := \"string.h\") strlen : String → Nat\n" ++
  "extern \"strerror\" (header := \"string.h\") strerror : Nat → String\n" ++
  "extern \"isdigit\" (header := \"ctype.h\") isdigit : Nat → Bool\n" ++
  "extern \"puts\" (header := \"stdio.h\") cputs : String → IO Unit\n" ++
  "extern \"labs\" (header := \"stdlib.h\") labs : Nat → Nat\n" ++
  "def show (n : Nat) : IO Unit := IO.println (Nat.toString n)\n" ++
  "def pick (b : Bool) (y n : String) : String := match b with\n  | .true => y\n  | .false => n\n" ++
  "def main : IO Unit := do\n  show (strlen \"hello, ünïcode\");\n  IO.println (strerror 0);\n" ++
  "  IO.println (pick (isdigit 55) \"digit\" \"not\");\n  IO.println (pick (isdigit 65) \"digit\" \"not\");\n" ++
  "  cputs \"from C\";\n  show (labs 42);\n" ++
  "  show (UInt64.toNat (UInt64.mul (UInt64.ofNat 1000000) (UInt64.ofNat 1000000)));\n" ++
  "  let big := UInt64.sub (UInt64.ofNat 0) (UInt64.ofNat 1);\n" ++
  "  IO.println (pick (UInt64.lt (UInt64.ofNat 5) big) \"wraps\" \"no\");\n" ++
  "  IO.println (pick (UInt64.eq (UInt64.add big (UInt64.ofNat 1)) (UInt64.ofNat 0)) \"zero\" \"no\");\n" ++
  "  IO.println (Float64.toString (Float64.div (Float64.ofNat 1) (Float64.ofNat 4)));\n" ++
  "  IO.println (Float64.toString (Float64.sub (Float64.ofNat 1) (Float64.ofNat 3)))\n"

def ffiExpected1 : String :=
  "16\nSuccess\ndigit\nnot\nfrom C\n42\n1000000000000\nwraps\nzero\n0.25\n-2\n"

/-- (21l) A foreign pointer type with a finalizer: `fclose` runs when the last reference
to the `FILE` goes (so the file is complete when it is read back). -/
def ffiProgramFin (flush : Bool) : String :=
  let file := s!"/tmp/wiz_ffi_fin_{flush}.txt"
  "import IO\nforeign_type FILE (finalizer := \"fclose\")\n" ++
  "extern \"fopen\" (header := \"stdio.h\") fopen : String → String → IO FILE\n" ++
  "extern \"fputs\" (header := \"stdio.h\") fputs : String → FILE → IO Nat\n" ++
  "extern \"fflush\" (header := \"stdio.h\") fflush : FILE → IO Nat\n" ++
  "def write (f : FILE) : Nat → IO Unit\n  | .zero => IO.pure ()\n  | .succ k => do\n    n ← fputs \"line\\n\" f;\n    write f k\n" ++
  "def main : IO Unit := do\n  f ← fopen \"" ++ file ++ "\" \"w\";\n  write f 3;\n" ++
  (if flush then "  n ← fflush f;\n" else "") ++
  "  s ← IO.readFile \"" ++ file ++ "\";\n  IO.print s\n"

/-- (stages 21i–j) Differential: each declaration after `header` is accepted (`true`) or
rejected by the Lean frontend and by the self-hosted one alike, as `expected` says. -/
def selfhostAgrees (header : String) (decls : List (String × Bool)) : IO Unit := do
  let loader ← preludeLoader
  for (d, ok) in decls do
    let src := "import Prelude\n" ++ header ++ d
    let s := runFrontend (R := ZeroOneMany) src { loader, trustedModule := Tests.libModule }
    let leanOk := (s.messages.filter (·.severity == .error)).isEmpty
    unless leanOk == ok do throw (IO.userError s!"the Lean frontend {if leanOk then "accepts" else "rejects"}:\n{d}")
    let some out ← selfhostOutput src | return
    let errs := (out.splitOn "\n").filter (·.startsWith "error")
    if errs.isEmpty then checkChecked src out
    unless errs.isEmpty == ok do
      throw (IO.userError s!"the self-hosted frontend {if errs.isEmpty then "accepts" else "rejects"}:\n{d}\n{out}")

/-- (stage 21m) Pinned differences between the frontends: each declaration after `header`
is accepted or rejected by the Lean frontend (`leanOk`) and by the self-hosted one
(`selfOk`) as given, which for the pinned ones differ. -/
def selfhostVerdicts (header : String) (decls : List (String × Bool × Bool)) : IO Unit := do
  let loader ← preludeLoader
  for (d, ok, selfOk) in decls do
    let src := "import Prelude\n" ++ header ++ d
    let s := runFrontend (R := ZeroOneMany) src { loader, trustedModule := Tests.libModule }
    let leanOk := (s.messages.filter (·.severity == .error)).isEmpty
    unless leanOk == ok do throw (IO.userError s!"the Lean frontend {if leanOk then "accepts" else "rejects"}:\n{d}")
    let some out ← selfhostOutput src | return
    let errs := (out.splitOn "\n").filter (·.startsWith "error")
    if errs.isEmpty then checkChecked src out
    unless errs.isEmpty == selfOk do
      throw (IO.userError s!"the self-hosted frontend {if errs.isEmpty then "accepts" else "rejects"}:\n{d}\n{out}")

/-- (13i, 13p, 13q) Same outputs: after `header`, each `(e, n)` has `#eval e` print `n` in the
Lean frontend, and `#reduce Nat.beq (e) n` compute `.true` in the self-hosted one (whose
output is the kernel's normal form). Both frontends report no errors. -/
def selfhostSameNats (header : String) (cases : List (String × Nat)) : IO Unit := do
  let loader ← preludeLoader
  let src := "import Prelude\n" ++ header ++ String.join (cases.map fun (e, _) => s!"#eval {e}\n")
  let s := runFrontend (R := ZeroOneMany) src { loader, trustedModule := Tests.libModule }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"the Lean frontend rejects:\n{"\n".intercalate errs.toList}")
  checkEq (repr (cases.map fun (_, n) => toString n)).pretty (repr (s.messages.toList.map (·.text))).pretty
  let src' := "import Prelude\n" ++ header ++ String.join (cases.map fun (e, n) => s!"#reduce Nat.beq ({e}) {n}\n")
  let some out ← selfhostOutput src' | return
  let lines := (out.splitOn "\n").filter (· != "")
  if let some e := lines.find? (fun l => l.startsWith "error" || l.startsWith "parse error") then
    throw (IO.userError s!"the self-hosted frontend rejects: {e}\n{out}")
  let results := lines.filter (·.startsWith "con(")
  unless results == cases.map (fun _ => "con((#1, (tt, tt)))") do
    throw (IO.userError s!"the self-hosted frontend computes otherwise:\n{out}")

/-- (A23) The same lines: each `#print axioms` message and each error or warning the Lean
frontend reports (its text, with an error's `error: ` prefix) is a line the self-hosted
checker prints, in the same order. (A definition's own `f : T` line is a message in the
checker's output, not in the host's, so it is left out on both sides; the axioms note's
second line, `(native: …)`, is kept.) -/
def selfhostSameLines (src : String) : IO Unit := do
  let loader ← preludeLoader
  let s := runFrontend (R := ZeroOneMany) src { loader, trustedModule := Tests.libModule }
  let lines := s.messages.toList.filterMap fun m =>
    let l := (if m.severity == .error then "error: " else if m.severity == .warning then "warning: " else "")
      ++ m.text
    if m.text.startsWith "'" || m.severity != .info then some l else none
  let some out ← selfhostOutput src | return
  let got := (out.splitOn "\n").filter fun l =>
    l.startsWith "'" || l.startsWith "(" || l.startsWith "error" || l.startsWith "warning"
  checkEq (String.join (lines.map (· ++ "\n"))) (String.join (got.map (· ++ "\n")))

/-- (13q) Literal patterns: a `String.beq` both frontends have (`lib/Text.wiz` isn't the
self-hosted frontend's). -/
def litHeader : String :=
  "def chEq : List Char → List Char → Bool\n  | .nil, .nil => .true\n" ++
  "  | .cons a as, .cons b bs => Bool.and (Nat.beq (Char.code a) (Char.code b)) (chEq as bs)\n  | _, _ => .false\n" ++
  "def String.beq : String → String → Bool\n  | .mk a, .mk b => chEq a b\n" ++
  "def sLen : String → Nat\n  | .mk cs => List.length cs\n" ++
  "def Name : Type := String\n" ++
  "inductive Color where\n  | red\n  | green\n"

def litProgram : String :=
  "def s : String → Nat\n  | \"a\" => 1\n  | \"bc\" => 2\n  | _ => 0\n" ++
  "def two (a : String) (n : Nat) : Nat := match a, n with\n  | \"x\", 0 => 10\n  | \"x\", k+1 => k\n  | \"y\", _ => 7\n  | _, _ => 0\n" ++
  "def nm (x : Name) : Nat := match x with\n  | \"n\" => 5\n  | y => sLen y\n" ++
  "def h : Nat → Nat\n  | 0x10 => 1\n  | 0b11 => 2\n  | .succ .zero => 3\n  | _ => 0\n" ++
  "def big : Nat := 0xFF + 0b1010 + 0X1f\n"

def litCases : List (String × Nat) := [
  ("s \"a\"", 1), ("s \"bc\"", 2), ("s \"b\"", 0), ("s \"abc\"", 0),
  ("two \"x\" 0", 10), ("two \"x\" 5", 4), ("two \"y\" 3", 7), ("two \"z\" 0", 0),
  ("nm \"n\"", 5), ("nm \"abc\"", 3),
  ("h 16", 1), ("h 3", 2), ("h 1", 3), ("h 4", 0), ("big", 296)]

def litDecls : List (String × Bool) := [
  ("def f : String → Nat\n  | \"a\" => 1\n  | x => sLen x\n", true),
  ("def f (b : Nat) : Nat := match b with\n  | 0x3F => 1\n  | 0b1 => 2\n  | _ => 3\n", true),
  ("def f : String → Nat\n  | \"a\" => 1\n  | \"b\" => 2\n", false),
  ("def f : String → Nat\n  | n + 1 => 1\n  | _ => 2\n", false),
  ("def f : Color → Nat\n  | 0 => 1\n  | _ => 2\n", false),
  ("def f : Bool → Nat\n  | .true => 0\n  | 1 => 1\n  | _ => 2\n", false),
  ("def f : Nat → Nat\n  | 300 => 1\n  | _ => 2\n", false),
  ("def f : Nat → Nat\n  | 30 => 1\n  | _ => 2\n", true),
  ("def f (m : Nat) : Nat → Nat\n  | n + m => 1\n  | _ => 2\n", false),
  ("def f : Nat → Nat\n  | \"a\" => 1\n  | _ => 2\n", false),
  ("def f : String → Nat\n  | \"a\" => 0\n  | .mk _ => 2\n  | _ => 3\n", false),
  ("def f : String → Nat\n  | \"a\" => 0\n  | 3 => 2\n  | _ => 3\n", false),
  ("def f (c : Color) : Nat := match c with\n  | \"red\" => 0\n  | _ => 1\n", false),
  ("def f : String → Nat → Nat\n  | \"a\", .succ n => f \"a\" n\n  | _, _ => 0\n", false),
  ("def f : Nat → String → Nat\n  | .succ n, \"a\" => f n \"a\"\n  | _, _ => 0\n", true)]

/-- (13i, 13p) Structure update. -/
def updHeader : String :=
  "structure Stats where\n  hits : Nat\n  misses : Nat\n" ++
  "structure In where\n  x : Nat\n  y : Nat\nstructure Out where\n  i : In\n  n : Nat\nstructure Deep where\n  o : Out\n" ++
  "structure Tx (r : Type → Type) where\n  line : r Bool\n  busy : r Nat\n" ++
  "def Id' (A : Type) : Type := A\ndef St : Type := Stats\n" ++
  "inductive One where\n  | mk (a : Nat)\n"

def updProgram : String :=
  "def s0 : Stats := Stats.mk 1 2\ndef s1 : Stats := { s0 with hits := 5 }\n" ++
  "def bump (s : Stats) : Stats := { s with misses := Nat.add s.misses 1, hits := 0 }\n" ++
  "def o0 : Out := Out.mk (In.mk 1 2) 3\ndef o1 : Out := { o0 with i.x := 10, n := 4 }\n" ++
  "def o2 : Out := { o0 with i.x := 5, i.y := 6 }\n" ++
  "def d (e : Deep) : Deep := { e with o.i.y := 0 }\n" ++
  "def setBusy {r : Type → Type} (t : Tx r) (b : r Nat) : Tx r := { t with busy := b }\n" ++
  "def t0 : Tx Id' := Tx.mk .true 1\n" ++
  "def st (s : St) : St := { s with hits := 9 }\n" ++
  "def fresh : Stats := { Stats.mk 3 4 with misses := 0 }\n"

def updCases : List (String × Nat) := [
  ("s1.hits", 5), ("s1.misses", 2), ("(bump s0).hits", 0), ("(bump s0).misses", 3),
  ("o1.i.x", 10), ("o1.i.y", 2), ("o1.n", 4), ("Nat.add o2.i.x o2.i.y", 11),
  ("In.y (Out.i (Deep.o (d (Deep.mk o0))))", 0), ("In.x (Out.i (Deep.o (d (Deep.mk o0))))", 1),
  ("(setBusy t0 5).busy", 5), ("Stats.hits (st s0)", 9), ("Stats.misses (st s0)", 2),
  ("Nat.add fresh.hits fresh.misses", 3)]

def updDecls : List (String × Bool) := [
  ("def f (s : Stats) : Stats := { s with hits := 1 }\n", true),
  ("def f (s : Stats) : Stats := { s with hit := 1 }\n", false),
  ("def f (s : Stats) : Stats := { s with hits := 1, hits := 2 }\n", false),
  ("def f (n : Nat) : Nat := { n with hits := 1 }\n", false),
  ("def f (s : Stats) : Stats := { s with hits := .true }\n", false),
  ("def f (s : Stats) : Nat := { s with hits := 1 }\n", false),
  ("def f (o : One) : One := { o with a := 1 }\n", false),
  ("def f (o : Out) : Out := { o with i.z := 1 }\n", false),
  ("def f (o : Out) : Out := { o with n.x := 1 }\n", false),
  ("def f (o : Out) : Out := { o with i := In.mk 0 0, i.x := 1 }\n", false),
  ("def f (o : Out) : Out := { o with i.x := 1, i := In.mk 0 0 }\n", false),
  ("def f (o : Out) : Out := { o with i.x := 1, i.x := 2 }\n", false),
  ("def f (o : Out) : Out := { o with i.x := 1, i.y := 2, n := 0 }\n", true),
  ("def f (e : Deep) : Deep := { e with o.i.x := 1, o.n := 2 }\n", true)]

/-- (stage 21m) Written quantities (finding K10 of audit 2): the declarations both frontends
accept or reject alike. -/
def quantityHeader : String :=
  "def lin (1 x : Nat) (f : (1 y : Nat) → Nat) : Nat := f x\naxiom lin1 : (1 x : Nat) → Nat\n" ++
  "structure Pt (w : Nat) where\n  x : Nat\n" ++
  "axiom Tok : Type\naxiom use : (1 t : Tok) → Nat\ninductive L1 where\n  | mk (1 t : Tok)\n"
def quantityDecls : List (String × Bool) := [
  ("def ok1 (1 x : Nat) : Nat := x\n", true),
  ("def impOk {n : Nat} (x : Nat) : Nat := x\n", true),
  ("def useLin (1 z : Nat) : Nat := lin z (fun y => y)\n", true),
  ("def l1 (x : Nat) : Nat := let 1 y := x; y\n", true),
  ("def fl : (1 y : Nat) → Nat := fun (1 y : Nat) => y\ndef flU : (1 y : Nat) → Nat := fun y => y\n", true),
  ("def useAx (1 y : Nat) : Nat := lin1 y\n", true),
  ("def ptx {w : Nat} (p : Pt w) : Nat := p.x\n", true),
  ("def T1 : Type := (1 x : Nat) → Nat\n", true),
  ("def len {0 A : Type} : List A → Nat\n  | .nil => 0\n  | .cons _ t => Nat.succ (len t)\n", true),
  ("def dup (ω x : Nat) : Nat := Nat.add x x\ndef ax2 (0 A : Type) (1 a : A) : A := a\n", true),
  ("def twice (1 x : Nat) (f : Nat → Nat → Nat) : Nat := f x x\n", false),
  ("def drop (1 x : Nat) : Nat := Nat.zero\n", false),
  -- a data implicit is ω by default (rule (b), the language decision of 2026-11-16)
  ("def imp {n : Nat} (x : Nat) : Nat := n\n", true),
  ("def er (0 x : Nat) : Nat := x\n", false),
  ("def bad2 (2 x : Nat) : Nat := x\n", false),
  ("def l1bad (x : Nat) : Nat := let 1 y := x; Nat.add y y\n", false),
  ("def flbad2 : (y : Nat) → Nat := fun (1 y : Nat) => y\n", false),
  ("def useAx2 (1 y : Nat) : Nat := Nat.add (lin1 y) y\n", false),
  -- an implicit width used as data (rule (b): `Nat` is data, so ω)
  ("def mk {w : Nat} : Pt w := Pt.mk w\n", true),
  ("def toW (1 x : Nat) : Nat := Nat.succ x\n", false),
  ("def l0 (x : Nat) : Nat := let 0 y := x; y\n", false),
  ("def linTwice (1 z : Nat) : Nat := lin z (fun y => Nat.add y y)\n", false)]

/-- (stage 21x, 22a) Constructor fields with quantities (`Desc.arg q S D`), implicit
constructor fields (by rule (b): ω for data, 0 for a sort or a proposition; filled in at
the call, not named by patterns) and instance constructor fields (`[i : C A]`: resolved
at the call, skipped by a pattern, never an explicit argument): the same verdicts in both
frontends. -/
def fieldQtyHeader : String :=
  "axiom Tok : Type\naxiom use : (1 t : Tok) → Nat\n" ++
  "inductive E0 where\n  | mk (0 n : Nat) (m : Nat)\n" ++
  "inductive L1 where\n  | mk (1 t : Tok)\n" ++
  "inductive W where\n  | mk (ω n : Nat)\n" ++
  "inductive V (A : Type) : Nat → Type where\n  | nil : V A Nat.zero\n" ++
  "  | cons {n : Nat} (a : A) (rest : V A n) : V A (Nat.succ n)\n" ++
  "structure S0 where\n  0 n : Nat\n  m : Nat\n" ++
  "structure P1 where\n  1 a : Tok\n  b : Nat\n" ++
  "class C (A : Type) where\n  f : A → Nat\n" ++
  "instance : C Nat := C.mk (fun x => x)\n" ++
  "inductive I where\n  | mk [i : C Nat] (x : Nat)\n" ++
  "inductive LI where\n  | mk [i : C Nat] (1 t : Tok)\n"
def fieldQtyDecls : List (String × Bool) := [
  -- 0: built with any argument, never read at run time
  ("def e0 : E0 := E0.mk 3 4\ndef getM : E0 → Nat\n  | .mk _ m => m\ndef getM2 : E0 → Nat\n  | .mk n m => m\n", true),
  ("def getN : E0 → Nat\n  | .mk n _ => n\n", false),
  ("def e0d (x : E0) : Nat := match x with\n  | .mk n m => Nat.add m m\n", true),
  -- 1: a linear field is used exactly once by a match
  ("def l1 (1 t : Tok) : L1 := L1.mk t\ndef useL : L1 → Nat\n  | .mk t => use t\n", true),
  ("def dropL : L1 → Nat\n  | .mk _ => 0\n", false),
  ("def twiceL : L1 → Nat\n  | .mk t => Nat.add (use t) (use t)\n", false),
  -- ω, written
  ("def w2 : W → Nat\n  | .mk n => Nat.add n n\n", true),
  -- an implicit data field: ω by default (rule (b)), inserted at the call, not named by a pattern
  ("def v1 : V Nat (Nat.succ Nat.zero) := V.cons 5 V.nil\n" ++
    "def vsum {n : Nat} : V Nat n → Nat\n  | .nil => 0\n  | .cons a r => Nat.add a (vsum r)\n", true),
  ("def vbad : V Nat (Nat.succ Nat.zero) := V.cons 0 5 V.nil\n", false),
  -- structures: a 0 field has no projection; a linear field is read by its projection
  ("def s0 : S0 := S0.mk 1 2\ndef s0m (s : S0) : Nat := s.m\n", true),
  ("def s0n (s : S0) : Nat := s.n\n", false),
  ("def p1 (1 x : Tok) : P1 := P1.mk x 3\ndef p1b (p : P1) : Nat := p.b\n", true),
  -- (the Lean elaborator takes a structure apart by projections at ω)
  ("def p1m (p : P1) : Nat := match p with\n  | .mk a b => b\n", true),
  -- (a match on a structure binds a field at 0 at 0, in both since #217)
  ("def s0mt (s : S0) : Nat := match s with\n  | .mk n m => m\n", true),
  ("def s0mn (s : S0) : Nat := match s with\n  | .mk n m => n\n", false),
  -- recursive fields carry quantities too; a bad quantity is an error
  ("inductive R1 where\n  | z\n  | s (1 r : R1)\n", true),
  ("inductive Q2 where\n  | mk (2 n : Nat)\n", false),
  -- (22a) an instance field: an instance argument of the constructor (resolved at the
  -- call, at ω as the Lean elaborator's `elabQuantity`), not an explicit one; a pattern
  -- skips it like an implicit field
  ("def i1 : I := I.mk 3\ndef iu : I → Nat\n  | .mk x => x\n", true),
  -- (a regression: `[i]` passed as an explicit argument)
  ("def ibad : I := I.mk (C.mk (fun x => x)) 3\n", false),
  -- (22a) and beside a linear field: construction, a match using it once, and a drop
  ("def li1 (1 t : Tok) : LI := LI.mk t\ndef liu : LI → Nat\n  | .mk t => use t\n", true),
  ("def lidrop : LI → Nat\n  | .mk _ => 0\n", false),
  ("def litwice : LI → Nat\n  | .mk t => Nat.add (use t) (use t)\n", false)]

/-- (stage 21x, 22a) Field quantities, implicit fields and an instance field, compiled and
run. -/
def fieldQtyProgram : String :=
  "import Prelude\n" ++
  "inductive E0 where\n  | mk (0 n : Nat) (m : Nat)\n" ++
  "inductive V (A : Type) : Nat → Type where\n  | nil : V A Nat.zero\n" ++
  "  | cons {n : Nat} (a : A) (rest : V A n) : V A (Nat.succ n)\n" ++
  "inductive L1 where\n  | mk (1 n : Nat)\n" ++
  "class C (A : Type) where\n  f : A → Nat\n" ++
  "instance : C Nat := C.mk (fun x => x)\n" ++
  "inductive I where\n  | mk [i : C Nat] (1 n : Nat)\n" ++
  "def getM : E0 → Nat\n  | .mk _ m => m\n" ++
  "def vsum {n : Nat} : V Nat n → Nat\n  | .nil => 0\n  | .cons a r => Nat.add a (vsum r)\n" ++
  "def unL : L1 → Nat\n  | .mk n => n\n" ++
  "def unI : I → Nat\n  | .mk n => n\n" ++
  "def main : IO Unit := do\n  IO.println (Nat.toString (getM (E0.mk 3 4)));\n" ++
  "  IO.println (Nat.toString (vsum (V.cons 1 (V.cons 2 V.nil))));\n" ++
  "  IO.println (Nat.toString (unL (L1.mk 9)));\n" ++
  "  IO.println (Nat.toString (unI (I.mk 7)))\n"

/-- (stage 21m, K1; 22a) The pinned differences, `(declaration, Lean accepts, self-hosted
accepts)` (docs/CoreSpec.md §15): the Lean frontend takes a `match` on a linear scrutinee
apart with `T.casesOn1` (the case at 1), the self-hosted frontend's match is the case at
ω, which uses the scrutinee ω times. (Constructor field quantities and implicit fields
were differences until 21x, instance fields until 22a; a linear variable used once in
each branch of a `match` until 21v: `linearMatchDecls`.) `wrapTwice` is the constructor
field at the same boundary: the ω case projects the payload, so the linear `t` inside the
scrutinee is used ω times. It needs the linear case (`scase` at 1) and `Kernel.wiz`'s
missing `split` (B7), not another field-quantity change: `fieldCols` already binds each
field at its declared quantity, and `scaseMethodTy` hands the payload over at `q`. -/
def quantityDiffs : List (String × Bool × Bool) := [
  ("def m2 (1 x : Nat) : Nat := match x with\n  | .zero => 0\n  | .succ k => k\n", true, false),
  ("def wrapTwice (1 t : Tok) : Nat := match L1.mk t with\n  | .mk u => use u\n", true, false)]

/-- (stage 21v) A variable at quantity 1 used once in each branch of a `match`: the Lean
frontend compiles the match to the additive `T.casesOnA` (its branches are alternatives,
as the self-hosted frontend's `scase`/`ecase` are), so both accept it; a branch that
drops it or uses it twice is rejected by both. -/
def linearMatchHeader : String :=
  "axiom Tok : Type\naxiom use : (1 t : Tok) → Nat\naxiom use2 : (1 t : Tok) → Nat\n" ++
  "inductive V (A : Type) : Nat → Type where\n  | nil : V A Nat.zero\n  | cons (n : Nat) (a : A) (rest : V A n) : V A (Nat.succ n)\n"

def linearMatchDecls : List (String × Bool) := [
  ("def m1 (1 x : Nat) (b : Bool) : Nat := match b with\n  | .true => x\n  | .false => x\n", true),
  ("def f (b : Bool) (1 t : Tok) : Nat := match b with\n  | .true => use t\n  | .false => use2 t\n", true),
  ("def g (n : Nat) (1 t : Tok) : Nat := match n with\n  | .zero => use t\n  | .succ _ => use2 t\n", true),
  ("def h (o : Option Nat) (1 t : Tok) : Nat := match o with\n  | .none => use t\n  | .some _ => use t\n", true),
  ("def l (xs : List Nat) (1 t : Tok) : Nat := match xs with\n  | .nil => use t\n  | .cons _ _ => use t\n", true),
  ("def nested (b c : Bool) (1 t : Tok) : Nat := match b, c with\n  | .true, .true => use t\n  | .true, .false => use2 t\n  | .false, _ => use t\n", true),
  ("def lt (b : Bool) (x : Tok) : Nat := let 1 t := x; match b with\n  | .true => use t\n  | .false => use2 t\n", true),
  ("def vec {n : Nat} (v : V Nat n) (1 t : Tok) : Nat := match v with\n  | .nil => use t\n  | .cons _ _ _ => use2 t\n", true),
  ("def bad1 (b : Bool) (1 t : Tok) : Nat := match b with\n  | .true => use t\n  | .false => 0\n", false),
  ("def bad2 (b : Bool) (1 t : Tok) : Nat := match b with\n  | .true => Nat.add (use t) (use t)\n  | .false => use t\n", false),
  ("def bad3 (b : Bool) (1 t : Tok) : Nat := match b with\n  | .true => use t\n  | .false => Nat.add (use t) 1\n", false),
  ("def bad4 (n : Nat) (1 t : Tok) : Nat := match n with\n  | .zero => use t\n  | .succ k => Nat.add k (use t)\n", false)]

/-- (stage 21v) The additive match computes, compiled by the Lean compiler. -/
def linearMatchProgram : String :=
  "import IO\ndef m1 (1 x : Nat) (b : Bool) : Nat := match b with\n  | .true => x\n  | .false => x\n" ++
  "def pick (1 x : Nat) (o : Option Nat) : Nat := match o with\n  | .none => x\n  | .some _ => x\n" ++
  "def main : IO Unit := do\n  IO.println (Nat.toString (m1 3 .true));\n  IO.println (Nat.toString (pick 5 .none));\n" ++
  "  IO.println (Nat.toString (pick 6 (.some 7)))\n"

/-- (stage 21u) Σ types, pairs, projections and `∀` in both frontends. -/
def sigmaDecls : List (String × Bool) := [
  ("def mkP (n : Nat) : Nat × Bool := (n, .true)\ndef fstP (p : Nat × Bool) : Nat := p.1\ndef sndP (p : Nat × Bool) : Bool := p.2\n", true),
  ("def t3 : Nat × Bool × Nat := (1, .false, 2)\ndef t3c : Nat := t3.2.2\ndef t3b : Bool := t3.2.1\n", true),
  ("def D : Type := (n : Nat) × List Nat\ndef d : (n : Nat) × List Nat := (3, .nil)\ndef DQ : Type := (0 n : Nat) × Nat\n", true),
  ("def F : Type := ∀ (n : Nat) (b : Bool), Nat\ndef F2 : Type 1 := ∀ {A : Type} (x : A), A\n" ++
    "def idF : ∀ {A : Type} (x : A), A := fun {A} x => x\ndef F3 : Type := ∀ (n m : Nat) (b : Bool), Nat\n", true),
  ("def tup : Nat × Bool := (1, Bool.true)\ndef swap (p : Nat × Bool) : Bool × Nat := (p.2, p.1)\n", true),
  ("def bad : Nat × Bool := (1, 2)\n", false),
  ("def bad : Nat := (1, 2).3\n", false),
  ("def bad (p : Nat × Bool) : Nat := p.2\n", false),
  ("def bad : Type := (n : Nat) × n\n", false),
  ("def bad : Type := ∀ (n : Nat), n\n", false)]

/-- (21an) A `×` type as an inductive constructor field or a structure field. The
scope checker names a global by its index and `closeG` closes those indices over the
globals; it did not visit a `sigma`, so both components of a syntactic pair were left
as scope indices and the kernel rejected the declaration with "internal error: a
variable out of scope". A field written through a definition (`def P : Type := A × B`)
was fine, which is why this went unnoticed. -/
def sigmaFieldDecls : List (String × Bool) := [
  ("inductive PairField where\n  | mk (p : Nat × Bool)\n", true),
  ("structure PairStruct where\n  n : Nat\n  p : Nat × Bool\n", true),
  ("inductive Many where\n  | mk (a : String) (b : String × Nat) (c : List (String × Nat))\n", true),
  ("inductive At (A : Type) where\n  | mk (p : A × Nat) (f : Nat → A)\n", true),
  ("inductive PairField where\n  | mk (p : Nat × Bool)\n\ndef pf : PairField := PairField.mk (1, .true)\ndef pfSnd : Bool := match pf with\n  | .mk p => p.2\n", true),
  ("structure Nest where\n  n : Nat\n  q : Nat × (Bool × Nat)\n", true),
  -- (still rejected by both: the pair's second component is a Nat, not a Bool)
  ("inductive Bad where\n  | mk (p : Nat × Bool)\n\ndef u : Bad := Bad.mk (1, 2)\n", false)]

/-- (stage 21m) A program with quantities, compiled by the self-hosted compiler: the
0-quantity arguments are erased, a `let 1` runs. -/
def quantityProgram : String :=
  "import Prelude\ninductive Box (w : Nat) where\n  | mk (n : Nat)\nstructure Pt (w : Nat) where\n  x : Nat\n  y : Nat\n" ++
  "def get {w : Nat} : Box w → Nat\n  | .mk n => n\ndef sum {w : Nat} (p : Pt w) : Nat := p.x + p.y\n" ++
  "def b : Box 8 := .mk 3\ndef p : Pt 8 := .mk 1 2\n" ++
  "def lin (1 x : Nat) (f : (1 y : Nat) → Nat) : Nat := f x\n" ++
  "def len {A : Type} : List A → Nat\n  | .nil => 0\n  | .cons _ t => Nat.succ (len t)\n" ++
  "def id1 (1 x : Nat) : Nat := let 1 y := x; y\ndef main : IO Unit := do\n" ++
  "  IO.println (Nat.toString (get b + sum p));\n  IO.println (Nat.toString (Nat.add 1 (lin 4 (fun y => y))));\n" ++
  "  IO.println (Nat.toString (Nat.add (id1 7) (len (List.cons 1 (List.cons 2 .nil)))))\n"

/-- (stage 21o) The files of `linkFiles`-style programs compiled by the self-hosted
compiler: `main.wiz` is its input, the `// wiz-link-c:`/`// wiz-link-lib:` lines of the C
it prints name the C files (relative to the input's directory) and libraries that `cc`
compiles and links with it. Compares the output, or (`fails`) the exit code (3, a
runtime error; 4, a leak) and a fragment of its message. -/
def selfhostLinkRun (files : List (String × String)) (expected : String) (flags : Array String := #[])
    (fails : Option String := none) (failCode : UInt32 := 3) : IO Unit := do
  let tc ← toolchain
  if tc.gcCflags.isEmpty then
    skip "no garbage collector (--gc-cflags)"
    return
  match ← selfhostCompiler with
  | .error e =>
    if (e.splitOn "gmp.h").length > 1 then IO.println "    (skipped: no toolchain)" else throw (IO.userError e)
  | .ok exe =>
    let dir ← IO.FS.createTempDir
    for (p, text) in files do
      let f := dir / p
      if let some d := f.parent then IO.FS.createDirAll d
      IO.FS.writeFile f text
    IO.FS.writeFile (dir / "input.wiz") (← IO.FS.readFile (dir / "main.wiz"))
    let out ← IO.Process.output { cmd := "timeout", args := #["300", exe.toString] ++ flags, cwd := dir }
    unless out.exitCode == 0 do throw (IO.userError s!"the compiler failed ({out.exitCode}): {out.stderr}")
    IO.FS.writeFile (dir / "out.c") out.stdout
    let lines := out.stdout.splitOn "\n"
    let cs := lines.filterMap fun l => (l.dropPrefix? "// wiz-link-c: ").map (·.toString)
    let libs := lines.filterMap fun l => (l.dropPrefix? "// wiz-link-lib: ").map (s!"-l{·}")
    let rt := (← IO.currentDir) / "selfhost"
    let args := #["-O2", "-w", s!"-I{rt}", "-I."] ++ tc.gcCflags.toArray ++ #["out.c"] ++ cs.toArray ++ #["-o", "prog"] ++
      tc.gcLdflags.toArray ++ libs.toArray
    let cc ← IO.Process.output { cmd := tc.cc, args, cwd := dir }
    unless cc.exitCode == 0 do throw (IO.userError s!"cc failed: {cc.stderr.take 2000}")
    let run ← IO.Process.output { cmd := "timeout", args := #["60", (dir / "prog").toString], cwd := dir }
    match fails with
    | none =>
      unless run.exitCode == 0 do throw (IO.userError s!"the program failed ({run.exitCode}): {run.stderr}")
      checkEq expected run.stdout
    | some frag =>
      unless run.exitCode == failCode && (run.stderr.splitOn frag).length > 1 do
        throw (IO.userError s!"expected the runtime error '{frag}', got exit {run.exitCode}: {run.stderr}")
      checkEq expected run.stdout

/-- (stage 21o) C calls Wiz: exports (numbers, strings both ways, `Bool`, `IO`) called from a
`link_c` file, which the program calls through externs, and a `link_lib` library. -/
def exportFiles : List (String × String) :=
  [("main.wiz", "import IO\nlink_c \"c/cb.c\"\nlink_lib \"m\"\n" ++
      "def double (n : Nat) : Nat := n + n\ndef greet (who : String) : String := String.append \"hello, \" who\n" ++
      "def isBig (n : Nat) : Bool := Nat.lt 10 n\ndef tick (n : Nat) : IO Nat := do\n  IO.println \"tick\";\n  IO.pure (n + 1)\n" ++
      "export \"ex_double\" double\nexport \"ex_greet\" greet : String → String\nexport \"ex_is_big\" isBig\nexport \"ex_tick\" tick\n" ++
      "extern \"call_double\" callDouble : Nat → Nat\nextern \"greet_len\" greetLen : String → Nat\n" ++
      "extern \"count_big\" countBig : Nat → Nat\nextern \"run_tick\" runTick : Nat → IO Nat\nextern \"root_of\" rootOf : Nat → Nat\n" ++
      "def show (n : Nat) : IO Unit := IO.println (Nat.toString n)\n" ++
      "def main : IO Unit := do\n  show (callDouble 20);\n  show (greetLen \"you\");\n  show (countBig 20);\n" ++
      "  r ← runTick 41;\n  show r;\n  show (rootOf 1764)\n"),
   ("c/cb.c", "#include <stdint.h>\n#include <stdlib.h>\n#include <string.h>\n#include <math.h>\n" ++
      "uint64_t ex_double(uint64_t);\nchar *ex_greet(const char *);\nint ex_is_big(uint64_t);\nuint64_t ex_tick(uint64_t);\n" ++
      "uint64_t call_double(uint64_t n) { return ex_double(n) + 1; }\n" ++
      "uint64_t greet_len(const char *s) { char *g = ex_greet(s); uint64_t n = strlen(g); free(g); return n; }\n" ++
      "uint64_t count_big(uint64_t n) { uint64_t k = 0; for (uint64_t i = 0; i < n; i++) k += ex_is_big(i) != 0; return k; }\n" ++
      "uint64_t run_tick(uint64_t n) { return ex_tick(ex_tick(n)); }\n" ++
      "uint64_t root_of(uint64_t n) { volatile double d = (double)n; return (uint64_t)sqrt(d); }\n")]

def exportExpected : String := "41\n10\n9\ntick\ntick\n43\n42\n"

/-- (stage 21o) The declarations both frontends reject alike (`export`, `link_lib`). -/
def exportHeader : String :=
  "def f (n : Nat) : Nat := n\ndef g {A : Type} (a : A) : A := a\ndef h (f : Nat → Nat) : Nat := f 1\ndef k (u : Unit) : Nat := 1\n"

def exportDecls : List (String × Bool) := [
  ("export \"ok_f\" f\nexport \"ok_f2\" f : Nat → Nat\n", true),
  ("export \"1x\" f\n", false), ("export \"ok_f\" nope\n", false), ("export \"ok_f\" f : Nat → Bool\n", false),
  ("export \"ok_g\" g\n", false), ("export \"ok_h\" h\n", false), ("export \"ok_k\" k\n", false),
  ("export \"ok_f\" f\nexport \"ok_f\" f\n", false), ("link_lib \"-lm\"\n", false)]

/-- (stages 21q–t) `selfhostAgrees` for declarations that need `import IO` in the Lean
toolchain (the self-hosted frontend's `import` is its one Prelude, which has `IO` and
`Callback`). -/
def selfhostAgreesIO (header : String) (decls : List (String × Bool)) : IO Unit := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let ioLib ← IO.FS.readFile "lib/IO.wiz"
  let loader : Name → Option String := fun m =>
    if m == "Prelude" then some prelude else if m == "IO" then some ioLib else none
  for (d, ok) in decls do
    let src := "import IO\n" ++ header ++ d
    let s := runFrontend (R := ZeroOneMany) src { loader, trustedModule := Tests.libModule }
    let leanOk := (s.messages.filter (·.severity == .error)).isEmpty
    unless leanOk == ok do throw (IO.userError s!"the Lean frontend {if leanOk then "accepts" else "rejects"}:\n{d}")
    let some out ← selfhostOutput src | return
    let errs := (out.splitOn "\n").filter (·.startsWith "error")
    if errs.isEmpty then checkChecked src out
    unless errs.isEmpty == ok do
      throw (IO.userError s!"the self-hosted frontend {if errs.isEmpty then "accepts" else "rejects"}:\n{d}\n{out}")

/-- (stage 21q) Callbacks: Wiz closures passed to C (qsort with Wiz comparators, borrowed
for the call; a string callback; a `Callback` C keeps, calls later in `IO` and releases). -/
def callbackFiles (release : Bool) : List (String × String) :=
  [("main.wiz", "import IO\nlink_c \"c/cb.c\"\n" ++
      "extern \"sort_some\" sortSome : (Nat → Nat → Bool) → String\n" ++
      "extern \"apply_str\" applyStr : (String → String) → String → String\n" ++
      "extern \"on_tick\" onTick : Callback (Nat → IO Unit) → IO Unit\n" ++
      "extern \"tick\" tick : Nat → IO Unit\nextern \"forget\" forget : IO Unit\n" ++
      "def byShift (k : Nat) (a b : Nat) : Bool := Nat.lt (Nat.mod (a + k) 10) (Nat.mod (b + k) 10)\n" ++
      "def say (p : String) (n : Nat) : IO Unit := IO.println (String.append p (Nat.toString n))\n" ++
      "def main : IO Unit := do\n  IO.println (sortSome (fun a b => Nat.lt a b));\n" ++
      "  IO.println (sortSome (fun a b => Nat.lt b a));\n  IO.println (sortSome (byShift 3));\n" ++
      "  IO.println (applyStr (fun s => String.append s \"!\") \"hey\");\n" ++
      "  onTick (say (String.append \"tick \" \"#\"));\n  IO.println \"registered\";\n" ++
      "  tick 2;\n  onTick (fun n => say \"tock \" (n + 10));\n  tick 1" ++ (if release then ";\n  forget\n" else "\n")),
   ("c/cb.c", sortHelper ++ tickHelper.replace "#include <stdint.h>\n" "" ++
      "const char *apply_str(char *(*f)(void *, const char *), void *ctx, const char *s) {\n" ++
      "  static char buf[64]; char *r = f(ctx, s); strncpy(buf, r, 63); free(r); return buf;\n}\n")]

def callbackExpected : String :=
  "1 3 4 5 7 9\n9 7 5 4 3 1\n7 9 1 3 4 5\nhey!\nregistered\ntick #0\ntick #1\ntock 10\n"

/-- (stage 21q) The checks of callbacks, both frontends alike. -/
def callbackHeader : String := "foreign_type FILE\n"

def callbackDecls : List (String × Bool) := [
  ("extern \"f1\" f1 : (Nat → Nat → Bool) → String\nextern \"f2\" f2 : (String → IO Unit) → IO Nat\n" ++
     "extern \"f3\" f3 : Callback (Nat → IO Bool) → IO Unit\nextern \"f4\" f4 : (FILE → Float64) → Nat → Nat\n", true),
  ("extern \"g1\" g1 : (Nat → IO Unit) → Nat\n", false),
  ("extern \"g2\" g2 : ((Nat → Nat) → Nat) → Nat\n", false),
  ("extern \"g3\" g3 : (Unit → Nat) → Nat\n", false),
  ("extern \"g4\" g4 : (Nat → FILE) → Nat\n", false),
  ("extern \"g5\" g5 : Callback ((Nat → Nat) → Nat) → IO Unit\n", false)]

/-- (stage 21r) Structs by value: `div_t` from a header, a struct defined from its fields
(numbers, a `Float64`, a `Bool`, a string) passed and returned, and one nesting it. -/
def structFiles : List (String × String) :=
  [("main.wiz", "import IO\nlink_c \"c/st.c\"\n" ++
      "c_struct \"div_t\" (header := \"stdlib.h\") DivT where\n  quot : Nat\n  rem : Nat\n" ++
      "extern \"div\" (header := \"stdlib.h\") cdiv : Nat → Nat → DivT\n" ++
      "c_struct \"struct pair\" Pair where\n  a : Nat\n  b : Float64\n  ok : Bool\n  name : String\n" ++
      "c_struct Outer where\n  p : Pair\n  n : Nat\n" ++
      "extern \"bump\" bump : Pair → Pair\nextern \"outer_sum\" outerSum : Outer → Nat\n" ++
      "extern \"make_outer\" makeOuter : Nat → IO Outer\n" ++
      "def showB : Bool → String\n  | .true => \"true\"\n  | .false => \"false\"\n" ++
      "def main : IO Unit := do\n  let d := cdiv 17 5;\n  IO.println (Nat.toString d.quot);\n  IO.println (Nat.toString d.rem);\n" ++
      "  let p := bump (Pair.mk 41 (Float64.ofNat 3) .false \"wiz\");\n  IO.println (Nat.toString p.a);\n" ++
      "  IO.println (Float64.toString p.b);\n  IO.println (showB p.ok);\n  IO.println p.name;\n" ++
      "  IO.println (Nat.toString (outerSum (Outer.mk p 8)));\n  o ← makeOuter 5;\n  let q := o.p;\n" ++
      "  IO.println q.name;\n  IO.println (Nat.toString (q.a + o.n))\n"),
   ("c/st.c", "#include <stdint.h>\n#include <string.h>\n" ++
      "struct pair { uint64_t a; double b; int ok; const char *name; };\n" ++
      "typedef struct { struct pair p; uint64_t n; } wiz_s_Outer;\n" ++
      "struct pair bump(struct pair p) { static char buf[32]; p.a += 1; p.b *= 2; p.ok = !p.ok;\n" ++
      "  strcpy(buf, p.name); strcat(buf, \"!\"); p.name = buf; return p; }\n" ++
      "uint64_t outer_sum(wiz_s_Outer o) { return o.p.a + o.n + strlen(o.p.name); }\n" ++
      "wiz_s_Outer make_outer(uint64_t n) { wiz_s_Outer o; o.p.a = n; o.p.b = 0.5; o.p.ok = 1; o.p.name = \"made in C\"; o.n = 2 * n; return o; }\n")]

def structExpected : String := "3\n2\n42\n6\ntrue\nwiz!\n54\nmade in C\n15\n"

/-- (C8) Structs nested two deep, each passed and returned by value, with a string and a
number read out of the outermost — the field order and the marshalling helpers compose. -/
def structDeepHeader : String :=
  "struct pt { unsigned long x; double y; };\n" ++
  "typedef struct { struct pt a; struct pt b; } wiz_seg;\n" ++
  "typedef struct { wiz_seg s; unsigned long n; } wiz_deep;\n" ++
  "static inline struct pt pt_bump(struct pt p) { p.x += 1; p.y *= 2; return p; }\n" ++
  "static inline unsigned long deep_sum(wiz_deep d) { return d.s.a.x + d.s.b.x + d.n; }\n" ++
  "static inline wiz_deep deep_make(unsigned long n) { wiz_deep d; d.s.a.x = n; d.s.a.y = 0.5;\n" ++
  "  d.s.b.x = n + 1; d.s.b.y = 1.5; d.n = 2 * n; return d; }\n"

def structDeepProgram (header : String) : String :=
  "import IO\n" ++
  s!"c_struct \"struct pt\" (header := \"{header}\") Pt where\n  x : Nat\n  y : Float64\n" ++
  s!"c_struct \"wiz_seg\" (header := \"{header}\") Seg where\n  a : Pt\n  b : Pt\n" ++
  s!"c_struct \"wiz_deep\" (header := \"{header}\") Deep where\n  s : Seg\n  n : Nat\n" ++
  s!"extern \"pt_bump\" (header := \"{header}\") ptBump : Pt → Pt\n" ++
  s!"extern \"deep_sum\" (header := \"{header}\") deepSum : Deep → Nat\n" ++
  s!"extern \"deep_make\" (header := \"{header}\") deepMake : Nat → IO Deep\n" ++
  "def main : IO Unit := do\n  let p := ptBump (Pt.mk 4 (Float64.ofNat 3));\n" ++
  "  IO.println (Nat.toString p.x);\n  IO.println (Float64.toString p.y);\n" ++
  "  let d := Deep.mk (Seg.mk p (Pt.mk 10 (Float64.ofNat 0))) 7;\n" ++
  "  IO.println (Nat.toString (deepSum d));\n  r ← deepMake 5;\n" ++
  "  IO.println (Nat.toString (r.s.a.x + r.s.b.x + r.n));\n  IO.println (Float64.toString r.s.b.y)\n"

def structDeepExpected : String := "5\n6\n22\n21\n1.5\n"

/-- (C8) A byte array (`unsigned char data[4]`) as a `c_struct` field, passed and
returned by value through an extern (not through `glue`): cut/zero-padded going in,
copied out. -/
def structArrayHeader : String :=
  "typedef struct { unsigned char data[4]; unsigned long n; } wiz_ab;\n" ++
  "static inline unsigned long ab_sum(wiz_ab m) {\n" ++
  "  return (unsigned long)m.data[0] + m.data[1] + m.data[2] + m.data[3] + m.n; }\n" ++
  "static inline wiz_ab ab_make(unsigned long n) {\n" ++
  "  wiz_ab m; m.data[0] = 1; m.data[1] = 2; m.data[2] = 3; m.data[3] = 4; m.n = n; return m; }\n"

def structArrayProgram (header : String) : String :=
  "import IO\n" ++
  s!"c_struct \"wiz_ab\" (header := \"{header}\") AB where\n  data : Bytes\n  n : Nat\n" ++
  s!"extern \"ab_sum\" (header := \"{header}\") abSum : AB → Nat\n" ++
  s!"extern \"ab_make\" (header := \"{header}\") abMake : Nat → IO AB\n" ++
  "def main : IO Unit := do\n" ++
  "  IO.println (Nat.toString (abSum (AB.mk (Bytes.ofString \"AB\") 5)));\n" ++
  "  m ← abMake 10;\n  IO.println (Bytes.show m.data);\n  IO.println (Nat.toString m.n)\n"

def structArrayExpected : String := "136\n[1, 2, 3, 4]\n10\n"

/-- (C8) A field at quantity 0 on master: the field kind is not `e` (erased) yet, so the
type is checked like any other field's (a `List` field at 0 is rejected) and the C
marshalling still writes the field into the header's struct. `agent/sh-cstruct` erases it
from the C struct (keeping the slot in the Wiz structure); these assertions are the
current behaviour and the prompt to promote this case when that lands. -/
def structErasedProbe : String :=
  "import Prelude\n" ++
  "c_struct \"wiz_q\" (header := \"wiz_q.h\") Q where\n  0 tag : Nat\n  x : Nat\n" ++
  "extern \"q_get\" (header := \"wiz_q.h\") qGet : Q → Nat\n" ++
  "def main : IO Unit := IO.println (Nat.toString (qGet (Q.mk 0 7)))\n"

/-- (stage 21r) The checks of `c_struct`, both frontends alike. -/
def structDecls : List (String × Bool) := [
  ("c_struct S3 where\n  x : Nat\n  y : Bool\ndef s3 : S3 := S3.mk 1 .true\ndef s3x : Nat := s3.x\n" ++
     "c_struct \"struct s4\" S4 where\n  s : S3\n  f : Float64\nextern \"f6\" f6 : S4 → IO S3\n", true),
  ("c_struct S0 where\n", false),
  ("c_struct S1 where\n  xs : List Nat\n", false),
  ("c_struct \"a:b\" S2 where\n  x : Nat\n", false),
  ("c_struct Nat where\n  x : Nat\n", false),
  ("extern \"f7\" f7 : Nat → Type\n", false)]

/-- (stage 21t) `implemented_by`: compiled code runs the implementation (here a different
answer, to see it), for a definition and for an axiom. -/
def implProgram : String :=
  "import IO\ndef model (n : Nat) : Nat := n\ndef fast (n : Nat) : Nat := n + 1\nattribute [implemented_by fast] model\n" ++
  "axiom secret : Nat → Nat\ndef secretImpl (n : Nat) : Nat := n * 2\nattribute [implemented_by secretImpl] secret\n" ++
  "def main : IO Unit := do\n  IO.println (Nat.toString (model 3));\n  IO.println (Nat.toString (secret 21))\n"

def implHeader : String := "def f1 (n : Nat) : Nat := n\ndef g1 (n : Nat) : Nat := n + 0\ndef g2 (b : Bool) : Bool := b\n" ++
  "extern \"strlen\" (header := \"string.h\") strlen : String → Nat\ndef myLen (s : String) : Nat := 0\n"

def implDecls : List (String × Bool) := [
  ("attribute [implemented_by g1] f1\n", true),
  ("attribute [implemented_by g1] nope\n", false), ("attribute [implemented_by nope] f1\n", false),
  ("attribute [implemented_by f1] f1\n", false), ("attribute [implemented_by g2] f1\n", false),
  ("attribute [implemented_by myLen] strlen\n", false)]

/-- (B12) The output of the native-representation program: a value built with `mk` (the
extern implementation), read back with `get`, combined and matched. -/
def reprExpected : String := "40\n42\n43\n125\n86\n"

/-- (B12) The declarations the `implemented_by mk get` verdicts are checked against: a
sealed type with one runtime field, a wrapper (`WR`) whose `mk`/`get` are ordinary
definitions, a two-live-field type, an unsealed one, and an unrelated definition. -/
def reprHeader : String :=
  "sealed inductive WR where\n  | private mk (n : Nat)\n" ++
  "def WR.mkImpl (n : Nat) : WR := .mk n\n" ++
  "def WR.getImpl (w : WR) : Nat := match w with\n  | .mk n => n\n" ++
  "sealed inductive W2 where\n  | private mk (a : Nat) (b : Nat)\n" ++
  "def W2.mkImpl (a b : Nat) : W2 := .mk a b\n" ++
  "def W2.getImpl (w : W2) : Nat := 0\n" ++
  "inductive Unsealed where\n  | mk (n : Nat)\n" ++
  "def f (n : Nat) : Nat := n\n"

def reprDecls : List (String × Bool) := [
  ("attribute [implemented_by WR.mkImpl WR.getImpl] WR.mk\n", true),
  ("attribute [implemented_by nope WR.getImpl] WR.mk\n", false),
  ("attribute [implemented_by WR.mkImpl nope] WR.mk\n", false),
  ("attribute [implemented_by f WR.getImpl] WR.mk\n", false),
  ("attribute [implemented_by WR.mkImpl f] WR.mk\n", false),
  ("attribute [implemented_by WR.mkImpl WR.getImpl] f\n", false),
  ("attribute [implemented_by W2.mkImpl W2.getImpl] W2.mk\n", false),
  ("attribute [implemented_by WR.mkImpl WR.getImpl] Unsealed.mk\n", false),
  ("attribute [implemented_by WR.mkImpl WR.getImpl] WR.mk\nattribute [implemented_by WR.mkImpl WR.getImpl] WR.mk\n", false)]

/-- (stage 21s) A Wiz library: the self-hosted compiler's C without a `main` (`--lib`, or
`--no-main`) and its header (`--header`), linked with a C program that calls the exports
and the handle functions. -/
def selfhostLibRun (src csrc expected : String) (flags : Array String := #[]) : IO Unit := do
  let tc ← toolchain
  if tc.gcCflags.isEmpty then skip "no garbage collector, --gc-cflags"; return
  match ← selfhostCompiler with
  | .error e =>
    if (e.splitOn "gmp.h").length > 1 then skip "no toolchain" else throw (IO.userError e)
  | .ok exe =>
    let dir ← IO.FS.createTempDir
    IO.FS.writeFile (dir / "input.wiz") src
    let out ← IO.Process.output { cmd := "timeout", args := #["300", exe.toString] ++ flags, cwd := dir }
    unless out.exitCode == 0 do throw (IO.userError s!"the compiler failed ({out.exitCode}): {out.stderr}")
    IO.FS.writeFile (dir / "lib.c") out.stdout
    let hdr ← IO.Process.output { cmd := "timeout", args := #["300", exe.toString, "--header"], cwd := dir }
    unless hdr.exitCode == 0 do throw (IO.userError s!"the compiler failed ({hdr.exitCode}): {hdr.stderr}")
    IO.FS.writeFile (dir / "lib.h") hdr.stdout
    IO.FS.writeFile (dir / "main.c") csrc
    let rt := (← IO.currentDir) / "selfhost"
    let args := #["-O2", "-w", s!"-I{rt}", "-I", dir.toString] ++ tc.gcCflags.toArray ++ #["main.c", "lib.c", "-o", "prog"] ++ tc.gcLdflags.toArray
    let cc ← IO.Process.output { cmd := tc.cc, args, cwd := dir }
    unless cc.exitCode == 0 do throw (IO.userError s!"cc failed: {cc.stderr.take 2000}")
    let run ← IO.Process.output { cmd := "timeout", args := #["60", (dir / "prog").toString], cwd := dir }
    unless run.exitCode == 0 do throw (IO.userError s!"the program failed ({run.exitCode}): {run.stderr}")
    checkEq expected run.stdout

/-- (stage 21s) The library of the `callbacks` group's `--lib` case. -/
def libSrc : String :=
  "import IO\ndef fact : Nat → Nat\n  | .zero => 1\n  | .succ n => (n + 1) * fact n\n" ++
  "export \"wiz_fact\" fact\n" ++
  "def greet (who : String) : String := String.append \"hello, \" who\nexport \"wiz_greet\" greet : String → String\n" ++
  "def shout (s : String) : IO Unit := IO.println (String.append s \"!\")\nexport \"wiz_shout\" shout\n" ++
  "structure Counter where\n  total : Nat\n  steps : Nat\n" ++
  "def Counter.zero : Counter := Counter.mk 0 0\ndef Counter.add (c : Counter) (n : Nat) : Counter := Counter.mk (c.total + n) (c.steps + 1)\n" ++
  "def Counter.get (c : Counter) : Nat := c.total * 100 + c.steps\n" ++
  "export \"wiz_counter_new\" Counter.zero\nexport \"wiz_counter_add\" Counter.add\nexport \"wiz_counter_get\" Counter.get\n"

def libMain : String :=
  "#include <stdio.h>\n#include <stdlib.h>\n#include \"lib.h\"\nint main(void) {\n" ++
  "  printf(\"%llu\\n\", (unsigned long long)wiz_fact(20));\n" ++
  "  char *s = wiz_greet(\"C\"); printf(\"%s\\n\", s); free(s);\n  wiz_shout(\"from Wiz\"); fflush(stdout);\n" ++
  "  wiz_val c = wiz_counter_new();\n  for (int i = 1; i <= 4; i++) c = wiz_counter_add(c, i);\n" ++
  "  wiz_retain((void *)c); printf(\"%llu\\n\", (unsigned long long)wiz_counter_get(c));\n" ++
  "  wiz_release((void *)c);\n  printf(\"live %ld\\n\", wiz_live_objects());\n  return 0;\n}\n"

def libExpected : String := "2432902008176640000\nhello, C\nfrom Wiz!\n1004\nlive 0\n"

/-- (stage 21n) `private` everywhere the Lean frontend takes it: with one module, the
names are used as usual (privacy is per module). -/
def privateDecls : List (String × Bool) := [
  ("private def secret : Nat := 42\ndef useIt : Nat := secret\nprivate axiom ax : Nat\ndef useAx : Nat := ax\n", true),
  ("inductive Tok where\n  | num (n : Nat)\n  | private hidden (n : Nat)\ndef t : Tok := Tok.hidden 3\n" ++
     "def val : Tok → Nat\n  | .num n => n\n  | .hidden n => n\n", true),
  ("structure Acct where\n  owner : Nat\n  private bal : Nat\ndef b (a : Acct) : Nat := a.bal\n" ++
     "structure Shr (A : Type) where\n  private mk ::\n  val : A\ndef s : Shr Nat := Shr.mk 3\n", true),
  ("private inductive P where\n  | a\ndef pa : P := P.a\nprivate structure S where\n  x : Nat\ndef sx (s : S) : Nat := s.x\n", true),
  ("private mutual\ndef ev : Nat → Bool\n  | .zero => .true\n  | .succ n => od n\ndef od : Nat → Bool\n" ++
     "  | .zero => .false\n  | .succ n => ev n\nend\ndef e2 : Bool := ev 2\n", true),
  ("mutual\nprivate def ev : Nat → Bool\n  | .zero => .true\n  | .succ n => od n\nprivate def od : Nat → Bool\n" ++
     "  | .zero => .false\n  | .succ n => ev n\nend\n", false),
  ("private def dup : Nat := 1\ndef dup : Nat := 2\n", false)]

/-- (B7, A18) `let () := u; b` (the unit eliminator) and `split` (`let q (x, y)`, and a
tuple `let (x, y, z)` as nested pairs): the Lean frontend's verdicts, which the
self-hosted one must match. A pair at quantity 1 can only be taken apart by `split`:
projections need an unrestricted pair, and the components are bound at `q·p` and `q`, so
at `let 1` a component of an unrestricted Σ can be reused but the second cannot be
dropped or used twice. -/
def splitDecls : List (String × Bool) := [
  ("def f (1 u : Unit) : Nat := let () := u; 42\n", true),
  ("def f (u : Unit) : Nat := let () := u; 42\n", true),
  ("def f (0 u : Unit) : Nat := let () := u; 42\n", false),
  ("def f (1 u : Unit) : Unit × Unit := let () := u; (u, ())\n", false),
  ("def f (1 p : Unit × Unit) : Nat := let 1 (x, y) := p; let () := x; let () := y; 42\n", true),
  ("def f (1 p : Unit × Unit) : Nat := let 1 (x, y) := p; let () := x; 42\n", false),
  ("def f (1 p : Unit × Unit) : Nat := let 1 (x, y) := p; let () := x; let () := y; let () := y; 42\n", false),
  ("def f (p : Nat × Nat) : Nat := let (x, y) := p; x + x + y\n", true),
  ("def f (p : Nat × Nat × Nat) : Nat := let (x, y, z) := p; x + y + z\n", true),
  ("def f (1 p : Nat × Nat) : Nat := p.1\n", false),
  ("def f : Nat := let (x, y) := 5; x\n", false)]

/-- (B7) The same forms as `splitDecls`, as a program the Lean and the self-hosted
compilers both compile and run. -/
def splitProgram : String :=
  "import IO\n" ++
  "def usePair (1 p : Unit × Unit) : Nat := let 1 (x, y) := p; let () := x; let () := y; 40\n" ++
  "def unitElim (1 u : Unit) : Nat := let () := u; 1\n" ++
  "def triple (p : Nat × Nat × Nat) : Nat := let (x, y, z) := p; x + y + z\n" ++
  "def main : IO Unit := do\n" ++
  "  IO.println (Nat.toString (usePair ((), ())));\n" ++
  "  IO.println (Nat.toString (unitElim ()));\n" ++
  "  IO.println (Nat.toString (triple (1, 2, 39)))\n"

/-- (stage 21i) Phantom parameters, for both frontends. -/
def phantomHeader : String :=
  "inductive UIntN (w : Nat) where\n  | mk (toNat : Nat)\ninductive Proxy (A : Type) where\n  | mk\n" ++
  "structure S (w : Nat) where\n  x : Nat\ninductive N (w : Nat) where\n  | z\n  | s (n : N w)\n" ++
  "def width (w : Nat) (a : UIntN w) : Nat := w\ndef u8 : UIntN 8 := .mk 3\n"

/-- Finding Y4 (audit 2): the probe (`def T` twice, with `Box T` in between), and the
other ways a command could declare a name again. -/
def dupNames : String :=
  "inductive Nat where\n  | zero\n  | succ (n : Nat)\ninductive Empty where\ninductive Box (A : Type) where\n  | mk (a : A)\n" ++
  "def unbox {A : Type} (x : Box A) : A := match x with\n  | .mk a => a\n" ++
  "def T : Type := Nat\ndef a : Box T := Box.mk Nat.zero\ndef T : Type := Empty\ndef c : Box Empty := a\n" ++
  "inductive Nat where\n  | zero\ninductive Two where\n  | a\n  | a\ndef Box.mk : Nat := Nat.zero\n" ++
  "inductive Fresh where\n  | mk\ndef Fresh.mk : Nat := Nat.zero\naxiom T : Type\naxiom Ax : Type\ndef Ax : Type := Nat\n" ++
  "partial def loop (n : Nat) : Nat := loop n\npartial def loop (n : Nat) : Nat := loop n\ndef loop : Nat := Nat.zero\n" ++
  "structure P where\n  mk : Nat\nstructure Q where\n  fst : Nat\ndef Q.fst : Nat := Nat.zero\n" ++
  "mutual\ndef ev : Nat → Nat\n  | .zero => .zero\n  | .succ n => ev n\ndef ev : Nat → Nat\n  | .zero => .zero\n  | .succ n => ev n\nend\n" ++
  "def fine : Nat := loop Nat.zero\n"

def dupNamesExpected : String :=
  "Nat : U0\nEmpty : U0\nBox : (x0 : U0) → U0\nunbox : (x0 :0 U0) → (x1 : (Box x0)) → x0\nT : U0\na : (Box T)\n" ++
  "error: 'T' has already been declared\nerror: type mismatch: expected (Box Empty), got (Box T)\n" ++
  "error: 'Nat' has already been declared\nerror: 'Two.a' has already been declared\nerror: 'Box.mk' has already been declared\n" ++
  "Fresh : U0\nerror: 'Fresh.mk' has already been declared\nerror: 'T' has already been declared\nAx : U0\n" ++
  "error: 'Ax' has already been declared\nloop : (x0 : Nat) → Nat\nerror: 'loop' has already been declared\n" ++
  "error: 'loop' has already been declared\nerror: 'P.mk' has already been declared\nQ : U0\nQ.fst : (x0 : Q) → Nat\n" ++
  "error: 'Q.fst' has already been declared\nerror: 'ev' has already been declared\nfine : Nat\n"

/-- The self-hosted checker accepts `file`: no `error` or `parse error` line, and it
printed declarations (not the input). -/
def selfhostChecks (file : String) : IO Unit := do
  let some out ← selfhostOutput file | return
  let bad := (out.splitOn "\n").filter fun l => l.startsWith "error" || l.startsWith "parse error"
  unless bad.isEmpty do
    throw (IO.userError s!"the self-hosted checker rejected the file:\n{"\n".intercalate bad}")
  checkChecked file out

def cofProbes : String :=
  "def showBool : Bool → String" ++ "\n" ++
    "  | .true => \"true\"" ++ "\n" ++
    "  | .false => \"false\"" ++ "\n" ++
    "def showNat (n : Nat) : String := Nat.toString n" ++ "\n" ++
    "def line (label : String) (b : Bool) : IO Unit :=" ++ "\n" ++
    "  IO.println (String.append label (showBool b))" ++ "\n" ++
    "def boolEq (a b : Bool) : Bool := match a, b with" ++ "\n" ++
    "  | .true, .true => .true" ++ "\n" ++
    "  | .false, .false => .true" ++ "\n" ++
    "  | _, _ => .false" ++ "\n" ++
    "def lineNat (label : String) (n : Nat) : IO Unit :=" ++ "\n" ++
    "  IO.println (String.append label (showNat n))" ++ "\n" ++
    "def llen : List CofCtx → Nat" ++ "\n" ++
    "  | .nil => 0" ++ "\n" ++
    "  | .cons _ rest => 1 + llen rest" ++ "\n" ++
    "def isSomeExt : Option Ext → Bool" ++ "\n" ++
    "  | .some _ => .true" ++ "\n" ++
    "  | .none => .false" ++ "\n" ++
    "def v0 : Dim := .dv 0" ++ "\n" ++
    "def v1 : Dim := .dv 1" ++ "\n" ++
    "def v2 : Dim := .dv 2" ++ "\n" ++
    "def φ : Cof := eqD v0 .d0" ++ "\n" ++
    "def ψ : Cof := eqD v1 .d1" ++ "\n" ++
    "def χ : Cof := eqD v2 .d0" ++ "\n" ++
    "def main : IO Unit := do" ++ "\n" ++
    "  line \"T01 and-top: \" (cofEq (andCof φ topCof) φ);" ++ "\n" ++
    "  line \"T02 and-bot: \" (cofEq (andCof φ botCof) botCof);" ++ "\n" ++
    "  line \"T03 or-bot: \" (cofEq (orCof φ botCof) φ);" ++ "\n" ++
    "  line \"T04 or-top: \" (cofEq (orCof φ topCof) topCof);" ++ "\n" ++
    "  line \"T05 and-idem: \" (cofEq (andCof φ φ) φ);" ++ "\n" ++
    "  line \"T06 or-idem: \" (cofEq (orCof φ φ) φ);" ++ "\n" ++
    "  line \"T07 and-comm: \" (cofEq (andCof φ ψ) (andCof ψ φ));" ++ "\n" ++
    "  line \"T08 or-comm: \" (cofEq (orCof φ ψ) (orCof ψ φ));" ++ "\n" ++
    "  line \"T09 and-assoc: \" (cofEq (andCof (andCof φ ψ) χ) (andCof φ (andCof ψ χ)));" ++ "\n" ++
    "  line \"T10 or-assoc: \" (cofEq (orCof (orCof φ ψ) χ) (orCof φ (orCof ψ χ)));" ++ "\n" ++
    "  line \"T11 absorption: \" (cofEq (orCof φ (andCof φ ψ)) φ);" ++ "\n" ++
    "  line \"T12 distributivity: \" (cofEq (andCof φ (orCof ψ χ)) (orCof (andCof φ ψ) (andCof φ χ)));" ++ "\n" ++
    "  line \"T13 subsumption: \" (cofEq (orCof (andCof φ ψ) φ) φ);" ++ "\n" ++
    "  line \"T14 contradiction: \" (cofEq (andCof (eqD v0 .d0) (eqD v0 .d1)) botCof);" ++ "\n" ++
    "  line \"T15 disjoint: \" (cofEq (andCof (eqD v0 .d0) (eqD v1 .d1)) botCof);" ++ "\n" ++
    "  line \"T16 orientation: \" (cofEq (eqD v0 v1) (eqD v1 v0));" ++ "\n" ++
    "  line \"T17 chain: \" (cofEq (andCof (eqD v0 v1) (eqD v1 .d0)) (andCof (eqD v0 .d0) (eqD v1 .d0)));" ++ "\n" ++
    "  line \"T18 transitivity: \" (cofEq (andCof (eqD v0 v1) (eqD v1 v2)) (andCof (eqD v1 v0) (eqD v2 v1)));" ++ "\n" ++
    "  line \"T19 entails-face: \" (entails (assume (eqD v0 .d0) emptyCtx) (orCof (eqD v0 .d0) (eqD v0 .d1)));" ++ "\n" ++
    "  line \"T20 not-entails: \" (entails (assume (eqD v0 .d0) emptyCtx) (eqD v0 .d1));" ++ "\n" ++
    "  line \"T21 entails-top: \" (entails emptyCtx topCof);" ++ "\n" ++
    "  line \"T22 entails-bot: \" (entails emptyCtx botCof);" ++ "\n" ++
    "  line \"T23 no-entail: \" (entails emptyCtx (eqD v0 .d0));" ++ "\n" ++
    "  line \"T24 consistent: \" (consistent emptyCtx (andCof (eqD v0 .d0) (eqD v1 .d1)));" ++ "\n" ++
    "  line \"T25 inconsistent: \" (consistent emptyCtx (andCof (eqD v0 .d0) (eqD v0 .d1)));" ++ "\n" ++
    "  line \"T26 refutes: \" (refutes emptyCtx (andCof (eqD v0 .d0) (eqD v0 .d1)));" ++ "\n" ++
    "  line \"T27 false-ctx-entails: \" (entails (assume (andCof (eqD v0 .d0) (eqD v0 .d1)) emptyCtx) (eqD v2 .d0));" ++ "\n" ++
    "  line \"T28 false-ctx-inconsistent: \" (consistent (assume (andCof (eqD v0 .d0) (eqD v0 .d1)) emptyCtx) topCof);" ++ "\n" ++
    "  line \"T29 dim-eq-ctx: \" (dimEqCtx (assume (eqD v0 v1) emptyCtx) v0 v1);" ++ "\n" ++
    "  line \"T30 dim-ne-ctx: \" (dimEqCtx (assume (eqD v0 .d0) emptyCtx) v0 v1);" ++ "\n" ++
    "  lineNat \"T31 split-count: \" (llen (branches (assume (orCof (eqD v0 .d0) (eqD v0 .d1)) emptyCtx)));" ++ "\n" ++
    "  line \"T32 split-entails: \" (entails (assume (orCof (eqD v0 .d0) (eqD v0 .d1)) emptyCtx) (orCof (eqD v0 .d0) (eqD v0 .d1)));" ++ "\n" ++
    "  line \"T33 split-no-entail: \" (entails (assume (orCof (eqD v0 .d0) (eqD v0 .d1)) emptyCtx) (eqD v0 .d0));" ++ "\n" ++
    "  lineNat \"T34 dead-branch: \" (llen (branches (assume (orCof (andCof (eqD v0 .d0) (eqD v0 .d1)) (eqD v1 .d0)) emptyCtx)));" ++ "\n" ++
    "  line \"T35 subst: \" (cofEq (substCof 0 .d0 (eqD v0 v1)) (eqD v1 .d0));" ++ "\n" ++
    "  line \"T36 subst-bot: \" (cofEq (substCof 0 .d1 (andCof (eqD v0 .d0) (eqD v1 .d1))) botCof);" ++ "\n" ++
    "  line \"T37 subst-boundary: \" (cofEq (substCof 0 .d0 (orCof (eqD v0 .d0) (eqD v0 .d1))) topCof);" ++ "\n" ++
    "  line \"T38 subst-var: \" (cofEq (substCof 0 v2 (eqD v0 .d0)) (eqD v2 .d0));" ++ "\n" ++
    "  line \"T39 subst-other: \" (cofEq (substCof 1 .d0 (eqD v0 v1)) (eqD v0 .d0));" ++ "\n" ++
    "  line \"T40 subst-agrees: \" (boolEq (entails (assume (eqD v0 .d0) emptyCtx) (orCof (eqD v0 .d0) (eqD v0 .d1))) (entails emptyCtx (substCof 0 .d0 (orCof (eqD v0 .d0) (eqD v0 .d1)))));" ++ "\n" ++
    "  line \"T40b subst-agrees: \" (boolEq (entails (assume (eqD v0 .d0) emptyCtx) (eqD v0 .d1)) (entails emptyCtx (substCof 0 .d0 (eqD v0 .d1))));" ++ "\n" ++
    "  line \"T41 within-1: \" (cofWithin 1 pathBoundary);" ++ "\n" ++
    "  line \"T42 within-0: \" (cofWithin 0 pathBoundary);" ++ "\n" ++
    "  line \"T43 within-2: \" (cofWithin 2 (eqD v1 .d0));" ++ "\n" ++
    "  line \"T44 within-2-neq: \" (cofWithin 1 (eqD v1 .d0));" ++ "\n" ++
    "  line \"T45 path-ext: \" (isSomeExt (pathExt \"a\" \"b\"));" ++ "\n" ++
    "  line \"T46 bad-ext: \" (Bool.not (isSomeExt (mkExt 0 pathBoundary (.cons (.face 0 .d0 \"a\") .nil))));" ++ "\n" ++
    "  line \"T47 path-at-0: \" (underDim emptyCtx 0 .d0 pathBoundary);" ++ "\n" ++
    "  line \"T48 path-at-1: \" (underDim emptyCtx 0 .d1 pathBoundary);" ++ "\n" ++
    "  line \"T49 path-at-neutral: \" (underDim emptyCtx 0 v2 pathBoundary);" ++ "\n" ++
    "  line \"T50 face-active: \" (entails (assume (faceCof (.face 0 .d0 \"a\")) emptyCtx) pathBoundary);" ++ "\n" ++
    "  line \"T51 other-face: \" (entails (assume (faceCof (.face 0 .d0 \"a\")) emptyCtx) (faceCof (.face 0 .d1 \"b\")));" ++ "\n" ++
    "  line \"T52 faces-overlap: \" (consistent emptyCtx (andCof (faceCof (.face 0 .d0 \"a\")) (faceCof (.face 0 .d1 \"b\"))));" ++ "\n" ++
    "  line \"T53 subst-path-0: \" (cofEq (substCof 0 .d0 pathBoundary) topCof);" ++ "\n" ++
    "  line \"T54 subst-path-1: \" (cofEq (substCof 0 .d1 pathBoundary) topCof);" ++ "\n" ++
    "  line \"T55 subst-path-free: \" (cofEq (substCof 1 .d0 pathBoundary) pathBoundary);" ++ "\n" ++
    "  line \"T56 ext2-face: \" (entails (assume (andCof (eqD v0 .d0) (eqD v1 .d0)) emptyCtx) (extBoundary 2));" ++ "\n" ++
    "  line \"T57 ext2-at-0: \" (cofEq (substCof 0 .d0 (extBoundary 2)) topCof);" ++ "\n" ++
    "  line \"T58 ext0-bot: \" (cofEq (extBoundary 0) botCof);" ++ "\n" ++
    "  line \"T59 ext1-path: \" (cofEq (extBoundary 1) pathBoundary);" ++ "\n" ++
    "  line \"T60 subst-ctx: \" (dimEqCtx (substCtx 0 .d0 (assume (eqD v0 v1) emptyCtx)) v1 .d0);" ++ "\n" ++
    "  line \"T61 boundary-cover: \" (entails (assume (eqD v0 .d0) emptyCtx) (extBoundary 2));" ++ "\n" ++
    "  line \"T62 path-cover: \" (match pathExt \"a\" \"b\" with" ++ "\n" ++
    "    | .some e => extFacesCover e" ++ "\n" ++
    "    | .none => .false);" ++ "\n" ++
    "  line \"T63 bad-cover: \" (match mkExt 1 (eqD v0 .d0) (.cons (.face 0 .d1 \"b\") .nil) with" ++ "\n" ++
    "    | .some e => extFacesCover e" ++ "\n" ++
    "    | .none => .false);" ++ "\n" ++
    "  line \"T64 cof-equiv: \" (cofEquiv emptyCtx (eqD v0 .d0) (eqD v0 .d0));" ++ "\n" ++
    "  line \"T65 cof-neq: \" (cofEquiv emptyCtx (orCof (eqD v0 .d0) (eqD v0 .d1)) topCof);" ++ "\n" ++
    "  line \"T66 cof-eq-ctx: \" (cofEquiv (assume (eqD v0 .d0) emptyCtx) (orCof (eqD v0 .d0) (eqD v0 .d1)) topCof);" ++ "\n" ++
    "  line \"T67 cof-bot: \" (cofEquiv emptyCtx botCof (eqD v0 .d0))"

def cofProbesExpected : String :=
  "T01 and-top: true\nT02 and-bot: true\nT03 or-bot: true\nT04 or-top: true\nT05 and-idem: true\nT06 or-idem: true\nT07 and-comm: true\nT08 or-comm: true\nT09 and-assoc: true\nT10 or-assoc: true\nT11 absorption: true\nT12 distributivity: true\nT13 subsumption: true\nT14 contradiction: true\nT15 disjoint: false\nT16 orientation: true\nT17 chain: true\nT18 transitivity: true\nT19 entails-face: true\nT20 not-entails: false\nT21 entails-top: true\nT22 entails-bot: false\nT23 no-entail: false\nT24 consistent: true\nT25 inconsistent: false\nT26 refutes: true\nT27 false-ctx-entails: true\nT28 false-ctx-inconsistent: false\nT29 dim-eq-ctx: true\nT30 dim-ne-ctx: false\nT31 split-count: 2\nT32 split-entails: true\nT33 split-no-entail: false\nT34 dead-branch: 1\nT35 subst: true\nT36 subst-bot: true\nT37 subst-boundary: true\nT38 subst-var: true\nT39 subst-other: true\nT40 subst-agrees: true\nT40b subst-agrees: true\nT41 within-1: true\nT42 within-0: false\nT43 within-2: true\nT44 within-2-neq: false\nT45 path-ext: true\nT46 bad-ext: true\nT47 path-at-0: true\nT48 path-at-1: true\nT49 path-at-neutral: false\nT50 face-active: true\nT51 other-face: false\nT52 faces-overlap: false\nT53 subst-path-0: true\nT54 subst-path-1: true\nT55 subst-path-free: true\nT56 ext2-face: true\nT57 ext2-at-0: true\nT58 ext0-bot: true\nT59 ext1-path: true\nT60 subst-ctx: true\nT61 boundary-cover: true\nT62 path-cover: true\nT63 bad-cover: false\nT64 cof-equiv: true\nT65 cof-neq: false\nT66 cof-eq-ctx: true\nT67 cof-bot: false\n"
/-- (A10) Type classes. A `class C (ps) where f : A` is the structure `C.mk`, plus a
method `C.f {ps} [self : C ps] : A`; an `instance` is a global of a class type (the
dictionary); a method call inserts a class problem, solved by a local `[i : C A]` or a
registered instance before the command ends. -/
def classCore : String :=
  "import Prelude\nclass Default (A : Type) where\n  d : A\n#check Default.d\n" ++
  "instance instDefaultNat : Default Nat := Default.mk 7\n" ++
  "instance instDefaultBool : Default Bool := Default.mk .true\n" ++
  "def get {A : Type} [Default A] : A := Default.d\n#check get\ndef seven : Nat := get\ndef yes : Bool := get\n" ++
  "#reduce Nat.beq seven 7\n#reduce yes\n"

def classCoreExpected : String :=
  "Default : (x0 : U0) → U0\n" ++
  "Default.d : (x0 :0 U0) → (x1 : (Default x0)) → x0\n" ++
  "(x0 :0 U0) → (x1 : (Default x0)) → x0\n" ++
  "instDefaultNat : (Default Nat)\ninstDefaultBool : (Default Bool)\n" ++
  "get : (x0 :0 U0) → (x1 : (Default x0)) → x0\n" ++
  "(x0 :0 U0) → (x1 : (Default x0)) → x0\nseven : Nat\nyes : Bool\n" ++
  "con((#1, (tt, tt)))\ncon((#1, (tt, tt)))\n"

/-- (A10) A `where` instance, fields in any order; a two-method class and a generic
function using both methods. -/
def classWhere : String :=
  "import Prelude\nclass Two (A : Type) where\n  one : A\n  two : A\n" ++
  "instance instTwoNat : Two Nat where\n  two := 20\n  one := 10\n" ++
  "def sum2 {A : Type} [Two A] (add : A → A → A) : A := add Two.one Two.two\n" ++
  "#reduce Nat.beq (sum2 Nat.add : Nat) 30\n"

def classWhereExpected : String :=
  "Two : (x0 : U0) → U0\n" ++
  "Two.one : (x0 :0 U0) → (x1 : (Two x0)) → x0\n" ++
  "Two.two : (x0 :0 U0) → (x1 : (Two x0)) → x0\n" ++
  "instTwoNat : (Two Nat)\n" ++
  "sum2 : (x0 :0 U0) → (x1 : (Two x0)) → (x2 : (x2 : x0) → (x3 : x0) → x0) → x0\n" ++
  "con((#1, (tt, tt)))\n"

/-- (A10) An instance with a parameter and an instance parameter (nested resolution). -/
def classNested : String :=
  "import Prelude\nclass Default (A : Type) where\n  d : A\n" ++
  "instance instDefaultNat : Default Nat := Default.mk 7\n" ++
  "instance instDefaultList {A : Type} [Default A] : Default (List A) where\n" ++
  "  d := List.cons Default.d List.nil\n" ++
  "def get {A : Type} [Default A] : A := Default.d\n" ++
  "#reduce List.length (get : List Nat)\n#reduce List.length (get : List (List Nat))\n"

def classNestedExpected : String :=
  "Default : (x0 : U0) → U0\n" ++
  "Default.d : (x0 :0 U0) → (x1 : (Default x0)) → x0\n" ++
  "instDefaultNat : (Default Nat)\n" ++
  "instDefaultList : (x0 :0 U0) → (x1 : (Default x0)) → (Default (List x0))\n" ++
  "get : (x0 :0 U0) → (x1 : (Default x0)) → x0\n" ++
  "con((#1, (con((#0, (tt, tt))), (tt, tt))))\n" ++
  "con((#1, (con((#0, (tt, tt))), (tt, tt))))\n"

/-- (A10) A class with instance parameters in its telescope (the `Commute` shape): using
the class type inserts those problems, and an instance for it resolves them. -/
def classInstParam : String :=
  "import Prelude\nclass MyMonad (m : Type → Type) where\n  ret : Nat\n" ++
  "class MyHandler (e : Type) (m : Type → Type) where\n  h : Nat\n" ++
  "instance instMyMonadOption : MyMonad Option := MyMonad.mk 0\n" ++
  "instance instMyHandlerNatOption : MyHandler Nat Option := MyHandler.mk 1\n" ++
  "class MyCommute (e₁ e₂ : Type) (m : Type → Type) [i : MyMonad m] [h₁ : MyHandler e₁ m] [h₂ : MyHandler e₂ m] where\n  comm : Nat\n" ++
  "instance instMyCommute : MyCommute Nat Nat Option where\n  comm := 2\n" ++
  "#reduce Nat.beq (@MyCommute.comm Nat Nat Option instMyMonadOption instMyHandlerNatOption instMyHandlerNatOption instMyCommute) 2\n"

def classInstParamExpected : String :=
  "MyMonad : (x0 : (x0 : U0) → U0) → U0\n" ++
  "MyMonad.ret : (x0 :0 (x0 : U0) → U0) → (x1 : (MyMonad x0)) → Nat\n" ++
  "MyHandler : (x0 : U0) → (x1 : (x1 : U0) → U0) → U0\n" ++
  "MyHandler.h : (x0 :0 U0) → (x1 :0 (x1 : U0) → U0) → (x2 : ((MyHandler x0) x1)) → Nat\n" ++
  "instMyMonadOption : (MyMonad Option)\n" ++
  "instMyHandlerNatOption : ((MyHandler Nat) Option)\n" ++
  "MyCommute : (x0 : U0) → (x1 : U0) → (x2 : (x2 : U0) → U0) → (x3 : (MyMonad x2)) → (x4 : ((MyHandler x0) x2)) → (x5 : ((MyHandler x1) x2)) → U0\n" ++
  "MyCommute.comm : (x0 :0 U0) → (x1 :0 U0) → (x2 :0 (x2 : U0) → U0) → (x3 : (MyMonad x2)) → (x4 : ((MyHandler x0) x2)) → (x5 : ((MyHandler x1) x2)) → (x6 : ((((((MyCommute x0) x1) x2) x3) x4) x5)) → Nat\n" ++
  "instMyCommute : ((((((MyCommute Nat) Nat) Option) instMyMonadOption) instMyHandlerNatOption) instMyHandlerNatOption)\n" ++
  "con((#1, (tt, tt)))\n"

/-- (A10) A method call with no instance for its class argument: an error. -/
def classMissing : String :=
  "import Prelude\nclass Default (A : Type) where\n  d : A\n" ++
  "instance instDefaultNat : Default Nat := Default.mk 7\n" ++
  "def get {A : Type} [Default A] : A := Default.d\n" ++
  "#reduce Nat.beq (get : Nat) 7\ndef bad : Bool := get\n"

def classMissingExpected : String :=
  "Default : (x0 : U0) → U0\n" ++
  "Default.d : (x0 :0 U0) → (x1 : (Default x0)) → x0\n" ++
  "instDefaultNat : (Default Nat)\n" ++
  "get : (x0 :0 U0) → (x1 : (Default x0)) → x0\n" ++
  "con((#1, (tt, tt)))\n" ++
  "error: failed to synthesize an instance of (Default ?m0)\n"

/-- (A10) A second instance of the same class type is an error. -/
def classDup : String :=
  "import Prelude\nclass Default (A : Type) where\n  d : A\n" ++
  "instance instDefaultNat : Default Nat := Default.mk 7\n" ++
  "instance instDefaultNat2 : Default Nat := Default.mk 8\n"

def classDupExpected : String :=
  "Default : (x0 : U0) → U0\n" ++
  "Default.d : (x0 :0 U0) → (x1 : (Default x0)) → x0\n" ++
  "instDefaultNat : (Default Nat)\n" ++
  "error: duplicate instance: instDefaultNat already has the type of this one ((Default Nat))\n"

/-- (A10) The header for the verdict-parity cases (a class with a method each). -/
def classAgreeHeader : String :=
  "class Base (A : Type) where\n  b : A\n"

/-- (A10) A class's dictionary passing compiles and runs: `get : Nat` is 7, and
`get : List Nat` is a singleton list (from `instDefaultList`). -/
def classProgram : String :=
  "import Prelude\nclass Default (A : Type) where\n  d : A\n" ++
  "instance instDefaultNat : Default Nat := Default.mk 7\n" ++
  "instance instDefaultList {A : Type} [Default A] : Default (List A) where\n" ++
  "  d := List.cons Default.d List.nil\n" ++
  "def get {A : Type} [Default A] : A := Default.d\n" ++
  "def main : IO Unit := do\n  IO.println (Nat.toString (get : Nat));\n" ++
  "  IO.println (Nat.toString (List.length (get : List Nat)))\n"

/-- (30f) A superclass is an instance-implicit parameter of the class's telescope:
`Loud : (A : Type) → [Show A] → Type`, so `#check Loud` shows the extra binder and each
method re-inserts it. A signature that forms `Loud A` carries `[d : Show A]` too: the
parameter form's cost, paid. (The method calls spell the class's parameters with `@`:
a problem whose arguments are still metavariables is `stuck` here — 30a — and the
postponed argument `x` has not fixed `A` when the problem is resolved.) -/
def superclassParam : String :=
  "import Prelude\nclass Show (A : Type) where\n  show : A → Nat\n" ++
  "class Loud (A : Type) [super : Show A] where\n  loud : A → Nat\n" ++
  "instance instShowNat : Show Nat := Show.mk (fun n => n)\n" ++
  "instance instLoudNat : Loud Nat := Loud.mk (fun n => n + 1)\n" ++
  "def both {A : Type} [d : Show A] [i : Loud A] (x : A) : Nat := @Loud.loud A d i x + @Show.show A d x\n" ++
  "#check Loud\n#check Loud.loud\n#check both\n#reduce Nat.beq (@both Nat instShowNat instLoudNat 2) 5\n"

def superclassParamExpected : String :=
  "Show : (x0 : U0) → U0\n" ++
  "Show.show : (x0 :0 U0) → (x1 : (Show x0)) → (x2 : x0) → Nat\n" ++
  "Loud : (x0 : U0) → (x1 : (Show x0)) → U0\n" ++
  "Loud.loud : (x0 :0 U0) → (x1 : (Show x0)) → (x2 : ((Loud x0) x1)) → (x3 : x0) → Nat\n" ++
  "instShowNat : (Show Nat)\n" ++
  "instLoudNat : ((Loud Nat) instShowNat)\n" ++
  "both : (x0 :0 U0) → (x1 : (Show x0)) → (x2 : ((Loud x0) x1)) → (x3 : x0) → Nat\n" ++
  "(x0 : U0) → (x1 : (Show x0)) → U0\n" ++
  "(x0 :0 U0) → (x1 : (Show x0)) → (x2 : ((Loud x0) x1)) → (x3 : x0) → Nat\n" ++
  "(x0 :0 U0) → (x1 : (Show x0)) → (x2 : ((Loud x0) x1)) → (x3 : x0) → Nat\n" ++
  "con((#1, (tt, tt)))\n"

/-- (30f) The same class compiles and runs with both dictionaries; `both 2` is 5
(`loud 2` is 3, `show 2` is 2). -/
def superclassProgram : String :=
  "import Prelude\nclass Show (A : Type) where\n  show : A → Nat\n" ++
  "class Loud (A : Type) [super : Show A] where\n  loud : A → Nat\n" ++
  "instance instShowNat : Show Nat := Show.mk (fun n => n)\n" ++
  "instance instLoudNat : Loud Nat := Loud.mk (fun n => n + 1)\n" ++
  "def both {A : Type} [d : Show A] [i : Loud A] (x : A) : Nat := @Loud.loud A d i x + @Show.show A d x\n" ++
  "def main : IO Unit := do\n  IO.println (Nat.toString (@both Nat instShowNat instLoudNat 2))\n"
/-- (A9) Named arguments: explicit, implicit, reordered, with `@f` and after other
positional arguments. -/
def namedArgHeader : String :=
  "def sub (a b : Nat) : Nat := Nat.sub a b\n" ++
  "def ident {A : Type} (x : A) : A := x\n" ++
  "def pick {A : Type} (x y : A) (b : Bool) : A := match b with\n  | .true => x\n  | .false => y\n" ++
  "def const2 {A B : Type} (a : A) (b : B) : A := a\n" ++
  "def mixed {A : Type} (x : A) {B : Type} (y : B) : A := x\n"

def namedArgCases : List (String × Nat) := [
  ("sub (b := 1) 5", 4),
  ("sub (a := 7) (b := 2)", 5),
  ("sub (b := 1) (Nat.succ 5)", 5),
  ("ident (A := Nat) 3", 3),
  ("@ident (A := Nat) 4", 4),
  ("@ident (x := 5) Nat", 5),
  ("pick (b := .false) 1 2", 2),
  ("const2 (B := Bool) 7 .true", 7),
  ("mixed (B := Bool) 3 .true", 3)]

/-- (A9) A constructor's fields (and its parameters) are named arguments too:
`P.mk (y := 2) (x := 1)` fills them in any order — the telescope is walked in its own
order, so a later field's type may mention an earlier named one — and a missing,
unknown or repeated field is an error, as in Lean. -/
def ctorNamedHeader : String :=
  "inductive P where\n  | mk (x : Nat) (y : Nat)\n" ++
  "def getX : P → Nat\n  | .mk x _ => x\n" ++
  "def getY : P → Nat\n  | .mk _ y => y\n" ++
  "inductive Pair (A B : Type) where\n  | mk (a : A) (b : B)\n" ++
  "inductive Vec (A : Type) : Nat → Type where\n  | nil : Vec A Nat.zero\n" ++
  "  | cons (n : Nat) (a : A) (v : Vec A n) : Vec A (Nat.succ n)\n" ++
  "def vhead : Vec Nat 1 → Nat\n  | .cons _ a _ => a\n" ++
  "inductive Imp where\n  | mk {n : Nat} (v : Nat)\n"

def ctorNamedDecls : List (String × Bool) := [
  ("def a : P := P.mk (y := 2) (x := 1)", true),
  ("def b : P := P.mk (x := 1)", false),
  ("def c : P := P.mk (z := 1)", false),
  ("def d : P := P.mk (x := 1) (x := 2)", false),
  ("def p : Pair Nat Bool := Pair.mk (B := Bool) (b := .true) (a := 1)", true),
  ("def v1 : Vec Nat 2 := Vec.cons (v := Vec.cons .zero 5 Vec.nil) (n := 1) (a := 7)", true),
  ("def i1 : Imp := Imp.mk (n := 3) 7", true)]

/-- The parser differential's corpus (`selfhost` group): the category and the input. The
Lean parser is the oracle; the tables generated here and the checked-in
`selfhost/Tables.wiz` must both accept it and produce the same tree. -/
def parseDiffCorpus : List (Name × String) := [
  ("term", "f x y"), ("term", "fun (x : Nat) => x"), ("term", "(x : A) → B x"),
  ("term", "(a, b).1"), ("term", "match n with\n  | .zero => a\n  | .succ m => b"),
  ("term", "let x := 1; x"), ("term", "f (g x"), ("term", "Type 1"),
  ("command", "def f (x : Nat) : Nat := x"),
  ("command", "inductive T where\n  | a\n  | b (t : T)"),
  ("command", "#eval f 41"), ("command", "def f : Nat → Nat\n  | .zero => 0\n  | .succ n => n")]


/-- (stage 30, C11) A header of our own for `Bytes`: a buffer function (`const void *buf,
size_t n`, one `Bytes` argument on the Wiz side) and a struct with a byte-array field
(`unsigned char data[4]`), with the types written out (the self-hosted compiler does not
run the C preprocessor, so a header it reads must be self-contained). -/
def bytesHeader : String :=
  "#ifndef WIZ_BYTES_H\n#define WIZ_BYTES_H\n" ++
  "static inline unsigned long wiz_sum_buf(const void *buf, unsigned long n) {\n" ++
  "  const unsigned char *p = (const unsigned char *)buf;\n" ++
  "  unsigned long s = 0;\n  for (unsigned long i = 0; i < n; i++) s += p[i];\n  return s;\n}\n" ++
  "typedef struct { unsigned char data[4]; unsigned long n; } wiz_byte_msg;\n" ++
  "static inline wiz_byte_msg wiz_byte_msg_make(unsigned long n) {\n" ++
  "  wiz_byte_msg m;\n  m.data[0] = 'x'; m.data[1] = 'y'; m.data[2] = 0; m.data[3] = 'z'; m.n = n;\n  return m;\n}\n" ++
  "static inline unsigned long wiz_byte_msg_first(wiz_byte_msg m) { return (unsigned long)m.data[0] + m.n; }\n" ++
  "static unsigned char wiz_static_buf[3] = {65, 66, 67};\n" ++
  "static inline const void *wiz_get_buf(void) { return wiz_static_buf; }\n" ++
  "#endif\n"

/-- Write `bytesHeader` to a fresh directory; its absolute path (both toolchains read the
header from the file system: the Lean one when it preprocesses, the self-hosted one when
the frontend asks for it). -/
def writeBytesHeader : IO String := do
  let dir ← IO.FS.createTempDir
  let h := dir / "wiz_bytes.h"
  IO.FS.writeFile h bytesHeader
  pure h.toString

/-- (stage 30, C11) The `Bytes` operations of `lib/IO.wiz` (`empty`, `push` and its
in-place update, `size`, `get` past the end, `slice`, `take`, `drop`, `append`, `eq`,
`isEmpty`, `at`, `ofString`/`toString`, `ofList`/`toList`/`singleton`/`show`), the same
in both toolchains. Prints the list below. -/
def bytesProgram : String :=
  "import IO\ndef atShow (b : Bytes) (i : Nat) : String := match Bytes.at b i with\n  | .some n => Nat.toString n\n  | .none => \"none\"\ndef main : IO Unit := do\n" ++
  "  let b := Bytes.ofList (List.cons 1 (List.cons 2 (List.cons 300 .nil)));\n" ++
  "  IO.println (Bytes.show b);\n" ++
  "  IO.println (Nat.toString (Bytes.size b));\n" ++
  "  IO.println (Nat.toString (Bytes.get b 1));\n" ++
  "  IO.println (Nat.toString (Bytes.get b 9));\n" ++
  "  IO.println (if Bytes.isEmpty Bytes.empty then \"empty\" else \"no\");\n" ++
  "  IO.println (Bytes.show (Bytes.slice b 1 2));\n" ++
  "  IO.println (Bytes.show (Bytes.slice b 2 9));\n" ++
  "  IO.println (Bytes.show (Bytes.singleton 7));\n" ++
  "  IO.println (Bytes.show (Bytes.take b 1));\n" ++
  "  IO.println (Bytes.show (Bytes.drop b 1));\n" ++
  "  IO.println (Bytes.show (Bytes.append b (Bytes.singleton 4)));\n" ++
  "  let a := Bytes.ofString \"AB\";\n" ++
  "  let p := Bytes.push a 67;\n" ++
  "  IO.println (Bytes.toString a);\n" ++
  "  IO.println (Bytes.toString p);\n" ++
  "  let q := Bytes.append a (Bytes.singleton 68);\n" ++
  "  IO.println (Bytes.toString a);\n" ++
  "  IO.println (Bytes.toString q);\n" ++
  "  IO.println (Bytes.show (Bytes.range 4));\n" ++
  "  let c := Bytes.ofString \"AB\";\n" ++
  "  IO.println (Bytes.toString c);\n" ++
  "  IO.println (Nat.toString (Bytes.size c));\n" ++
  "  IO.println (if Bytes.eq c (Bytes.ofString \"AB\") then \"eq\" else \"ne\");\n" ++
  "  IO.println (if Bytes.eq c (Bytes.ofString \"ab\") then \"eq\" else \"ne\");\n" ++
  "  IO.println (Bytes.show (Bytes.append c (Bytes.ofString \"c\")));\n" ++
  "  IO.println (atShow (Bytes.ofList (List.cons 5 (List.cons 6 .nil))) 1);\n" ++
  "  IO.println (atShow (Bytes.ofString \"a\") 7)\n"

def bytesExpected : String :=
  "[1, 2, 44]\n3\n2\n0\nempty\n[2, 44]\n[44]\n[7]\n[1]\n[2, 44]\n[1, 2, 44, 4]\nAB\nABC\nAB\nABD\n[0, 1, 2, 3]\nAB\n2\neq\nne\n[65, 66, 99]\n6\nnone\n"

/-- (stage 30, C11) `Bytes` across the FFI: one `Bytes` argument for a buffer and its
length (`C.wiz_sum_buf`), a struct with a byte-array field given to C and read back
(`Msg.mk`, `C.wiz_byte_msg_first`, `C.wiz_byte_msg_make`). -/
def bytesFfiProgram (header : String) : String :=
  "import IO\n" ++
  s!"c_struct \"wiz_byte_msg\" (header := \"{header}\") Msg where\n  data : Bytes\n  n : Nat\n" ++
  s!"import_c \"{header}\" (pure)\n" ++
  s!"foreign_type BUF\n" ++
  s!"extern \"wiz_get_buf\" (header := \"{header}\") getBuf : IO BUF\n" ++
  "glue sumBuf (p : BUF) (n : Nat) : Nat := \"return wiz_sum_buf(p, n);\"\n" ++
  "def main : IO Unit := do\n" ++
  "  IO.println (Nat.toString (C.wiz_sum_buf (Bytes.ofString \"ABC\")));\n" ++
  "  IO.println (Nat.toString (C.wiz_byte_msg_first (Msg.mk (Bytes.ofString \"AB\") 5)));\n" ++
  "  let m := C.wiz_byte_msg_make 5;\n" ++
  "  IO.println (Bytes.show m.data);\n" ++
  "  IO.println (Nat.toString m.n);\n" ++
  "  b ← getBuf;\n" ++
  "  IO.println (Nat.toString (sumBuf b 3))\n"

def bytesFfiExpected : String := "198\n70\n[120, 121, 0, 122]\n5\n198\n"

/-- (21ag) The encodings of `lib/IO.wiz`: `ofUtf8`/`toUtf8` (every character, NULs
included; the decoder checks overlong forms and surrogates), `ofString`/`toString`
(through a C string: they stop at a NUL) and `ofLatin1`/`toLatin1` (one byte per
character, an error above 255). The strings are observed through `Bytes` only (a text
module is not in the self-hosted Prelude). Prints the list below.

Every `match` scrutinee is `let`-bound first: the self-hosted compiler evaluates a closed
scrutinee in full while it compiles (`scrutLets` binds its value; #422), and the
Prelude's `Bytes.toUtf8` model on `"𝄞"` alone took over 200 s and 3.4 GB there. The
case "a closed match scrutinee is evaluated at compile time" pins that pattern. -/
def bytesEncProgram : String :=
  "import Std\ndef main : IO Unit := do\n" ++
  "  let u := Bytes.ofUtf8 \"a\\x00b\";\n" ++
  "  IO.println (Nat.toString (Bytes.size u));\n" ++
  "  IO.println (Nat.toString (Bytes.size (Bytes.ofString \"a\\x00b\")));\n" ++
  "  IO.println (Bytes.show (Bytes.ofString (Bytes.toString u)));\n" ++
  "  IO.println (if Bytes.eq (Bytes.ofString (Bytes.toString u)) (Bytes.ofList (List.cons 97 .nil)) then \"eq\" else \"ne\");\n" ++
  "  IO.println (Nat.toString (Bytes.size (Bytes.ofUtf8 \"𝄞\")));\n" ++
  "  IO.println (Nat.toString (Bytes.size (Bytes.ofString \"𝄞\")));\n" ++
  "  let e1 := Bytes.toUtf8 (Bytes.ofUtf8 \"𝄞\");\n" ++
  "  IO.println (match e1 with\n    | .ok t => if Bytes.eq (Bytes.ofUtf8 t) (Bytes.ofUtf8 \"𝄞\") then \"eq\" else \"ne\"\n    | .error _ => \"err\");\n" ++
  "  let e2 := Bytes.ofLatin1 \"é\";\n" ++
  "  IO.println (match e2 with\n    | .ok b => Bytes.show b\n    | .error _ => \"err\");\n" ++
  "  let e3 := Bytes.ofLatin1 (Bytes.toLatin1 (Bytes.ofList (List.cons 233 .nil)));\n" ++
  "  IO.println (match e3 with\n    | .ok b => Bytes.show b\n    | .error _ => \"err\");\n" ++
  "  let e4 := Bytes.ofLatin1 \"\\u{100}\";\n" ++
  "  IO.println (match e4 with\n    | .ok _ => \"ok\"\n    | .error e => e);\n" ++
  "  let e5 := Bytes.toUtf8 (Bytes.ofList (List.cons 128 .nil));\n" ++
  "  IO.println (match e5 with\n    | .ok _ => \"ok\"\n    | .error e => e);\n" ++
  "  let e6 := Bytes.toUtf8 (Bytes.ofList (List.cons 192 (List.cons 128 .nil)));\n" ++
  "  IO.println (match e6 with\n    | .ok _ => \"ok\"\n    | .error e => e);\n" ++
  "  let e7 := Bytes.toUtf8 (Bytes.ofList (List.cons 237 (List.cons 160 (List.cons 128 .nil))));\n" ++
  "  IO.println (match e7 with\n    | .ok _ => \"ok\"\n    | .error e => e)\n"

def bytesEncExpected : String :=
  "3\n1\n[97]\neq\n4\n4\neq\n[233]\n[233]\nnot Latin-1: character 0 is U+256\n" ++
  "invalid UTF-8 at byte 0\ninvalid UTF-8 at byte 0\ninvalid UTF-8 at byte 0\n"

/-- `l` as the bracketed list `Bytes.show` prints: `[1, 2, 255]`. -/
def showNats (l : List Nat) : String := "[" ++ ", ".intercalate (l.map toString) ++ "]"

/-- `l` as a Wiz `List Nat` literal (`(List.cons 1 .nil)`; `[]` for the empty list). -/
def natListLit : List Nat → String
  | [] => ".nil"
  | x :: xs => s!"(List.cons {x} {natListLit xs})"

/-- A `Bytes` of `l` as a Wiz expression (`Bytes.ofList` for a non-empty list). -/
def bytesLit : List Nat → String
  | [] => "Bytes.empty"
  | l => s!"(Bytes.ofList {natListLit l})"

/-- (21ag) The UTF-8 differential table: `(label, bytes, what the C-string decoder
(`Bytes.toString`) makes of them, as bytes, and what the checked decoder
(`Bytes.toUtf8`) says)`. The third column is the fourth column's opposite: the lenient
decoder writes U+FFFD (`EF BF BD`) for an invalid sequence and resumes after the bytes
the lead claimed, or stops at a NUL; `none` in the last column means the checked
decoder accepts the bytes and re-encodes them unchanged, `some k` that it reports
`invalid UTF-8 at byte k`.

ASCII, 2/3/4-byte sequences, the maximum scalar, a truncated sequence, an overlong
`C0 80` and `E0 80 80`, a lone continuation byte, a surrogate half, above U+10FFFF, a
byte that is not a lead (`F8`), a bad continuation, a NUL inside the buffer, and a valid
character before an invalid one. -/
def utf8Table : List (String × List Nat × List Nat × Option Nat) := [
  ("ascii", [0x41, 0x42, 0x43], [0x41, 0x42, 0x43], none),
  ("two bytes", [0xC3, 0xA9], [0xC3, 0xA9], none),
  ("three bytes", [0xE2, 0x82, 0xAC], [0xE2, 0x82, 0xAC], none),
  ("four bytes", [0xF0, 0x9D, 0x84, 0x9E], [0xF0, 0x9D, 0x84, 0x9E], none),
  ("max scalar", [0xF4, 0x8F, 0xBF, 0xBF], [0xF4, 0x8F, 0xBF, 0xBF], none),
  ("truncated", [0xE2, 0x82], [0xEF, 0xBF, 0xBD], some 0),
  ("overlong C0 80", [0xC0, 0x80], [0xEF, 0xBF, 0xBD], some 0),
  ("overlong E0 80 80", [0xE0, 0x80, 0x80], [0xEF, 0xBF, 0xBD], some 0),
  ("lone continuation", [0x88, 0x41], [0xEF, 0xBF, 0xBD, 0x41], some 0),
  ("surrogate half", [0xED, 0xA0, 0x80], [0xEF, 0xBF, 0xBD], some 0),
  ("above 10FFFF", [0xF4, 0x90, 0x80, 0x80], [0xEF, 0xBF, 0xBD], some 0),
  ("not a lead F8", [0xF8, 0x41], [0xEF, 0xBF, 0xBD, 0x41], some 0),
  ("bad continuation", [0xE2, 0x28, 0xA1], [0xEF, 0xBF, 0xBD], some 0),
  ("NUL inside", [0x41, 0x00, 0x42], [0x41], none),
  ("valid then invalid", [0x41, 0xE2, 0x82], [0x41, 0xEF, 0xBF, 0xBD], some 1)]

/-- (21ag) The encoders' table: `(label, code point, the bytes every encoder writes)`.
A non-scalar code point is U+FFFD. -/
def utf8EncTable : List (String × Nat × List Nat) := [
  ("enc one byte", 0x41, [0x41]),
  ("enc two bytes low", 0x80, [0xC2, 0x80]),
  ("enc two bytes high", 0x7FF, [0xDF, 0xBF]),
  ("enc three bytes low", 0x800, [0xE0, 0xA0, 0x80]),
  ("enc three bytes high", 0xFFFF, [0xEF, 0xBF, 0xBF]),
  ("enc four bytes low", 0x10000, [0xF0, 0x90, 0x80, 0x80]),
  ("enc max scalar", 0x10FFFF, [0xF4, 0x8F, 0xBF, 0xBF]),
  ("enc surrogate low", 0xD800, [0xEF, 0xBF, 0xBD]),
  ("enc surrogate high", 0xDFFF, [0xEF, 0xBF, 0xBD]),
  ("enc above max", 0x110000, [0xEF, 0xBF, 0xBD])]

/-- `l` with each element's index, in order. -/
def listIdx : List α → List (α × Nat)
  | [] => []
  | x :: xs => (x, 0) :: (listIdx xs).map fun (a, n) => (a, n + 1)

/-- (21ag) The differential program: every row of `utf8Table` through `Bytes.toString`
(the C-string decoder) and `Bytes.toUtf8` (checked), then every row of `utf8EncTable`
through `Bytes.pushUtf8`, `Bytes.ofUtf8` and `Bytes.ofString` (the last two from a
one-character `String`), with an encode → decode → encode round trip. The same source is
compiled by the Lean toolchain and the self-hosted one; the outputs must be equal, byte
for byte, and equal to `utf8Expected`.

Every `match` scrutinee is `let`-bound (a closed one is evaluated while the self-hosted
compiler compiles; #422). -/
def utf8Program : String :=
  "import Std\ndef main : IO Unit := do\n" ++
  String.join ((listIdx utf8Table).map fun ((label, bs, _, _), n) =>
    s!"  IO.println \"{label}\";\n" ++
    s!"  let b{n} := {bytesLit bs};\n" ++
    s!"  IO.println (Bytes.show (Bytes.ofUtf8 (Bytes.toString b{n})));\n" ++
    s!"  let c{n} := Bytes.toUtf8 b{n};\n" ++
    s!"  IO.println (match c{n} with\n    | .ok s => Bytes.show (Bytes.ofUtf8 s)\n" ++
    s!"    | .error e => String.append \"err \" e);\n")
  ++
  String.join ((listIdx utf8EncTable).map fun ((label, cp, _), n) =>
    s!"  IO.println \"{label}\";\n" ++
    s!"  let e{n} := Bytes.pushUtf8 Bytes.empty {cp};\n" ++
    s!"  IO.println (Bytes.show e{n});\n" ++
    s!"  let t{n} := String.mk (List.cons (Char.mk {cp}) .nil);\n" ++
    s!"  IO.println (Bytes.show (Bytes.ofUtf8 t{n}));\n" ++
    s!"  IO.println (Bytes.show (Bytes.ofString t{n}));\n" ++
    s!"  IO.println (if Bytes.eq (Bytes.ofUtf8 (Bytes.toString e{n})) e{n} then \"eq\" else \"ne\");\n") ++
  "  IO.pure ()\n"

/-- What `utf8Program` prints: each row's label, the two decoders' bytes (or the checked
error), the three encoders' bytes, and the round trip. -/
def utf8Expected : String :=
  String.join ((utf8Table).map fun (label, bs, out, chk) =>
    label ++ "\n" ++ showNats out ++ "\n" ++
    (match chk with
     | none => showNats bs
     | some k => s!"err invalid UTF-8 at byte {k}") ++ "\n") ++
  String.join ((utf8EncTable).map fun (label, _, out) =>
    label ++ "\n" ++ showNats out ++ "\n" ++ showNats out ++ "\n" ++ showNats out ++ "\neq\n")


/-- (#422) A closed `match` scrutinee that is expensive to evaluate: `fib k n` doubles
`n` `k` times by recursion (2^18 calls here). The self-hosted compiler evaluates such a
scrutinee in full while it compiles (`scrutLets` binds its value), and the `let`-bound
form below does not; the host compiles both at once. -/
def closedScrutFib : String :=
  "import Std\ndef fib : Nat → Nat → Nat\n  | .zero, n => n\n  | .succ k, n => Nat.add (fib k n) (fib k n)\n"

def closedScrutInline : String :=
  closedScrutFib ++ "def main : IO Unit := IO.println (match Nat.beq (fib 18 1) 0 with\n  | .true => \"z\"\n  | .false => \"nz\")\n"

def closedScrutLet : String :=
  closedScrutFib ++ "def main : IO Unit := do\n  let r := Nat.beq (fib 18 1) 0;\n  IO.println (match r with\n  | .true => \"z\"\n  | .false => \"nz\")\n"

/-- (21ag) `Array ↔ Bytes` (`lib/Std.wiz`: `Bytes.ofArray`, `Bytes.toArray`) and the
`Bytes.slice`/`append`/`eq`/`get`/`push` boundaries the semantics matrix pins: a slice
past the end clamps, a drop past the end is empty, a read past the end is 0, a pushed
number keeps its low eight bits, and equality is byte for byte, length included. -/
def bytesArrayProgram : String :=
  "import Std\ndef main : IO Unit := do\n" ++
  "  let a := Array.push (Array.push (Array.push Array.empty 1) 2) 300;\n" ++
  "  let b := Bytes.ofArray a;\n" ++
  "  IO.println (Bytes.show b);\n" ++
  "  IO.println (Nat.toString (Array.size (Bytes.toArray b)));\n" ++
  "  IO.println (Nat.toString (Array.getD (Bytes.toArray b) 2 0));\n" ++
  "  IO.println (Bytes.show (Bytes.ofArray (Bytes.toArray b)));\n" ++
  "  let c := Bytes.ofList (List.cons 1 (List.cons 2 (List.cons 3 .nil)));\n" ++
  "  IO.println (Bytes.show (Bytes.slice c 2 99));\n" ++
  "  IO.println (Nat.toString (Bytes.size (Bytes.drop c 5)));\n" ++
  "  IO.println (Bytes.show (Bytes.take c 9));\n" ++
  "  IO.println (Bytes.show (Bytes.append (Bytes.ofList (List.cons 1 .nil)) (Bytes.ofList (List.cons 2 (List.cons 3 .nil)))));\n" ++
  "  IO.println (if Bytes.eq c (Bytes.ofList (List.cons 1 (List.cons 2 (List.cons 3 .nil)))) then \"eq\" else \"ne\");\n" ++
  "  IO.println (if Bytes.eq (Bytes.ofList (List.cons 1 .nil)) c then \"eq\" else \"ne\");\n" ++
  "  IO.println (if Bytes.eq (Bytes.ofList (List.cons 2 .nil)) (Bytes.ofList (List.cons 1 .nil)) then \"eq\" else \"ne\");\n" ++
  "  IO.println (Nat.toString (Bytes.get (Bytes.ofList (List.cons 7 .nil)) 9));\n" ++
  "  IO.println (Bytes.show (Bytes.ofList (List.cons 256 (List.cons 257 .nil))));\n" ++
  "  IO.println (Bytes.show (Bytes.slice (Bytes.ofList (List.cons 1 .nil)) 9 2))\n"

def bytesArrayExpected : String :=
  "[1, 2, 44]\n3\n44\n[1, 2, 44]\n[3]\n0\n[1, 2, 3]\n[1, 2, 3]\neq\nne\nne\n0\n[0, 1]\n[]\n"

/-- (21ag) A header for a buffer pointer written three ways: `const char *`,
`uint8_t *` (a typedef for `unsigned char`) and `unsigned char *`, each followed by its
length, which the frontends fold into one `Bytes` parameter (kind `y`, or `Y` when the
pointer is writable and the argument is a copy). `wiz_scribble_chars` writes through a
writable pointer, to show the Wiz buffer does not change. -/
def bytesPtrHeader : String :=
  "#ifndef WIZ_BYTES2_H\n#define WIZ_BYTES2_H\n" ++
  "typedef unsigned char uint8_t;\n" ++
  "static inline unsigned long wiz_sum_chars(const char *buf, unsigned long n) {\n" ++
  "  unsigned long s = 0; for (unsigned long i = 0; i < n; i++) s += (unsigned char)buf[i]; return s;\n}\n" ++
  "static inline unsigned long wiz_sum_u8(const uint8_t *buf, unsigned long n) {\n" ++
  "  unsigned long s = 0; for (unsigned long i = 0; i < n; i++) s += buf[i]; return s;\n}\n" ++
  "static inline unsigned long wiz_sum_u8c(unsigned char *buf, unsigned long n) {\n" ++
  "  unsigned long s = 0; for (unsigned long i = 0; i < n; i++) s += buf[i]; return s;\n}\n" ++
  "typedef struct { unsigned char data[4]; unsigned long n; } wiz_byte_msg;\n" ++
  "static inline wiz_byte_msg wiz_byte_msg_make(unsigned long n) {\n" ++
  "  wiz_byte_msg m;\n  m.data[0] = 'x'; m.data[1] = 'y'; m.data[2] = 0; m.data[3] = 'z'; m.n = n;\n  return m;\n}\n" ++
  "static inline unsigned long wiz_byte_msg_first(wiz_byte_msg m) { return (unsigned long)m.data[0] + m.n; }\n" ++
  "#endif\n"

/-- (21ag) A header of the writable-pointer case: `char *` with a length, writing
through the pointer and returning the length (a pure function whose result the program
prints, so the call cannot be dropped: the copy is what keeps the Wiz buffer intact). -/
def bytesPtrIoHeader : String :=
  "#ifndef WIZ_BYTES2_IO_H\n#define WIZ_BYTES2_IO_H\n" ++
  "static inline unsigned long wiz_scribble_chars(char *buf, unsigned long n) {\n" ++
  "  if (n) buf[0] = 'X';\n  return n;\n}\n" ++
  "#endif\n"

/-- (21ag) A C function taking a `char *`/`uint8_t *`/`unsigned char *` and its length,
called with one `Bytes` argument; a `const` buffer is **borrowed** for the call (C may
read it and must not keep it), a writable one is a **copy** (C's writes are discarded),
so the same Wiz buffer is usable and unchanged after either call. Prints
`198 258 198 [65, 66, 67] 3 3 [65, 66, 67]` (the second `3` is the writable call's
result: it saw the copy). -/
def bytesPtrProgram (header ioHeader : String) : String :=
  "import IO\n" ++
  s!"import_c \"{header}\" (pure)\n" ++
  s!"import_c \"{ioHeader}\" (pure)\n" ++
  "def main : IO Unit := do\n" ++
  "  let b := Bytes.ofString \"ABC\";\n" ++
  "  IO.println (Nat.toString (C.wiz_sum_chars b));\n" ++
  "  IO.println (Nat.toString (C.wiz_sum_u8 (Bytes.ofList (List.cons 1 (List.cons 2 (List.cons 255 .nil))))));\n" ++
  "  IO.println (Nat.toString (C.wiz_sum_u8c b));\n" ++
  "  IO.println (Bytes.show b);\n" ++
  "  IO.println (Nat.toString (Bytes.size b));\n" ++
  "  IO.println (Nat.toString (C.wiz_scribble_chars b));\n" ++
  "  IO.println (Bytes.show b)\n"

def bytesPtrExpected : String := "198\n258\n198\n[65, 66, 67]\n3\n3\n[65, 66, 67]\n"

/-- (21ag) A `c_struct` with a `Bytes` field through `glue`: the struct goes to C by
value and comes back by value (the field is copied into the C array and out of it), and
glue may pass the struct on but not read the buffer field (`glueDeclFields` leaves it
out, as the Lean frontend does). Prints `70`, the field's bytes, `7`, `127`. -/
def bytesGlueProgram (header : String) : String :=
  "import IO\n" ++
  s!"c_struct \"wiz_byte_msg\" (header := \"{header}\") Msg where\n  data : Bytes\n  n : Nat\n" ++
  s!"import_c \"{header}\" (pure)\n" ++
  "glue msgFirst (m : Msg) : Nat := \"return wiz_byte_msg_first(m);\"\n" ++
  "glue msgMake (k : Nat) : Msg := \"return wiz_byte_msg_make(k);\"\n" ++
  "def main : IO Unit := do\n" ++
  "  IO.println (Nat.toString (msgFirst (Msg.mk (Bytes.ofString \"AB\") 5)));\n" ++
  "  let m := msgMake 7;\n" ++
  "  IO.println (Bytes.show m.data);\n" ++
  "  IO.println (Nat.toString m.n);\n" ++
  "  IO.println (Nat.toString (C.wiz_byte_msg_first m))\n"

def bytesGlueExpected : String := "70\n[120, 121, 0, 122]\n7\n127\n"

/-- (U2b) Polymorphic declarations: a structure at a level parameter, an inductive whose
fields are at two different level parameters, a class at a level parameter, and generic
instances for `List` and `Option`. The `Duo` fields are in smaller universes than
`Type (max u v)`, so their description fields are `ULift`ed (Q4), as in the Lean
frontend. -/
def u2bDecls : String :=
  "structure Box.{u} (A : Type u) where\n  val : A\n" ++
  "inductive Duo.{u, v} (A : Type u) (B : Type v) : Type (max u v) where\n  | mk (a : A) (b : B)\n" ++
  "def unbox.{u} {A : Type u} (b : Box A) : A := b.val\n" ++
  "def duoSnd.{u, v} {A : Type u} {B : Type v} (d : Duo A B) : B := match d with\n  | .mk _ b => b\n" ++
  "def duoUp : Duo.{1, 0} (Type 0) Nat := Duo.mk Nat 5\n" ++
  "def duoBUp : Nat := duoSnd duoUp\n" ++
  "class Repr.{u} (A : Type u) where\n  repr : A → Nat\n" ++
  "instance instReprNat : Repr Nat where\n  repr := fun n => n\n" ++
  "instance instReprType : Repr (Type 0) where\n  repr := fun _ => 0\n" ++
  "def typeRepr : Nat := Repr.repr Nat\n" ++
  "def sumRepr {A : Type} [Repr A] : List A → Nat\n" ++
  "  | .nil => 0\n  | .cons x xs => Repr.repr x + sumRepr xs\n" ++
  "instance instReprList {A : Type} [Repr A] : Repr (List A) where\n  repr := fun xs => sumRepr xs\n" ++
  "class Inhabited.{u} (A : Type u) where\n  default : A\n" ++
  "instance instInhabitedNat : Inhabited Nat where\n  default := 42\n" ++
  "instance instInhabitedOption {A : Type} [Inhabited A] : Inhabited (Option A) where\n" ++
  "  default := Option.some Inhabited.default\n" ++
  "instance instInhabitedList {A : Type} [Inhabited A] : Inhabited (List A) where\n" ++
  "  default := List.cons Inhabited.default List.nil\n" ++
  "def duoVal : Duo Nat String := Duo.mk 9 \"xy\"\n" ++
  "def boxVal : Box Nat := Box.mk 7\n" ++
  "def optDefault : Nat := match (Inhabited.default : Option Nat) with\n  | .some n => n\n  | .none => 0\n" ++
  "def listDefault : Nat := match (Inhabited.default : List Nat) with\n  | .cons n _ => n\n  | .nil => 0\n"

/-- (U2b) A program with the polymorphic declarations (`u2bDecls`), printing
`3 xy 42 42 7`: the generic `Repr (List A)` and `Inhabited (Option/List A)` instances,
a `Duo` at two level parameters, and a `Box` structure. -/
def u2bProgram : String := "import IO\n" ++ u2bDecls ++
  "def main : IO Unit := do\n" ++
  "  IO.println (Nat.toString (Repr.repr (List.cons 1 (List.cons 2 List.nil))));\n" ++
  "  IO.println (duoSnd duoVal);\n" ++
  "  IO.println (Nat.toString optDefault);\n" ++
  "  IO.println (Nat.toString listDefault);\n" ++
  "  IO.println (Nat.toString (unbox boxVal))\n"

/-- (U2b) Each declaration after `import Prelude` is a level mistake: both frontends
reject it on the same line, the Lean one's message contains `phrase`, and the
self-hosted one is a positioned `file:line:col: error:` line whose message contains the
same `phrase`. (The self-hosted position is the command's, not the offending token's:
D6.) -/
def selfhostLevelErrors (decls : List (String × String)) : IO Unit := do
  let loader ← preludeLoader
  match ← selfhostCompiler with
  | .error e => if (e.splitOn "gmp.h").length > 1 then skip "no toolchain" else throw (IO.userError e)
  | .ok exe =>
    for (d, phrase) in decls do
      let src := "import Prelude\n" ++ d
      let s := runFrontend (R := ZeroOneMany) src { loader, trustedModule := Tests.libModule }
      let hostErrs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
      let some hostErr := hostErrs[0]? | throw (IO.userError s!"the Lean frontend accepts:\n{d}")
      unless (hostErr.splitOn phrase).length > 1 do
        throw (IO.userError s!"the Lean frontend's message does not say {repr phrase}:\n{hostErr}")
      let hostLine := hostErr.takeWhile (· != ':')
      let dir ← IO.FS.createTempDir
      IO.FS.writeFile (dir / "bad.wiz") src
      let out ← IO.Process.output { cmd := "timeout", args := #["120", exe.toString, "check", "bad.wiz"], cwd := dir }
      checkEq (1 : UInt32) out.exitCode
      checkEq "" out.stdout
      let lines := (out.stderr.splitOn "\n").filter (!·.isEmpty)
      let some line := lines[0]? | throw (IO.userError s!"the self-hosted frontend accepts:\n{d}")
      unless line.startsWith "bad.wiz:" do
        throw (IO.userError s!"the self-hosted diagnostic has no span:\n{line}")
      let rest := (line.drop "bad.wiz:".length)
      checkEq hostLine (rest.takeWhile (· != ':'))
      unless (line.splitOn phrase).length > 1 do
        throw (IO.userError s!"the self-hosted message does not say {repr phrase}:\n{line}")

/-- (A11) `deriving`: a `deriving` clause on an inductive/structure and
`deriving instance … for …`, with the class declared in the file (the self-hosted
prelude has none). A 0-field type, 1/2/3-field structures, a recursive polymorphic
inductive and an after-the-fact instance. -/
def selfhostDeriving : String :=
  "import Prelude\nclass BEq (A : Type) where\n  beq : A → A → Bool\n" ++
  "instance : BEq Nat := BEq.mk Nat.beq\n" ++
  "def Bool.beqEq : Bool → Bool → Bool\n  | .true, .true => .true\n  | .false, .false => .true\n" ++
  "  | _, _ => .false\ninstance : BEq Bool := BEq.mk Bool.beqEq\n" ++
  "inductive Zero where\n  | z\n  deriving BEq\n" ++
  "structure One where\n  a : Nat\n  deriving BEq\n" ++
  "structure Two where\n  a : Nat\n  b : Bool\n  deriving BEq\n" ++
  "structure Three where\n  a : Nat\n  b : Bool\n  c : Nat\n  deriving BEq\n" ++
  "inductive Tree (A : Type) where\n  | leaf\n  | node (l : Tree A) (x : A) (r : Tree A)\n  deriving BEq\n" ++
  "structure Box (A : Type) where\n  val : A\n" ++
  "deriving instance BEq for Box\n" ++
  "class Repr (A : Type) where\n  reprPrec : A → Nat → String\n" ++
  "instance : Repr Nat := Repr.mk (fun n p => \"n\")\n" ++
  "instance : Repr Bool := Repr.mk (fun b p => \"b\")\n" ++
  "structure R2 where\n  a : Nat\n  b : Bool\n  deriving Repr\n" ++
  "inductive RT where\n  | leaf\n  | node (l : RT) (x : Nat)\n  deriving Repr\n" ++
  "def t1 : Tree Nat := Tree.node Tree.leaf 1 Tree.leaf\n" ++
  "def t2 : Tree Nat := Tree.node (Tree.node Tree.leaf 2 Tree.leaf) 1 Tree.leaf\n" ++
  "#reduce BEq.beq Zero.z Zero.z\n" ++
  "#reduce BEq.beq (One.mk 1) (One.mk 1)\n" ++
  "#reduce BEq.beq (One.mk 1) (One.mk 2)\n" ++
  "#reduce BEq.beq (Two.mk 1 .true) (Two.mk 1 .true)\n" ++
  "#reduce BEq.beq (Two.mk 1 .true) (Two.mk 1 .false)\n" ++
  "#reduce BEq.beq (Three.mk 1 .true 2) (Three.mk 1 .true 2)\n" ++
  "#reduce BEq.beq (Three.mk 1 .true 2) (Three.mk 1 .false 2)\n" ++
  "#reduce BEq.beq t1 t1\n" ++
  "#reduce BEq.beq t1 t2\n" ++
  "#reduce BEq.beq (Box.mk 3) (Box.mk 3)\n" ++
  "#reduce BEq.beq (Box.mk 3) (Box.mk 4)\n" ++
  "#reduce Nat.beq (String.length (Repr.reprPrec (R2.mk 1 .true) 0)) 9\n" ++
  "#reduce Nat.beq (String.length (Repr.reprPrec (R2.mk 1 .true) 1024)) 11\n" ++
  "#reduce Nat.beq (String.length (Repr.reprPrec (RT.node RT.leaf 1) 0)) 17\n"

def selfhostDerivingExpected : String :=
  "BEq : (x0 : U0) → U0\nBEq.beq : (x0 :0 U0) → (x1 : (BEq x0)) → (x2 : x0) → (x3 : x0) → Bool\ninstBEq : (BEq Nat)\nBool.beqEq : (x0 : Bool) → (x1 : Bool) → Bool\ninstBEq1 : (BEq Bool)\nZero : U0\nOne : U0\nOne.a : (x0 : One) → Nat\nTwo : U0\nTwo.a : (x0 : Two) → Nat\nTwo.b : (x0 : Two) → Bool\nThree : U0\nThree.a : (x0 : Three) → Nat\nThree.b : (x0 : Three) → Bool\nThree.c : (x0 : Three) → Nat\nTree : (x0 : U0) → U0\nBox : (x0 : U0) → U0\nBox.val : (x0 :0 U0) → (x1 : (Box x0)) → x0\nRepr : (x0 : U0) → U0\nRepr.reprPrec : (x0 :0 U0) → (x1 : (Repr x0)) → (x2 : x0) → (x3 : Nat) → String\ninstRepr : (Repr Nat)\ninstRepr1 : (Repr Bool)\nR2 : U0\nR2.a : (x0 : R2) → Nat\nR2.b : (x0 : R2) → Bool\nRT : U0\nt1 : (Tree Nat)\nt2 : (Tree Nat)\ncon((#1, (tt, tt)))\ncon((#1, (tt, tt)))\ncon((#0, (tt, tt)))\ncon((#1, (tt, tt)))\ncon((#0, (tt, tt)))\ncon((#1, (tt, tt)))\ncon((#0, (tt, tt)))\ncon((#1, (tt, tt)))\ncon((#0, (tt, tt)))\ncon((#1, (tt, tt)))\ncon((#0, (tt, tt)))\ncon((#1, (tt, tt)))\ncon((#1, (tt, tt)))\ncon((#1, (tt, tt)))\n"

/-- (A11) The five classes `lib/Deriving.wiz` gives derivers to, declared in the file:
the self-hosted prelude has no classes, so a `deriving` case writes them out. -/
def derivingSelfHeader : String :=
  "class Inhabited (A : Type) where\n  default : A\n" ++
  "class BEq (A : Type) where\n  beq : A → A → Bool\n" ++
  "class Repr (A : Type) where\n  reprPrec : A → Nat → String\n" ++
  "class DecidableEq (A : Type) where\n  decide : A → A → Bool\n" ++
  "inductive Ordering where\n  | lt\n  | eq\n  | gt\n" ++
  "class Compare (K : Type) where\n  compare : K → K → Ordering\n" ++
  "instance : Inhabited Nat := Inhabited.mk 0\n" ++
  "instance : Inhabited Bool := Inhabited.mk .false\n" ++
  "def Bool.beqE : Bool → Bool → Bool\n  | .true, .true => .true\n  | .false, .false => .true\n" ++
  "  | _, _ => .false\n" ++
  "instance : BEq Nat := BEq.mk Nat.beq\ninstance : BEq Bool := BEq.mk Bool.beqE\n" ++
  "instance : DecidableEq Nat := DecidableEq.mk Nat.beq\n" ++
  "instance : DecidableEq Bool := DecidableEq.mk Bool.beqE\n" ++
  "instance : Repr Nat := Repr.mk (fun n p => \"n\")\n" ++
  "instance : Repr Bool := Repr.mk (fun b p => \"b\")\n" ++
  "def Nat.compare (a b : Nat) : Ordering :=\n  if Nat.lt a b then Ordering.lt else (if Nat.beq a b then Ordering.eq else Ordering.gt)\n" ++
  "instance : Compare Nat := Compare.mk Nat.compare\n" ++
  "def Bool.cmp : Bool → Bool → Ordering\n  | .false, .true => Ordering.lt\n  | .true, .false => Ordering.gt\n" ++
  "  | _, _ => Ordering.eq\n" ++
  "instance : Compare Bool := Compare.mk Bool.cmp\n"

/-- (A11) The deriver table and the five built-ins, on every form: a `deriving` clause on
an `inductive` and on a `structure`, `deriving instance C for T`, several classes and
several types in one instance, and a built-in re-registered for another class with
`attribute [deriver …]`. Every result is reduced. -/
def selfhostDerivingTable : String :=
  "import Prelude\n" ++ derivingSelfHeader ++
  "def ordIs (o : Ordering) : Nat := match o with\n  | .lt => 1\n  | .eq => 2\n  | .gt => 3\n" ++
  "inductive Color where\n  | red\n  | green\n  | blue\n  deriving Inhabited, BEq, Repr, DecidableEq, Compare\n" ++
  "structure Point where\n  x : Nat\n  y : Bool\n  deriving Inhabited, BEq, Repr, DecidableEq, Compare\n" ++
  "inductive Tree (A : Type) where\n  | leaf\n  | node (l : Tree A) (x : A) (r : Tree A)\n  deriving Inhabited, BEq, Repr, Compare\n" ++
  "structure Box (A : Type) where\n  val : A\n" ++
  "deriving instance Inhabited, BEq, Repr for Box\n" ++
  "structure One where\n  a : Nat\nstructure Two where\n  a : Nat\n  b : Nat\n" ++
  "deriving instance BEq for One, Two\n" ++
  "class Eq2 (A : Type) where\n  decide : A → A → Bool\n" ++
  "instance : Eq2 Nat := Eq2.mk Nat.beq\n" ++
  "attribute [deriver Eq2] deriveDecidableEq\n" ++
  "inductive Swatch where\n  | on\n  | off\n  deriving Eq2\n" ++
  "def t1 : Tree Nat := Tree.node Tree.leaf 1 Tree.leaf\n" ++
  "def t2 : Tree Nat := Tree.node (Tree.node Tree.leaf 2 Tree.leaf) 1 Tree.leaf\n" ++
  "#reduce BEq.beq (Inhabited.default : Color) Color.red\n" ++
  "#reduce BEq.beq (Inhabited.default : Color) Color.blue\n" ++
  "#reduce BEq.beq Color.red Color.blue\n" ++
  "#reduce ordIs (Compare.compare Color.green Color.red)\n" ++
  "#reduce ordIs (Compare.compare Color.red Color.green)\n" ++
  "#reduce ordIs (Compare.compare Color.green Color.green)\n" ++
  "#reduce BEq.beq (Point.mk 1 .true) (Point.mk 1 .true)\n" ++
  "#reduce BEq.beq (Point.mk 1 .true) (Point.mk 1 .false)\n" ++
  "#reduce DecidableEq.decide (Point.mk 1 .true) (Point.mk 2 .true)\n" ++
  "#reduce ordIs (Compare.compare (Point.mk 1 .false) (Point.mk 1 .true))\n" ++
  "#reduce ordIs (Compare.compare (Point.mk 2 .true) (Point.mk 1 .true))\n" ++
  "#reduce BEq.beq t1 t1\n" ++
  "#reduce BEq.beq t1 t2\n" ++
  "#reduce ordIs (Compare.compare t1 t2)\n" ++
  "#reduce BEq.beq (Box.mk 3) (Box.mk 3)\n" ++
  "#reduce BEq.beq (One.mk 1) (One.mk 2)\n" ++
  "#reduce BEq.beq (Two.mk 1 0) (Two.mk 1 0)\n" ++
  "#reduce Eq2.decide Swatch.on Swatch.on\n" ++
  "#reduce Eq2.decide Swatch.on Swatch.off\n" ++
  "#reduce Nat.beq (String.length (Repr.reprPrec (Point.mk 1 .true) 0)) 12\n" ++
  "#reduce Nat.beq (String.length (Repr.reprPrec (Point.mk 1 .true) 1024)) 14\n" ++
  "#reduce Nat.beq (String.length (Repr.reprPrec (Box.mk 7) 0)) 8\n"

def selfhostDerivingTableExpected : String :=
  "Inhabited : (x0 : U0) → U0\nInhabited.default : (x0 :0 U0) → (x1 : (Inhabited x0)) → x0\nBEq : (x0 : U0) → U0\nBEq.beq : (x0 :0 U0) → (x1 : (BEq x0)) → (x2 : x0) → (x3 : x0) → Bool\nRepr : (x0 : U0) → U0\nRepr.reprPrec : (x0 :0 U0) → (x1 : (Repr x0)) → (x2 : x0) → (x3 : Nat) → String\nDecidableEq : (x0 : U0) → U0\nDecidableEq.decide : (x0 :0 U0) → (x1 : (DecidableEq x0)) → (x2 : x0) → (x3 : x0) → Bool\nOrdering : U0\nCompare : (x0 : U0) → U0\nCompare.compare : (x0 :0 U0) → (x1 : (Compare x0)) → (x2 : x0) → (x3 : x0) → Ordering\ninstInhabited : (Inhabited Nat)\ninstInhabited1 : (Inhabited Bool)\nBool.beqE : (x0 : Bool) → (x1 : Bool) → Bool\ninstBEq : (BEq Nat)\ninstBEq1 : (BEq Bool)\ninstDecidableEq : (DecidableEq Nat)\ninstDecidableEq1 : (DecidableEq Bool)\ninstRepr : (Repr Nat)\ninstRepr1 : (Repr Bool)\nNat.compare : (x0 : Nat) → (x1 : Nat) → Ordering\ninstCompare : (Compare Nat)\nBool.cmp : (x0 : Bool) → (x1 : Bool) → Ordering\ninstCompare1 : (Compare Bool)\nordIs : (x0 : Ordering) → Nat\nColor : U0\nPoint : U0\nPoint.x : (x0 : Point) → Nat\nPoint.y : (x0 : Point) → Bool\nTree : (x0 : U0) → U0\nBox : (x0 : U0) → U0\nBox.val : (x0 :0 U0) → (x1 : (Box x0)) → x0\nOne : U0\nOne.a : (x0 : One) → Nat\nTwo : U0\nTwo.a : (x0 : Two) → Nat\nTwo.b : (x0 : Two) → Nat\nEq2 : (x0 : U0) → U0\nEq2.decide : (x0 :0 U0) → (x1 : (Eq2 x0)) → (x2 : x0) → (x3 : x0) → Bool\ninstEq2 : (Eq2 Nat)\nSwatch : U0\nt1 : (Tree Nat)\nt2 : (Tree Nat)\ncon((#1, (tt, tt)))\ncon((#0, (tt, tt)))\ncon((#0, (tt, tt)))\ncon((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (tt, tt))))\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\ncon((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt))))\ncon((#1, (tt, tt)))\ncon((#0, (tt, tt)))\ncon((#0, (tt, tt)))\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\ncon((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (tt, tt))))\ncon((#1, (tt, tt)))\ncon((#0, (tt, tt)))\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\ncon((#1, (tt, tt)))\ncon((#0, (tt, tt)))\ncon((#1, (tt, tt)))\ncon((#1, (tt, tt)))\ncon((#0, (tt, tt)))\ncon((#1, (tt, tt)))\ncon((#1, (tt, tt)))\ncon((#1, (tt, tt)))\n"

/-- (A11) The deriver table's errors: a class with no deriver, a type a deriver rejects
(an indexed family, an all-recursive constructor, a recursive field for `DecidableEq`), a
deriver registered with the wrong arity, a registered deriver this frontend cannot run,
and `deriving` on a `mutual` block. -/
def selfhostDerivingNeg : String :=
  "import Prelude\n" ++ derivingSelfHeader ++
  "class Size (A : Type) where\n  size : A → Nat\n" ++
  "deriving instance Size for Nat\n" ++
  "inductive Vec (A : Type) : Nat → Type where\n" ++
  "  | vnil : Vec A Nat.zero\n  | vcons (x : A) (xs : Vec A Nat.zero) : Vec A Nat.zero\n  deriving BEq\n" ++
  "inductive L where\n  | nil\n  | cons (n : Nat) (t : L)\n  deriving DecidableEq\n" ++
  "inductive R where\n  | mk (r : R)\n  deriving Inhabited\n" ++
  "def myD (x y : String) : String := x\nattribute [deriver Foo] myD\n" ++
  "class Bar (A : Type) where\n  bar : A → Nat\n" ++
  "def myDeriver (n : String) : String := n\nattribute [deriver Bar] myDeriver\n" ++
  "deriving instance Bar for Nat\n" ++
  "mutual\ninductive A where\n  | a\ninductive B where\n  | b (x : A)\n  deriving BEq\nend\n"

def selfhostDerivingNegExpected : String :=
  "Inhabited : (x0 : U0) → U0\nInhabited.default : (x0 :0 U0) → (x1 : (Inhabited x0)) → x0\nBEq : (x0 : U0) → U0\nBEq.beq : (x0 :0 U0) → (x1 : (BEq x0)) → (x2 : x0) → (x3 : x0) → Bool\nRepr : (x0 : U0) → U0\nRepr.reprPrec : (x0 :0 U0) → (x1 : (Repr x0)) → (x2 : x0) → (x3 : Nat) → String\nDecidableEq : (x0 : U0) → U0\nDecidableEq.decide : (x0 :0 U0) → (x1 : (DecidableEq x0)) → (x2 : x0) → (x3 : x0) → Bool\nOrdering : U0\nCompare : (x0 : U0) → U0\nCompare.compare : (x0 :0 U0) → (x1 : (Compare x0)) → (x2 : x0) → (x3 : x0) → Ordering\ninstInhabited : (Inhabited Nat)\ninstInhabited1 : (Inhabited Bool)\nBool.beqE : (x0 : Bool) → (x1 : Bool) → Bool\ninstBEq : (BEq Nat)\ninstBEq1 : (BEq Bool)\ninstDecidableEq : (DecidableEq Nat)\ninstDecidableEq1 : (DecidableEq Bool)\ninstRepr : (Repr Nat)\ninstRepr1 : (Repr Bool)\nNat.compare : (x0 : Nat) → (x1 : Nat) → Ordering\ninstCompare : (Compare Nat)\nBool.cmp : (x0 : Bool) → (x1 : Bool) → Ordering\ninstCompare1 : (Compare Bool)\nSize : (x0 : U0) → U0\nSize.size : (x0 :0 U0) → (x1 : (Size x0)) → (x2 : x0) → Nat\nerror: no deriver for Size (register one with `attribute [deriver Size] f`)\nerror: deriving BEq for Vec: indexed families are not supported\nerror: deriving DecidableEq for L: DecidableEq is derived for an enumeration or a single-constructor record only, and L\nerror: deriving Inhabited for R: every constructor of R is recursive or has a proof field\nmyD : (x0 : String) → (x1 : String) → String\nerror: myD is not a deriver: it takes 2 arguments, expected one (String → MacroM (List Syntax))\nBar : (x0 : U0) → U0\nBar.bar : (x0 :0 U0) → (x1 : (Bar x0)) → (x2 : x0) → Nat\nmyDeriver : (x0 : String) → String\nerror: deriving Bar for Nat: the deriver myDeriver cannot be run (this frontend has no elaboration-time evaluator; the derivers it runs are deriveInhabited, deriveBEq, deriveRepr, deriveDecidableEq and deriveCompare)\nerror: deriving BEq for B: a mutual inductive is not supported (the host derives for the joint family, an indexed family); derive each member's instances by hand\n"

/-- (A11, D6) The self-hosted driver's `check` reports a refused derivation at the
command's position, in the host's message shape. -/
def selfhostDerivingSpan : String :=
  "import Prelude\nclass Size (A : Type) where\n  size : A → Nat\nderiving instance Size for Nat\n"

def selfhostDerivingSpanExpected : String :=
  "input.wiz:4:1: error: no deriver for Size (register one with `attribute [deriver Size] f`)\n"

/-- (A11) `deriving` rejects what it cannot do, with the message naming the class and the
type (the command's offset, as every command's, becomes `file:line:col` in the driver's
diagnostics): a field with no `BEq` instance, and a class with no deriver. -/
def selfhostDerivingBad : String :=
  "import Prelude\nclass BEq (A : Type) where\n  beq : A → A → Bool\n" ++
  "structure Bad where\n  f : Nat → Nat\n  deriving BEq\n" ++
  "class Size (A : Type) where\n  size : A → Nat\nderiving instance Size for Nat\n"

def selfhostDerivingBadExpected : String :=
  "BEq : (x0 : U0) → U0\nBEq.beq : (x0 :0 U0) → (x1 : (BEq x0)) → (x2 : x0) → (x3 : x0) → Bool\nerror: failed to synthesize an instance of (BEq ((((((((((((((((((?m0 x✝0) x✝1) j✝) i✝) xs✝) ih✝) rest✝) ihs✝) _) j✝) i✝) xs✝) ih✝) rest✝) ihs✝) _) a✝0) b✝0))\nSize : (x0 : U0) → U0\nSize.size : (x0 :0 U0) → (x1 : (Size x0)) → (x2 : x0) → Nat\nerror: no deriver for Size (register one with `attribute [deriver Size] f`)\n"

/-- (#422) Programs whose `match` (or `if`) scrutinee is closed and costly: `fib k n` doubles
`n` `k` times by recursion (2^k calls). The scrutinee is an argument (`IO.println`, `f`), a
postponed argument (`pick`: its type is a metavariable until `"x"` fixes it), a
`let`-bound variable's use in an argument, and an `if`. The self-hosted frontend used to
evaluate such a match while it compiled (the codomain at the argument, `let` values and
postponed arguments were evaluated eagerly), so its time grew with `fib`'s. -/
def closedScrutProgram (k : Nat) : String :=
  "import Std\ndef fib : Nat → Nat → Nat\n  | .zero, n => n\n  | .succ k, n => Nat.add (fib k n) (fib k n)\n" ++
  "def f (x : String) : String := x\n" ++
  "def pick {A : Type} (a : A) (b : A) : A := a\n" ++
  s!"def a : IO Unit := IO.println (match Nat.beq (fib {k} 1) 0 with\n  | .true => \"z\"\n  | .false => \"nz\")\n" ++
  s!"def b : String := f (if Nat.beq (fib {k} 1) 0 then \"z\" else \"nz\")\n" ++
  s!"def c : String := pick (match Nat.beq (fib {k} 1) 0 with\n  | .true => \"z\"\n  | .false => \"nz\") \"x\"\n" ++
  s!"def d : String := let r := Nat.beq (fib {k} 1) 0; f (match r with\n  | .true => \"z\"\n  | .false => \"nz\")\n" ++
  "def main : IO Unit := do\n  a;\n  IO.println b;\n  IO.println c;\n  IO.println d\n"

/-- (#422) `closedScrutProgram 40` through the self-hosted compiler, `check` and then the
one-shot C, each within `secs`: evaluating any of its scrutinees (2^40 calls) would not
finish. The program is not run. -/
def selfhostClosedScrutBounded (secs : Nat) : IO Unit := do
  match ← selfhostCompiler with
  | .error e =>
    if (e.splitOn "gmp.h").length > 1 then skip "no toolchain" else throw (IO.userError e)
  | .ok exe =>
    let dir ← IO.FS.createTempDir
    IO.FS.writeFile (dir / "input.wiz") (closedScrutProgram 40)
    for (label, args) in [("check", #[exe.toString, "check", "input.wiz"]), ("the one-shot compile", #[exe.toString])] do
      let t0 ← IO.monoMsNow
      let out ← IO.Process.output { cmd := "timeout", args := #[toString secs] ++ args, cwd := dir }
      let t1 ← IO.monoMsNow
      unless out.exitCode == 0 do
        throw (IO.userError s!"{label}: exit {out.exitCode} after {t1 - t0} ms (124 is over {secs} s: the closed scrutinees were evaluated while compiling, #422): {out.stderr.take 2000}")
      -- (a stub that echoed its input would pass the exit code: demand the real output)
      if label == "check" then checkChecked (closedScrutProgram 40) out.stdout
      else unless (out.stdout.splitOn "int main").length > 1 do
        throw (IO.userError s!"{label}: the compiler printed no C:\n{out.stdout.take 500}")
      note s!"#422 {label}: {t1 - t0} ms"

/-- The host frontend elaborates the two programs the cases below compile. A break in
`selfhost/*.wiz` used to surface only when a case built one (a merge left a `)` out of
`knownTopFlag`'s `Bool.or` chain; `classCmd` had a `match` arm whose type the host would
not infer), minutes into an already heavy shard. This case reads the same files and calls
the same `checkerSource`/`compilerSource` the builders do, but stops at the host frontend:
no kernel evaluation, no C toolchain, and the first errors print with their positions.
The compiler's buffer comes first and a failure there short-circuits: it holds every
shared file (the frontend and the tables) and the driver, so both incidents surface in
its half of the ~50 s, not after the checker's. -/
def selfhostHostGuard : IO Unit := do
  let loader ← selfhostLoader
  let checkProg (what : String) (prog : String) : IO (List String) := do
    let s := runFrontend (R := ZeroOneMany) prog { loader, trustedModule := Tests.libModule }
    let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render prog
    if errs.isEmpty then pure [] else
      pure (s!"the host frontend rejects the self-hosted {what} ({errs.size} error(s)):"
        :: errs.toList.take 5)
  let check (what : String) (files : List String) (source : List String → String) : IO (List String) := do
    let srcs ← files.mapM (fun (f : String) => IO.FS.readFile f)
    checkProg what (source srcs)
  let bad ← check "compiler" Selfhost.compilerFiles Selfhost.compilerSource
  -- (`Check.wiz` is the only file of the checker's buffer the compiler's does not have)
  let bad ← if bad.isEmpty then check "checker" Selfhost.checkerFiles Selfhost.checkerSource
    else pure bad
  -- (`web/playground-exports.wiz` is built only by the `wiz-playground` derivation:
  -- neither `lake build` nor `=selfhost` sees it, so a frontend signature change can
  -- leave it behind. Check the engine's exact buffer here, as `build-playground.sh`
  -- assembles it: the frontend's files, the tables, then the export.)
  let bad ← if bad.isEmpty then do
    let srcs ← Selfhost.frontendFiles.mapM (fun (f : String) => IO.FS.readFile f)
    let tables ← IO.FS.readFile "selfhost/Tables.wiz"
    let exports ← IO.FS.readFile "web/playground-exports.wiz"
    let prog := "import IO\nimport Std\n" ++ String.join (srcs.map Selfhost.strip) ++ tables ++ exports
    checkProg "playground export" prog
    else pure bad
  unless bad.isEmpty do throw (IO.userError ("\n".intercalate bad))

/-- (A23) `#print axioms` on the forms the host distinguishes: a definition with no
axioms, a chain to an axiom, an axiom, an inductive type and its constructor, an
`implemented_by` target (walked as code and marked `native`), a `sealed` type's native
representation (`native T := mk/get`), and a foreign function. -/
def axiomsPrintProgram : String :=
  "import Prelude\n" ++
  "def base : Nat := 1\n" ++
  "axiom a : Nat\naxiom b : Nat\n" ++
  "def g : Nat := Nat.add a b\ndef h : Nat := g\n" ++
  "inductive T where\n  | mk (x : Nat)\n" ++
  "def mkT : T := T.mk 1\n" ++
  "def model (n : Nat) : Nat := n\ndef fast (n : Nat) : Nat := n + 1\n" ++
  "attribute [implemented_by fast] model\n" ++
  "def slow (n : Nat) : Nat := n\ndef fastA (n : Nat) : Nat := n + a\n" ++
  "attribute [implemented_by fastA] slow\n" ++
  "sealed inductive U where\n  | private mk (n : Nat)\n" ++
  "def umk (n : Nat) : U := U.mk n\n" ++
  "def uget (u : U) : Nat := match u with | .mk n => n\n" ++
  "attribute [implemented_by umk uget] U.mk\n" ++
  "def useU : Nat := uget (umk 3)\n" ++
  "extern \"strlen\" (header := \"string.h\") strlen : String → Nat\n" ++
  "def myLen : Nat := strlen \"abc\"\n" ++
  "#print axioms base\n#print axioms g\n#print axioms h\n#print axioms a\n" ++
  "#print axioms mkT\n#print axioms model\n#print axioms slow\n" ++
  "#print axioms useU\n#print axioms myLen\n#print axioms strlen\n"

/-- (B18) The trust ledger's view of `#print axioms`: a definition's *dependency* (here
`h`'s value uses `g`, whose value uses the axiom `a`) must still be listed. The selfhost
toolchain has no checked-in ledger (`.github/trust-baseline.tsv` covers `lib/`), so this
line is what makes what a run trusted visible; a walk that stopped at a definition's own
constants prints `'h' does not depend on any axioms` instead, and the ledger would
silently lose the row. -/
def axiomsDependencyProgram : String :=
  "import Prelude\n" ++
  "axiom a : Nat\n" ++
  "def g : Nat := Nat.add a a\n" ++
  "def h : Nat := g\n" ++
  "#print axioms h\n"

def axiomsDependencyExpected : String := "a : Nat\ng : Nat\nh : Nat\n'h' depends on axioms: [a]\n"

/-- (A23) `#print axioms` on partial definitions: the body is walked only where the host
walks the implementation (an `implemented_by` target), never from a type or a value, so
`loopA` and its users depend on nothing while `modelA` (implemented by `loopA`) lists
`pa`. -/
def partialAxiomsProgram : String :=
  "import Prelude\n" ++
  "axiom pa : Nat\n" ++
  "partial (default := 0) def loop : Nat := loop\n" ++
  "partial (default := 0) def loopA : Nat := pa\n" ++
  "def usesLoopA : Nat := loopA\n" ++
  "def modelA : Nat := 0\n" ++
  "attribute [implemented_by loopA] modelA\n" ++
  "#print axioms loop\n#print axioms loopA\n#print axioms usesLoopA\n#print axioms modelA\n"

/-- (A23) `set_option`: the two printing options take `true`/`false`, a bad value and an
unknown option are the same errors as the host's, and the accepted ones change nothing
(the self-hosted printer has no notation to switch). -/
def setOptionProgram : String :=
  "import Prelude\n" ++
  "set_option pp.notation false\nset_option pp.all true\n" ++
  "def f : Nat := 1\n#print axioms f\n" ++
  "set_option pp.notation maybe\n" ++
  "set_option pp.all 1\n" ++
  "set_option pp.other true\n" ++
  "set_option pp.notation false\n#print axioms f\n"

/-- (B13) A *source-level* numeral: the frontend does not emit `Tm.nlit`/`Tm.natFn` yet
(`natLitDigits`/`natRegistered` is the hook), so `2` still elaborates as
`Nat.succ (Nat.succ Nat.zero)` and `#reduce` prints the constructor, not `2`. The kernel's
literal rules are exercised separately by the `(E-K) Kernel.wiz literals` cases, which
hand `Kernel.wiz` hand-written `nlit`/`natFn` terms. This is the source side: if the
frontend starts emitting literals, `#reduce 2` prints `2` and this case fails (promote it,
and extend the backend, which has no `nlit` case yet). -/
def numeralSourceProgram : String := "import Prelude\n#reduce 2\n"

def numeralSourceExpected : String :=
  "con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt))))\n"

/-- (C14, D9) The driver's side of the trust flag: the one-shot compiler's driver takes no
`--trust-native`, so a `native_refl` body is refused by default. `--trust-native` is a
checker flag (the C14 cases above drive the checker); the driver recognises it as an
unknown flag. A regression that enabled trust by default would compile this file (exit 0,
C on stdout) and fail the case. -/
def nativeReflDriverProgram : String :=
  "import Prelude\n" ++
  "def sumTo : Nat → Nat\n  | .zero => 0\n  | .succ n => Nat.add (Nat.succ n) (sumTo n)\n" ++
  "def s : sumTo 3 = 6 := native_refl\n"

def nativeReflDriverExpected : String :=
  "error: native evaluation is not enabled: `native_refl` decides an equation by running compiled code, which the kernel does not check; run with --trust-native to allow it\n"

-- ------------------------------------------------------------------------------------
-- (A17/A18) Surface syntax: list literals, `&&`/`||`, as-patterns, tuple patterns,
-- `let (x, y)`, `let ()`. The host and the self-hosted frontend compile each program,
-- and their outputs must agree.

/-- (A17) List literals, including nested and empty lists and a literal pattern. -/
def surfaceListProgram : String :=
  "import Prelude\nimport IO\n" ++
  "def sum : List Nat → Nat\n  | .nil => 0\n  | .cons x xs => x + sum xs\n" ++
  "def sum3 : List (List Nat) → Nat\n  | .nil => 0\n  | .cons l ls => sum l + sum3 ls\n" ++
  "def two : List Nat → Nat\n  | [x, y] => x * 10 + y\n  | _ => 0\n" ++
  "def mapS (f : Nat → Nat) : List Nat → List Nat\n  | .nil => .nil\n  | .cons x xs => .cons (f x) (mapS f xs)\n" ++
  "def empty : List Nat := []\n" ++
  "def main : IO Unit := do\n" ++
  "  IO.println (Nat.toString (sum [1, 2, 3, 4]));\n" ++
  "  IO.println (Nat.toString (List.length empty));\n" ++
  "  IO.println (Nat.toString (sum3 [[1, 2], [], [3, 4, 5]]));\n" ++
  "  IO.println (Nat.toString (two [6, 7]));\n" ++
  "  IO.println (Nat.toString (two [8]));\n" ++
  "  IO.println (Nat.toString (sum (mapS (fun x => x + 1) [1, 2, 3])))\n"

/-- (A17) `&&`/`||` short-circuit and bind as on the host (`!` too). -/
def surfaceBoolProgram : String :=
  "import Prelude\nimport IO\n" ++
  "partial def boom : Bool := boom\n" ++
  "def main : IO Unit := do\n" ++
  "  IO.println (if Bool.true && Bool.false then \"t\" else \"f\");\n" ++
  "  IO.println (if Bool.false && boom then \"boom\" else \"short\");\n" ++
  "  IO.println (if Bool.true || boom then \"short\" else \"boom\");\n" ++
  "  IO.println (if !Bool.false then \"not\" else \"no\");\n" ++
  "  IO.println (if Bool.true || Bool.false && Bool.false then \"prec\" else \"bad\");\n" ++
  "  IO.println (if (Bool.false && boom) || Bool.true then \"mixed\" else \"no\");\n" ++
  "  IO.println (Nat.toString (if Bool.true && Bool.true then 1 else 0))\n"

/-- (A18) As-patterns: over a constructor in equations and in a `match`, in a tuple, and
`x@y` over a variable. -/
def surfaceAsProgram : String :=
  "import Prelude\nimport IO\n" ++
  "inductive T where\n  | leaf (n : Nat)\n  | node (l : T) (r : T)\n" ++
  "def size : T → Nat\n  | .leaf _ => 1\n" ++
  "  | t@(.node l r) => size l + size r + (match t with\n" ++
  "      | .node _ _ => 0\n      | .leaf _ => 0)\n" ++
  "def headOr (d : Nat) : List Nat → Nat\n" ++
  "  | xs@(.cons x _) => x + (match xs with\n      | .cons y _ => y\n      | .nil => 0)\n" ++
  "  | .nil => d\n" ++
  "def sumP (p : Nat × Nat) : Nat := match p with\n  | (x@a, y@b) => x + y + a + b\n" ++
  "def dup (n : Nat) : Nat := match n with\n  | k@_ => k + k\n" ++
  "def main : IO Unit := do\n" ++
  "  IO.println (Nat.toString (size (.node (.leaf 1) (.node (.leaf 2) (.leaf 3)))));\n" ++
  "  IO.println (Nat.toString (headOr 0 (.cons 5 .nil)));\n" ++
  "  IO.println (Nat.toString (headOr 9 .nil));\n" ++
  "  IO.println (Nat.toString (sumP (3, 4)));\n" ++
  "  IO.println (Nat.toString (dup 6))\n"

/-- (A18) Tuple patterns: a pair, a right-nested triple, a tuple rebuilt, and a tuple in
a list. -/
def surfaceTupleProgram : String :=
  "import Prelude\nimport IO\n" ++
  "def fstP (p : Nat × Nat) : Nat := match p with\n  | (a, b) => a\n" ++
  "def three : Nat × (Nat × Nat) → Nat\n  | (a, (b, c)) => a * 100 + b * 10 + c\n" ++
  "def swap : Nat × Nat → Nat × Nat\n  | (a, b) => (b, a)\n" ++
  "def head : List (Nat × Nat) → Nat\n  | .nil => 0\n  | .cons (a, _) _ => a\n" ++
  "def main : IO Unit := do\n" ++
  "  IO.println (Nat.toString (fstP (3, 4)));\n" ++
  "  IO.println (Nat.toString (three (1, (2, 3))));\n" ++
  "  IO.println (Nat.toString (match swap (5, 6) with\n    | (a, b) => a + b));\n" ++
  "  IO.println (Nat.toString (head (.cons (7, 8) .nil)))\n"

/-- (A18) `let (x, y) := e; b`, including three components and a nested pair. -/
def surfaceLetPairProgram : String :=
  "import Prelude\nimport IO\n" ++
  "def addP (p : Nat × Nat) : Nat :=\n  let (x, y) := p;\n  x + y\n" ++
  "def three (p : Nat × (Nat × Nat)) : Nat :=\n  let (a, b, c) := p;\n  a * 100 + b * 10 + c\n" ++
  "def nested (p q : Nat × Nat) : Nat :=\n  let (x, y) := p;\n  let (u, v) := q;\n  (x + y) * 10 + (u + v)\n" ++
  "def main : IO Unit := do\n" ++
  "  IO.println (Nat.toString (addP (3, 4)));\n" ++
  "  IO.println (Nat.toString (three (1, (2, 3))));\n" ++
  "  IO.println (Nat.toString (nested (10, 20) (1, 2)))\n"

/-- (A18) `let () := u; b` (the kernel's unit eliminator). -/
def surfaceLetUnitProgram : String :=
  "import Prelude\nimport IO\n" ++
  "def use (u : Unit) : Nat :=\n  let () := u;\n  7\n" ++
  "def twice (n : Nat) : Nat :=\n  let () := ();\n  n + n\n" ++
  "def through (u : Unit) (n : Nat) : Nat :=\n  let () := u;\n  n * 3\n" ++
  "def main : IO Unit := do\n" ++
  "  IO.println (Nat.toString (use ()));\n" ++
  "  IO.println (Nat.toString (twice 21));\n" ++
  "  IO.println (Nat.toString (through () 5))\n"
/-- (E-K) A natural-number type for `Kernel.wiz`'s number literals, written as kernel terms:
`N` (the description `arg Enum2 [ret, rec ret]`), its constructors, and definitions by
`ind` (`N.pred`, `N.add`, `N.sub`, `N.mul`, `N.isZero`, `N.beq`, `N.blt`; `N.div` and
`N.mod` are axioms, which an operation may be). `lit n` is a literal of the registration
`nb`, `unary n` is `N.succ` applied `n` times, `op o` is the registered operation `o`. -/
def ekNatDefs : String :=
  "def uT : Tm := .unit (ln 1)\n" ++
  "def eT : Tm := .lam (.ecase (.descr (ln 0) uT) (.var 0) (.tcons (.dret .star) (.tcons (.drec (.qlit .qw) .star (.dret .star)) .tnil)))\n" ++
  "def dT : Tm := .darg (.qlit .qw) (.enum 2) eT\n" ++
  "def mkC (n : String) (v ty : Tm) : Tm := .const n .nil .nil (markClosed v (sortsTy ty)) (sortsTy ty)\n" ++
  "def nC : Tm := mkC \"N\" (.mu (ln 0) uT dT .star) (.univ 0)\n" ++
  "def zC : Tm := mkC \"N.zero\" (.ann (.con (.pair (.tag 2 0) (.pair .star .star))) nC) nC\n" ++
  "def sC : Tm := mkC \"N.succ\" (.lam (.con (.pair (.tag 2 1) (.pair (.var 0) (.pair .star .star))))) (piH nC nC)\n" ++
  "def nb : NatB := .mk nC zC sC\n" ++
  "def lit (n : Nat) : Tm := .nlit (knOfNat n) nb\n" ++
  "def litS (s : String) : Tm := .nlit (knOfDigits s) nb\n" ++
  "def unary : Nat → Tm\n" ++
  "  | .zero => zC\n" ++
  "  | .succ k => .app sC (unary k)\n" ++
  "def famX : Tm := .lam (.mu (ln 0) uT dT (.var 0))\n" ++
  "def motN : Tm := .lam (.lam nC)\n" ++
  "def recMot : Tm := .pi .qw .lhole .lhole (interpApp (ln 0) uT (.app eT (.var 0)) famX .star)\n" ++
  "  (.pi .qw .lhole .lhole (tApps (allTm (ln 0) (ln 1)) (args6 uT dT famX motN .star (.pair (.var 1) (.var 0)))) nC)\n" ++
  "def iter (z : Tm) (s : Tm → Tm → Tm) (x : Tm) : Tm :=\n" ++
  "  .ind (ln 0) uT dT (ln 1) motN (.lam (.lam (.lam (.app (.app (.ecase recMot (.fst (.var 1))\n" ++
  "    (.tcons (.lam (.lam z)) (.tcons (.lam (.lam (s (.fst (.var 1)) (.fst (.var 0))))) .tnil))) (.snd (.var 1))) (.var 0))))) .star x\n" ++
  "def n2n : Tm := piH nC nC\n" ++
  "def n3n : Tm := piH nC (piH nC nC)\n" ++
  "def app2 (f a b : Tm) : Tm := .app (.app f a) b\n" ++
  "def predC : Tm := mkC \"N.pred\" (.lam (iter zC (fun f _ => f) (.var 0))) n2n\n" ++
  "def addC : Tm := mkC \"N.add\" (.lam (.lam (iter (.var 5) (fun _ ih => .app sC ih) (.var 1)))) n3n\n" ++
  "def subC : Tm := mkC \"N.sub\" (.lam (.lam (iter (.var 6) (fun _ ih => .app predC ih) (.var 0)))) n3n\n" ++
  "def mulC : Tm := mkC \"N.mul\" (.lam (.lam (iter zC (fun _ ih => app2 addC (.var 5) ih) (.var 1)))) n3n\n" ++
  "def isZeroC : Tm := mkC \"N.isZero\" (.lam (.ind (ln 0) uT dT (ln 1) (.lam (.lam (.enum 2))) (.lam (.lam (.lam (.fst (.var 1))))) .star (.var 0))) (piH nC (.enum 2))\n" ++
  "def beqC : Tm := mkC \"N.beq\" (.lam (.lam (.app isZeroC (app2 addC (app2 subC (.var 1) (.var 0)) (app2 subC (.var 0) (.var 1)))))) (piH nC (piH nC (.enum 2)))\n" ++
  "def bltC : Tm := mkC \"N.blt\" (.lam (.lam (.app isZeroC (app2 subC (.app sC (.var 1)) (.var 0))))) (piH nC (piH nC (.enum 2)))\n" ++
  "def divC : Tm := .axiomC \"N.div\" (sortsTy n3n)\n" ++
  "def modC : Tm := .axiomC \"N.mod\" (sortsTy n3n)\n" ++
  "def op (o : NatOp) : Tm := match o with\n" ++
  "  | .nsucc => .natFn o nb sC\n" ++
  "  | .npred => .natFn o nb predC\n" ++
  "  | .nadd => .natFn o nb addC\n" ++
  "  | .nsub => .natFn o nb subC\n" ++
  "  | .nmul => .natFn o nb mulC\n" ++
  "  | .ndiv => .natFn o nb divC\n" ++
  "  | .nmod => .natFn o nb modC\n" ++
  "  | .nbeq => .natFn o nb beqC\n" ++
  "  | .nblt => .natFn o nb bltC\n" ++
  "def op2 (o : NatOp) (a b : Tm) : Tm := app2 (op o) a b\n" ++
  "def verdict (r : TyRes) : String := match r with\n" ++
  "  | .ok ty _ => show .nil 0 (quote 0 ty)\n" ++
  "  | .err m => String.append \"error: \" m\n" ++
  "def okErr (r : TyRes) : String := match r with\n" ++
  "  | .ok _ _ => \"ok\"\n" ++
  "  | .err _ => \"error\"\n" ++
  "def tyOf (t : Tm) : String := verdict (infer empty (sortsInfer t))\n" ++
  "def prfOk (t : Tm) : String := verdict (infer (TCtx.inProof empty) (sortsInfer t))\n" ++
  "def chkPrf (t ty : Tm) : String := match check (TCtx.inProof empty) (sortsInfer t) (eval .nil (sortsInfer ty)) with\n" ++
  "  | .ok _ _ => \"ok\"\n" ++
  "  | .err m => String.append \"error: \" m\n" ++
  "def nf (t : Tm) : String := match infer empty (sortsInfer t) with\n" ++
  "  | .ok _ _ => normalize t\n" ++
  "  | .err m => String.append \"error: \" m\n" ++
  "def hnf (t : Tm) : String := match infer empty (sortsInfer t) with\n" ++
  "  | .ok _ _ => show .nil 0 (quote 0 (whnf (eval .nil (sortsInfer t))))\n" ++
  "  | .err m => String.append \"error: \" m\n" ++
  "def eqN (a b : Tm) : Tm := .ann (.eqRefl nC a) (.eq nC a b)\n" ++
  "def vecC : Tm := .axiomC \"Vec\" (sortsTy (piH nC (.univ 0)))\n" ++
  "def vecId (a b : Tm) : Tm := .ann (.lam (.var 0)) (piH (.app vecC a) (.app vecC b))\n" ++
  -- (B13) the value of a term as it is read back, without `whnf` (`quote`, not `nf`)
  "def readBack (t : Tm) : String := show .nil 0 (quote 0 (eval .nil (sortsInfer t)))\n" ++
  -- (B13) a definition's glued value: a constant whose value is the literal 2
  "def twoC : Tm := mkC \"N.two\" (lit 2) nC\n" ++
  -- (B13) `Nat.pow 2 (Nat.pow 2 28)`, a plain definition (`nat.pow` is not one of the
  -- native operations here): computing it is the huge numeral, so a comparison that only
  -- asks whether two applications are the same must not force it
  "def powC : Tm := mkC \"Nat.pow\" (.lam (.lam (iter (lit 1) (fun _ ih => app2 mulC (.var 6) ih) (.var 0)))) n3n\n" ++
  "def printAll : List String → IO Unit\n" ++
  "  | .nil => IO.pure ()\n" ++
  "  | .cons s ss => do\n" ++
  "    IO.println s;\n" ++
  "    printAll ss\n"

/-- (E-K) A `main` printing each Wiz expression (a `String`) of `calls`. -/
def ekMain (calls : List String) : String :=
  "def main : IO Unit := printAll " ++ calls.foldr (fun c acc => s!"(.cons ({c}) {acc})") ".nil" ++ "\n"

/-- (E-K) Literal arithmetic by reduction: the registered operations on literals, natively
(exact past 64 bits), the zero shortcuts, the stuck applications. -/
def ekArithCalls : List String :=
    ["tyOf (lit 5)",
     "nf (op2 .nadd (lit 2) (lit 3))",
     "nf (op2 .nmul (lit 6) (lit 7))",
     "nf (op2 .nsub (lit 3) (lit 5))",
     "nf (op2 .nsub (lit 10) (lit 4))",
     "nf (op2 .ndiv (lit 17) (lit 5))",
     "nf (op2 .nmod (lit 17) (lit 5))",
     "nf (op2 .ndiv (lit 7) (lit 0))",
     "nf (op2 .nmod (lit 7) (lit 0))",
     "nf (op2 .nbeq (lit 4) (lit 4))",
     "nf (op2 .nbeq (lit 4) (lit 5))",
     "nf (op2 .nblt (lit 3) (lit 4))",
     "nf (op2 .nblt (lit 4) (lit 3))",
     "nf (.app (op .nsucc) (lit 9))",
     "nf (.app (op .npred) (lit 0))",
     "nf (op2 .nmul (lit 4294967296) (lit 4294967296))",
     "nf (op2 .nsub (litS \"18446744073709551616\") (lit 1))",
     "nf (op2 .nmul (litS \"123456789012345678901234567890\") (litS \"987654321098765432109876543210\"))",
     "nf (op2 .ndiv (litS \"121932631137021795226185032733622923332237463801111263526900\") (litS \"987654321098765432109876543210\"))",
     "nf (op2 .nmod (litS \"121932631137021795226185032733622923332237463801111263526901\") (litS \"987654321098765432109876543210\"))",
     "nf (op2 .nmul (lit 0) (unary 2))",
     "nf (op2 .nadd (lit 0) (unary 2))",
     "nf (op2 .nsub (unary 2) (lit 0))",
     "nf (op2 .nadd (unary 2) (lit 3))",
     "nf (.app (op .nsucc) (unary 1))",
     "nf (.app (op .nadd) (lit 2))",
     "nf (.ann (.lam (op2 .nsub (.var 0) (lit 3))) n2n)"]
def ekArithExpected : String := "N\n5\n42\n0\n6\n3\n2\n0\n7\n#0\n#1\n#0\n#1\n10\n0\n18446744073709551616\n18446744073709551615\n121932631137021795226185032733622923332237463801111263526900\n123456789012345678901234567890\n1\n0\ncon((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt))))\ncon((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt))))\ncon((#1, (con((#1, (3, (tt, tt)))), (tt, tt))))\ncon((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt))))\n(N.add 2)\nλx0. ((N.sub x0) 3)\n"

/-- (E-K) Literals and unary numerals are convertible both ways: the equation, conversion
(a neutral `Vec n`), and the eliminators looking inside a literal. -/
def ekConvCalls : List String :=
    ["prfOk (eqN (lit 3) (unary 3))",
     "prfOk (eqN (unary 3) (lit 3))",
     "prfOk (eqN (op2 .nadd (lit 2) (lit 3)) (unary 5))",
     "prfOk (eqN (app2 addC (unary 2) (lit 3)) (lit 5))",
     "prfOk (eqN (app2 mulC (lit 3) (lit 4)) (lit 12))",
     "prfOk (eqN (lit 0) zC)",
     "tyOf (vecId (lit 3) (unary 3))",
     "tyOf (vecId (unary 3) (lit 3))",
     "tyOf (vecId (op2 .nadd (lit 1) (lit 2)) (.app sC (lit 2)))",
     "tyOf (vecId (app2 subC (lit 5) (lit 2)) (lit 3))",
     "hnf (.app isZeroC (lit 0))",
     "hnf (.app isZeroC (lit 7))",
     "hnf (.app predC (lit 10))"]
def ekConvExpected : String := "True\nTrue\nTrue\nTrue\nTrue\nTrue\n(x0 : (Vec 3)) → (Vec (N.succ (N.succ (N.succ N.zero))))\n(x0 : (Vec (N.succ (N.succ (N.succ N.zero))))) → (Vec 3)\n(x0 : (Vec 3)) → (Vec (N.succ 2))\n(x0 : (Vec ((N.sub 5) 2))) → (Vec 3)\n#0\n#1\n9\n"

/-- (E-K) Rejections: different numbers, a literal at another type, an ill-typed
registration, an operation registered at the wrong type or with a non-constant. -/
def ekRejectCalls : List String :=
    ["okErr (infer (TCtx.inProof empty) (sortsInfer (eqN (lit 3) (unary 4))))",
     "okErr (infer (TCtx.inProof empty) (sortsInfer (eqN (unary 4) (lit 3))))",
     "okErr (infer (TCtx.inProof empty) (sortsInfer (eqN (op2 .nadd (lit 2) (lit 2)) (lit 5))))",
     "okErr (infer empty (sortsInfer (vecId (lit 3) (unary 4))))",
     "okErr (infer empty (sortsInfer (vecId (lit 2) (lit 3))))",
     "tyOf (.ann (lit 3) (.enum 2))",
     "tyOf (.nlit (knOfNat 1) (.mk nC sC sC))",
     "tyOf (.nlit (knOfNat 1) (.mk nC zC zC))",
     "tyOf (.nlit (knOfNat 1) (.mk (.univ 0) zC sC))",
     "tyOf (.natFn .nadd nb predC)",
     "tyOf (.natFn .nadd nb (lit 3))"]
def ekRejectExpected : String := "error\nerror\nerror\nerror\nerror\nerror: type mismatch: expected Enum2, got N\nerror: the registered nat.zero is not a N\nerror: the registered nat.succ is not a function from and to N\nerror: numerals need `builtin nat`, `builtin nat.zero` and `builtin nat.succ` registered as definitions\nerror: nat.add is registered with a constant of the wrong type: N.pred\nerror: nat.add is registered with a term that is not a constant\n"

/-- (B13) A big literal, a `Nat` operation on a definition's glued value, the expansive
`Nat.pow 2 (Nat.pow 2 28)`, and a normal form that must compute: the host's rules
(`wiz-notes/kernel-lazy-let.md` §8.1, §8.4, §9.3) on the self-hosted kernel. -/
def ekLazyCalls : List String :=
    ["tyOf (litS \"123456789012345678901234567890\")",
     "nf (op2 .nadd (litS \"123456789012345678901234567890\") (lit 1))",
     "readBack (op2 .nadd twoC (lit 3))",
     "hnf (op2 .nadd twoC (lit 3))",
     "prfOk (eqN (op2 .nadd twoC (lit 3)) (lit 5))",
     "okErr (infer (TCtx.inProof empty) (sortsInfer (eqN (op2 .nadd twoC (lit 3)) (lit 6))))",
     "readBack (app2 powC (lit 2) (app2 powC (lit 2) (lit 28)))",
     "okErr (infer (TCtx.inProof empty) (sortsInfer (eqN (app2 powC (lit 2) (app2 powC (lit 2) (lit 28))) (app2 powC (lit 2) (app2 powC (lit 2) (lit 28))))))",
     "chkPrf (.eqRefl nC (app2 powC (lit 2) (app2 powC (lit 2) (lit 28)))) (.eq nC (app2 powC (lit 2) (app2 powC (lit 2) (lit 28))) (app2 powC (lit 2) (app2 powC (lit 2) (lit 28))))",
     "nf (op2 .nadd twoC (lit 3))"]
def ekLazyExpected : String :=
  "N\n123456789012345678901234567891\n((N.add N.two) 3)\n5\nTrue\nerror\n" ++
  "((Nat.pow 2) ((Nat.pow 2) 28))\nok\nok\n5\n"

/-- (E-K) The cost literals remove (`wiz-notes/elab-evaluator-plan.md` §3.5: the hygiene
mark `✝` is code 10013): the equation `77 * 130 + 3 = 10013`, once with the registered
operations on literals and once with the definitions on unary numerals. -/
def ekTimingDefs : String :=
  "def unaryWork : Tm := eqN (app2 addC (app2 mulC (unary 77) (unary 130)) (unary 3)) (unary 10013)\n" ++
  "def litWork : Tm := eqN (op2 .nadd (op2 .nmul (lit 77) (lit 130)) (lit 3)) (lit 10013)\n"

/-- The timing program: both verdicts and the two times in nanoseconds. -/
def ekTimingMain : String := ekTimingDefs ++
  "def main : IO Unit := do\n" ++
  "  t0 ← Clock.monotonic;\n" ++
  "  IO.println (prfOk litWork);\n" ++
  "  t1 ← Clock.monotonic;\n" ++
  "  IO.println (prfOk unaryWork);\n" ++
  "  t2 ← Clock.monotonic;\n" ++
  "  IO.println (String.append (Nat.toString (Duration.sub t1 t0).ns) (String.append \" \" (Nat.toString (Duration.sub t2 t1).ns)))\n"

/-- (E-K) The timing program's output: the equation holds both ways, and the literal path
is at least ten times faster than the unary one (the ratio, not the times, is the claim,
and the machine is shared). -/
def checkEkTiming (out : String) : IO Unit := do
  match out.splitOn "\n" with
  | l :: u :: t :: _ =>
    unless l == "True" && u == "True" do
      throw (IO.userError s!"the equation was not decided True both ways: {l} / {u}")
    match t.splitOn " " with
    | [a, b] => match a.toNat?, b.toNat? with
      | some lit, some unary =>
        -- (a generous bound: a light probe measured about 64 µs against 1.2 s)
        unless lit * 10 < unary do
          throw (IO.userError s!"literals were not 10 times faster: {lit} ns against {unary} ns")
      | _, _ => throw (IO.userError s!"unexpected timing line: {t}")
    | _ => throw (IO.userError s!"unexpected timing line: {t}")
  | _ => throw (IO.userError s!"unexpected output: {out}")


/-- The pipeline group: every case here runs the **self-hosted** compiler (`selfhostCompiler`)
or checker (`selfhostChecker`), and compares what it says. A case that only runs the Lean
host belongs in `selfhost-host`; the case that sets an echoing stub proves this group
cannot regress into cases that do not reach the pipeline. -/
def selfHostGroup : Group where
  name := "selfhost"
  exercise := "Stages 12b–14q (the self-hosted pipeline)"
  cases := [
    -- Y4: `Kernel.wiz` compares two constants by name, so a name has one declaration
    { name := "a name is declared once: a second declaration is an error (it proved an empty type inhabited)", run := fun _ =>
        selfhostCheckFile dupNames dupNamesExpected },
    { name := "a file of definitions, checked in Wiz", run := fun _ =>
        selfhostCheckFile ("def N : Type 1 := (A : Type) → (A → A) → A → A\ndef two : N := fun A s z => s (s z)\n" ++
          "def add (m n : N) : N := fun A s z => m A s (n A s z)\n#reduce add two two\n#check add two\n" ++
          "def bad : Type := Type\n#check bad\n")
          ("N : U1\ntwo : N\nadd : (x0 : N) → (x1 : N) → N\nλx0. λx1. λx2. (x1 (x1 (x1 (x1 x2))))\n" ++
          "(x0 : N) → N\n" ++
          "error: type mismatch: expected U0, got U1\nerror: unknown identifier bad\n") },
    { name := "inductive types, checked in Wiz", run := fun _ => do
        let file := "inductive Nat where\n  | zero\n  | succ (n : Nat)\ndef two : Nat := Nat.succ (Nat.succ Nat.zero)\n" ++
          "#check Nat.succ\n#reduce two\ninductive Pair where\n  | mk (a b : Nat)\n#check Pair.mk\n" ++
          "#reduce Pair.mk two Nat.zero\ninductive Bad where\n  | mk (f : Bad → Bad)\ndef bad : Nat := Nat.succ Type\n"
        selfhostCheckFile file ("Nat : U0\ntwo : Nat\n(x0 : Nat) → Nat\n" ++
          "con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt))))\n" ++
          "Pair : U0\n(x0 : Nat) → (x1 : Nat) → Pair\n" ++
          "con((#0, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (con((#0, (tt, tt))), (tt, tt)))))\n" ++
          s!"error: the type being defined may only occur as the type of a recursive field or the result\nerror: type mismatch: expected Nat, got U1\n") },
    { name := "pattern matching and structural recursion, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\ndef two : Nat := Nat.succ (Nat.succ Nat.zero)\ndef add (m n : Nat) : Nat := match m with\n  | .zero => n\n  | .succ k => Nat.succ (add k n)\n#reduce add two two\ndef mul (m n : Nat) : Nat := match n with\n  | .zero => Nat.zero\n  | .succ k => add m (mul m k)\n#reduce mul two (Nat.succ (Nat.succ (Nat.succ Nat.zero)))\ndef Code (n : Nat) : Type := match n with\n  | .zero => Nat\n  | _ => Nat → Nat\n#check Code\ndef pred (n : Nat) : Nat := match n with\n  | .succ k => k\n  | x => x\n#reduce pred two\ndef bad (n : Nat) : Nat := match n with\n  | .succ k => k\ndef bad2 (m n : Nat) : Nat := match m with\n  | .zero => n\n  | .succ k => add k (bad2 n k)\n"
          "Nat : U0\ntwo : Nat\nadd : (x0 : Nat) → (x1 : Nat) → Nat\ncon((#1, (con((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt))))\nmul : (x0 : Nat) → (x1 : Nat) → Nat\ncon((#1, (con((#1, (con((#1, (con((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt))))\nCode : (x0 : Nat) → U0\n(x0 : Nat) → U0\npred : (x0 : Nat) → Nat\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\nerror: missing case zero\nerror: unknown identifier bad2\n" },
    { name := "parameterised inductive types, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\ndef add (m n : Nat) : Nat := match m with\n  | .zero => n\n  | .succ k => Nat.succ (add k n)\ninductive List (A : Type) where\n  | nil\n  | cons (head : A) (tail : List A)\n#check List.cons\ndef one : Nat := Nat.succ Nat.zero\ndef xs : List Nat := List.cons one (List.cons Nat.zero List.nil)\ndef length (A : Type) (l : List A) : Nat := match l with\n  | .nil => Nat.zero\n  | .cons h t => Nat.succ (length A t)\n#reduce length Nat xs\ndef sum (l : List Nat) : Nat := match l with\n  | .nil => Nat.zero\n  | .cons h t => add h (sum t)\n#reduce sum xs\ndef append (A : Type) (l r : List A) : List A := match l with\n  | .nil => r\n  | .cons h t => List.cons h (append A t r)\n#reduce length Nat (append Nat xs xs)\ninductive Pair (A B : Type) where\n  | mk (a : A) (b : B)\ndef fst (A B : Type) (p : Pair A B) : A := match p with\n  | .mk a b => a\n#reduce fst Nat (List Nat) (Pair.mk one xs)\n"
          "Nat : U0\nadd : (x0 : Nat) → (x1 : Nat) → Nat\nList : (x0 : U0) → U0\n(x0 :0 U0) → (x1 : x0) → (x2 : (List x0)) → (List x0)\none : Nat\nxs : (List Nat)\nlength : (x0 : U0) → (x1 : (List x0)) → Nat\ncon((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt))))\nsum : (x0 : (List Nat)) → Nat\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\nappend : (x0 : U0) → (x1 : (List x0)) → (x2 : (List x0)) → (List x0)\ncon((#1, (con((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt))))\nPair : (x0 : U0) → (x1 : U0) → U0\nfst : (x0 : U0) → (x1 : U0) → (x2 : ((Pair x0) x1)) → x0\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\n" },
    { name := "definitions by equations, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\ninductive List (A : Type) where\n  | nil\n  | cons (head : A) (tail : List A)\ndef len (A : Type) : List A → Nat\n  | .nil => Nat.zero\n  | .cons h t => Nat.succ (len A t)\n#check len\n#reduce len Nat (List.cons Nat.zero List.nil)\ndef double : (n : Nat) → Nat\n  | .zero => Nat.zero\n  | .succ k => Nat.succ (Nat.succ (double k))\n#reduce double (Nat.succ Nat.zero)\n"
          "Nat : U0\nList : (x0 : U0) → U0\nlen : (x0 : U0) → (x1 : (List x0)) → Nat\n(x0 : U0) → (x1 : (List x0)) → Nat\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\ndouble : (x0 : Nat) → Nat\ncon((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt))))\n" },
    { name := "several scrutinees and nested patterns, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\ninductive Bool where\n  | false\n  | true\ndef eq : Nat → Nat → Bool\n  | .zero, .zero => Bool.true\n  | .succ m, .succ n => eq m n\n  | _, _ => Bool.false\ndef one : Nat := Nat.succ Nat.zero\ndef two : Nat := Nat.succ one\n#reduce eq two two\n#reduce eq two one\ninductive List (A : Type) where\n  | nil\n  | cons (head : A) (tail : List A)\ndef zipAdd : List Nat → List Nat → List Nat\n  | .cons a as, .cons b bs => List.cons (Nat.succ a) (zipAdd as bs)\n  | _, _ => List.nil\n#reduce zipAdd (List.cons one (List.cons two List.nil)) (List.cons Nat.zero List.nil)\ndef second (A : Type) (d : A) : List A → A\n  | .cons _ (.cons b _) => b\n  | _ => d\n#reduce second Nat Nat.zero (List.cons one (List.cons two List.nil))\ndef sub : Nat → Nat → Nat\n  | m, .zero => m\n  | .zero, _ => Nat.zero\n  | .succ m, .succ n => sub m n\n#reduce sub two one\ndef g : Nat → Nat\n  | .succ k => g k\n  | x => Nat.succ x\n#reduce g two\n"
          "Nat : U0\nBool : U0\neq : (x0 : Nat) → (x1 : Nat) → Bool\none : Nat\ntwo : Nat\ncon((#1, (tt, tt)))\ncon((#0, (tt, tt)))\nList : (x0 : U0) → U0\nzipAdd : (x0 : (List Nat)) → (x1 : (List Nat)) → (List Nat)\ncon((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (con((#0, (tt, tt))), (tt, tt)))))\nsecond : (x0 : U0) → (x1 : x0) → (x2 : (List x0)) → x0\ncon((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt))))\nsub : (x0 : Nat) → (x1 : Nat) → Nat\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\ng : (x0 : Nat) → Nat\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\n" },
    { name := "implicit arguments, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\ndef id {A : Type} (x : A) : A := x\n#check id\n#check id Nat.zero\n#reduce id (Nat.succ Nat.zero)\ndef const {A B : Type} (a : A) (b : B) : A := a\n#reduce const Nat.zero (Nat.succ Nat.zero)\ninductive List (A : Type) where\n  | nil\n  | cons (head : A) (tail : List A)\ndef one : List Nat := List.cons Nat.zero List.nil\n#check one\n#reduce one\ndef two : List Nat := List.cons (id Nat.zero) (List.cons (Nat.succ Nat.zero) List.nil)\n#reduce two\ndef twice {A : Type} (f : A → A) (x : A) : A := f (f x)\n#reduce twice Nat.succ Nat.zero\ndef bad : List Nat := List.nil\ndef bad2 : Nat := id List.nil\ndef map {A B : Type} (f : A → B) (l : List A) : List B := match l with\n  | .nil => List.nil\n  | .cons h t => List.cons (f h) (map f t)\n#reduce map Nat.succ (List.cons Nat.zero List.nil)\ndef length {A : Type} : List A → Nat\n  | .nil => Nat.zero\n  | .cons _ t => Nat.succ (length t)\n#reduce length one\n"
          "Nat : U0\nid : (x0 :0 U0) → (x1 : x0) → x0\n(x0 :0 U0) → (x1 : x0) → x0\nNat\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\nconst : (x0 :0 U0) → (x1 :0 U0) → (x2 : x0) → (x3 : x1) → x0\ncon((#0, (tt, tt)))\nList : (x0 : U0) → U0\none : (List Nat)\n(List Nat)\ncon((#1, (con((#0, (tt, tt))), (con((#0, (tt, tt))), (tt, tt)))))\ntwo : (List Nat)\ncon((#1, (con((#0, (tt, tt))), (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (con((#0, (tt, tt))), (tt, tt))))), (tt, tt)))))\ntwice : (x0 :0 U0) → (x1 : (x1 : x0) → x0) → (x2 : x0) → x0\ncon((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt))))\nbad : (List Nat)\nerror: type mismatch: expected Nat, got (List ?m1)\nmap : (x0 :0 U0) → (x1 :0 U0) → (x2 : (x2 : x0) → x1) → (x3 : (List x0)) → (List x1)\ncon((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (con((#0, (tt, tt))), (tt, tt)))))\nlength : (x0 :0 U0) → (x1 : (List x0)) → Nat\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\n" },
    { name := "the self-hosted frontend: named arguments, explicit and implicit (A9)", run := fun _ =>
        selfhostSameNats namedArgHeader namedArgCases },
    { name := "the self-hosted frontend: named argument errors (A9)", run := fun _ => do
        selfhostCheckFile "import Prelude\ndef sub (a b : Nat) : Nat := Nat.sub a b\ndef x : Nat := sub (c := 1) 2\n"
          "sub : (x0 : Nat) → (x1 : Nat) → Nat\nerror: no parameter named 'c'\n"
        selfhostCheckFile "import Prelude\ndef sub (a b : Nat) : Nat := Nat.sub a b\ndef x : Nat := sub (b := 1) (b := 2)\n"
          "sub : (x0 : Nat) → (x1 : Nat) → Nat\nerror: argument 'b' was already given\n"
        selfhostCheckFile "import Prelude\ndef sub (a b : Nat) : Nat := Nat.sub a b\ndef x : Nat := sub (b := 1)\n"
          "sub : (x0 : Nat) → (x1 : Nat) → Nat\nerror: named argument 'b' comes after the explicit parameter 'a', which has no argument\n"
        selfhostCheckFile "import Prelude\ndef x : Nat := (b := 1)\n"
          "error: a named argument `(x := e)` is only allowed as an argument of an application\n" },
    { name := "the self-hosted frontend: a named argument for a binder written in the type (A9)", run := fun _ =>
        selfhostCheckFile "import Prelude\naxiom f : {A : Type} → A → A\ndef g : Nat := f (A := Nat) 3\n"
          "f : (x0 :0 U0) → (x1 : x0) → x0\ng : Nat\n" },
    { name := "the self-hosted frontend: named arguments of a constructor (A9)", run := fun _ => do
        selfhostAgrees ctorNamedHeader ctorNamedDecls
        selfhostSameNats (ctorNamedHeader ++ "def a : P := P.mk (y := 2) (x := 1)\n")
          [("getX a", 1), ("getY a", 2)]
        selfhostSameNats ctorNamedHeader
          [("vhead (Vec.cons (v := Vec.nil) (n := 0) (a := 5))", 5)] },
    { name := "the self-hosted frontend: constructor named-argument errors (A9)", run := fun _ => do
        let p := "import Prelude\ninductive P where\n  | mk (x : Nat) (y : Nat)\n"
        selfhostCheckFile (p ++ "def c : P := P.mk (z := 1)\n")
          "P : U0\nerror: no parameter named 'z'\n"
        selfhostCheckFile (p ++ "def d : P := P.mk (x := 1) (x := 2)\n")
          "P : U0\nerror: argument 'x' was already given\n"
        selfhostCheckFile (p ++ "def e : P := P.mk (y := 2)\n")
          "P : U0\nerror: named argument 'y' comes after the explicit parameter 'x', which has no argument\n" },
    { name := "constructors by their names (.c) and @f, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\ninductive List (A : Type) where\n  | nil\n  | cons (head : A) (tail : List A)\ndef two : Nat := .succ (.succ .zero)\n#reduce two\ndef xs : List Nat := .cons .zero (.cons two .nil)\n#reduce xs\ndef id {A : Type} (x : A) : A := x\n#reduce @id Nat .zero\ndef add : Nat → Nat → Nat\n  | .zero, n => n\n  | .succ m, n => .succ (add m n)\n#reduce add two two\ndef map {A B : Type} (f : A → B) : List A → List B\n  | .nil => .nil\n  | .cons h t => .cons (f h) (map f t)\n#reduce map (add two) xs\ndef bad : Nat := .nil\n"
          "Nat : U0\nList : (x0 : U0) → U0\ntwo : Nat\ncon((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt))))\nxs : (List Nat)\ncon((#1, (con((#0, (tt, tt))), (con((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (con((#0, (tt, tt))), (tt, tt))))), (tt, tt)))))\nid : (x0 :0 U0) → (x1 : x0) → x0\ncon((#0, (tt, tt)))\nadd : (x0 : Nat) → (x1 : Nat) → Nat\ncon((#1, (con((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt))))\nmap : (x0 :0 U0) → (x1 :0 U0) → (x2 : (x2 : x0) → x1) → (x3 : (List x0)) → (List x1)\ncon((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (con((#1, (con((#1, (con((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (con((#0, (tt, tt))), (tt, tt))))), (tt, tt)))))\nerror: unknown identifier Nat.nil\n" },
    { name := "partial definitions and mutual blocks, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\ninductive Bool where\n  | false\n  | true\npartial def loop (n : Nat) : Nat := loop (.succ n)\n#check loop\nmutual\ndef isEven : Nat → Bool\n  | .zero => .true\n  | .succ n => isOdd n\ndef isOdd : Nat → Bool\n  | .zero => .false\n  | .succ n => isEven n\nend\n#check isOdd\npartial def bad (n : Nat) : Nat := Type\n"
          "Nat : U0\nBool : U0\nloop : (x0 : Nat) → Nat\n(x0 : Nat) → Nat\nisEven : (x0 : Nat) → Bool\nisOdd : (x0 : Nat) → Bool\n(x0 : Nat) → Bool\nerror: type mismatch: expected Nat, got U1\n" },
    { name := "indexed families, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\ninductive Vec (A : Type) : Nat → Type where\n  | nil : Vec A Nat.zero\n  | cons (n : Nat) (a : A) (v : Vec A n) : Vec A (Nat.succ n)\n#check Vec.cons\ndef v2 : Vec Nat (.succ (.succ .zero)) := Vec.cons (.succ .zero) .zero (Vec.cons .zero (.succ .zero) Vec.nil)\n#reduce v2\ndef len {A : Type} {n : Nat} (v : Vec A n) : Nat := match v with\n  | .nil => Nat.zero\n  | .cons _ _ t => Nat.succ (len t)\n#reduce len v2\ndef head {A : Type} {n : Nat} (d : A) (v : Vec A n) : A := match v with\n  | .cons _ a _ => a\n  | _ => d\n#reduce head (.succ (.succ .zero)) v2\ndef bad : Vec Nat .zero := Vec.cons .zero .zero Vec.nil\n"
          "Nat : U0\nVec : (x0 : U0) → (x1 : Nat) → U0\n(x0 :0 U0) → (x1 : Nat) → (x2 : x0) → (x3 : ((Vec x0) x1)) → ((Vec x0) (Nat.succ x1))\nv2 : ((Vec Nat) (Nat.succ (Nat.succ Nat.zero)))\ncon((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (con((#0, (tt, tt))), (con((#1, (con((#0, (tt, tt))), (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (con((#0, (refl(Nat, Nat.zero), tt))), (refl(Nat, (Nat.succ con((#0, (tt, tt))))), tt)))))), (refl(Nat, (Nat.succ con((#1, (con((#0, (tt, tt))), (tt, tt)))))), tt))))))\nlen : (x0 :0 U0) → (x1 : Nat) → (x2 : ((Vec x0) x1)) → Nat\ncon((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt))))\nhead : (x0 :0 U0) → (x1 : Nat) → (x2 : x0) → (x3 : ((Vec x0) x1)) → x0\ncon((#0, (tt, tt)))\nerror: type mismatch: expected ((Vec Nat) Nat.zero), got ((Vec ?m0) (Nat.succ Nat.zero))\n" },
    { name := "impossible cases ruled out by index equations, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\ninductive Vec (A : Type) : Nat → Type where\n  | nil : Vec A Nat.zero\n  | cons (n : Nat) (a : A) (v : Vec A n) : Vec A (Nat.succ n)\ndef head1 {A : Type} (v : Vec A (.succ .zero)) : A := match v with\n  | .cons _ a _ => a\n#reduce head1 (Vec.cons .zero (Nat.succ Nat.zero) Vec.nil)\ndef isNil {A : Type} (v : Vec A .zero) : Nat := match v with\n  | .nil => .zero\n#reduce isNil (@Vec.nil Nat)\ndef bad {A : Type} (v : Vec A (.succ .zero)) : A := match v with\n  | .nil => Type\n"
          "Nat : U0\nVec : (x0 : U0) → (x1 : Nat) → U0\nhead1 : (x0 :0 U0) → (x1 : ((Vec x0) (Nat.succ Nat.zero))) → x0\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\nisNil : (x0 :0 U0) → (x1 : ((Vec x0) Nat.zero)) → Nat\ncon((#0, (tt, tt)))\nerror: type mismatch: expected A, got U1\n" },
    { name := "mutual inductive types, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\nmutual\ninductive Tm where\n  | var (n : Nat)\n  | app (f : Tm) (args : Tms)\ninductive Tms where\n  | nil\n  | cons (t : Tm) (rest : Tms)\nend\n#check Tm.app\ndef t1 : Tm := .app (.var .zero) (.cons (.var (.succ .zero)) .nil)\n#check t1\ndef head : Tm → Nat\n  | .var n => n\n  | .app f _ => head f\n#reduce head t1\ndef len : Tms → Nat\n  | .nil => .zero\n  | .cons _ r => .succ (len r)\n#reduce len (.cons (.var .zero) (.cons (.var .zero) .nil))\n"
          "Nat : U0\nTm : U0\nTms : U0\n(x0 : Tm) → (x1 : Tms) → Tm\nt1 : Tm\nTm\nhead : (x0 : Tm) → Nat\ncon((#0, (tt, tt)))\nlen : (x0 : Tms) → Nat\ncon((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt))))\n" },
    { name := "parameterised mutual inductive types, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\nmutual\ninductive Tree (A : Type) where\n  | leaf (a : A)\n  | node (kids : Forest A)\ninductive Forest (A : Type) where\n  | nil\n  | cons (t : Tree A) (rest : Forest A)\nend\n#check Tree.node\ndef t : Tree Nat := .node (.cons (.leaf .zero) (.cons (.leaf (.succ .zero)) .nil))\ndef size {A : Type} : Forest A → Nat\n  | .nil => .zero\n  | .cons _ r => .succ (size r)\ndef kids {A : Type} (d : Forest A) : Tree A → Forest A\n  | .node k => k\n  | _ => d\n#reduce size (kids .nil t)\n"
          "Nat : U0\nTree : (x0 : U0) → U0\nForest : (x0 : U0) → U0\n(x0 :0 U0) → (x1 : (Forest x0)) → (Tree x0)\nt : (Tree Nat)\nsize : (x0 :0 U0) → (x1 : (Forest x0)) → Nat\nkids : (x0 :0 U0) → (x1 : (Forest x0)) → (x2 : (Tree x0)) → (Forest x0)\ncon((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt))))\n" },
    { name := "mutual types sharing a constructor name (Ev.s, Od.s), checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\nmutual\ninductive Ev where\n  | z\n  | s (o : Od)\ninductive Od where\n  | s (e : Ev)\nend\n#check Ev.s\n#check Od.s\ndef two : Ev := .s (.s .z)\ndef isZ : Ev → Nat\n  | .z => .zero\n  | Ev.s _ => .succ .zero\ndef unOd : Od → Ev\n  | .s e => e\n#reduce isZ (unOd (.s two))\n#reduce isZ (unOd (Od.s Ev.z))\n"
          "Nat : U0\nEv : U0\nOd : U0\n(x0 : Od) → Ev\n(x0 : Ev) → Od\ntwo : Ev\nisZ : (x0 : Ev) → Nat\nunOd : (x0 : Od) → Ev\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\ncon((#0, (tt, tt)))\n" },
    { name := "structures and projections, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\nstructure Pair (A B : Type) where\n  fst : A\n  snd : B\n#check Pair.mk\ndef p : Pair Nat (Pair Nat Nat) := .mk .zero (.mk (.succ .zero) .zero)\n#reduce Pair.fst (Pair.snd p)\ndef swap {A B : Type} (q : Pair A B) : Pair B A := .mk (Pair.snd q) (Pair.fst q)\n#reduce Pair.fst (swap p)\n#reduce p.snd.fst\ndef swap2 {A B : Type} (q : Pair A B) : Pair B A := .mk q.snd q.fst\n#reduce (swap2 p).fst\n"
          "Nat : U0\nPair : (x0 : U0) → (x1 : U0) → U0\nPair.fst : (x0 :0 U0) → (x1 :0 U0) → (x2 : ((Pair x0) x1)) → x0\nPair.snd : (x0 :0 U0) → (x1 :0 U0) → (x2 : ((Pair x0) x1)) → x1\n(x0 :0 U0) → (x1 :0 U0) → (x2 : x0) → (x3 : x1) → ((Pair x0) x1)\np : ((Pair Nat) ((Pair Nat) Nat))\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\nswap : (x0 :0 U0) → (x1 :0 U0) → (x2 : ((Pair x0) x1)) → ((Pair x1) x0)\ncon((#0, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (con((#0, (tt, tt))), (tt, tt)))))\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\nswap2 : (x0 :0 U0) → (x1 :0 U0) → (x2 : ((Pair x0) x1)) → ((Pair x1) x0)\ncon((#0, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (con((#0, (tt, tt))), (tt, tt)))))\n" },
    { name := "numerals and match as a term, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\ndef add : Nat → Nat → Nat\n  | 0, n => n\n  | .succ m, n => .succ (add m n)\n#reduce add 2 3\ndef isSmall : Nat → Nat\n  | 0 => 1\n  | 1 => 1\n  | _ => 0\n#reduce isSmall 1\n#reduce isSmall 5\ninductive Bool where\n  | false\n  | true\ndef lt : Nat → Nat → Bool\n  | _, 0 => .false\n  | 0, .succ _ => .true\n  | .succ m, .succ n => lt m n\n#reduce lt 1 3\ndef pick (b : Bool) (x y : Nat) : Nat := add (match b with\n  | .true => x\n  | .false => y) 1\n#reduce pick .false 2 5\ndef both (a b : Bool) : Bool := match a, b with\n  | .true, .true => .true\n  | _, _ => .false\n#reduce both .true .false\n"
          "Nat : U0\nadd : (x0 : Nat) → (x1 : Nat) → Nat\ncon((#1, (con((#1, (con((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt))))\nisSmall : (x0 : Nat) → Nat\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\ncon((#0, (tt, tt)))\nBool : U0\nlt : (x0 : Nat) → (x1 : Nat) → Bool\ncon((#1, (tt, tt)))\npick : (x0 : Bool) → (x1 : Nat) → (x2 : Nat) → Nat\ncon((#1, (con((#1, (con((#1, (con((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt))))\nboth : (x0 : Bool) → (x1 : Bool) → Bool\ncon((#0, (tt, tt)))\n" },
    { name := "the Prelude, if and strings, checked in Wiz", run := fun _ =>
        selfhostCheckFile "import Prelude\n#check Nat.add\ndef three : Nat := Nat.add 1 2\n#reduce Nat.beq three 3\ndef min (m n : Nat) : Nat := if Nat.lt m n then m else n\n#reduce min 2 1\ndef hi : String := \"hi\"\n#reduce String.length (String.append hi \"!\")\ndef firstCode (s : String) : Nat := match s.data with\n  | .cons c _ => c.code\n  | .nil => 0\n#reduce Nat.beq (firstCode \"A\") 65\n"
          "(x0 : Nat) → (x1 : Nat) → Nat\nthree : Nat\ncon((#1, (tt, tt)))\nmin : (x0 : Nat) → (x1 : Nat) → Nat\ncon((#1, (con((#0, (tt, tt))), (tt, tt))))\nhi : String\ncon((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (tt, tt))))\nfirstCode : (x0 : String) → Nat\ncon((#1, (tt, tt)))\n" },
    { name := "infix operators, checked in Wiz", run := fun _ =>
        selfhostCheckFile "import Prelude\n#reduce Nat.beq (2 + 3 * 2) 8\ndef pred2 : Nat → Nat\n  | n + 2 => n\n  | _ => 0\n#reduce Nat.beq (pred2 5) 3\n#reduce Nat.beq (10 - 3 - 2) 5\ninfixr:50 \" ⊕ \" => Bool.or\n#reduce .false ⊕ .false ⊕ .true\ndef len3 : Nat := List.length (List.cons 1 .nil ++ List.cons 2 (List.cons 3 .nil))\n#reduce Nat.beq len3 3\n#reduce Nat.le 3 3\n"
          "con((#1, (tt, tt)))\npred2 : (x0 : Nat) → Nat\ncon((#1, (tt, tt)))\ncon((#1, (tt, tt)))\ncon((#1, (tt, tt)))\nlen3 : Nat\ncon((#1, (tt, tt)))\ncon((#1, (tt, tt)))\n" },
    { name := "axioms, Unit, Array, IO and do, checked in Wiz", run := fun _ =>
        selfhostCheckFile "import Prelude\nforeign_type Secret\nextern \"wiz_peek\" peek : Secret → Nat\ndef unit : Unit := ()\ndef twice (s : String) : IO Unit := do\n  IO.println s;\n  let t := String.append s \"!\";\n  IO.println t\ndef readLen (p : String) : IO Nat := do\n  s ← IO.readFile p;\n  IO.pure (String.length s)\ndef push2 (a : Array Nat) : Array Nat := Array.push (Array.push a 1) 2\ndef size2 : Nat := Array.size (push2 Array.empty)\ndef sum3 (n : Nat) : Nat :=\n  let m := n + n;\n  m + n\n#reduce Nat.beq (sum3 2) 6\n"
          "Secret : U0\npeek : (x0 : Secret) → Nat\nunit : Unit0\ntwice : (x0 : String) → (IO Unit0)\nreadLen : (x0 : String) → (IO Nat)\npush2 : (x0 : (Array Nat)) → (Array Nat)\nsize2 : Nat\nsum3 : (x0 : Nat) → Nat\ncon((#1, (tt, tt)))\n" },
    { name := "Syntax, StrMap and definitions as types, checked in Wiz", run := fun _ =>
        selfhostCheckFile "import Prelude\ndef leaf : Syntax := .node \"leaf\" (.cons (.atom \"x\") .nil)\ndef kindOf : Syntax → String\n  | .node k _ => k\n  | _ => \"\"\n#reduce String.length (kindOf leaf)\ndef argCount {b : Bool} : SyntaxF b → Nat\n  | .cons _ t => argCount t + 1\n  | .node _ args => argCount args\n  | _ => 0\n#reduce Nat.beq (argCount leaf) 1\ninductive Cat where\n  | mk (name : String) (n : Nat)\ndef find : List Cat → String → Option Cat\n  | .nil, _ => .none\n  | .cons (.mk m n) rest, name => match Nat.beq (String.length m) (String.length name) with\n    | .true => .some (.mk m n)\n    | .false => find rest name\ndef m : StrMap Nat := StrMap.insert StrMap.empty (Str.ofString \"k\") 1\n"
          "leaf : Syntax\nkindOf : (x0 : Syntax) → String\ncon((#1, (con((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt))))\nargCount : (x0 : Bool) → (x1 : (SyntaxF x0)) → Nat\ncon((#1, (tt, tt)))\nCat : U0\nfind : (x0 : (List Cat)) → (x1 : String) → (Option Cat)\nm : (StrMap Nat)\n" },
    { name := "function fields and catch-alls on mutual types, checked in Wiz", run := fun _ =>
        selfhostCheckFile "import Prelude\nmutual\ninductive Tm where\n  | lit (n : Nat)\n  | app (f : Tm) (a : Tm)\n  | many (ts : Tms)\ninductive Tms where\n  | nil\n  | cons (t : Tm) (ts : Tms)\nend\ndef litOr : Tm → Tm\n  | .lit n => .lit (n + 1)\n  | t => t\n#reduce litOr (.lit 1)\n#reduce litOr (.many .nil)\nmutual\ninductive Val where\n  | vnat (n : Nat)\n  | vlazy (v : Unit → Val)\n  | vbox (b : Box)\ninductive Box where\n  | mk (v : Val)\nend\npartial def force : Val → Val\n  | .vlazy v => force (v ())\n  | v => v\ndef unwrap : Val → Val\n  | .vlazy v => v ()\n  | v => v\n#reduce unwrap (Val.vlazy (fun _ => Val.vnat 3))\ndef big (n : Nat) : Nat := Nat.max n 3\n#reduce Nat.beq (big 1) 3\n"
          "Tm : U0\nTms : U0\nlitOr : (x0 : Tm) → Tm\ncon((#0, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (refl(Enum2, #0), tt))))\ncon((#2, (con((#3, (refl(Enum2, #1), tt))), (refl(Enum2, #0), tt))))\nVal : U0\nBox : U0\nforce : (x0 : Val) → Val\nunwrap : (x0 : Val) → Val\ncon((#0, (con((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (refl(Enum2, #0), tt))))\nbig : (x0 : Nat) → Nat\ncon((#1, (tt, tt)))\n" },
    { name := "recursion through function fields, reordered parameters, big numerals, checked in Wiz", run := fun _ =>
        selfhostCheckFile "import Prelude\nmutual\ninductive Val where\n  | vnat (n : Nat)\n  | vsuc (v : Val)\n  | vlazy (v : Unit → Val)\n  | vbox (b : Box)\ninductive Box where\n  | mk (v : Val)\nend\ndef whnf : Val → Val\n  | .vlazy v => whnf (v ())\n  | v => v\ndef depth : Val → Nat\n  | .vsuc v => depth v + 1\n  | .vlazy v => depth (v ())\n  | _ => 0\n#reduce Nat.beq (depth (whnf (Val.vlazy (fun _ => Val.vlazy (fun _ => Val.vnat 3))))) 0\n#reduce Nat.beq (depth (Val.vsuc (Val.vlazy (fun _ => Val.vsuc (Val.vnat 0))))) 2\ndef apps : Nat → List Nat → Nat\n  | f, .nil => f\n  | f, .cons a rest => apps (f + a) rest\n#reduce Nat.beq (apps 1 (List.cons 2 (List.cons 3 .nil))) 6\ndef big : Nat := 100000\n#check big\ndef bigger : Nat := 1000000000\n#reduce Nat.beq (Nat.sub 1000 999) 1\n"
          "Val : U0\nBox : U0\nwhnf : (x0 : Val) → Val\ndepth : (x0 : Val) → Nat\ncon((#1, (tt, tt)))\ncon((#1, (tt, tt)))\napps : (x0 : Nat) → (x1 : (List Nat)) → Nat\ncon((#1, (tt, tt)))\nbig : Nat\nNat\nbigger : Nat\ncon((#1, (tt, tt)))\n" },
    { name := "postponed and inferred matches, pruning, checked in Wiz", run := fun _ =>
        selfhostCheckFile "import Prelude\ndef h1 : List Syntax → List String\n  | .nil => .nil\n  | .cons s rest => .cons (match s with\n      | .ident n => n\n      | _ => \"_\") .nil\ndef h2 (s : Syntax) : List String := .cons (match s with\n      | .ident n => n\n      | _ => \"_\") .nil\ndef h3 (s : List Nat) : List Nat := .cons (match s with\n      | .nil => 0\n      | _ => 1) .nil\ndef h4 (s : List Nat) : List Nat := List.cons (match s with\n      | .nil => 0\n      | _ => 1) .nil\ndef k1 (s : List Nat) : Nat :=\n  let x := match s with\n    | .nil => 0\n    | _ => 1;\n  x + 1\ndef k2 (b : Bool) : Nat :=\n  let y := if b then 2 else 3;\n  y\n#reduce Nat.beq (k1 .nil) 1\n#reduce Nat.beq (k2 .false) 3\ndef genTys (p base : Nat) : Nat → List Nat → List Nat\n  | _, .nil => .nil\n  | m, .cons t rest => .cons (t + m + p) (genTys p base (m + 1) rest)\n#reduce Nat.beq (List.length (genTys 1 2 0 (List.cons 1 (List.cons 2 .nil)))) 2\ndef kw (stx : Syntax) (p : Nat) : String :=\n  let kw := match stx with\n    | .atom v => v\n    | _ => \"infix\";\n  kw\ndef g2 (xs : List Nat) : Nat := match xs with\n    | .cons _ t => match List.append t t with\n      | .nil => 0\n      | later => List.length later\n    | .nil => 0\n#reduce Nat.beq (g2 (List.cons 1 (List.cons 2 .nil))) 2\ndef takeL {A : Type} : Nat → List A → List A\n  | .zero, _ => .nil\n  | .succ n, xs => match xs with\n    | .nil => .nil\n    | .cons x rest => .cons x (takeL n rest)\ndef sp (k : Nat) : List (List Nat) → List (List Nat)\n  | .nil => .nil\n  | .cons pats rest =>\n    let before := takeL k pats;\n    match List.length pats with\n    | .zero => .cons (List.append before .nil) (sp k rest)\n    | .succ _ => sp k rest\ndef sp2 (k : Nat) (pats : List Nat) : List (List Nat) :=\n    let before := takeL k pats;\n    .cons (List.append before .nil) .nil\ninductive Cl where\n  | mk (pats : List Nat) (binds : List Nat) (rhs : Nat)\ndef sp3 (k : Nat) : List Cl → List Cl\n  | .nil => .nil\n  | .cons (.mk pats binds rhs) rest =>\n    let before := takeL k pats;\n    let after := takeL k pats;\n    match List.length pats with\n    | .zero => .cons (.mk (List.append before (List.append pats after)) binds rhs) (sp3 k rest)\n    | .succ _ => sp3 k rest\ndef sp4 (T : String) (k : Nat) : List Cl → List Cl\n  | .nil => .nil\n  | .cons (.mk pats binds rhs) rest =>\n    let before := takeL k pats;\n    match List.length pats with\n    | .zero => .cons (.mk (List.append before pats) binds rhs) (sp4 T k rest)\n    | .succ _ =>\n      let binds' := match Nat.beq k 0 with\n        | .true => binds\n        | .false => List.append binds (.cons k .nil);\n      .cons (.mk before binds' rhs) (sp4 T k rest)\n"
          "h1 : (x0 : (List Syntax)) → (List String)\nh2 : (x0 : Syntax) → (List String)\nh3 : (x0 : (List Nat)) → (List Nat)\nh4 : (x0 : (List Nat)) → (List Nat)\nk1 : (x0 : (List Nat)) → Nat\nk2 : (x0 : Bool) → Nat\ncon((#1, (tt, tt)))\ncon((#1, (tt, tt)))\ngenTys : (x0 : Nat) → (x1 : Nat) → (x2 : Nat) → (x3 : (List Nat)) → (List Nat)\ncon((#1, (tt, tt)))\nkw : (x0 : Syntax) → (x1 : Nat) → String\ng2 : (x0 : (List Nat)) → Nat\ncon((#1, (tt, tt)))\ntakeL : (x0 :0 U0) → (x1 : Nat) → (x2 : (List x0)) → (List x0)\nsp : (x0 : Nat) → (x1 : (List (List Nat))) → (List (List Nat))\nsp2 : (x0 : Nat) → (x1 : (List Nat)) → (List (List Nat))\nCl : U0\nsp3 : (x0 : Nat) → (x1 : (List Cl)) → (List Cl)\nsp4 : (x0 : String) → (x1 : Nat) → (x2 : (List Cl)) → (List Cl)\n" },
    { name := "the self-hosted frontend: a lambda waits for the arguments that fix its domains", run := fun _ =>
        selfhostCheckFile ("import Prelude\n" ++
          "def zip3 {A B C D : Type} (f : A → B → C → D) : List A → List B → List C → List D\n" ++
          "  | .cons a as, .cons b bs, .cons c cs => .cons (f a b c) (zip3 f as bs cs)\n  | _, _, _ => .nil\n" ++
          "def sel (c : List Bool) (t e : List Nat) : List Nat := zip3 (fun b x y => if b then x else y) c t e\n" ++
          "#reduce Nat.beq (List.length (sel (List.cons .true .nil) (List.cons 1 .nil) (List.cons 2 .nil))) 1\n")
          ("zip3 : (x0 :0 U0) → (x1 :0 U0) → (x2 :0 U0) → (x3 :0 U0) → (x4 : (x4 : x0) → (x5 : x1) → (x6 : x2) → x3) → (x5 : (List x0)) → (x6 : (List x1)) → (x7 : (List x2)) → (List x3)\n" ++
          "sel : (x0 : (List Bool)) → (x1 : (List Nat)) → (x2 : (List Nat)) → (List Nat)\ncon((#1, (tt, tt)))\n") },
    { name := "the self-hosted backend compiles and runs a program", run := fun _ =>
        selfhostCompileRun selfhostProgram1
          "6765\n5050\n1989\n2\nyes, ünïcode\n2\n5\n" },
    -- (erasure audit) a function into `Unit` (`(0 x : D) → … → Unit`) has one inhabitant
    -- up to η, so its value has no runtime content (`erasedFunTy`). The self-hosted
    -- backend's `erasable` lacked that case, so `ghost` survived as a closure and
    -- applying it ran `spin`: this program looped when the self-hosted compiler ran it
    -- (Lean's erasure drops the field and the application).
    { name := "erasure: a contentless function field is not run (a function into Unit)", run := fun _ => do
        let src := "import IO\n" ++
          "partial def spin (n : Nat) : Unit := match n with\n  | 0 => spin 0\n  | .succ k => spin k\n" ++
          "def ghostLoop : (0 x : Nat) → Unit := fun x => spin 0\n" ++
          "structure S where\n  n : Nat\n  ghost : (0 x : Nat) → Unit\n" ++
          "def mkS : S := S.mk 1 ghostLoop\n" ++
          "def force (s : S) : Nat := match s with\n  | .mk n g => ((g 5, n + 1) : Unit × Nat).2\n" ++
          "def main : IO Unit := IO.println (Nat.toString (force mkS))\n"
        -- the intended semantics (erasure drops both the field and `g 5`)
        ioRun src "2\n"
        selfhostCompileRun src "2\n"
        selfhostCompileRun src "2\n" (flags := #["--rc"]) },
    { name := "the self-hosted backend compiles and runs a program with reference counting (no leaks)", run := fun _ =>
        selfhostCompileRun selfhostProgram1 "6765\n5050\n1989\n2\nyes, ünïcode\n2\n5\n" (flags := #["--rc"]) },
    { name := "reference counting: deep lists, unused parameters and hypotheses, shared arrays, closures", run := fun _ =>
        selfhostCompileRun selfhostProgram2 "1000000\n0\n6\n15\n5\n3\n" (flags := #["--rc"]) },
    { name := "the first-line pragma `-- wiz: rc` still selects reference counting (a fallback, 21k)", run := fun _ =>
        selfhostCompileRun ("-- wiz: rc\n" ++ selfhostProgram2) "1000000\n0\n6\n15\n5\n3\n" },
    { name := "self tail calls are loops: 10M iterations on a 1 MB stack, at -O0, with the GC and with RC (15f)", run := fun _ => do
        -- (in a branch of a match on a parameter: in the GC mode a call under a match on a
        -- computed value is still inside a suspended `let`'s closure)
        let prog := "import Prelude\npartial def count (n acc : Nat) : Nat := match n with\n  | .zero => acc\n" ++
          "  | .succ m => count m (acc + 1)\ndef main : IO Unit := IO.println (Nat.toString (count 10000000 0))\n"
        selfhostCompileRun prog "10000000\n" (opt := "-O0") (smallStack := true)
        selfhostCompileRun prog "10000000\n" (flags := #["--rc"]) (opt := "-O0") (smallStack := true)
        selfhostCompileRun prog "10000000\n" (flags := #["--rc-owned"]) (opt := "-O0") (smallStack := true)
        -- under reference counting lets are strict: a call under a match on a computed value loops too
        let nested := "import Prelude\npartial def count (n acc : Nat) : Nat := match n with\n  | .zero => acc\n" ++
          "  | .succ m => match Nat.beq (Nat.mod m 3) 0 with\n    | .true => count m (acc + 2)\n    | .false => count m acc\n" ++
          "def main : IO Unit := IO.println (Nat.toString (count 10000000 0))\n"
        selfhostCompileRun nested "6666668\n" (flags := #["--rc"]) (opt := "-O0") (smallStack := true) },
    { name := "big numerals with the self-hosted compiler: no deep recursion, 63-bit words (15g)", run := fun _ => do
        selfhostCompileRun selfhostBigLits selfhostBigLitsExpected
        selfhostCompileRun selfhostBigLits selfhostBigLitsExpected (flags := #["--rc"]) },
    { name := "the self-hosted compiler stops at a frontend error: exit code 1, the errors on stderr, no C (15g)", run := fun _ =>
        selfhostCompileFails ("import Prelude\ndef a : Nat := 9223372036854775808\ndef b : Nat := nope\n" ++
          "def main : IO Unit := IO.println (Nat.toString 1)\n")
          ("error: the numeral does not fit in 63 bits (numbers are 63-bit words here)\nerror: unknown identifier nope\n") },
    { name := "a numeral from 2^63 is an error in the self-hosted frontend, not a wrapped number (15g)", run := fun _ =>
        selfhostCheckFile ("import Prelude\ndef a : Nat := 9223372036854775807\ndef b : Nat := 9223372036854775808\n" ++
          "def c : Nat := 18446744073709551616\ndef d : Nat := 18446744073709551617\ndef e : Nat := 1000000000000000000000000000000\n" ++
          "def f : Nat := 0009223372036854775807\n")
          ("a : Nat\n" ++ "error: the numeral does not fit in 63 bits (numbers are 63-bit words here)\n" ++ "error: the numeral does not fit in 63 bits (numbers are 63-bit words here)\n" ++
            "error: the numeral does not fit in 63 bits (numbers are 63-bit words here)\n" ++ "error: the numeral does not fit in 63 bits (numbers are 63-bit words here)\n" ++ "f : Nat\n") },
    { name := "dead lets without effects are not computed (15e)", run := fun _ =>
        selfhostCompileRun ("import Prelude\ndef f (n : Nat) : Nat :=\n  let unused := List.cons n (List.cons 2 .nil);\n" ++
          "  let alsoUnused := List.cons unused .nil;\n  n + 1\ndef main : IO Unit := IO.println (Nat.toString (f 41))\n") "42\n" (flags := #["--rc"]) },
    { name := "reference counting: cells reused (shared and unique lists, trees, pairs)", run := fun _ =>
        selfhostCompileRun selfhostProgram3 "1000000\n9900\n18\n4\n" (flags := #["--rc"]) },
    { name := "reference counting: lets strict, dropped, moved into a branch or suspended by their demand", run := fun _ => do
        selfhostCompileRun selfhostProgram4 "110\n0\n7\n23\n13\n" (flags := #["--rc"])
        selfhostCompileRun selfhostProgram4 "110\n0\n7\n23\n13\n" },
    { name := "reference counting: hypotheses read once or as functions are not memoised (and a reused partial recursion stays linear per call)", run := fun _ => do
        selfhostCompileRun selfhostProgram5 "4498500\n3000\n1099511627775\n65536\n" (flags := #["--rc"]) },
    { name := "self-hosted programs read their command-line arguments (IO.args, 21k), with either collector", run := fun _ => do
        let prog := "import Prelude\ndef printAll : List String → IO Unit\n  | .nil => IO.pure ()\n  | .cons s rest => do\n    IO.println s;\n    printAll rest\n" ++
          "def main : IO Unit := do\n  n ← IO.argCount;\n  IO.println (Nat.toString n);\n  args ← IO.args;\n  printAll args\n"
        selfhostCompileRun prog "0\n"
        selfhostCompileRun prog "2\n--rc\nünï code\n" (progArgs := #["--rc", "ünï code"])
        selfhostCompileRun prog "1\nx\n" (flags := #["--rc"]) (progArgs := #["x"]) },
    { name := "the self-hosted backend: division, powers and bits", run := fun _ =>
        selfhostCompileRun ("import Prelude\ndef show (n : Nat) : IO Unit := IO.println (Nat.toString n)\n" ++
          "def main : IO Unit := do\n  show (100 / 7);\n  show (Nat.mod 100 7);\n  show (Nat.div 5 0);\n  show (Nat.mod 5 0);\n" ++
          "  show (Nat.pow 3 20);\n  show (Nat.land 12 10);\n  show (Nat.lor 12 10);\n  show (Nat.xor 12 10);\n" ++
          "  show (Nat.shiftLeft 3 20);\n  show (Nat.shiftRight 1000 3);\n  show (Nat.log2 1025);\n" ++
          "  IO.println (if Nat.testBit 5 2 then \"set\" else \"clear\")\n")
          "14\n2\n0\n5\n3486784401\n8\n14\n6\n3145728\n125\n10\nset\n" },
    { name := "foreign functions: the Lean and the self-hosted compilers agree (21l)", run := fun _ =>
        ffiAgrees ffiProgram1 ffiExpected1 },
    { name := "threads: the channel, MVar and lock natives agree in both runtimes (25a, D1)", run := fun _ =>
        bothRuntimes concNatives "36\n8\n" },
    { name := "foreign pointers: the finalizer runs with the last reference, in both compilers (21l)", run := fun _ =>
        ffiAgrees (ffiProgramFin false) "line\nline\nline\n" (gc := false) },
    { name := "foreign pointers passed around and flushed, with either collector (21l)", run := fun _ =>
        ffiAgrees (ffiProgramFin true) "line\nline\nline\n" },
    { name := "the self-hosted frontend: foreign types are checked (21l)", run := fun _ =>
        selfhostCheckFile "import Prelude\nextern \"f\" f : ((Nat → Nat) → Nat) → Nat\nforeign_type T\nextern \"g\" g : {A : Type} → A → T → IO A\n"
          "error: a foreign function's arguments and result must be Nat, UInt64, Float64, String, Bool, Unit, a c_struct, a Wiz data type or a function of those (a callback; the result may be in IO)\nT : U0\ng : (x0 :0 U0) → (x1 : x0) → (x2 : T) → (IO x0)\n" },
    { name := "the self-hosted frontend: the Prelude's division and bits compute", run := fun _ =>
        selfhostCheckFile "import Prelude\n#reduce Nat.beq (Nat.mod 17 5) 2\n#reduce Nat.beq (Nat.xor 6 3) 5\n#reduce Nat.beq (Nat.log2 9) 3\n"
          "con((#1, (tt, tt)))\ncon((#1, (tt, tt)))\ncon((#1, (tt, tt)))\n" },
    { name := "the self-hosted frontend: phantom parameters count, as in the Lean frontend (21i)", run := fun _ =>
        selfhostAgrees phantomHeader [
          ("def same (x : UIntN 8) : UIntN 8 := x\n", true),
          ("def bad (x : UIntN 8) : UIntN 16 := x\n", false),
          ("def badP (x : Proxy Nat) : Proxy Bool := x\n", false),
          ("def badS (x : S 8) : S 16 := x\n", false),
          ("def badN (x : N 1) : N 2 := x\n", false),
          ("def w8 : Nat := width _ u8\ndef get {w : Nat} : UIntN w → Nat\n  | .mk n => n\ndef sx {w : Nat} (a : S w) : Nat := a.x\n" ++
            "def N.add {w : Nat} : N w → N w → N w\n  | .z, m => m\n  | .s n, m => .s (N.add n m)\n", true)] },
    { name := "the self-hosted frontend: phantom parameters are inferred, and computation is unchanged (21i)", run := fun _ =>
        selfhostCheckFile ("import Prelude\n" ++ phantomHeader ++
          "#reduce Nat.beq (width _ u8) 8\n#reduce Nat.beq (S.x (S.mk 5 : S 16)) 5\n" ++
          "def N.toNat {w : Nat} : N w → Nat\n  | .z => 0\n  | .s n => N.toNat n + 1\n#reduce Nat.beq (N.toNat (.s (.s .z) : N 3)) 2\n" ++
          "inductive V (w : Nat) (A : Type) : Nat → Type where\n  | nil : V w A .zero\n")
          ("UIntN : (x0 : Nat) → U0\nProxy : (x0 : U0) → U0\nS : (x0 : Nat) → U0\nS.x : (x0 :0 Nat) → (x1 : (S x0)) → Nat\nN : (x0 : Nat) → U0\n" ++
          "width : (x0 : Nat) → (x1 : (UIntN x0)) → Nat\nu8 : (UIntN (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))))\n" ++
          "con((#1, (tt, tt)))\ncon((#1, (tt, tt)))\nN.toNat : (x0 : Nat) → (x1 : (N x0)) → Nat\ncon((#1, (tt, tt)))\n" ++
          "error: a parameter that no constructor mentions (a phantom parameter) of an indexed family is not supported by the self-hosted frontend\n") },
    { name := "the self-hosted backend: shared projection prefixes, with the collector and with reference counting (15j)", run := fun _ => do
        selfhostCompileRun selfhostProjShare "21\n17\n43\n22\n23\n"
        selfhostCompileRun selfhostProjShare "21\n17\n43\n22\n23\n" (flags := #["--rc"])
        -- (the prefixes of `sumW`'s parameter are locals, read once each)
        for flags in [#[], #["--rc"]] do
          if let some c ← selfhostC selfhostProjShare flags then
            let fn := (((c.splitOn "V d_sumW(V p0) {").getD 1 "").takeWhile (· != '\n')).toString
            -- (`p0.2` read once, into `qp0_1`)
            check ((fn.splitOn "fld(p0, 1)").length == 2 && (fn.splitOn "V qp0_1 = ").length == 2)
              s!"no shared prefixes ({flags}):\n{fn.take 2000}" },
    { name := "the self-hosted backend: phantom parameters are erased (21i)", run := fun _ =>
        selfhostCompileRun ("import Prelude\ninductive Box (w : Nat) where\n  | mk (n : Nat)\nstructure Pt (w : Nat) where\n  x : Nat\n  y : Nat\n" ++
          "def get {w : Nat} : Box w → Nat\n  | .mk n => n\ndef sum {w : Nat} (p : Pt w) : Nat := p.x + p.y\n" ++
          "def b : Box 8 := .mk 3\ndef p : Pt 8 := .mk 1 2\n" ++
          "def main : IO Unit := IO.println (Nat.toString (get b + sum p))\n") "6\n" },
    { name := "the self-hosted frontend: written quantities, as in the Lean frontend (21m, K10)", run := fun _ =>
        selfhostAgrees quantityHeader quantityDecls },
    { name := "the self-hosted frontend: constructor field quantities (0, 1, ω), implicit and instance fields, as in the Lean frontend (21x, 22a)", run := fun _ =>
        selfhostAgrees fieldQtyHeader fieldQtyDecls },
    { name := "constructor field quantities, implicit and instance fields: the Lean and the self-hosted compilers agree (21x, 22a)", run := fun _ => do
        ioRun (fieldQtyProgram.replace "import Prelude" "import IO") "4\n3\n9\n7\n"
        selfhostCompileRun fieldQtyProgram "4\n3\n9\n7\n"
        selfhostCompileRun fieldQtyProgram "4\n3\n9\n7\n" (flags := #["--rc"]) },
    { name := "the self-hosted frontend: quantities, the pinned differences (21m, K1)", run := fun _ =>
        selfhostVerdicts quantityHeader quantityDiffs },
    { name := "a linear variable used once in each branch of a match: both frontends accept it (21v)", run := fun _ =>
        selfhostAgrees linearMatchHeader linearMatchDecls },
    { name := "the linear fixpoint: a recursive call's result may be used at ω when it contains no linear content, as in the Lean frontend", run := fun _ =>
        -- (a linear token recurred on an ω `Nat`: the self-hosted frontend cannot yet
        -- take a linear scrutinee apart, but threading the token through the recursive
        -- call is exactly the linear fixpoint; `Nat.inc`/`Tok.use` are applications, not
        -- constructor payloads, so both kernels reach the same rule)
        selfhostAgrees
          ("axiom Tok : Type\naxiom Tok.use : (1 t : Tok) → Nat\n" ++
           "axiom Tok.useB : (1 t : Tok) → Bool\n" ++
           "axiom Tok.useP : (1 t : Tok) → Nat × Nat\n" ++
           "axiom Tok.useO : (1 t : Tok) → Option Nat\n" ++
           "axiom Tok.useTok : (1 t : Tok) → Tok × Nat\n" ++
           "def Nat.inc (n : Nat) : Nat := Nat.succ n\n")
          [
            -- the call's result is `Nat`: no linear content, so it may be copied
            ("partial def loop (1 t : Tok) (n : Nat) : Nat :=\n" ++
             "  let m := n;\n  match m with\n  | 0 => Tok.use t\n  | .succ k => Nat.inc (loop t k)\n", true),
            ("partial def loopB (1 t : Tok) (n : Nat) : Bool :=\n" ++
             "  let m := n;\n  match m with\n  | 0 => Tok.useB t\n  | .succ k => Bool.and (loopB t k) Bool.true\n", true),
            -- a recursive call bound by an ω `let`: a pair of ω types
            ("partial def loopP (1 t : Tok) (n : Nat) : Nat × Nat :=\n" ++
             "  let m := n;\n  match m with\n  | 0 => Tok.useP t\n" ++
             "  | .succ k =>\n    let r := loopP t k;\n    (r.1 + 1, r.2)\n", true),
            -- ... and an `Option Nat` matched after the let
            ("partial def loopO (1 t : Tok) (n : Nat) : Option Nat :=\n" ++
             "  let m := n;\n  match m with\n  | 0 => Tok.useO t\n" ++
             "  | .succ k =>\n    let r := loopO t k;\n    match r with\n" ++
             "    | .none => Option.none\n    | .some v => Option.some (Nat.inc v)\n", true),
            -- the result contains `Tok`: copied at ω it would copy the token
            ("partial def bad (1 t : Tok) (d : Tok) (n : Nat) : Tok × Nat :=\n" ++
             "  let m := n;\n  match m with\n  | 0 => Tok.useTok t\n" ++
             "  | .succ k =>\n    let r := bad t d k;\n    r\n", false),
            -- two calls, and a path that never calls
            ("partial def dup (1 t : Tok) (n : Nat) : Nat :=\n" ++
             "  let m := n;\n  match m with\n  | 0 => Tok.use t\n  | .succ k => Nat.add (dup t k) (dup t k)\n", false),
            ("partial def drop (1 t : Tok) (n : Nat) : Nat :=\n" ++
             "  let m := n;\n  match m with\n  | 0 => Tok.use t\n  | .succ k => 0\n", false)
          ] },
    { name := "the self-hosted frontend: `let () := u; b` and `split` (`let (x, y)`), as in the Lean frontend (B7, A18)", run := fun _ =>
        selfhostAgrees "" splitDecls },
    { name := "`let () := u; b` and split: the Lean and the self-hosted compilers agree (B7)", run := fun _ => do
        ioRun splitProgram "40\n1\n42\n"
        selfhostCompileRun splitProgram "40\n1\n42\n"
        selfhostCompileRun splitProgram "40\n1\n42\n" (flags := #["--rc"]) },
    { name := "the self-hosted frontend: Σ types, pairs, projections and ∀, as in the Lean frontend (21u)", run := fun _ =>
        selfhostAgrees "" sigmaDecls },
    { name := "the self-hosted frontend: a `×` type as an inductive or structure field, as in the Lean frontend (21an)", run := fun _ =>
        selfhostAgrees "" sigmaFieldDecls },
    { name := "the self-hosted backend: quantities erase and run, with either collector (21m)", run := fun _ => do
        selfhostCompileRun quantityProgram "6\n5\n9\n"
        selfhostCompileRun quantityProgram "6\n5\n9\n" (flags := #["--rc"]) },
    { name := "the self-hosted frontend: private declarations, constructors and fields, as in one Lean module (21n)", run := fun _ =>
        selfhostAgrees "" privateDecls },
    -- (`attribute [macro …]`/`[tactic …]` are commands A12 now accepts; these are still
    -- unknown to the frontend)
    { name := "the self-hosted frontend: an unknown command is an error naming it (21n)", run := fun _ =>
        selfhostCheckFile "import Prelude\ndef f : Nat := 1\n#erase f\ndef g : Nat := f\n"
          "f : Nat\nerror: unsupported command command.erase\ng : Nat\n" },
    { name := "the self-hosted frontend: #print axioms lists the same axioms as the Lean frontend (A23)", run := fun _ =>
        selfhostSameLines axiomsPrintProgram },
    { name := "the self-hosted frontend: #print axioms walks a partial definition's body only as code, as the Lean frontend (A23)", run := fun _ =>
        selfhostSameLines partialAxiomsProgram },
    { name := "the self-hosted frontend: #print axioms lists a dependency's axiom (no checked-in selfhost trust ledger) (B18)", run := fun _ =>
        selfhostCheckFile axiomsDependencyProgram axiomsDependencyExpected },
    { name := "the self-hosted frontend: set_option values and unknown options, as in the Lean frontend (A23)", run := fun _ =>
        selfhostSameLines setOptionProgram },
    { name := "the self-hosted frontend: #eval and attribute [inline], as in the Lean frontend (21u)", run := fun _ => do
        selfhostCheckFile "import Prelude\ndef f : Nat := 1\n#eval Nat.add f f\nattribute [inline] f\ndef g : Nat := f\n"
          "f : Nat\ncon((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt))))\ng : Nat\n"
        selfhostAgrees "def f : Nat := 1\naxiom a : Nat\n" [
          ("attribute [inline] f\n", true), ("attribute [inline] a\n", false), ("attribute [inline] nope\n", false),
          ("#eval Nat.add f f\n", true), ("#eval nope\n", false)] },
    { name := "the self-hosted frontend: export and link_lib are checked as in the Lean frontend (21o)", run := fun _ =>
        selfhostAgrees exportHeader exportDecls },
    { name := "export, link_c and link_lib: the Lean and the self-hosted compilers agree (21o)", run := fun _ => do
        linkRun exportFiles exportExpected
        selfhostLinkRun exportFiles exportExpected
        selfhostLinkRun exportFiles exportExpected (flags := #["--rc"]) },
    { name := "callbacks: Wiz closures passed to C, borrowed or kept (Callback), the Lean and the self-hosted compilers agree (21q)", run := fun _ => do
        linkRun (callbackFiles true) callbackExpected
        selfhostLinkRun (callbackFiles true) callbackExpected
        selfhostLinkRun (callbackFiles true) callbackExpected (flags := #["--rc"]) },
    { name := "a kept callback that C never releases is a leak, in both compilers (21q)", run := fun _ => do
        let files := callbackFiles false
        ioRunC ((files.lookup "main.wiz").get!.replace "link_c \"c/cb.c\"\n" "") (files.lookup "c/cb.c").get! "" (fails := some "leaked")
        selfhostLinkRun files callbackExpected (flags := #["--rc"]) (fails := some "objects leaked") (failCode := 4) },
    { name := "the self-hosted frontend: callbacks are checked as in the Lean frontend (21q)", run := fun _ =>
        selfhostAgreesIO callbackHeader callbackDecls },
    { name := "c_struct: C structs by value, the Lean and the self-hosted compilers agree (21r)", run := fun _ => do
        linkRun structFiles structExpected
        selfhostLinkRun structFiles structExpected
        selfhostLinkRun structFiles structExpected (flags := #["--rc"]) },
    { name := "the self-hosted frontend: c_struct is checked as in the Lean frontend (21r)", run := fun _ =>
        selfhostAgreesIO "" structDecls },
    { name := "c_struct: two levels of nesting pass and return by value, in both compilers (C8)", run := fun _ => do
        let dir ← IO.FS.createTempDir
        let h := dir / "wiz_deep.h"
        IO.FS.writeFile h structDeepHeader
        let prog := structDeepProgram h.toString
        ioRun prog structDeepExpected
        selfhostCompileRun prog structDeepExpected
        selfhostCompileRun prog structDeepExpected (flags := #["--rc"]) },
    { name := "c_struct: a byte-array field passes and returns by value, in both compilers (C8)", run := fun _ => do
        let dir ← IO.FS.createTempDir
        let h := dir / "wiz_ab.h"
        IO.FS.writeFile h structArrayHeader
        let prog := structArrayProgram h.toString
        ioRun prog structArrayExpected
        selfhostCompileRun prog structArrayExpected
        selfhostCompileRun prog structArrayExpected (flags := #["--rc"]) },
    { name := "c_struct: a field at quantity 0 is not erased yet: its type is still checked and the C struct still carries it (C8)", run := fun _ => do
        -- (the shape `agent/sh-cstruct` @ 02342c6c erases: kind `e`, a slot only in Wiz)
        selfhostCheckFails "import Prelude\nc_struct Q where\n  0 xs : List Nat\n  y : Nat\n"
          "input.wiz:2:1: error: c_struct field xs: a field must be Nat, UInt64, Float64, String, Bool, a foreign type, another c_struct or (with a header) Bytes\n"
        let some c ← selfhostC structErasedProbe | return
        check ((c.splitOn "c->tag = rt_in_nat").length > 1)
          s!"the 0-quantity field is erased from the C struct:\n{c.take 2000}" },
    { name := "a Wiz library (--lib, --no-main, --header) used by a C program, with the handle functions (21s)", run := fun _ => do
        libRunC libSrc libMain libExpected
        selfhostLibRun libSrc libMain libExpected (flags := #["--lib"])
        selfhostLibRun libSrc libMain libExpected (flags := #["--no-main", "--rc"]) },
    { name := "implemented_by: compiled code runs the implementation, in both compilers (21t)", run := fun _ =>
        ffiAgrees implProgram "4\n42\n" },
    { name := "the self-hosted frontend: implemented_by is checked as in the Lean frontend (21t)", run := fun _ =>
        selfhostAgreesIO implHeader implDecls },
    { name := "import_c binds a header's functions and glue calls them (stage 30)", run := fun _ => do
        let header := "static inline unsigned long hdr_add(unsigned long a, unsigned long b) { return a + b; }\n" ++
          "static inline unsigned long hdr_mul(unsigned long a, unsigned long b) { return a * b; }\n" ++
          "static inline unsigned long hdr_sub(unsigned long a, unsigned long b) { return a - b; }\n"
        let prog := "import IO\nimport_c \"h.h\" (pure)\n" ++
          "glue twice (n : Nat) : Nat := \"return hdr_add(n, n);\"\n" ++
          "glue square (n : Nat) : Nat := \"return hdr_mul(n, n);\"\n" ++
          "glue sub (a b : Nat) : Nat := \"return hdr_sub(a, b);\"\n" ++
          "def main : IO Unit := do\n  IO.println (Nat.toString (C.hdr_add 20 22));\n" ++
          "  IO.println (Nat.toString (twice 21));\n  IO.println (Nat.toString (square 7));\n" ++
          "  IO.println (Nat.toString (sub 40 10))"
        selfhostLinkRun [("main.wiz", prog), ("h.h", header)] "42\n42\n49\n30\n"
        selfhostLinkRun [("main.wiz", prog), ("h.h", header)] "42\n42\n49\n30\n" (flags := #["--rc"]) },
    { name := "Bytes (C11): the type and its operations, in the Lean toolchain and the self-hosted one (stage 30)", run := fun _ =>
        ffiAgrees bytesProgram bytesExpected },
    { name := "Bytes: a buffer argument and a byte-array struct field through import_c (stage 30)", run := fun _ => do
        let h ← writeBytesHeader
        let prog := bytesFfiProgram h
        ioRun prog bytesFfiExpected
        selfhostCompileRun prog bytesFfiExpected
        selfhostCompileRun prog bytesFfiExpected (flags := #["--rc"]) },
    { name := "Bytes (21ag): the encodings (ofUtf8/toUtf8, ofString/toString, ofLatin1/toLatin1), in both toolchains", run := fun _ =>
        ffiAgrees bytesEncProgram bytesEncExpected },
    { name := "Bytes (21ag): one UTF-8 rule — the differential table through both decoders and three encoders", run := fun _ =>
        ffiAgrees utf8Program utf8Expected },
    -- (#422, expected slow) the pattern `bytesEncProgram` works around: a closed `match`
    -- scrutinee is evaluated while the self-hosted compiler compiles (about 2 s at
    -- `fib 16` and four times that per two more levels, against 0.4 s let-bound). Both
    -- must still compile within `selfhostCompileRun`'s 300 s; the note keeps the gap
    -- visible until #422 is fixed, when the two times should match
    { name := "a closed match scrutinee is evaluated at compile time (expected slow, #422)", run := fun _ => do
        ioRun closedScrutInline "nz\n"
        let t0 ← IO.monoMsNow
        selfhostCompileRun closedScrutInline "nz\n"
        let t1 ← IO.monoMsNow
        selfhostCompileRun closedScrutLet "nz\n"
        let t2 ← IO.monoMsNow
        note s!"#422: inline scrutinee {t1 - t0} ms, let-bound {t2 - t1} ms" },
    { name := "Bytes (21ag): Array ↔ Bytes and the slice/append/eq boundaries, in both toolchains", run := fun _ =>
        ffiAgrees bytesArrayProgram bytesArrayExpected },
    { name := "Bytes (21ag): a char*/uint8_t*/unsigned char* buffer and its length, borrowed or copied for the call, in both toolchains", run := fun _ => do
        let dir ← IO.FS.createTempDir
        let h := dir / "wiz_bytes2.h"
        let hi := dir / "wiz_bytes2_io.h"
        IO.FS.writeFile h bytesPtrHeader
        IO.FS.writeFile hi bytesPtrIoHeader
        let prog := bytesPtrProgram h.toString hi.toString
        ioRun prog bytesPtrExpected
        selfhostCompileRun prog bytesPtrExpected
        selfhostCompileRun prog bytesPtrExpected (flags := #["--rc"]) },
    { name := "Bytes (21ag): #reduce in the self-hosted checker (the Prelude's Bytes model)", run := fun _ =>
        selfhostCheckFile
          ("import Prelude\n" ++
           "#reduce Nat.beq (Bytes.size (Bytes.ofList (List.cons 1 (List.cons 2 (List.cons 300 .nil))))) 3\n" ++
           "#reduce Nat.beq (Bytes.get (Bytes.ofList (List.cons 7 (List.cons 8 .nil))) 1) 8\n" ++
           "#reduce Nat.beq (Bytes.get (Bytes.ofList (List.cons 7 .nil)) 9) 0\n" ++
           "#reduce Bytes.eq (Bytes.ofList (List.cons 1 .nil)) (Bytes.ofList (List.cons 1 .nil))\n" ++
           "#reduce Bytes.eq (Bytes.ofList (List.cons 1 .nil)) (Bytes.ofList (List.cons 2 .nil))\n" ++
           "#reduce Nat.beq (Bytes.size (Bytes.slice (Bytes.ofList (List.cons 1 (List.cons 2 (List.cons 3 .nil)))) 2 9)) 1\n" ++
           "#reduce Nat.beq (Bytes.size (Bytes.append (Bytes.ofList (List.cons 1 .nil)) (Bytes.ofList (List.cons 2 .nil)))) 2\n" ++
           "#reduce Nat.beq (Bytes.size (Bytes.ofString \"a\\x00b\")) 1\n" ++
           "#reduce Nat.beq (Bytes.size (Bytes.ofUtf8 \"a\\x00b\")) 3\n" ++
           "#reduce Bytes.ofList (List.cons 1 (List.cons 2 .nil))\n")
          "con((#1, (tt, tt)))\ncon((#1, (tt, tt)))\ncon((#1, (tt, tt)))\ncon((#1, (tt, tt)))\ncon((#0, (tt, tt)))\ncon((#1, (tt, tt)))\ncon((#1, (tt, tt)))\ncon((#1, (tt, tt)))\ncon((#1, (tt, tt)))\ncon((#0, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (con((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (con((#0, (tt, tt))), (tt, tt))))), (tt, tt))))), (tt, tt))))\n" },
    { name := "Bytes (21ag): a c_struct with a Bytes field through glue, in both toolchains", run := fun _ => do
        let dir ← IO.FS.createTempDir
        let h := dir / "wiz_bytes2.h"
        IO.FS.writeFile h bytesPtrHeader
        let prog := bytesGlueProgram h.toString
        ioRun prog bytesGlueExpected
        selfhostCompileRun prog bytesGlueExpected
        selfhostCompileRun prog bytesGlueExpected (flags := #["--rc"]) },
    { name := "the self-hosted frontend: a Bytes c_struct field takes a header, as in the Lean frontend (stage 30)", run := fun _ =>
        selfhostAgreesIO "" [
          ("c_struct \"wiz_byte_msg\" (header := \"wiz_bytes.h\") Msg where\n  data : Bytes\n  n : Nat\n", true),
          ("c_struct \"struct b\" B where\n  data : Bytes\n", false)] },
    -- (B12) a native representation: the type's values are the implementation's, in both
    -- toolchains and in both memory modes. `wnat_of`/`wnat_bits` keep a word as a boxed
    -- Nat (the host's `wiz_val` and the self-hosted `V` are both `uintptr_t`).
    { name := "(B12) native representation: implemented_by mk/get on a sealed type, built and read back by the host and by the self-hosted compiler", run := fun _ => do
        let prog := "import IO\nlink_c \"c/wnat.c\"\n" ++
          "sealed inductive WN where\n  | private mk (n : Nat)\n" ++
          "extern \"wnat_of\" WN.ofBits : Nat → WN\n" ++
          "extern \"wnat_bits\" WN.toBits : WN → Nat\n" ++
          "attribute [implemented_by WN.ofBits WN.toBits] WN.mk\n" ++
          "def WN.ofNat (n : Nat) : WN := .mk n\n" ++
          "def WN.toNat (w : WN) : Nat := WN.toBits w\n" ++
          "def WN.add (a b : WN) : WN := .mk (WN.toNat a + WN.toNat b)\n" ++
          "def WN.inc (w : WN) : WN := match w with\n  | .mk n => .mk (n + 1)\n" ++
          "def WN.sum : List WN → Nat\n  | .nil => 0\n  | .cons w ws => WN.toNat w + WN.sum ws\n" ++
          "def main : IO Unit := do\n" ++
          "  let a := WN.ofNat 40;\n  IO.println (Nat.toString (WN.toNat a));\n" ++
          "  let b := WN.add a (WN.ofNat 2);\n  IO.println (Nat.toString (WN.toNat b));\n" ++
          "  let c := WN.inc b;\n  IO.println (Nat.toString (WN.toNat c));\n" ++
          "  IO.println (Nat.toString (WN.sum (.cons a (.cons b (.cons c .nil)))));\n" ++
          "  IO.println (Nat.toString (match c with\n    | .mk n => n * 2))\n"
        let csrc := "#include <stdint.h>\ntypedef uintptr_t wv;\n" ++
          "wv wnat_of(uint64_t n) { return (wv)((n << 1) | 1); }\n" ++
          "uint64_t wnat_bits(wv v) { return (uint64_t)(v >> 1); }\n"
        let files := [("main.wiz", prog), ("c/wnat.c", csrc)]
        linkRun files reprExpected
        selfhostLinkRun files reprExpected
        selfhostLinkRun files reprExpected (flags := #["--rc"]) },
    { name := "(B12) implemented_by mk/get: the host and the self-hosted frontend accept and reject the same registrations", run := fun _ =>
        selfhostAgreesIO reprHeader reprDecls },
    { name := "(B12) implemented_by mk/get: the diagnostics are the host's (unknown name, unsuitable constructor or getter)", run := fun _ =>
        selfhostLevelErrors [
          ("def f (n : Nat) : Nat := n\nattribute [implemented_by nope] f\n", "unknown declaration 'nope'"),
          ("sealed inductive WM where\n  | private mk (a : Nat) (b : Nat)\n" ++
           "def WM.mkImpl (a b : Nat) : WM := .mk a b\ndef WM.getImpl (w : WM) : Nat := 0\n" ++
           "attribute [implemented_by WM.mkImpl WM.getImpl] WM.mk\n",
           "is not a constructor with exactly one runtime field"),
          ("sealed inductive WM where\n  | private mk (n : Nat)\n" ++
           "def WM.mkImpl (n : Nat) : WM := .mk n\ndef WM.getImpl (n : Nat) : Nat := n\n" ++
           "attribute [implemented_by WM.mkImpl WM.getImpl] WM.mk\n",
           "must take a value of WM as its last argument")] },
    { name := "a link_c file that does not exist is an error, in both toolchains (21t)", run := fun _ => do
        let prog := "import IO\nlink_c \"c/nope.c\"\ndef main : IO Unit := IO.println \"hi\"\n"
        let (s, src, _) ← elabTree [("main.wiz", prog)]
        let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
        unless errs.any (fun e => (e.splitOn "link_c: no file c/nope.c").length > 1) do
          throw (IO.userError s!"the Lean frontend: {errs}")
        selfhostCompileFails prog "error: link_c: no file c/nope.c (paths are relative to the .wiz file)\n" },
    { name := "a C Nat that does not fit the self-hosted runtime's 63 bits is an error, not cut (21p)", run := fun _ => do
        let prog := "import IO\ndef main : IO Unit := do\n  IO.println (Nat.toString (UInt64.toNat (UInt64.ofNat 1000000)));\n" ++
          "  IO.println (Nat.toString (UInt64.toNat (UInt64.sub (UInt64.ofNat 0) (UInt64.ofNat 1))))\n"
        ioRun prog "1000000\n18446744073709551615\n"
        selfhostLinkRun [("main.wiz", prog)] "1000000\n" (fails := some "does not fit in 63 bits")
        selfhostLinkRun [("main.wiz", prog)] "1000000\n" (flags := #["--rc"]) (fails := some "does not fit in 63 bits") },
    { name := "the self-hosted frontend: a sealed type has no look-alikes, as in the Lean frontend (22k)", run := fun _ =>
        selfhostAgrees sealHeader [
          ("def same (x : W 8) : W 8 := x\ndef get {w : Nat} : W w → Nat\n  | .mk n => n\ndef five : Nat := get (W.mk 5 : W 8)\n", true),
          ("def bad (x : L 8) : W 8 := x\n", false),
          ("def bad (x : W 8) : L 8 := x\n", false),
          ("def bad (x : V 8) : W 8 := x\n", false),
          ("def bad (x : W 8) : W 16 := x\n", false),
          ("sealed structure P where\n  x : Nat\n", false)] },
    { name := "the self-hosted frontend: inductive recursion is guarded (positivity), as in the Lean frontend", run := fun _ =>
        selfhostAgrees "" [
          ("inductive Rose where\n  | leaf\n  | node (l : Rose) (r : Rose)\n", true),
          ("inductive Bad where\n  | mk (x : Bad)\n", true),
          ("inductive Bad where\n  | mk (f : Bad → Prop)\n", false),
          ("inductive Bad where\n  | mk (f : (Bad → Prop) → Prop)\n", false),
          ("inductive Bad where\n  | mk (xs : List Bad)\n", false)] },
    { name := "the self-hosted frontend: constructor parameters from the expected type (21j)", run := fun _ =>
        selfhostAgrees ("def Code : Bool → Type\n  | .true => Nat\n  | .false => Bool\n" ++
          "structure Tagged (b : Bool) where\n  val : Code b\n")
          [("def t : Tagged .true := Tagged.mk 3\ndef f : Tagged .false := Tagged.mk .true\n" ++
              "def g (x : Nat) : Tagged .true := Tagged.mk (Nat.succ x)\n", true),
           ("def bad : Tagged .false := Tagged.mk 3\n", false)] },
    { name := "the self-hosted frontend: literal patterns at other types, hex and binary numerals, as in the Lean frontend (13q)", run := fun _ =>
        selfhostSameNats (litHeader ++ litProgram) litCases },
    { name := "the self-hosted frontend: literal pattern verdicts, as in the Lean frontend (13q)", run := fun _ =>
        selfhostAgrees litHeader litDecls },
    { name := "the self-hosted frontend: `x :: xs` is List.cons, as in the Lean frontend (13k)", run := fun _ => do
        let header := "def len : List Nat → Nat\n  | .nil => 0\n  | x :: xs => Nat.succ (len xs)\n"
        selfhostAgrees header [
          ("def ys : List Nat := 1 :: 2 :: List.nil\n#eval len ys\n", true),
          ("def bad : List Nat := 1 :: 2\n", false)]
        selfhostSameNats header [("len (1 :: 2 :: List.cons 3 List.nil)", 3)] },
    { name := "the self-hosted frontend: structure update, plain and nested, as in the Lean frontend (13i, 13p)", run := fun _ =>
        selfhostSameNats (updHeader ++ updProgram) updCases },
    { name := "the self-hosted frontend: structure update verdicts, as in the Lean frontend (13i, 13p)", run := fun _ =>
        selfhostAgrees updHeader updDecls },
    { name := "the self-hosted frontend checks itself (Lex, Parse, Kernel, CParse, CGlue and Frontend.wiz)", run := fun _ => do
        let srcs ← Selfhost.frontendFiles.mapM (fun (f : String) => IO.FS.readFile f)
        let src := "\n".intercalate srcs
        let body := "\n".intercalate ((src.splitOn "\n").filter (!·.startsWith "import"))
        -- every declaration is reported, none with an error
        let decls := (src.splitOn "\n").filter fun l =>
          ["def ", "partial def ", "inductive ", "structure ", "extern "].any (fun (p : String) => l.startsWith p)
        -- a `structure` also reports each projection (`T.f`), which is not a source line
        let structs : List String := (src.splitOn "\n").filterMap fun l =>
          if l.startsWith "structure " then
            let n := ((l.drop 10).takeWhile (fun c => c != ' ' && c != '(')).toString
            if n.isEmpty then none else some n
          else none
        let isProjection (l : String) : Bool := structs.any fun T => l.startsWith (T ++ ".")
        let some out ← selfhostOutputPeak ("import Prelude\n" ++ body) 4096 | pure ()
        let lines := (out.splitOn "\n").filter (· != "")
        for l in lines do
          if l.startsWith "error" || l.startsWith "parse error" then throw (IO.userError l)
        let projs := (lines.filter isProjection).length
        unless lines.length == decls.length + projs do
          throw (IO.userError s!"{lines.length} lines for {decls.length} declarations and {projs} projections") },
    -- (agent/selfhost-memory) The parser's `mutual` block of partial definitions: the
    -- checker used to retain an inlined value built with `tmSubst` at every constant use,
    -- a tree copy of a shared term. The block peaks at ~3.2 GB before the `substIfAny`
    -- fix (and the whole self-check at 10.7 GB); it is ~17 MB now. The bound is loose
    -- enough for the compiler's own heap, and catches the exponential cache again.
    { name := "the selfhost checker: the parser's mutual block stays under 512 MB", run := fun _ => do
        let strip := fun (s : String) => "\n".intercalate ((s.splitOn "\n").filter (!·.startsWith "import"))
        let lex ← IO.FS.readFile "selfhost/Lex.wiz"
        let parse ← IO.FS.readFile "selfhost/Parse.wiz"
        let parseHead := (parse.splitOn "\ndef sexpr").headD parse
        let src := "import Prelude\n" ++ strip lex ++ "\n" ++ strip parseHead
        let some out ← selfhostOutputPeak src 512
          | pure ()
        for l in out.splitOn "\n" do
          if l.startsWith "error" || l.startsWith "parse error" then throw (IO.userError l)
        checkChecked src out },
    -- (agent/checker-mem) The grammar has no `if`: it is a flat application spine, so a
    -- nested unparenthesised `if` in a then branch must take the first `else` (the
    -- dangling else). Before the split fix the outer else was applied as a function
    -- (`not a function: its type is μ0(…)`); the self-check hit this in CParse.wiz.
    { name := "the self-hosted frontend: a nested if in a then branch (the dangling else)", run := fun _ => do
        selfhostCheckFile ("import Prelude\n" ++
          "def f (x : Nat) : Nat := x\n" ++
          "def g (b1 b2 : Bool) : Nat :=\n  if b1 then\n    if b2 then (f 1)\n    else (f 2)\n  else (f 3)\n" ++
          "def h (b1 b2 : Bool) : Nat :=\n  if (if b1 then b2 else b1) then (f 4) else (f 5)\n")
          ("f : (x0 : Nat) → Nat\n" ++
           "g : (x0 : Bool) → (x1 : Bool) → Nat\n" ++
           "h : (x0 : Bool) → (x1 : Bool) → Nat\n") },
    { name := "the self-hosted frontend: universe levels, Sort and Prop, as in the Lean frontend (A15/U1)", run := fun _ =>
        let header := "def id.{u} {A : Type u} (x : A) : A := x\n" ++
          "def id2.{u, v} {A : Type u} {B : Type v} (x : A) (y : B) : A := x\n" ++
          "def prodT.{u, v} (A : Type u) (B : Type v) : Type (max u v) := A × B\n" ++
          "def imp.{u} (A : Type u) (P : Prop) : Prop := A → P\n" ++
          "def p : Prop := (P : Prop) → P → P\n" ++
          "def s.{u} : Sort (u + 1) := Sort u\n" ++
          "def t : Type 1 := Type\n" ++
          "def n : Nat := id.{0} 5\n" ++
          "def m : Nat := id 5\n" ++
          "def m2.{u} (A : Type u) (x : A) : A := id x\n"
        selfhostAgrees header [
          ("def n2 : Nat := id.{0} 5\n", true),
          ("def m3 : Nat := id 5\n", true),
          ("def m4.{u} (A : Type u) (x : A) : A := id x\n", true),
          ("def t2 : Type 1 := Type\n", true),
          ("def t3 : Sort 2 := Sort 1\n", true),
          -- unknown level, a proposition that is a type, a universe mismatch, a wrong
          -- number of levels, and an unsolved level metavariable: rejected by both
          ("def bad.{u} : Type v := Nat\n", false),
          ("def bad2 : Prop := Type\n", false),
          ("def bad3.{u} : Sort u := Sort u\n", false),
          ("def bad4.{u} : Type u := Type u\n", false),
          ("def bad5 : Nat := id.{1, 2} 5\n", false),
          ("axiom bad6 : Sort _\n", false)] },
    { name := "the self-hosted frontend: universe levels are inferred at a constant's use (A15/U1)", run := fun _ =>
        selfhostSameNats ("def id.{u} {A : Type u} (x : A) : A := x\n" ++
          "def id2.{u, v} {A : Type u} {B : Type v} (x : A) (y : B) : A := x\n")
          [("id.{0} 5", 5), ("id 5", 5), ("id2 5 7", 5), ("id2 3 4", 3)] },
    { name := "modules: an imported module's declarations are in scope", run := fun _ =>
        selfhostCheckModules
          [("B.wiz", "import Prelude\ndef one : Nat := 1\n"),
           ("input.wiz", "import Prelude\nimport B\ndef two : Nat := one\n")]
          "one : Nat\ntwo : Nat\n" },
    { name := "modules: a transitive import (A imports B, B imports C)", run := fun _ =>
        selfhostCheckModules
          [("C.wiz", "import Prelude\ndef three : Nat := 3\n"),
           ("B.wiz", "import Prelude\nimport C\ndef two : Nat := three\n"),
           ("input.wiz", "import Prelude\nimport B\ndef four : Nat := three + two\n")]
          "three : Nat\ntwo : Nat\nfour : Nat\n" },
    { name := "modules: a module imported twice is checked once (a diamond)", run := fun _ =>
        selfhostCheckModules
          [("D.wiz", "import Prelude\ndef four : Nat := 4\n"),
           ("B.wiz", "import Prelude\nimport D\ndef b : Nat := four\n"),
           ("C.wiz", "import Prelude\nimport D\ndef c : Nat := four\n"),
           ("input.wiz", "import Prelude\nimport B\nimport C\ndef sum2 : Nat := b + c\n")]
          "four : Nat\nb : Nat\nc : Nat\nsum2 : Nat\n" },
    { name := "modules: an import cycle is an error naming it", run := fun _ =>
        selfhostCheckModules
          [("B.wiz", "import Prelude\nimport C\n"),
           ("C.wiz", "import Prelude\nimport B\n"),
           ("input.wiz", "import Prelude\nimport B\n")]
          "error: import cycle: B -> C -> B\n" },
    { name := "modules: a missing module is an error naming it", run := fun _ =>
        selfhostCheckModules
          [("input.wiz", "import Prelude\nimport Nope\n")]
          "error: cannot find module Nope\n" },
    { name := "modules: a duplicate name across modules is rejected", run := fun _ =>
        selfhostCheckModules
          [("B.wiz", "import Prelude\ndef x : Nat := 1\n"),
           ("input.wiz", "import Prelude\nimport B\ndef x : Nat := 2\n")]
          "x : Nat\nerror: 'x' has already been declared\n" },
    { name := "modules: a -I root is searched before the working directory", run := fun _ => do
        let files := [("sub/B.wiz", "import Prelude\ndef one : Nat := 1\n"),
                      ("input.wiz", "import Prelude\nimport B\n")]
        -- without the root, B is not found; with it, it is
        selfhostCheckModules files "error: cannot find module B\n"
        selfhostCheckModules files "one : Nat\n" (args := #["-I", "sub"]) },
    { name := "modules: a dotted import is a path (A.B.C is A/B/C.wiz)", run := fun _ =>
        selfhostCheckModules
          [("A/B/C.wiz", "import Prelude\ndef deep : Nat := 3\n"),
           ("input.wiz", "import Prelude\nimport A.B.C\ndef one : Nat := deep\n")]
          "deep : Nat\none : Nat\n" },
    { name := "modules: the -I roots are searched in order", run := fun _ => do
        let files := [("r1/B.wiz", "import Prelude\ndef one : Nat := 1\n"),
                      ("r2/B.wiz", "import Prelude\ndef one : Bool := Bool.true\n"),
                      ("input.wiz", "import Prelude\nimport B\n#check one\n")]
        -- the first root with the file wins
        selfhostCheckModules files "one : Nat\nNat\n" (args := #["-I", "r1", "-I", "r2"])
        selfhostCheckModules files "one : Bool\nBool\n" (args := #["-I", "r2", "-I", "r1"])
        -- a root without the file is skipped, not a failure
        let fallthrough := [("r2/A.wiz", "import Prelude\ndef a : Nat := 1\n"),
                            ("input.wiz", "import Prelude\nimport A\ndef two : Nat := a\n")]
        selfhostCheckModules fallthrough "a : Nat\ntwo : Nat\n" (args := #["-I", "r1", "-I", "r2"]) },
    { name := "modules: an import cycle through three modules names the whole path", run := fun _ =>
        selfhostCheckModules
          [("B.wiz", "import Prelude\nimport C\n"),
           ("C.wiz", "import Prelude\nimport D\n"),
           ("D.wiz", "import Prelude\nimport B\n"),
           ("input.wiz", "import Prelude\nimport B\n")]
          "error: import cycle: B -> C -> D -> B\n" },
    { name := "modules: a duplicate name in two imported modules is rejected", run := fun _ =>
        selfhostCheckModules
          [("B.wiz", "import Prelude\ndef x : Nat := 1\n"),
           ("C.wiz", "import Prelude\ndef x : Nat := 2\n"),
           ("input.wiz", "import Prelude\nimport B\nimport C\n")]
          "x : Nat\nerror: 'x' has already been declared\n" },
    { name := "modules: the cache key includes the module graph", run := fun _ => do
        let root := "import Prelude\nimport B\ndef two : Nat := one\n"
        let files1 := [("B.wiz", "import Prelude\ndef one : Nat := 1\n"), ("input.wiz", root)]
        let files2 := [("B.wiz", "import Prelude\ndef one : Nat := 2\n"), ("input.wiz", root)]
        let some k1 ← selfhostModuleOutput files1 #["--key"] | return
        let some k1' ← selfhostModuleOutput files1 #["--key"] | return
        let some k2 ← selfhostModuleOutput files2 #["--key"] | return
        unless k1 == k1' do throw (IO.userError s!"the key is not stable: {k1} / {k1'}")
        if k1 == k2 then throw (IO.userError s!"the key ignores a module's text: {k1}") },
    { name := "modules: the cache key includes a transitive module's text", run := fun _ => do
        let root := "import Prelude\nimport B\ndef two : Nat := one\n"
        let b := "import Prelude\nimport C\ndef one : Nat := c\n"
        let files1 := [("B.wiz", b), ("C.wiz", "import Prelude\ndef c : Nat := 1\n"),
                       ("input.wiz", root), ("Unused.wiz", "import Prelude\ndef u : Nat := 0\n")]
        let files2 := [("B.wiz", b), ("C.wiz", "import Prelude\ndef c : Nat := 2\n"),
                       ("input.wiz", root), ("Unused.wiz", "import Prelude\ndef u : Nat := 0\n")]
        let files3 := [("B.wiz", b), ("C.wiz", "import Prelude\ndef c : Nat := 1\n"),
                       ("input.wiz", root), ("Unused.wiz", "import Prelude\ndef u : Nat := 9\n")]
        let some k1 ← selfhostModuleOutput files1 #["--key"] | return
        let some k1' ← selfhostModuleOutput files1 #["--key"] | return
        let some k2 ← selfhostModuleOutput files2 #["--key"] | return
        let some k3 ← selfhostModuleOutput files3 #["--key"] | return
        unless k1 == k1' do throw (IO.userError s!"the key is not stable: {k1} / {k1'}")
        if k1 == k2 then throw (IO.userError s!"the key ignores an imported module's text: {k1}")
        unless k1 == k3 do throw (IO.userError s!"the key depends on a module outside the graph: {k1} / {k3}") },
    { name := "modules: IO, Std and Sys load the embedded Prelude once", run := fun _ =>
        selfhostCheckModules
          [("B.wiz", "import IO\nimport Std\ndef y : Nat := 1\n"),
           ("input.wiz", "import Prelude\nimport IO\nimport Std\nimport Sys\nimport B\ndef x : Nat := y\n")]
          "y : Nat\nx : Nat\n" },
    { name := "modules: the CLI root spellings (-Idir, --include DIR, --include=DIR)", run := fun _ => do
        let files := [("sub/B.wiz", "import Prelude\ndef one : Nat := 1\n"),
                      ("input.wiz", "import Prelude\nimport B\ndef two : Nat := one\n")]
        selfhostCheckModules files "one : Nat\ntwo : Nat\n" (args := #["-Isub"])
        selfhostCheckModules files "one : Nat\ntwo : Nat\n" (args := #["--include", "sub"])
        selfhostCheckModules files "one : Nat\ntwo : Nat\n" (args := #["--include=sub"]) },
    { name := "modules: the compiler driver resolves its -I and --include roots", run := fun _ => do
        let files := [("sub/B.wiz", "import Prelude\ndef one : Nat := 41\n"),
                      ("input.wiz", "import Prelude\nimport B\ndef main : IO Unit := IO.println (Nat.toString (one + 1))\n")]
        for args in [#["-I", "sub"], #["-Isub"], #["--include", "sub"], #["--include=sub"]] do
          let some c ← selfhostModuleC files args | return
          unless (c.splitOn "/* one : Nat */\n").length > 1 do
            throw (IO.userError s!"the module is missing from the C ({args}): {c.take 300}") },
    { name := "layout: an if branch may start on the next line with match or let, and long chains parse", run := fun _ =>
        selfhostChecks "import Prelude\ndef branch (b : Bool) (n : Nat) : Nat :=\n  if b then 1 else\n  match n with\n  | .zero => 0\n  | .succ k => k\ndef nested (b c : Bool) : Nat :=\n  if b then 2 else\n  if c then\n    match b with\n    | .true => 3\n    | .false => 4\n  else 5\ndef letBranch (b : Bool) : Nat :=\n  if b then 1 else\n  let x := 2;\n  x\ndef chain (a b c d e f g h : Bool) : Nat :=\n  if a then 1 else\n  if b then 2 else\n  if c then 3 else\n  if d then 4 else\n  if e then 5 else\n  if f then 6 else\n  if g then 7 else\n  if h then 8 else\n  9\n#check branch\n#check letBranch\n#check chain\n" },
    { name := "the boolean operators parse, short-circuit and bind as on the host; a tuple pattern binds", run := fun _ =>
        selfhostCompileRun ("import Prelude\npartial def boom : Bool := boom\ndef fstP (p : Nat × Nat) : Nat := match p with\n  | (a, b) => a\ndef pairHead : List (Nat × Nat) → Nat\n  | .nil => 0\n  | .cons (a, b) _ => a\ndef main : IO Unit := do\n  IO.println (if Bool.true && Bool.false then \"and-t\" else \"and-f\");\n  IO.println (if Bool.false && boom then \"and-boom\" else \"and-short\");\n  IO.println (if Bool.true || boom then \"or-short\" else \"or-boom\");\n  IO.println (if !Bool.false then \"not-t\" else \"not-f\");\n  IO.println (if Bool.true || Bool.false && Bool.false then \"prec-ok\" else \"prec-bad\");\n  IO.println (Nat.toString (fstP (3, 4)));\n  IO.println (Nat.toString (pairHead (.cons (5, 6) .nil)))\n")
          "and-f\nand-short\nor-short\nnot-t\nprec-ok\n3\n5\n" },
    -- (A17/A18) The host and the self-hosted compiler agree on the same program
    { name := "A17: list literals (nested, empty, in a pattern) agree with the host", run := fun _ =>
        selfhostAgreesHost surfaceListProgram },
    { name := "A17: `&&`/`||` short-circuit, bind as on the host and agree with it", run := fun _ =>
        selfhostAgreesHost surfaceBoolProgram },
    { name := "A18: as-patterns (in equations, nested, over a variable, in a tuple) agree with the host", run := fun _ =>
        selfhostAgreesHost surfaceAsProgram },
    { name := "A18: tuple patterns (a pair, a nested triple, a tuple in a list) agree with the host", run := fun _ =>
        selfhostAgreesHost surfaceTupleProgram },
    { name := "A18: `let (x, y)` (and three components, nested) agrees with the host", run := fun _ =>
        selfhostAgreesHost surfaceLetPairProgram },
    { name := "A18: `let () := u; b` agrees with the host", run := fun _ =>
        selfhostAgreesHost surfaceLetUnitProgram },
    -- (A19) the coinductive surface is the one frontend feature with no case at all:
    -- pin the missing half rather than assuming parity (`command.coinductive` is in
    -- `Tables.wiz`, the host elaborates it, and the self-hosted frontend rejects it).
    { name := "A19: the coinductive surface is not ported: the host accepts `coinductive`, the self-hosted frontend rejects it", run := fun _ =>
        selfhostVerdicts "" [
          ("coinductive Stream (A : Type) where\n  head : A\n  tail : Stream A\n", true, false)] },
    -- (21n) `private` is module-scoped: the importing modules are A <- B <- input
    { name := "modules: a private name is visible in its module and rejected in an importer (21n)", run := fun _ =>
        selfhostCheckModules
          [("A.wiz", "import Prelude\nprivate def secret : Nat := 42\ndef visible : Nat := secret\n"),
           ("B.wiz", "import Prelude\nimport A\ndef fromA : Nat := visible\ndef bad : Nat := secret\n"),
           ("input.wiz", "import Prelude\nimport B\ndef total : Nat := fromA\n#check secret\n")]
          ("secret : Nat\nvisible : Nat\nfromA : Nat\n" ++
           "error: 'secret' is private to module A\n" ++
           "total : Nat\nerror: 'secret' is private to module A\n") },
    { name := "modules: a private type and constructor are rejected in an importer (21n)", run := fun _ =>
        selfhostCheckModules
          [("A.wiz", "import Prelude\nprivate inductive S where\n  | mk (n : Nat)\n" ++
             "def s : S := S.mk 1\ndef nOf : S → Nat\n  | .mk n => n\n"),
           ("input.wiz", "import Prelude\nimport A\ndef bad : Nat := S.mk 2\ndef badTy (s : S) : Nat := 0\n")]
          ("S : U0\ns : S\nnOf : (x0 : S) → Nat\n" ++
           "error: 'S.mk' is private to module A\nerror: 'S' is private to module A\n") },
    { name := "modules: two modules' private names of the same spelling do not clash (21n)", run := fun _ =>
        selfhostCheckModules
          [("A.wiz", "import Prelude\nprivate def secret : Nat := 1\ndef a : Nat := secret\n"),
           ("B.wiz", "import Prelude\nprivate def secret : Nat := 2\ndef b : Nat := secret\n"),
           ("input.wiz", "import Prelude\nimport A\nimport B\ndef sum : Nat := a + b\n")]
          "secret : Nat\na : Nat\nsecret : Nat\nb : Nat\nsum : Nat\n" },
    { name := "modules: a source name is declared once per module, private or not (21n)", run := fun _ =>
        selfhostCheckModules
          [("input.wiz", "import Prelude\nprivate def p : Nat := 1\ndef p : Nat := 2\n" ++
             "def q : Nat := 3\nprivate def q : Nat := 4\nprivate def r : Nat := 5\nprivate def r : Nat := 6\n")]
          ("p : Nat\nerror: 'p' has already been declared\nq : Nat\nerror: 'q' has already been declared\n" ++
           "r : Nat\nerror: 'r' has already been declared\n") },
    { name := "modules: a public name shadows another module's private one (21n)", run := fun _ =>
        selfhostCheckModules
          [("A.wiz", "import Prelude\nprivate def x : Bool := .true\ndef a : Bool := x\n"),
           ("B.wiz", "import Prelude\ndef x : Nat := 2\n"),
           ("input.wiz", "import Prelude\nimport A\nimport B\n#check x\n#check a\n")]
          "x : Bool\na : Bool\nx : Nat\nNat\nBool\n" },
    { name := "modules: a private name is rejected in an importer with the host's message shape, by the compiler too (A8, 21n)", run := fun _ => do
        let files :=
          [("A.wiz", "import Prelude\nprivate def secret : Nat := 42\ndef visible : Nat := secret\n"),
           ("B.wiz", "import Prelude\nimport A\ndef fromA : Nat := visible\ndef bad : Nat := secret\n"),
           ("input.wiz", "import Prelude\nimport B\ndef total : Nat := fromA\n#check secret\n")]
        let phrase := "'secret' is private to module A"
        let errs ← hostModuleErrors files
        unless errs.any (· == phrase) do
          throw (IO.userError s!"the Lean frontend's message is not {repr phrase}:\n{errs}")
        -- (the checker's pinned output is the test above; the compiler reports the same
        -- error, and writes no C)
        selfhostModuleCompileFails files [phrase] },
    { name := "the one-shot path (checkFile) is one module, input (21n)", run := fun _ =>
        selfhostCheckModules
          [("input.wiz", "import Prelude\nprivate def secret : Nat := 42\ndef use : Nat := secret\n#check use\n")]
          "secret : Nat\nuse : Nat\nNat\n" (args := #["--oneshot"]) },
    { name := "the self-hosted backend: private declarations compile and run (21n)", run := fun _ =>
        selfhostCompileRun ("import Prelude\n" ++
          "private def secret : Nat := 40\n" ++
          "private inductive S where\n  | mk (n : Nat)\n" ++
          "def useS : S → Nat\n  | .mk n => n\n" ++
          "private structure P where\n  x : Nat\n" ++
          "def useP (p : P) : Nat := p.x\n" ++
          "def main : IO Unit := do\n  IO.println (Nat.toString (secret + useS (S.mk 1) + useP (P.mk 1)))\n")
          "42\n" },
    -- (cubical M1) `selfhost/Cof.wiz`: the shared interval/cofibration layer. The case
    -- compiles the module with the Lean toolchain and again with the self-hosted
    -- compiler and backend, and compares both programs' output.
    { name := "the cofibration solver (cubical M1): DNF laws, entailment, substitution and Path boundaries", run := fun _ => do
        let cof ← IO.FS.readFile "selfhost/Cof.wiz"
        let body := "\n".intercalate ((cof.splitOn "\n").filter (!·.startsWith "import"))
        let src := "import IO\n" ++ body ++ "\n" ++ cofProbes
        ioRun src cofProbesExpected
        selfhostCompileRun src cofProbesExpected },
    { name := "the self-hosted frontend: a class, instances for Nat and Bool, and a generic function (A10)", run := fun _ =>
        selfhostCheckFile classCore classCoreExpected },
    { name := "the self-hosted frontend: `where` instances, a multi-method class, and a class with instance parameters (A10)", run := fun _ => do
        selfhostCheckFile classWhere classWhereExpected
        selfhostCheckFile classNested classNestedExpected
        selfhostCheckFile classInstParam classInstParamExpected },
    { name := "the self-hosted frontend: a missing instance is an error naming the class (A10)", run := fun _ =>
        selfhostCheckFile classMissing classMissingExpected },
    { name := "the self-hosted frontend: a duplicate instance is an error (A10)", run := fun _ =>
        selfhostCheckFile classDup classDupExpected },
    { name := "type classes and instances agree with the Lean frontend (A10)", run := fun _ =>
        selfhostAgrees classAgreeHeader [
          ("class Default (A : Type) where\n  d : A\ninstance instDefaultNat : Default Nat := Default.mk 7\ndef get {A : Type} [Default A] : A := Default.d\ndef seven : Nat := get\n", true),
          ("class Two (A : Type) where\n  one : A\n  two : A\ninstance instTwoNat : Two Nat where\n  two := 20\n  one := 10\ndef sum2 {A : Type} [Two A] (add : A → A → A) : A := add Two.one Two.two\n", true),
          ("class MyMonad (m : Type → Type) where\n  ret : Nat\nclass MyHandler (e : Type) (m : Type → Type) where\n  h : Nat\ninstance instMyMonadOption : MyMonad Option := MyMonad.mk 0\ninstance instMyHandlerNatOption : MyHandler Nat Option := MyHandler.mk 1\nclass MyCommute (e₁ e₂ : Type) (m : Type → Type) [i : MyMonad m] [h₁ : MyHandler e₁ m] [h₂ : MyHandler e₂ m] where\n  comm : Nat\ninstance instMyCommute : MyCommute Nat Nat Option where\n  comm := 2\n#reduce Nat.beq (@MyCommute.comm Nat Nat Option instMyMonadOption instMyHandlerNatOption instMyHandlerNatOption instMyCommute) 2\n", true),
          -- rejected by both: a private class field, a missing field, too many fields,
          -- an instance for something that is not a class, and a missing instance
          ("class Priv (A : Type) where\n  private d : A\n", false),
          ("class Two (A : Type) where\n  one : A\n  two : A\ninstance instTwoNat : Two Nat := Two.mk 1\n", false),
          ("class Two (A : Type) where\n  one : A\n  two : A\ninstance instTwoNat : Two Nat := Two.mk 1 2 3\n", false),
          ("def Nat.f (n : Nat) : Nat := n\ninstance instNat : Nat.f := instNat\n", false),
          ("class Default (A : Type) where\n  d : A\ndef get {A : Type} [Default A] : A := Default.d\ndef bad : Bool := get\n", false)] },
    { name := "type class verdicts pinned against the Lean frontend (A10: duplicate instances, outParam)", run := fun _ =>
        selfhostVerdicts "" [
          -- (both instances are ordinary candidates in Lean; the self-hosted frontend
          -- rejects two with definitionally equal types, since it has no priorities)
          ("class Default (A : Type) where\n  d : A\ninstance instDefaultNat : Default Nat := Default.mk 7\ninstance instDefaultNat2 : Default Nat := Default.mk 8\n", true, false),
          -- (an output parameter rewrites a class parameter's type; not implemented here)
          ("class MyAdd (A B : Type) (C : outParam Type) where\n  add : A → B → C\ninstance instMyAdd : MyAdd Nat Nat Nat := MyAdd.mk Nat.add\ndef three : Nat := MyAdd.add 1 2\n", true, false)] },
    { name := "the self-hosted backend: a class's dictionary passing compiles and runs (A10)", run := fun _ =>
        selfhostCompileRun classProgram "7\n1\n" },
    { name := "the proof surface: Prop, Sort, equality, refl/rfl, cast and transp, as in the Lean frontend (A16)", run := fun _ => do
        let file := "import Prelude\n" ++
          "def reflNat (n : Nat) : n = n := rfl\n" ++
          "def alwaysTrue : Prop := ∀ (n : Nat), n = n\n#check alwaysTrue\n" ++
          "#check Prop\n#check Sort 0\n#check Sort (max 1 2)\n" ++
          "def S2 : Sort (max 1 2) := Type\n#check S2\n" ++
          "def SProp : Sort 1 := Prop\n#check SProp\n" ++
          "def SU.{u} : Sort (u + 1) := Sort u\n" ++
          "def castId {A B : Type} (e : A = B) (a : A) : B := cast e a\n#check castId\n" ++
          "def transEq {A : Type} {a b : A} (c : Nat) (e : a = b) (f : A → Nat) (h : f a = c) : f b = c :=\n" ++
          "  transp (fun b _ => f b = c) h e\n" ++
          "#check True\n#check False\n" ++
          "def badEq {A : Type} (x y : A) : x = y := rfl\n" ++
          "def badProp : Prop := Type\ndef badSort : Sort 1 := Type 1\n" ++
          "def badCast (e : False) (n : Nat) : Nat := cast e n\n" ++
          "def badLevel : Sort u := Type\n"
        selfhostCheckFile file ("reflNat : (x0 : Nat) → Eq(Nat, x0, x0)\n" ++
          "alwaysTrue : Prop\nProp\nU0\nU0\nU2\nS2 : U1\nU1\nSProp : U0\nU0\nSU : Sort((u)+1)\n" ++
          "castId : (x0 :0 U0) → (x1 :0 U0) → (x2 : Eq(U0, x0, x1)) → (x3 : x0) → x1\n" ++
          "(x0 :0 U0) → (x1 :0 U0) → (x2 : EqTy(x0, x1)) → (x3 : x0) → x1\n" ++
          "transEq : (x0 :0 U0) → (x1 : x0) → (x2 : x0) → (x3 : Nat) → (x4 : Eq(x0, x1, x2)) → " ++
          "(x5 : (x5 : x0) → Nat) → (x6 : Eq(Nat, (x5 x1), x3)) → Eq(Nat, (x5 x2), x3)\n" ++
          "Prop\nProp\n" ++
          "error: type mismatch: expected Eq(x0, x1, x2), got Eq(x0, x1, x1)\n" ++
          "error: type mismatch: expected Prop, got U1\n" ++
          "error: type mismatch: expected U0, got U2\n" ++
          "error: cannot infer the type of this cast: its proof's type is an empty equation, so it no longer shows the target type; write `(cast e t : T)`\n" ++
          "error: unknown universe level 'u'\n") },
    { name := "the proof surface: the Lean and self-hosted frontends agree (A16)", run := fun _ =>
        selfhostAgrees "" [
          ("def reflNat (n : Nat) : n = n := rfl\n", true),
          ("def P : Prop := ∀ (n : Nat), n = n\n", true),
          ("def small : Prop := False → False\n", true),
          ("def S : Sort 1 := Prop\n", true),
          ("def S2 : Sort (max 1 2) := Type\n", true),
          ("def SU.{u} : Sort (u + 1) := Sort u\n", true),
          ("def castId {A B : Type} (e : A = B) (a : A) : B := cast e a\n", true),
          ("def transEq {A : Type} {a b : A} (c : Nat) (e : a = b) (f : A → Nat) (h : f a = c) : f b = c :=\n" ++
            "  transp (fun b _ => f b = c) h e\n", true),
          ("def badEq {A : Type} (x y : A) : x = y := rfl\n", false),
          ("def badProp : Prop := Type\n", false),
          ("def badSort : Sort 1 := Type 1\n", false),
          ("def badCast (e : False) (n : Nat) : Nat := cast e n\n", false)] },
    -- (U2) symbolic levels in an inductive description: the description's level is the
    -- declaration's universe parameter (no closed numeral), which `Repr.{u}`/`Inhabited.{u}`
    -- need (Q4 lifts the tag into the data type's universe)
    { name := "U2: symbolic levels in inductive descriptions (U2/A15): a polymorphic data type, structure and classes", run := fun _ =>
        selfhostCheckFile ("import Prelude\n" ++
          "inductive Box.{u} (A : Type u) : Type u where\n  | mk (a : A)\n" ++
          "structure Wrap.{u} (A : Type u) where\n  val : A\n" ++
          "class Repr.{u} (A : Type u) where\n  repr : A → Nat\n" ++
          "instance instReprNat : Repr Nat where\n  repr := fun n => n\n" ++
          "class Inhabited.{u} (A : Type u) where\n  default : A\n" ++
          "instance instInhabitedNat : Inhabited Nat where\n  default := 42\n" ++
          "def unbox.{u} {A : Type u} (b : Box A) : A := match b with\n  | .mk a => a\n" ++
          "def wget.{u} {A : Type u} (w : Wrap A) : A := w.val\n" ++
          "def unboxNat (b : Box Nat) : Nat := match b with\n  | .mk a => a\n" ++
          "def wgetNat (w : Wrap Nat) : Nat := match w with\n  | .mk a => a\n" ++
          "def reprWrap.{u} {A : Type u} [Repr A] (w : Wrap A) : Nat := Repr.repr w.val\n" ++
          "def defaultNat : Nat := Inhabited.default\n" ++
          "def natBox : Box Nat := Box.mk 7\n" ++
          "def w5 : Wrap Nat := Wrap.mk 5\n" ++
          "#reduce Nat.beq (unbox natBox) 7\n" ++
          "#reduce Nat.beq (wget w5) 5\n" ++
          "#reduce Nat.beq (unboxNat natBox) 7\n" ++
          "#reduce Nat.beq (wgetNat w5) 5\n" ++
          "#reduce Nat.beq (reprWrap w5) 5\n" ++
          "#reduce Nat.beq defaultNat 42\n")
          ("Box : (x0 : Sort((u)+1)) → Sort((u)+1)\n" ++
           "Wrap : (x0 : Sort((u)+1)) → Sort((max(0, u))+1)\n" ++
           "Wrap.val : (x0 :0 Sort((u)+1)) → (x1 : (Wrap.{u} x0)) → x0\n" ++
           "Repr : (x0 : Sort((u)+1)) → Sort((max(0, u))+1)\n" ++
           "Repr.repr : (x0 :0 Sort((u)+1)) → (x1 : (Repr.{u} x0)) → (x2 : x0) → Nat\n" ++
           "instReprNat : (Repr.{0} Nat)\n" ++
           "Inhabited : (x0 : Sort((u)+1)) → Sort((max(0, u))+1)\n" ++
           "Inhabited.default : (x0 :0 Sort((u)+1)) → (x1 : (Inhabited.{u} x0)) → x0\n" ++
           "instInhabitedNat : (Inhabited.{0} Nat)\n" ++
           "unbox : (x0 :0 Sort((u)+1)) → (x1 : (Box.{u} x0)) → x0\n" ++
           "wget : (x0 :0 Sort((u)+1)) → (x1 : (Wrap.{u} x0)) → x0\n" ++
           "unboxNat : (x0 : (Box.{0} Nat)) → Nat\n" ++
           "wgetNat : (x0 : (Wrap.{0} Nat)) → Nat\n" ++
           "reprWrap : (x0 :0 Sort((u)+1)) → (x1 : (Repr.{u} x0)) → (x2 : (Wrap.{u} x0)) → Nat\n" ++
           "defaultNat : Nat\n" ++
           "natBox : (Box.{0} Nat)\n" ++
           "w5 : (Wrap.{0} Nat)\n" ++
           "con((#1, (tt, tt)))\ncon((#1, (tt, tt)))\ncon((#1, (tt, tt)))\ncon((#1, (tt, tt)))\n" ++
           "con((#1, (tt, tt)))\ncon((#1, (tt, tt)))\n") },
    { name := "U2: level mismatches in a symbolic data type are rejected, as in the Lean frontend (U2/A15)", run := fun _ =>
        selfhostAgrees ("inductive Box.{u} (A : Type u) : Type u where\n  | mk (a : A)\n" ++
          "structure Wrap.{u} (A : Type u) where\n  val : A\n" ++
          "class Repr.{u} (A : Type u) where\n  repr : A → Nat\n" ++
          "instance instReprNat : Repr Nat where\n  repr := fun n => n\n") [
          ("def ok.{u} (A : Type u) (a : A) : Box.{u} A := Box.mk a\n", true),
          ("def ok2.{u} (A : Type u) (w : Wrap A) : A := w.val\n", true),
          ("def ok3 : Wrap Nat := Wrap.mk 3\n", true),
          ("def ok4 : Nat := Repr.repr 5\n", true),
          ("def bad1 : Box.{1} Nat := Box.mk 7\n", false),
          ("def bad2.{u} : Wrap.{u} Nat := Wrap.mk 7\n", false),
          ("def bad3.{u} : Box.{u} Nat := Box.mk 7\n", false),
          ("def bad4.{u} (A : Type u) : Box A := Box.mk A\n", false),
          -- an undeclared universe, and a field type above the data type's universe
          ("inductive Bad : Type u where\n  | mk\n", false),
          ("inductive Bad.{u} : Type u where\n  | mk (a : Type u)\n", false)] },
    { name := "U2: an undeclared universe in a data type is a positioned error (U2/A15)", run := fun _ => do
        match ← selfhostCompiler with
        | .error e => if (e.splitOn "gmp.h").length > 1 then skip "no toolchain" else throw (IO.userError e)
        | .ok exe =>
          let dir ← IO.FS.createTempDir
          IO.FS.writeFile (dir / "bad.wiz") "import Prelude\ninductive Bad : Type u where\n  | mk\n"
          let out ← IO.Process.output { cmd := "timeout", args := #["120", exe.toString, "check", "bad.wiz"], cwd := dir }
          checkEq (1 : UInt32) out.exitCode
          checkEq "" out.stdout
          checkEq ("bad.wiz:2:1: error: the data type's universe must be a declared universe parameter, not u (declare one: `inductive T.{u}`)\n") out.stderr },
    -- (U2b) a field at another level: `Duo`'s fields live in `Type u`/`Type v`, below
    -- `Type (max u v)`, so the description lifts them (Q4); a `structure` at a level
    -- parameter (the `Box.{u}` shape) and a `Box.{1}` instance
    { name := "U2b: a structure at a level parameter, and an inductive whose fields are at different levels (U2/A15)", run := fun _ =>
        selfhostCheckFile ("import Prelude\n" ++ u2bDecls ++
          "def boxOfType : Box.{1} (Type 0) := Box.mk Nat\n" ++
          "#check Box\n#check Duo\n#check unbox\n#check duoSnd\n#check boxOfType\n" ++
          "#reduce Nat.beq (unbox boxVal) 7\n" ++
          "#reduce Nat.beq (String.length (duoSnd duoVal)) 2\n" ++
          "#reduce Nat.beq (String.length (duoSnd (Duo.mk 1 \"abc\"))) 3\n" ++
          "#reduce Nat.beq duoBUp 5\n")
          "Box : (x0 : Sort((u)+1)) → Sort((max(0, u))+1)\nBox.val : (x0 :0 Sort((u)+1)) → (x1 : (Box.{u} x0)) → x0\nDuo : (x0 : Sort((u)+1)) → (x1 : Sort((v)+1)) → Sort((max(u, v))+1)\nunbox : (x0 :0 Sort((u)+1)) → (x1 : (Box.{u} x0)) → x0\nduoSnd : (x0 :0 Sort((u)+1)) → (x1 :0 Sort((v)+1)) → (x2 : ((Duo.{u, v} x0) x1)) → x1\nduoUp : ((Duo.{1, 0} U0) Nat)\nduoBUp : Nat\nRepr : (x0 : Sort((u)+1)) → Sort((max(0, u))+1)\nRepr.repr : (x0 :0 Sort((u)+1)) → (x1 : (Repr.{u} x0)) → (x2 : x0) → Nat\ninstReprNat : (Repr.{0} Nat)\ninstReprType : (Repr.{1} U0)\ntypeRepr : Nat\nsumRepr : (x0 :0 U0) → (x1 : (Repr.{0} x0)) → (x2 : (List x0)) → Nat\ninstReprList : (x0 :0 U0) → (x1 : (Repr.{0} x0)) → (Repr.{max(0, 0)} (List x0))\nInhabited : (x0 : Sort((u)+1)) → Sort((max(0, u))+1)\nInhabited.default : (x0 :0 Sort((u)+1)) → (x1 : (Inhabited.{u} x0)) → x0\ninstInhabitedNat : (Inhabited.{0} Nat)\ninstInhabitedOption : (x0 :0 U0) → (x1 : (Inhabited.{0} x0)) → (Inhabited.{max(0, 0)} (Option x0))\ninstInhabitedList : (x0 :0 U0) → (x1 : (Inhabited.{0} x0)) → (Inhabited.{max(0, 0)} (List x0))\nduoVal : ((Duo.{0, 0} Nat) String)\nboxVal : (Box.{0} Nat)\noptDefault : Nat\nlistDefault : Nat\nboxOfType : (Box.{1} U0)\n(x0 : Sort((?u0)+1)) → Sort((max(0, ?u0))+1)\n(x0 : Sort((?u0)+1)) → (x1 : Sort((?u1)+1)) → Sort((max(?u0, ?u1))+1)\n(x0 :0 Sort((?u0)+1)) → (x1 : (Box.{?u0} x0)) → x0\n(x0 :0 Sort((?u0)+1)) → (x1 :0 Sort((?u1)+1)) → (x2 : ((Duo.{?u0, ?u1} x0) x1)) → x1\n(Box.{1} U0)\ncon((#1, (tt, tt)))\ncon((#1, (tt, tt)))\ncon((#1, (tt, tt)))\ncon((#1, (tt, tt)))\n" },
    -- (U2b) a polymorphic class and generic instances: `Repr (List A)` from `[Repr A]`,
    -- and `Inhabited` for `Option`/`List` from `[Inhabited A]` (the resolution is at
    -- level metavariables, U2)
    { name := "U2b: a polymorphic class and generic instances (Repr (List A), Inhabited for Option/List) (U2/A15)", run := fun _ =>
        selfhostCheckFile ("import Prelude\n" ++ u2bDecls ++
          "#check instReprList\n#check instInhabitedOption\n#check instInhabitedList\n" ++
          "#check instReprType\n#check typeRepr\n" ++
          "#reduce Nat.beq (Repr.repr (List.cons 1 (List.cons 2 List.nil))) 3\n" ++
          "#reduce Nat.beq (Repr.repr (List.nil : List Nat)) 0\n" ++
          "#reduce Nat.beq optDefault 42\n" ++
          "#reduce Nat.beq listDefault 42\n" ++
          "#reduce Nat.beq typeRepr 0\n")
          "Box : (x0 : Sort((u)+1)) → Sort((max(0, u))+1)\nBox.val : (x0 :0 Sort((u)+1)) → (x1 : (Box.{u} x0)) → x0\nDuo : (x0 : Sort((u)+1)) → (x1 : Sort((v)+1)) → Sort((max(u, v))+1)\nunbox : (x0 :0 Sort((u)+1)) → (x1 : (Box.{u} x0)) → x0\nduoSnd : (x0 :0 Sort((u)+1)) → (x1 :0 Sort((v)+1)) → (x2 : ((Duo.{u, v} x0) x1)) → x1\nduoUp : ((Duo.{1, 0} U0) Nat)\nduoBUp : Nat\nRepr : (x0 : Sort((u)+1)) → Sort((max(0, u))+1)\nRepr.repr : (x0 :0 Sort((u)+1)) → (x1 : (Repr.{u} x0)) → (x2 : x0) → Nat\ninstReprNat : (Repr.{0} Nat)\ninstReprType : (Repr.{1} U0)\ntypeRepr : Nat\nsumRepr : (x0 :0 U0) → (x1 : (Repr.{0} x0)) → (x2 : (List x0)) → Nat\ninstReprList : (x0 :0 U0) → (x1 : (Repr.{0} x0)) → (Repr.{max(0, 0)} (List x0))\nInhabited : (x0 : Sort((u)+1)) → Sort((max(0, u))+1)\nInhabited.default : (x0 :0 Sort((u)+1)) → (x1 : (Inhabited.{u} x0)) → x0\ninstInhabitedNat : (Inhabited.{0} Nat)\ninstInhabitedOption : (x0 :0 U0) → (x1 : (Inhabited.{0} x0)) → (Inhabited.{max(0, 0)} (Option x0))\ninstInhabitedList : (x0 :0 U0) → (x1 : (Inhabited.{0} x0)) → (Inhabited.{max(0, 0)} (List x0))\nduoVal : ((Duo.{0, 0} Nat) String)\nboxVal : (Box.{0} Nat)\noptDefault : Nat\nlistDefault : Nat\n(x0 :0 U0) → (x1 : (Repr.{0} x0)) → (Repr.{max(0, 0)} (List x0))\n(x0 :0 U0) → (x1 : (Inhabited.{0} x0)) → (Inhabited.{max(0, 0)} (Option x0))\n(x0 :0 U0) → (x1 : (Inhabited.{0} x0)) → (Inhabited.{max(0, 0)} (List x0))\n(Repr.{1} U0)\nNat\ncon((#1, (tt, tt)))\ncon((#1, (tt, tt)))\ncon((#1, (tt, tt)))\ncon((#1, (tt, tt)))\ncon((#1, (tt, tt)))\n" },
    -- (U2b) the level mistakes the Lean frontend rejects, with the same message and a
    -- positioned diagnostic (`selfhostLevelErrors`)
    { name := "U2b: a level escape, a max/imax mismatch and a universe inconsistency are rejected like the Lean frontend (U2/A15)", run := fun _ =>
        selfhostLevelErrors [
          ("def bad.{v} (A : Type u) : Type u := A\n", "unknown universe level 'u'"),
          ("def bad.{u, v} (A : Sort (max u v)) : Sort (imax u v) := A\n", "type mismatch"),
          ("inductive Bad.{u} : Type u where\n  | mk (a : Sort (u+1))\n", "can't lift")] },
    -- (U2b) differential: the same polymorphic program (structure, two-level inductive,
    -- generic class instances) is compiled by the Lean host and by the self-hosted
    -- compiler (GC and RC) and prints the same values
    { name := "U2b: the same polymorphic program compiles and runs in both toolchains (U2/A15)", run := fun _ => do
        ioRun u2bProgram "3\nxy\n42\n42\n7\n"
        selfhostCompileRun u2bProgram "3\nxy\n42\n42\n7\n"
        selfhostCompileRun u2bProgram "3\nxy\n42\n42\n7\n" (flags := #["--rc"]) },
    { name := "(A11) deriving BEq: 0/1/2/3 fields, a recursive polymorphic inductive, and an after-the-fact instance", run := fun _ =>
        selfhostCheckFile selfhostDeriving selfhostDerivingExpected },
    { name := "(A11) deriving rejects a field with no BEq instance and a class with no deriver", run := fun _ =>
        selfhostCheckFile selfhostDerivingBad selfhostDerivingBadExpected },
    -- (A13) `by`: the core tactic engine. A real block is intro/apply/assumption, an
    -- equation is rewritten, and `calc`, `have`, `suffices` and `obtain` are exercised.
    { name := "the self-hosted frontend: `by` and the core tactics (A13)", run := fun _ => do
        let src := "import Prelude\n" ++
          "def ap : (A B : Type) → (A → B) → A → B := by\n" ++
          "  intro A; intro B; intro f; intro a\n" ++
          "  apply f\n" ++
          "  assumption\n" ++
          "def k : Nat → Bool → Nat := by intro n; intro b; assumption\n" ++
          "def two : 1 + 1 = 2 := by rfl\n" ++
          "def rwL (a b : Nat) (h : a = b) (P : Nat → Prop) (pb : P b) : P a := by\n" ++
          "  rw h\n" ++
          "  exact pb\n" ++
          "def rwR (a b : Nat) (h : a = b) (P : Nat → Prop) (pa : P a) : P b := by\n" ++
          "  rw ← h\n" ++
          "  exact pa\n" ++
          "def tr (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := by\n" ++
          "  calc a = b := h₁\n" ++
          "       _ = c := h₂\n" ++
          "def hv (a b : Nat) (h : a = b) : a = b := by\n" ++
          "  have h₂ : a = b := h\n" ++
          "  exact h₂\n" ++
          "def sf (a b : Nat) (h : a = b) : a = b := by\n" ++
          "  suffices h₂ : a = b\n" ++
          "  exact h\n" ++
          "  exact h₂\n" ++
          "def ob (p : Nat × Nat) : Nat := by\n" ++
          "  obtain ⟨x, y⟩ := p\n" ++
          "  exact x\n" ++
          "#check ap\n#check tr\n#check ob\n"
        let some out ← selfhostOutput src | return
        let errs := (out.splitOn "\n").filter (fun l => l.startsWith "error" || l.startsWith "parse error")
        unless errs.isEmpty do throw (IO.userError s!"the self-hosted frontend rejects the core tactics:\n{out}")
        checkChecked src out },
    { name := "(A13) per-tactic cases: intros, change, unfold, constructor, try/first/repeat", run := fun _ => do
        let src := "import Prelude\n" ++
          "def idn : Nat → Nat := by intro n; exact n\n" ++
          "def id2 : Nat → Nat → Nat := by intros; assumption\n" ++
          "def ch : 1 + 1 = 2 := by change 2 = 2; rfl\n" ++
          "def F (A : Type) : Type := A\n" ++
          "def un : List (F Nat) := by unfold F; exact List.nil\n" ++
          "inductive Box where\n" ++
          "  | mk (n : Nat)\n" ++
          "def box : Box := by constructor; exact 7\n" ++
          "def tf : Nat := by first | exact 0 | exact 1\n" ++
          "def tt (n : Nat) : n = n := by try (exact 0); rfl\n" ++
          "def rep (a b : Nat) (h : a = b) : a = b := by repeat rw h; rfl\n" ++
          "#check idn\n#check box\n"
        let some out ← selfhostOutput src | return
        let errs := (out.splitOn "\n").filter (fun l => l.startsWith "error" || l.startsWith "parse error")
        unless errs.isEmpty do throw (IO.userError s!"the self-hosted frontend rejects a core tactic:\n{out}")
        checkChecked src out },
    { name := "the self-hosted frontend: unsolved goals are reported with their context (A13)", run := fun _ =>
        selfhostCheckFile "import Prelude\ndef bad : Nat → Bool := by intro n\n"
          "error: unsolved goals:\nn : Nat\n⊢ Bool\n" },
    { name := "the self-hosted frontend: a tactic failure is an error with the goals (A13)", run := fun _ => do
        let some out ← selfhostOutput "import Prelude\ndef bad : Nat := by assumption\n" | return
        unless (out.splitOn "assumption: no hypothesis matches the goal").length > 1 do
          throw (IO.userError s!"the failure does not name the tactic:\n{out}")
        unless (out.splitOn "remaining goals:").length > 1 do
          throw (IO.userError s!"the failure does not list the remaining goals:\n{out}") },
    -- the differential case: the same script, host and selfhost, verdict and error text
    { name := "the core tactics: the Lean and self-hosted frontends agree (A13)", run := fun _ => do
        let loader ← preludeLoader
        let src := "import Prelude\ndef ap : (A B : Type) → (A → B) → A → B := by\n" ++
          "  intro A; intro B; intro f; intro a\n  apply f\n  assumption\n"
        let s := runFrontend (R := ZeroOneMany) src { loader, trustedModule := Tests.libModule }
        let errs := s.messages.filter (·.severity == .error)
        unless errs.isEmpty do throw (IO.userError "the Lean frontend rejects the differential script")
        let some out ← selfhostOutput src | return
        let selfErrs := (out.splitOn "\n").filter (fun l => l.startsWith "error" || l.startsWith "parse error")
        unless selfErrs.isEmpty do throw (IO.userError s!"the self-hosted frontend rejects the differential script:\n{out}")
        checkChecked src out
        -- and a failing rewrite: the same verdict and the same message
        let bad := "import Prelude\ndef r (a b c : Nat) (h : a = b) (P : Nat → Prop) (pc : P c) : P c := by\n" ++
          "  rw h\n  exact pc\n"
        let sBad := runFrontend (R := ZeroOneMany) bad { loader, trustedModule := Tests.libModule }
        let leanBad := sBad.messages.filter (·.severity == .error)
        unless !leanBad.isEmpty do throw (IO.userError "the Lean frontend accepts the bad rewrite")
        let some badOut ← selfhostOutput bad | return
        let selfBad := (badOut.splitOn "\n").filter (fun l => l.startsWith "error")
        unless !selfBad.isEmpty do throw (IO.userError s!"the self-hosted frontend accepts the bad rewrite:\n{badOut}")
        let expected := "error: " ++ (leanBad.toList.head!).text
        unless selfBad.head! == expected do
          throw (IO.userError s!"the error texts differ:\nLean: {expected}\nselfhost: {selfBad.head!}") },
    { name := "(A11) the deriver table: the five built-ins on every form (inductive, structure, after the fact, several classes, several types, re-registered)", run := fun _ =>
        selfhostCheckFile selfhostDerivingTable selfhostDerivingTableExpected },
    { name := "(A11) the deriver table's errors: no deriver, an indexed family, a recursive field, a wrong arity, an unrunnable deriver, a mutual block", run := fun _ =>
        selfhostCheckFile selfhostDerivingNeg selfhostDerivingNegExpected },
    { name := "(A11) deriving: the Lean host and the self-hosted frontend agree on every form", run := fun _ =>
        derivingAgrees derivingSelfHeader [
          -- (pinned difference) indexed `BEq` is derived by the host (a dependent motive)
          -- and still rejected by this frontend; the rejection stays pinned by
          -- `selfhostDerivingNeg`, and the host's derivation by `=deriving`.
          ("inductive D1 where\n  | a\n  | b\n  | c\n  deriving BEq\n", true),
          ("structure D2 where\n  x : Nat\n  deriving BEq\n", true),
          ("structure D3 where\n  x : Nat\n  b : Bool\nderiving instance BEq, Repr for D3\n", true),
          ("structure D4 where\n  x : Nat\nstructure D5 where\n  x : Bool\nderiving instance BEq for D4, D5\n", true),
          ("inductive D6 where\n  | a\n  deriving Inhabited, BEq, Repr, DecidableEq\n", true),
          ("inductive L where\n  | nil\n  | cons (n : Nat) (t : L)\n  deriving DecidableEq\n", false),
          ("inductive R where\n  | mk (r : R)\n  deriving Inhabited\n", false),
          ("class Sz (A : Type) where\n  size : A → Nat\nderiving instance Sz for Nat\n", false),
          ("def myD (x y : String) : String := x\nattribute [deriver Foo] myD\n", false)] },
    { name := "(A11) a rejected derivation is reported at the command's line and column (D6)", run := fun _ =>
        selfhostCheckFails selfhostDerivingSpan selfhostDerivingSpanExpected },
    { name := "(#422) a match on a closed scrutinee is not evaluated while compiling: an argument, a postponed argument, a let-bound use, an if (bounded at 120 s; the same at fib 4 runs in both toolchains)", run := fun _ => do
        selfhostClosedScrutBounded 120
        ioRun (closedScrutProgram 4) "nz\nnz\nnz\nnz\n"
        selfhostCompileRun (closedScrutProgram 4) "nz\nnz\nnz\nnz\n" },
    -- (C14) `native_refl` behind `--trust-native` (the host's stage 27a): the decision is
    -- recorded as the axiom `X.native✝`, never as a kernel-checked `refl`, and the
    -- self-hosted toolchain has no trust ledger, so `#print axioms` (implemented with it)
    -- is how a run makes what it trusted visible
    { name := "(C14) native_refl: decided with --trust-native and recorded as the axiom X.native✝; refused without the flag", run := fun _ => do
        let src := "import Prelude\ndef sumTo : Nat → Nat\n  | .zero => 0\n  | .succ n => Nat.add (Nat.succ n) (sumTo n)\n" ++
          "def s : sumTo 3 = 6 := native_refl\n#print axioms s\n"
        let has (out frag : String) : Bool := (out.splitOn frag).length > 1
        let some trusted ← selfhostModuleOutput [("input.wiz", src)] #["--trust-native"] | return
        check (has trusted "'s' depends on axioms: [s.native✝]") s!"no .native✝ axiom in the trusted run:\n{trusted}"
        check (has trusted ".native✝: a closed proposition decided by running it") s!"no trust note in the trusted run:\n{trusted}"
        check (!has trusted "error:") s!"unexpected error in the trusted run:\n{trusted}"
        let some plain ← selfhostModuleOutput [("input.wiz", src)] #[] | return
        check (has plain "error: native evaluation is not enabled") s!"accepted without the flag:\n{plain}"
        check (!has plain "s.native✝") s!"the axiom was added without the flag:\n{plain}" },
    { name := "(C14) native_refl: a false equation is refuted, and a function type and a bare native_refl are refused", run := fun _ => do
        let src := "import Prelude\ndef sumTo : Nat → Nat\n  | .zero => 0\n  | .succ n => Nat.add (Nat.succ n) (sumTo n)\n" ++
          "def bad : sumTo 10 = 54 := native_refl\n" ++
          "def fn : ((fun (x : Nat) => x) = (fun (x : Nat) => x)) := native_refl\n" ++
          "def r : Nat := native_refl\n" ++
          "def q : sumTo 3 = 6 := (native_refl : sumTo 3 = 6)\n"
        let has (out frag : String) : Bool := (out.splitOn frag).length > 1
        let some out ← selfhostModuleOutput [("input.wiz", src)] #["--trust-native"] | return
        check (has out "native evaluation refutes it") s!"the false equation was accepted:\n{out}"
        check (has out "native_refl compares first-order data") s!"a function type was accepted:\n{out}"
        check (has out "native_refl proves an equation `a = b`; this type is not one") s!"native_refl at Nat was accepted:\n{out}"
        check (has out "native_refl can only be the whole body of a definition") s!"an ascription was accepted:\n{out}"
        check (!has out "bad.native✝") s!"the false equation added an axiom:\n{out}" },
    { name := "(C14) native_refl: the driver has no --trust-native, so it refuses a native_refl body without the flag (D9)", run := fun _ =>
        selfhostCompileFails nativeReflDriverProgram nativeReflDriverExpected },

    -- (E-K) number literals in `Kernel.wiz` (`Tm.nlit`, `Tm.natFn`): the Lean kernel's
    -- `natLit`/`natOp` rules, on hand-written terms (the frontend does not emit literals yet).
    -- Each case runs the kernel program twice: through the Lean host, against its pinned
    -- output, and then through the self-hosted compiler, which must print the same output.
    { name := "(E-K) Kernel.wiz literals: the registered operations compute natively on literals (exact past 64 bits), with the zero shortcuts and the stuck applications of the Lean kernel", run := fun _ => do
        let kernel ← IO.FS.readFile "selfhost/Kernel.wiz"
        let prog := kernel ++ "\n" ++ ekNatDefs ++ ekMain ekArithCalls
        ioRun prog ekArithExpected (split := 8)
        selfhostCompileRun prog ekArithExpected (opt := "-O0") },

    { name := "(E-K) Kernel.wiz literals: a literal and its unary numeral are convertible both ways (the equation, conversion, ind looking inside a literal)", run := fun _ => do
        let kernel ← IO.FS.readFile "selfhost/Kernel.wiz"
        let prog := kernel ++ "\n" ++ ekNatDefs ++ ekMain ekConvCalls
        ioRun prog ekConvExpected (split := 8)
        selfhostCompileRun prog ekConvExpected (opt := "-O0") },

    { name := "(E-K) Kernel.wiz literals: different numbers, a literal at another type and ill-typed registrations are rejected", run := fun _ => do
        let kernel ← IO.FS.readFile "selfhost/Kernel.wiz"
        let prog := kernel ++ "\n" ++ ekNatDefs ++ ekMain ekRejectCalls
        ioRun prog ekRejectExpected (split := 8)
        selfhostCompileRun prog ekRejectExpected (opt := "-O0") },

    -- (B13) parity with the host's `vNatOp` rules (`kernel-lazy-let.md` §8.1, §8.4,
    -- §9.3): a big literal is exact; an operation on a definition's glued value stays
    -- glued until its value is needed; `vEq` does not force an expansive `Nat.pow`; `nf`
    -- computes. The pow case would allocate 2^(2^28) if the equation forced its sides.
    { name := "(B13) Kernel.wiz literals: a big literal, a glued `Nat` operation, an expansive `Nat.pow` that is not forced, and `nf` that computes", run := fun _ => do
        let kernel ← IO.FS.readFile "selfhost/Kernel.wiz"
        let prog := kernel ++ "\n" ++ ekNatDefs ++ ekMain ekLazyCalls
        ioRun prog ekLazyExpected (split := 8)
        selfhostCompileRun prog ekLazyExpected (opt := "-O0") },

    { name := "(E-K) Kernel.wiz literals: 77 * 130 + 3 = 10013 by literals is at least 10 times faster than by unary numerals", run := fun _ => do
        let kernel ← IO.FS.readFile "selfhost/Kernel.wiz"
        -- the ratio is measured on the host build (the clock is not in the embedded
        -- prelude, so the self-hosted program below prints the verdicts only); the unary
        -- side is the slow one, so give the loaded-shard machine a longer budget
        ioRunWith ("import Sys\n" ++ kernel ++ "\n" ++ ekNatDefs ++ ekTimingMain) (split := 8) (timeout := 600) checkEkTiming
        -- and the self-hosted pipeline must decide the literal equation (the unary
        -- side is a 10 000-numeral reduction: at -O0 it does not fit the 60 s run
        -- budget, and the ratio above is the host build's claim anyway)
        selfhostCompileRun (kernel ++ "\n" ++ ekNatDefs ++ ekTimingDefs ++ ekMain ["prfOk litWork"])
          "True\n" (opt := "-O0") },
    { name := "(B13) source numerals still elaborate as successor trees, not `nlit`/`natFn` (the kernel literal rules are covered separately)", run := fun _ =>
        selfhostCheckFile numeralSourceProgram numeralSourceExpected },
    { name := "the lexer in Wiz agrees with the Lean lexer", run := fun _ => do
        let lexSrc ← IO.FS.readFile "selfhost/Lex.wiz"
        let input := "def f (x : Nat) : Nat := x + 1 -- a comment\n/- a /- nested -/ block -/ #eval f 41\n" ++
          "inductive T where | a | b (t : T)\ndef s : String := \"hi\\n\" -- strings\ndef α₁ : List.cons → Nat.add := λ x => x.1\n" ++
          "0x3F 0b1010 0XfF 0B1 0x 0b2 0xg 007 0x7FFFFFFFFFFFFFFF 0x8000000000000000 " ++
          -- every escape, then a bad one (both lexers stop there with the same message)
          "def e := \"a\\r\\t\\\\\\\"\\'\\x41\\u{3bb}\\u{1F600}z\" \"bad \\q\""
        let toks := Builtin.tables.tokens
        let expected := leanTokens toks input
        let table := toks.toList.foldr (fun t acc => s!"(.cons {wizLit t} {acc})") ".nil"
        let prog := lexSrc ++ s!"\ndef main : IO Unit := printAll (List.reverseL (tokenize {table} {wizLit input}) .nil)\n"
        let prog := prog.replace "def printAll" "def List.reverseL : List String → List String → List String\n  | .nil, acc => acc\n  | .cons x xs, acc => List.reverseL xs (.cons x acc)\ndef printAll"
        selfhostCompileRun prog ("\n".intercalate expected ++ "\n") },
    { name := "the parser in Wiz agrees with the Lean parser", run := fun _ => do
        let lexSrc ← IO.FS.readFile "selfhost/Lex.wiz"
        let parseSrc ← IO.FS.readFile "selfhost/Parse.wiz"
        let t := Builtin.tables
        let expected := parseDiffCorpus.map fun (c, i) => leanParse t c i
        let calls := parseDiffCorpus.map fun (c, i) => s!"(parse cats tokens {wizLit c} {wizLit i})"
        let prog := lexSrc ++ "\n" ++ parseSrc ++ "\n" ++ wizTables t ++
          s!"def tokens : List String := {wizList (t.tokens.toList.map wizLit)}\n" ++
          s!"def main : IO Unit := printAll {wizList calls}\n"
        selfhostCompileRun prog ("\n".intercalate expected ++ "\n") },
    { name := "the checked-in tables accept the corpus the Lean parser accepts", run := fun _ => do
        -- the semantic check of the file: not "the text is the same" but "the tables in
        -- selfhost/Tables.wiz parse, on the differential's corpus, exactly what the Lean
        -- parser produces" (the case above does the same with freshly generated tables)
        let lexSrc ← IO.FS.readFile "selfhost/Lex.wiz"
        let parseSrc ← IO.FS.readFile "selfhost/Parse.wiz"
        let tablesSrc ← IO.FS.readFile "selfhost/Tables.wiz"
        let t := Builtin.tables
        let expected := parseDiffCorpus.map fun (c, i) => leanParse t c i
        let calls := parseDiffCorpus.map fun (c, i) => s!"(parse cats tokens {wizLit c} {wizLit i})"
        let prog := lexSrc ++ "\n" ++ parseSrc ++ "\n" ++ tablesSrc ++
          s!"def main : IO Unit := printAll {wizList calls}\n"
        selfhostCompileRun prog ("\n".intercalate expected ++ "\n") },
    { name := "the type checker in Wiz", run := fun _ => do
        let kernel ← IO.FS.readFile "selfhost/Kernel.wiz"
        let defs := "def idTy : Tm := piH (.univ 0) (piH (.var 0) (.var 1))\n" ++
          "def idTm : Tm := .ann (.lam (.lam (.var 0))) idTy\n" ++
          "def cnat : Tm := piH (.univ 0) (piH (piH (.var 0) (.var 1)) (piH (.var 1) (.var 2)))\n" ++
          "def two : Tm := .ann (.lam (.lam (.lam (.app (.var 1) (.app (.var 1) (.var 0)))))) cnat\n" ++
          "def add : Tm := .ann (.lam (.lam (.lam (.lam (.lam (.app (.app (.app (.var 4) (.var 2)) (.var 1)) " ++
          "(.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0)))))))) (piH cnat (piH cnat cnat))\n" ++
          "def viaId : Tm := .ann (.lam (.lam (.app (.app idTm (.var 1)) (.var 0)))) idTy\n"
        let main := "def main : IO Unit := do\n  IO.println (typeOf idTm);\n  IO.println (typeOf viaId);\n" ++
          "  IO.println (typeOf (.app idTm cnat));\n  IO.println (typeOf (.app (.app add two) two));\n" ++
          "  IO.println (normalize (.app (.app add two) two));\n  IO.println (typeOf (.app (.univ 0) (.univ 0)));\n" ++
          -- a variable out of scope is an error (it was `Sort 0`, as a type and as a value: `Prop : Prop`)
          "  IO.println (typeOf (.var 0));\n  IO.println (typeOf (.ann (.lam (.var 3)) (piH (.unit (ln 1)) .prop)))\n"
        selfhostCompileRun (kernel ++ "\n" ++ defs ++ main) ("(x0 : U0) → (x1 : x0) → x0\n(x0 : U0) → (x1 : x0) → x0\n" ++
          "error: type mismatch: expected U0, got U1\n(x0 : U0) → (x1 : (x1 : x0) → x0) → (x2 : x0) → x0\n" ++
          "λx0. λx1. λx2. (x1 (x1 (x1 (x1 x2))))\nerror: not a function: its type is U1\n" ++
          "error: internal error: a variable out of scope\nerror: internal error: a variable out of scope\n") },
    -- W1 (`wiz-notes/kernel-lint.md`): the structural fast path (`valSame`) compared two
    -- constants by name, without their universe levels, so two stuck cases whose
    -- environments held `d.{0}` and `d.{1}` were convertible: a closed term of type `False`
    { name := "W1: a constant at two universe levels is not the same value (the fast path for stuck cases)", run := fun _ => do
        let kernel ← IO.FS.readFile "selfhost/Kernel.wiz"
        let probe :=
          "def dVal : Tm := sortsTy (piH (.sortL (.lparam \"u\")) (piH (.var 0) (piH (.var 1) (piH (piH (.var 2) .prop)\n" ++
          "  (piH (.app (.var 0) (.var 2)) (.app (.var 1) (.var 2)))))))\n" ++
          "def dAt (l : Lvl) : Tm := .const \"d\" (.cons \"u\" .nil) (.cons l .nil) dVal .prop\n" ++
          "def d0 : Tm := dAt (.lnum 0)\n" ++
          "def d1 : Tm := dAt (.lnum 1)\n" ++
          "def d0Proof : Tm := .ann (.lam (.lam (.lam (.lam (.lam (.var 0)))))) d0\n" ++
          "def fTy : Tm := sortsTy (piH .prop (piH (.enum 1) .prop))\n" ++
          "def fVal : Tm := .lam (.lam (.ecase .prop (.var 0) (.tcons (.var 1) .tnil)))\n" ++
          "def fC : Tm := .const \"F\" .nil .nil fVal fTy\n" ++
          "def fAt (a x : Tm) : Tm := .app (.app fC a) x\n" ++
          "def h (a b : Tm) : Tm := .ann (.lam (.lam (.var 0))) (piH (.enum 1) (piH (fAt a (.var 0)) (fAt b (.var 1))))\n" ++
          "def isFirst : Tm := .ann (.lam (.ecase .prop (.var 0) (.tcons .ptrue (.tcons .pfalse .tnil)))) (piH (.enum 2) .prop)\n" ++
          "def refute (p : Tm) : Tm := .app (.app (.app (.app (.app p (.enum 2)) (.tag 2 0)) (.tag 2 1)) isFirst) .star\n" ++
          "def bad (a b : Tm) : Tm := .ann (refute (.app (.app (h a b) (.tag 1 0)) d0Proof)) .pfalse\n" ++
          "def verdict (r : TyRes) : String := match r with\n" ++
          "  | .ok _ _ => \"ok\"\n" ++
          "  | .err _ => \"error\"\n" ++
          -- (P2) the probes are proofs (their types are propositions): checked inside a proof,
          -- where they need no marker
          "def typeOk (t : Tm) : String := verdict (infer (TCtx.inProof empty) (sortsInfer t))\n" ++
          "def typeOfP (t : Tm) : String := match infer (TCtx.inProof empty) (sortsInfer t) with\n  | .ok ty _ => show .nil 0 (quote 0 ty)\n  | .err m => String.append \"error: \" m\n" ++
          "def main : IO Unit := do\n" ++
          "  IO.println (String.append \"d's declaration, at every level: \" (verdict (checkDecl .prop (.some dVal))));\n" ++
          "  IO.println (String.append \"F's declaration: \" (verdict (checkDecl fTy (.some fVal))));\n" ++
          "  IO.println (String.append \"the proof of d.{0}: \" (typeOk d0Proof));\n" ++
          "  IO.println (String.append \"control, d.{0} used as d.{1} directly (want error): \" (typeOk (.ann d0Proof d1)));\n" ++
          "  IO.println (String.append \"control, F d.{0} x → F d.{0} x (want ok): \" (typeOk (h d0 d0)));\n" ++
          "  IO.println (String.append \"F d.{0} x → F d.{1} x (want error): \" (typeOk (h d0 d1)));\n" ++
          "  IO.println (String.append \"a closed term of type False (want error): \" (typeOfP (bad d0 d1)))\n"
        selfhostCompileRun (kernel ++ "\n" ++ probe) ("d's declaration, at every level: ok\nF's declaration: ok\nthe proof of d.{0}: ok\n" ++
          "control, d.{0} used as d.{1} directly (want error): error\ncontrol, F d.{0} x → F d.{0} x (want ok): ok\n" ++
          "F d.{0} x → F d.{1} x (want error): error\n" ++
          "a closed term of type False (want error): error: type mismatch: expected case(Prop, x0, d.{1}), got ((F d.{0}) x0)\n") },
    { name := "the frontend gives the types it builds their sorts (sortTy, and the sorts pass)", run := fun _ => do
        -- `(True → Unit) = ((True → True) → Unit)` computes to the domains' equivalence: with
        -- the sorts `sortTy` fills in, and (mandatory sorts) with those the sorts pass fills
        -- in where none were written (`normalize` runs it), so both are the same
        let src ← Selfhost.frontendFiles.mapM (fun (f : String) => IO.FS.readFile f)
        let body := "\n".intercalate (src.map fun f => "\n".intercalate ((f.splitOn "\n").filter (!·.startsWith "import")))
        let prog := "import IO\nimport Std\n" ++ body ++ "\n" ++
          "def gTy (X : Tm) : Tm := piH X (.unit (ln 1))\n" ++
          "def eqn (s : Bool) : Tm := match s with\n" ++
          "  | .true => .eqTy (sortTy (gTy .ptrue)) (sortTy (gTy (piH .ptrue .ptrue)))\n" ++
          "  | .false => .eqTy (gTy .ptrue) (gTy (piH .ptrue .ptrue))\n" ++
          "def main : IO Unit := do\n  IO.println (normalize (eqn .false));\n  IO.println (normalize (eqn .true));\n" ++
          "  IO.println (typeOf (sortTy (gTy (piH .ptrue .ptrue))))\n"
        let computed := "(x0 :0 (x0 :0 (x0 :0 (x0 : True) → True) → True) × (x1 :0 True) → (x2 : True) → True) × " ++
          "(x1 :0 (x1 : True) → True) → True\n"
        selfhostCompileRun prog (computed ++ computed ++ "U0\n") },
    { name := "text to checked term, all in Wiz", run := fun _ => do
        let src ← Selfhost.frontendFiles.mapM (fun (f : String) => IO.FS.readFile f)
        let body := "\n".intercalate (src.map fun f => "\n".intercalate ((f.splitOn "\n").filter (!·.startsWith "import")))
        let t := Builtin.tables
        let bad := "(fun (x : Type) => x"
        let cases := ["(fun A x => x : (A : Type) → A → A)", "Type 2", "let T : Type 1 := Type; (fun x => x : T → T)",
          "fun x => x", "y", "(fun f x => f x : (Type → Type) → Type → Type)", bad]
        let calls := cases.map fun c => s!"(checkText cats tokens {wizLit c})"
        let prog := "import IO\nimport Std\n" ++ body ++ "\n" ++ wizTables t ++
          s!"def tokens : List String := {wizList (t.tokens.toList.map wizLit)}\n" ++
          s!"def main : IO Unit := printAll {wizList calls}\n"
        selfhostCompileRun prog ("(x0 : U0) → (x1 : x0) → x0\nU3\n(x0 : U0) → U0\n" ++
          "error: cannot infer the type of a λ; add a type ascription\nscope error: unknown identifier y\n" ++
          "(x0 : (x0 : U0) → U0) → (x1 : U0) → U0\nparse " ++ leanParse t "term" bad ++ "\n") },
    { name := "Kernel.wiz quantity terms: the same variable is the same quantity, and a Σ at a stuck non-variable quantity is rejected, as in the Lean kernel (21x, review probes 7a, 15b)", run := fun _ => do
        -- (`MTm` has no `Qty` terms; the Lean kernel's verdicts are in
        -- wiz-notes/fieldq-review-probes: 7a accepted, 15b rejected by `qtyPoly`)
        let kernel ← IO.FS.readFile "selfhost/Kernel.wiz"
        -- (mandatory sorts: the sorts pass fills the `Π`s' holes, as the frontend runs it)
        let verdict := "def piW (a b : Tm) : Tm := .pi .qw .lhole .lhole a b\n" ++
          "def verdict (t : Tm) : String := match infer empty (sortsInfer t) with\n  | .ok _ _ => \"ok\"\n  | .err _ => \"error\"\n"
        let dq := "(.ann (.darg (.var 0) (.unit (ln 1)) (.lam (.dret .star))) (.descr (ln 0) (.unit (ln 1))))"
        let p7a := s!"(.ann (.lam (.lam (.letq .qz (.eqTy (.unit (ln 1)) (.unit (ln 1))) (.fst (.var 0)) .star))) (piW .qty (piW (.eq (.descr (ln 0) (.unit (ln 1))) {dq} {dq}) (.unit (ln 1)))))"
        let p15b := "(.ann (.lam (.con (.pair .star (.pair .star .star)))) (piW (piW (.unit (ln 1)) .qty) (.mu (ln 0) (.unit (ln 1)) " ++
          "(.app (.ann (.lam (.darg (.var 0) (.unit (ln 1)) (.lam (.dret .star)))) (piW .qty (.descr (ln 0) (.unit (ln 1))))) (.app (.var 0) .star)) .star)))"
        selfhostCompileRun (kernel ++ "\n" ++ verdict ++ s!"def main : IO Unit := do\n  IO.println (verdict {p7a});\n  IO.println (verdict {p15b})\n")
          "ok\nerror\n" },
    { name := "the Wiz kernel agrees with the Lean kernel (400 random terms)", run := fun _ => do
        let kernel ← IO.FS.readFile "selfhost/Kernel.wiz"
        let mut terms : Array MTm := MTm.samples.toArray
        let mut seed := 42
        for i in [0:400] do
          let (t, s) := MTm.gen seed (2 + i % 3) 0
          terms := terms.push t
          seed := s
        let expected := terms.toList.map leanVerdict
        let verdict := wizVerdict
        let calls := terms.toList.map fun t => s!"(verdict {t.toWiz})"
        let main := s!"def main : IO Unit := printAll {wizList calls}\n"
        let printAll := "def printAll : List String → IO Unit\n  | .nil => IO.pure ()\n  | .cons s ss => do\n    IO.println s;\n    printAll ss\n"
        unless (expected.filter (· != "error")).length ≥ 30 do throw (IO.userError "too few well-typed terms")
        selfhostCompileRun (kernel ++ "\n" ++ verdict ++ printAll ++ main) ("\n".intercalate expected ++ "\n") },
    -- P2 (soundness review of PR #61). A suspended proof never reaches these positions from
    -- a checked term (it only sits in the proof positions of `cast` and `transp`), so the
    -- values are built by hand, in both kernels.
    { name := "P2: comparing types erases suspended proofs, but not what follows an absurd (both kernels)", run := fun _ => do
        let g : Globals ZeroOneMany := {}
        let ls : List Name := ["a", "b"]
        let E : Val ZeroOneMany := .enum ls
        let pf (sp : Array (Elim ZeroOneMany)) : Val ZeroOneMany :=
          .neutral (.prf [] .tt) sp
        -- (the kernel's read-back, as its comparisons and its messages use it)
        let sameVal (g : Globals ZeroOneMany) (a b : Val ZeroOneMany) : Bool :=
          quote { g with quoteErasesProofs := true } 0 a == quote { g with quoteErasesProofs := true } 0 b
        -- two proofs are equal, whatever was projected
        checkEq "true" (toString (sameVal g (pf #[.fst]) (pf #[.snd])))
        -- `absurd E p` is a value of `E`, not a proof: what is done with it is compared
        checkEq "false" (toString (sameVal g (pf #[.absurd E, .app (.tag ls 0)]) (pf #[.absurd E, .app (.tag ls 1)])))
        -- and what was done before the `absurd` is not
        checkEq "true" (toString (sameVal g (pf #[.fst, .absurd E, .app (.tag ls 0)]) (pf #[.snd, .absurd E, .app (.tag ls 0)])))
        -- the same proof as a stuck `refl` head and as a suspension reads back alike (the
        -- two forms of one proof must not make two types differ: `prf-marker.md` §4.3)
        checkEq "true" (toString (sameVal g (.neutral (.refl E (.tag ls 0)) #[.fst]) (pf #[.snd])))
        checkEq "true" (toString (sameVal g (.neutral (.refl E (.tag ls 0)) #[.absurd E]) (pf #[.fst, .absurd E])))
        -- conversion, a suspended proof against a `refl`, both under `absurd`: a proof under
        -- `absurd` is not compared, in either kernel (they differed before the marker)
        let refl : Val ZeroOneMany := .neutral (.refl E (.tag ls 0)) #[.absurd E]
        checkEq "true" (toString (conv g #[] E (pf #[.absurd E]) refl))
        -- (I-2) and with no `absurd`, where the type was not seen to be a proposition: a
        -- suspended proof and a `refl` head are two proofs, equal in both kernels
        checkEq "true" (toString (conv g #[] E (pf #[.fst]) (.neutral (.refl E (.tag ls 0)) #[.fst])))
        let kernel ← IO.FS.readFile "selfhost/Kernel.wiz"
        let main := "def b2s : Bool → String\n  | .true => \"true\"\n  | .false => \"false\"\n" ++
          "def pf : Head := .hprf .nil .star\n" ++
          "def rf : Head := .hrefl (.venum 2) (.vtag 2 0)\n" ++
          "def sameVal (a b : Val) : Bool := tmEq (quoteM .false .false 0 a) (quoteM .false .false 0 b)\n" ++
          "def ab (sp : Spine) : Spine := .sabsurd sp (.venum 2)\n" ++
          "def main : IO Unit := do\n" ++
          "  IO.println (b2s (sameVal (.vne pf (.sfst .snil)) (.vne pf (.ssnd .snil))));\n" ++
          "  IO.println (b2s (sameVal (.vne pf (.sapp (ab .snil) (.vtag 2 0))) (.vne pf (.sapp (ab .snil) (.vtag 2 1)))));\n" ++
          "  IO.println (b2s (sameVal (.vne pf (.sapp (ab (.sfst .snil)) (.vtag 2 0))) (.vne pf (.sapp (ab (.ssnd .snil)) (.vtag 2 0)))));\n" ++
          "  IO.println (b2s (sameVal (.vne rf (.sfst .snil)) (.vne pf (.ssnd .snil))));\n" ++
          "  IO.println (b2s (sameVal (.vne rf (ab .snil)) (.vne pf (ab (.sfst .snil)))));\n" ++
          "  IO.println (b2s (conv empty (.venum 2) (.vne pf (ab .snil)) (.vne (.hrefl (.venum 2) (.vtag 2 0)) (ab .snil))));\n" ++
          "  IO.println (b2s (conv empty (.venum 2) (.vne pf (.sfst .snil)) (.vne (.hrefl (.venum 2) (.vtag 2 0)) (.sfst .snil))))\n"
        selfhostCompileRun (kernel ++ "\n" ++ main) "true\nfalse\ntrue\ntrue\ntrue\ntrue\ntrue\n" },
    { name := "every constructor of Term is covered by the traversals (S1: a missed one proved False)", run := fun _ => do
        let samples := termSamples (.var 5) (.param "pw")
        -- a sample for every constructor
        let names := (samples.map (termCtor ·.1)).eraseDups -- complexity: ok (one sample per term constructor, a few dozen)
        unless names.length == termCtorCount && samples.length == termCtorCount do
          throw (IO.userError s!"{names.length} constructors have a sample, of {termCtorCount}")
        for (t, nTerms, nLevels) in samples do
          let c := termCtor t
          -- `mapChildrenM` visits every term child and every level
          let (_, (ts, ls)) := (t.forChildren (m := StateM (Nat × Nat))
            (fun _ => modify fun (a, b) => (a, b + 1)) (fun _ _ => modify fun (a, b) => (a + 1, b))).run (0, 0)
          unless (ts, ls) == (nTerms, nLevels) do
            throw (IO.userError s!"{c}: mapChildrenM visits {ts} terms and {ls} levels, expected {nTerms} and {nLevels}")
          -- so do the traversals built on it: shifting, substitution, occurrence, the levels
          if nTerms > 0 then
            unless t.lift 1 != t do throw (IO.userError s!"{c}: lift misses the children")
            unless (List.range 3).any (fun d => t.instantiateAt (5 - d) .tt != t) do throw (IO.userError s!"{c}: instantiateAt misses the children")
            unless (List.range 3).any (fun d => t.hasVar (5 - d)) do throw (IO.userError s!"{c}: hasVar misses the children")
          if nLevels > 0 then
            unless t.instLevels ["pw"] [.zero] != t do throw (IO.userError s!"{c}: instLevels misses a level")
            unless (t.levelParamsUsed.filter (· == "pw")).length == nLevels do
              throw (IO.userError s!"{c}: levelParamsUsed misses a level")
        -- the marker's level is instantiated: `prf.{u} t` is a suspended proof at `u := 0`
        let g : Globals ZeroOneMany := {}
        let m : Term ZeroOneMany := (Term.prf (.param "u") .tt).instLevels ["u"] [.zero]
        unless (eval g [] m) matches .neutral (.prf ..) #[] do throw (IO.userError "prf.{u} at u := 0 is not suspended")
        -- the Wiz kernel's traversals
        let kernel ← IO.FS.readFile "selfhost/Kernel.wiz"
        let main := "def b2s : Bool → String\n  | .true => \"true\"\n  | .false => \"false\"\n" ++
          "def z : Lvl := .lnum 0\n" ++
          "def main : IO Unit := do\n" ++
          "  IO.println (b2s (usesVar 0 (.prf z (.var 0))));\n" ++
          "  IO.println (b2s (usesVar 0 (.prf z .star)));\n" ++
          "  IO.println (b2s (tmEq (.prf z (.var 0)) (.prf z (.var 1))));\n" ++
          "  IO.println (b2s (tmEq (.prf z .star) (.prf (.lnum 1) .star)));\n" ++
          "  IO.println (b2s (tmEq (tmSubst (.cons \"u\" .nil) (.cons z .nil) (.prf (.lparam \"u\") .star)) (.prf z .star)));\n" ++
          "  IO.println (b2s (tmEq (quote 1 (eval (.cons (fresh 0) .nil) (.prf z (.var 0)))) (.prf z (.var 0))))\n"
        selfhostCompileRun (kernel ++ "\n" ++ main) "true\nfalse\nfalse\nfalse\ntrue\ntrue\n" },
    { name := "P2: the proof marker is required and verified, by both kernels (terms without the marking pass)", run := fun _ => do
        let kernel ← IO.FS.readFile "selfhost/Kernel.wiz"
        let samples := MTm.markerSamples
        let show' (b : Bool) : String := if b then "ok" else "error"
        for (t, ok) in samples, i in [0:samples.length] do
          let v := leanVerdict t (mark := false)
          unless (v != "error") == ok do
            throw (IO.userError s!"sample {i}: the Lean kernel says {v}, expected {show' ok}")
        let okV := "def okVerdict (t : Tm) : String := match infer empty (sortsInfer t) with\n  | .ok _ _ => \"ok\"\n  | .err _ => \"error\"\n"
        let calls := samples.map fun (t, _) => s!"(okVerdict {t.toWiz})"
        let printAll := "def printAll : List String → IO Unit\n  | .nil => IO.pure ()\n  | .cons s ss => do\n    IO.println s;\n    printAll ss\n"
        selfhostCompileRun (kernel ++ "\n" ++ okV ++ printAll ++ s!"def main : IO Unit := printAll {wizList calls}\n")
          ("\n".intercalate (samples.map fun (_, ok) => show' ok) ++ "\n")
        -- Marking on demand (`withMarksOnDemand`): a declaration the kernel finds unmarked is
        -- marked and checked again, and what is stored (and cached) is the marked term
        let g0 : Globals ZeroOneMany := {}
        let T2 : Term ZeroOneMany := (MTm.pi .ptrue .ptrue).toTerm
        let pairTy : Term ZeroOneMany := (MTm.sorted 1 0 (.sigma (.enum 2) (.sorted 0 0 (.pi .ptrue .ptrue)))).toTerm
        let d : Decl ZeroOneMany := { name := "d", type := pairTy, value := some (.pair (.tag ["a", "b"] 0) (.lam "x" (.var 0))) }
        match addDeclSorted g0 d with
        | .error e => throw (IO.userError s!"marking on demand failed: {e}")
        | .ok g => match (g.find? "d").bind (·.value) with
          | some (.pair _ (.prf ..)) => pure ()
          | v => throw (IO.userError s!"the stored value is not the marked one: {repr v}")
        -- a theorem is marked at once
        match addDeclSorted g0 { name := "t", type := T2, value := some (.lam "x" (.var 0)) } with
        | .ok g => unless ((g.find? "t").bind (·.value)) matches some (.prf ..) do throw (IO.userError "the theorem is stored unmarked")
        | .error e => throw (IO.userError s!"{e}")
        -- and when the marked term fails, the error is the second check's (not "unmarked proof")
        match addDeclSorted g0 { name := "e", type := pairTy, value := some (.pair (.tag ["a", "b"] 0) (.lam "x" (.tag ["a", "b"] 0))) } with
        | .ok _ => throw (IO.userError "an ill-typed declaration was accepted")
        | .error (.unmarkedProof ..) => throw (IO.userError "the error of the first check was reported")
        | .error _ => pure () },
    { name := "P1/PF-C: regularity is decided by conversion in both kernels (the probes as core terms; the type-position control)", run := fun _ => do
        let kernel ← IO.FS.readFile "selfhost/Kernel.wiz"
        let samples := MTm.convSamples
        let show' (b : Bool) : String := if b then "ok" else "error"
        -- the Lean kernel, by default (`conv`)
        for (n, t, ok) in samples do
          let v := leanVerdict t
          unless (v != "error") == ok do throw (IO.userError s!"{n}: the Lean kernel says {v}, expected {show' ok}")
        -- with the fast path alone (`--inert ground`): the *value* comparisons inside an
        -- equation are still accepted (PF-C's prop gate sets conversion-level full
        -- regularity, which does not consult `inertReg`); the *type* controls (`ty`, `tv`)
        -- need the inert-only rule and are rejected
        let ground (t : MTm) : Bool :=
          let g : Globals ZeroOneMany := { leanGlobals () with inertReg := .ground }
          -- (mandatory sorts and proof markers: the same pre-check, sorts pass and marking
          -- pass as `leanVerdict`, at the ground globals)
          if !(infer (R := ZeroOneMany) { globals := { g with lazyProofs := false, sortHolesOk := true } } t.toTerm).toBool then false else
          let t0 := (Mark.infer (R := ZeroOneMany) { globals := g, sortsOnly := true } t.toTerm).1
          (infer (R := ZeroOneMany) { globals := g } (Mark.infer (R := ZeroOneMany) { globals := g } t0).1).toBool
        for (n, t, _) in samples do
          unless ground t == (n != "ty" && n != "tv") do throw (IO.userError s!"{n}: unexpected verdict with the fast path alone")
        -- the Wiz kernel
        let okV := "def okVerdict (t0 : Tm) : String :=\n  let t := sortsInfer t0;\n  match infer (TCtx.inProof empty) t with\n  | .err _ => \"error\"\n  | .ok _ _ => match infer empty (MR.tm (markInfer empty t)) with\n    | .ok _ _ => \"ok\"\n    | .err _ => \"error\"\n"
        let calls := samples.map fun (_, t, _) => s!"(okVerdict {t.toWiz})"
        let printAll := "def printAll : List String → IO Unit\n  | .nil => IO.pure ()\n  | .cons s ss => do\n    IO.println s;\n    printAll ss\n"
        selfhostCompileRun (kernel ++ "\n" ++ wizVerdict ++ okV ++ printAll ++ s!"def main : IO Unit := printAll {wizList calls}\n")
          ("\n".intercalate (samples.map fun (_, _, ok) => show' ok) ++ "\n")
        -- and with `kernelInertConv := .false` the value comparisons are still accepted by
        -- the prop gate; only the type controls (`ty`, `tv`) are rejected
        let on := "def kernelInertConv : Bool := .true"
        unless (kernel.splitOn on).length == 2 do throw (IO.userError "kernelInertConv not found")
        let groundK := kernel.replace on "def kernelInertConv : Bool := .false"
        selfhostCompileRun (groundK ++ "\n" ++ wizVerdict ++ okV ++ printAll ++ s!"def main : IO Unit := printAll {wizList calls}\n")
          ("\n".intercalate (samples.map fun (n, _, _) => show' (n != "ty" && n != "tv")) ++ "\n") },
    { name := "U5b: a cast at a Π/Σ whose sort depends on a level variable is stuck, as the equation it goes along is; a Π without its sorts is rejected (both kernels)", run := fun _ => do
        -- (prop-harness, `wiz-notes/soundness-probes/ph-u5b-cast-at-unknown-sort.txt`) the cast
        -- used to compute, projecting a proof whose type is a stuck equation and no pair
        let g : Globals ZeroOneMany := {}
        let ω : Term ZeroOneMany := .qlit .many
        let stuck (v : Val ZeroOneMany) : Bool := (whnf v) matches .neutral (.cast ..) #[]
        -- (a) a level variable: T := True × Unit.{u}
        let T : Term ZeroOneMany := .sigma "x" ω (.unit 0) (.unit (.param "u")) ⟨0, .param "u"⟩
        unless stuck (eval g [] (.cast T T (.reflTy T) (.pair .tt .tt))) do throw (IO.userError "(a) the cast computed")
        -- at an instance it computes: `u := 1`
        let T1 := T.instLevels ["u"] [Level.ofNat 1]
        unless (whnf (eval g [] (.cast T1 T1 (.reflTy T1) (.pair .tt .tt)))) matches .pair .. do throw (IO.userError "(a) at u := 1 the cast is stuck")
        -- (b) (mandatory sorts) a Π without its sorts can't be formed: the kernel rejects it
        let F (s : BinderSorts) : Term ZeroOneMany := .pi "x" .default ω (.unit 1) (.unit 0) s
        let e : Val ZeroOneMany := Val.var 0
        let f : Val ZeroOneMany := Val.var 1
        match infer (R := ZeroOneMany) { globals := g } (F .hole) with
        | .ok _ => throw (IO.userError "(b) a Π without its sorts was accepted")
        | .error err => unless ((toString err).splitOn "without its sort").length > 1 do throw (IO.userError s!"(b) {err}")
        -- (b') `Unit → True` with its sorts is a proposition: a cast between propositions is stuck (P2)
        unless stuck (vCast g (eval g [] (F ⟨1, 0⟩)) (eval g [] (F ⟨1, 0⟩)) e f) do throw (IO.userError "(b') the cast computed")
        -- with both sorts known and not propositions it computes (a λ), as before
        let G : Term ZeroOneMany := .pi "x" .default ω (.unit 1) (.unit 1) ⟨1, 1⟩
        unless (vCast g (eval g [] G) (eval g [] G) e f) matches .lam .. do throw (IO.userError "an annotated Π cast is stuck")
        let kernel ← IO.FS.readFile "selfhost/Kernel.wiz"
        let main := "def shape (v : Val) : String := match whnf v with\n  | .vne (.hcast _ _ _ _) .snil => \"stuck\"\n  | .vlam _ _ => \"lam\"\n  | .vpair _ _ => \"pair\"\n  | _ => \"other\"\n" ++
          "def okT (t : Tm) : String := match infer empty t with\n  | .ok _ _ => \"ok\"\n  | .err m => m\n" ++
          "def FP : Val := eval .nil (.pi .qw (.lnum 1) (.lnum 0) (.unit (ln 1)) .ptrue)\n" ++
          "def U : Val := eval .nil (.pi .qw (.lnum 1) (.lparam \"u\") (.unit (ln 1)) (.unit (ln 1)))\n" ++
          "def G : Val := eval .nil (.pi .qw (.lnum 1) (.lnum 1) (.unit (ln 1)) (.unit (ln 1)))\n" ++
          "def S : Val := eval .nil (.sigma .qw (.lnum 0) (.lparam \"u\") .ptrue (.unit (ln 1)))\n" ++
          "def S1 : Val := eval .nil (.sigma .qw (.lnum 0) (.lnum 1) .ptrue (.unit (ln 1)))\n" ++
          "def main : IO Unit := do\n" ++
          "  IO.println (okT (.pi .qw .lhole .lhole (.unit (ln 1)) .ptrue));\n" ++
          "  IO.println (shape (vCast FP FP (fresh 0) (fresh 1)));\n" ++
          "  IO.println (shape (vCast U U (fresh 0) (fresh 1)));\n" ++
          "  IO.println (shape (vCast S S (fresh 0) (.vpair .vtt .vtt)));\n" ++
          "  IO.println (shape (vCast S1 S1 (fresh 0) (.vpair .vtt .vtt)));\n" ++
          "  IO.println (shape (vCast G G (fresh 0) (fresh 1)))\n"
        selfhostCompileRun (kernel ++ "\n" ++ main) "internal error: a Π's domain without its sort (the sorts pass did not fill it)\nstuck\nstuck\nstuck\npair\nlam\n" },
    { name := "P2 (I-1): a proof inside a marked proof is not evaluated: a tower of exponentials in Prop checks at once (both kernels)", run := fun _ => do
        -- k = 3 is 65 536 β-steps and k = 4 is 2^65536 if the checker runs the proof (it
        -- did: a `let` evaluated its value to bind it). The kernel has no step budget, so
        -- nothing but not evaluating can make these answer.
        for k in [3, 4, 6] do
          let t0 ← IO.monoMsNow
          checkEq "True" (leanVerdict (MTm.proofTower k) (mark := false))
          let ms := (← IO.monoMsNow) - t0
          unless ms < 5000 do throw (IO.userError s!"k = {k}: the Lean kernel took {ms} ms")
        -- the same term as a relevant `let` is rejected unmarked, as before
        let kernel ← IO.FS.readFile "selfhost/Kernel.wiz"
        let calls := [3, 4, 6].map fun k => s!"(rawVerdict {(MTm.proofTower k).toWiz})"
        let printAll := "def printAll : List String → IO Unit\n  | .nil => IO.pure ()\n  | .cons s ss => do\n    IO.println s;\n    printAll ss\n"
        selfhostCompileRun (kernel ++ "\n" ++ wizVerdict ++ printAll ++ s!"def main : IO Unit := printAll {wizList calls}\n") "True\nTrue\nTrue\n" },
    { name := "F7: reading a proof back stops at its step budget in the self-hosted kernel too (a tower under absurd, read back in a type)", run := fun _ => do
        -- (review F7) `quote` evaluates a suspended proof, to read it back as a normal form;
        -- Kernel.wiz's had no budget, and reading this type back did not finish (30 s). The
        -- Lean read-back stops at its budget and writes the proof as the message; the Wiz one
        -- must too, with the same message (and the kernels accept the term at once).
        let t := MTm.proofTowerAbsurd 4
        let g := leanGlobals ()
        let msg := Budget.message Budget.defaultSteps
        match infer (R := ZeroOneMany) { globals := g } t.toTerm with
        | .error e => throw (IO.userError s!"the Lean kernel rejects the term: {e}")
        | .ok (ty, _) =>
          unless ((reprStr (quote g 0 ty)).splitOn "a proof was not read back: it needs more than 1000000 evaluation steps").length > 1 do
            throw (IO.userError s!"the Lean read-back of the type did not stop at the budget: {(reprStr (quote g 0 ty)).take 400}")
        let kernel ← IO.FS.readFile "selfhost/Kernel.wiz"
        -- (and the stub is no constant: the kernel rejects a term that holds it, with the message)
        let stub := "(.prf (.lnum 0) (.axiomC proofStub .star))"
        let main := s!"def main : IO Unit := do\n  IO.println (rawVerdict {t.toWiz});\n  IO.println (match infer empty {stub} with\n    | .ok _ _ => \"ok\"\n    | .err m => m)\n"
        selfhostCompileRun (kernel ++ "\n" ++ wizVerdict ++ main)
          s!"(x0 : False) → Eq(Enum2, absurd(Enum2, x0), absurd(Enum2, {msg}))\n{msg}\n" },
    { name := "D2 (closed by mandatory sorts): a Π/Σ/ULift cast across components of different sorts is stuck, and its normal form is accepted (both kernels)", run := fun _ => do
        -- (meta-review D2, `wiz-notes/soundness-probes/mr-cast-component-sorts.lean`) the casts
        -- used to compute with no check on the components' sorts, and the kernel rejected the
        -- normal form of a term it had accepted ("cast between different universes"):
        -- subject reduction failed. With mandatory sorts every Π/Σ carries its components'
        -- sorts and `ULift` its content's, and the structural casts compute only when the
        -- two domains (contents) are in one sort and the two codomains are
        -- (`wiz-notes/mandatory-sorts.md` §5.3): the four probes are stuck casts, accepted
        -- with their normal forms; the control still computes.
        let castCase (X Y : MTm) : MTm × MTm := (.pi (.eqTy X Y) (.pi X Y), .lam (.lam (.cast X Y (.var 1) (.var 0))))
        let fn (i j : Nat) (a b : MTm) : MTm := .sorted i j (.pi a b)
        -- `X : Sort 1`, `Y : Sort 2`, `e : (X → Type) ≡ (Y → Type)`
        let nTy : MTm := .pi (.univ 0) (.pi (.univ 1) (.pi (.eqTy (fn 1 2 (.var 1) (.univ 0)) (fn 2 2 (.var 0) (.univ 0)))
          (.pi (fn 1 2 (.var 2) (.univ 0)) (fn 2 2 (.var 2) (.univ 0)))))
        let nV : MTm := .lam (.lam (.lam (.lam (.cast (fn 1 2 (.var 3) (.univ 0)) (fn 2 2 (.var 2) (.univ 0)) (.var 1) (.var 0)))))
        -- (name, term, type, does it compute?)
        let cases : List (String × (MTm × MTm) × Bool) :=
          [("Π, domains Unit₁ / Unit₂", castCase (fn 1 2 (.unit 0) (.univ 0)) (fn 2 2 (.unit 1) (.univ 0)), false),
           ("Σ, first components Unit₁ / Unit₂", castCase (.sorted 1 2 (.sigma (.unit 0) (.unit 1))) (.sorted 2 2 (.sigma (.unit 1) (.unit 1))), false),
           ("ULift.{1}, contents True / Unit₁", castCase (.ulift 0 1 .ptrue) (.ulift 1 1 (.unit 0)), false),
           ("Π, domains X : Sort 1 / Y : Sort 2", (nTy, nV), false),
           ("control: Π, domains and codomains pairwise in one sort", castCase (fn 2 1 (.unit 1) (.unit 0)) (fn 2 1 (.unit 1) (.enum 2)), true)]
        for (name, (ty, v), computes) in cases do
          let d0 : Decl ZeroOneMany := Decl.withSorts {} { name := "d", levelParams := [], type := ty.toTerm, value := some v.toTerm }
          let g ← match addDecl (R := ZeroOneMany) {} d0 with
            | .ok g => pure g
            | .error e => throw (IO.userError s!"{name}: the term is rejected: {e}")
          let vv := d0.value.getD .tt
          let nf := quote g 0 (eval g [] vv)
          match addDecl (R := ZeroOneMany) {} { d0 with value := some nf } with
          | .error e => throw (IO.userError s!"{name}: its normal form is rejected: {e}")
          | .ok _ => pure ()
          -- the normal form: under `e` and `t`, a stuck cast (or the control's λ)
          let isStuck : Bool := match nf with
            | .lam _ (.lam _ (.cast ..)) | .lam _ (.lam _ (.lam _ (.lam _ (.cast ..)))) => true
            | _ => false
          unless isStuck == !computes do throw (IO.userError s!"{name}: expected {if computes then "a reduct" else "a stuck cast"}, got {repr nf}")
        let kernel ← IO.FS.readFile "selfhost/Kernel.wiz"
        let calls := cases.map fun (_, (ty, v), _) => s!"  both {v.toWiz} {ty.toWiz};\n"
        let (_, cV) := castCase (fn 2 1 (.unit 1) (.unit 0)) (fn 2 1 (.unit 1) (.enum 2))
        let main := "def okT (t : Tm) : String := match infer empty t with\n  | .ok _ _ => \"ok\"\n  | .err _ => \"error\"\n" ++
          "def both (v ty : Tm) : IO Unit := do\n  let t := sortsInfer (.ann v ty);\n  IO.println (okT t);\n" ++
          "  match t with\n  | .ann v' ty' => IO.println (okT (.ann (quote 0 (eval .nil v')) ty'))\n  | _ => IO.println \"?\"\n" ++
          "def lamShape : Tm → String\n  | .lam (.lam (.lam _)) => \"lam\"\n  | _ => \"other\"\n" ++
          "def main : IO Unit := do\n" ++ String.join calls ++
          s!"  IO.println (lamShape (quote 0 (eval .nil (sortsInfer {cV.toWiz}))))\n"
        selfhostCompileRun (kernel ++ "\n" ++ main) (String.join (cases.map fun _ => "ok\nok\n") ++ "lam\n") },
    { name := "F1 (prf-review): the marking passes go inside a marker already in the term (both kernels)", run := fun _ => do
        -- a marker written by read-back (`prf.{0} (refl B2 ((), fun x => x))`, a solved hole)
        -- holds a relevant subterm whose proof needs a marker of its own (I-1)
        let surf := "def B2 : Type := (x : Unit) × (True → True)\n" ++
          "def P (h : ((), fun (x : True) => x) = (((), fun x => x) : B2)) : Prop := True\n" ++
          "def t3 (h : ((), fun (x : True) => x) = (((), fun x => x) : B2)) : P h := ()\n" ++
          -- (the pair ascribed: since #123 an equation at a type whose second part is a
          -- proposition computes to `True` only once that is known, and the elaborator
          -- does not solve the pair's type through it; the same on master without P2)
          "def t5 : P (refl (((), fun x => x) : B2)) := t3 (refl (((), fun x => x) : B2))\n" ++
          "def t4 : P (refl (((), fun x => x) : B2)) := t3 _\n"
        ok surf
        -- the pair's type left to inference (#130: `refl` retries against the expected
        -- equation's type), as in prf-review's probe
        ok (surf.replace "(((), fun x => x) : B2)" "((), fun x => x)")
        -- raw: prf.{0} ((fun _ => () : a = a → True) (refl B2 a)) : True, a := ((), fun x => x)
        let B2 : MTm := .sigma (.unit 0) (.pi .ptrue .ptrue)
        let a : MTm := .ann (.pair .star (.lam (.var 0))) B2
        let v : MTm := .prf (.num 0) (.app (.ann (.lam .star) (.pi (.eq B2 a a) .ptrue)) (.refl B2 a))
        let ty : MTm := .ptrue
        let g : Globals ZeroOneMany := {}
        let d : Decl ZeroOneMany := { name := "f1", levelParams := [], type := ty.toTerm, value := some v.toTerm }
        -- as it is, the kernel rejects it (the λ inside `refl`'s relevant `a` is unmarked) ...
        unless (addDecl g (Decl.withSorts g d)) matches .error (.unmarkedProof ..) do throw (IO.userError "the unmarked term was not rejected for its inner proof")
        -- ... and the pass marks it
        if let .error e := addDecl g (Decl.withMarks g d) then throw (IO.userError s!"the marked term is rejected: {e}")
        let kernel ← IO.FS.readFile "selfhost/Kernel.wiz"
        let main := "def okD (v : Tm) : String := match checkDecl .ptrue (.some (sortsClosed v .ptrue)) with\n  | .ok _ _ => \"ok\"\n  | .err _ => \"error\"\n" ++
          s!"def main : IO Unit := do\n  IO.println (okD {v.toWiz});\n  IO.println (okD (markClosed {v.toWiz} .ptrue))\n"
        selfhostCompileRun (kernel ++ "\n" ++ main) "error\nok\n" },
    { name := "P2 (R1): a level-generic term is marked at its level, and is a suspended proof at the instance 0 (both kernels)", run := fun _ => do
        -- k.{u} (A : Sort u) (a : A) : A := (fun x => x : A → A) a
        let ty : MTm := .pi (.sortParam "u") (.pi (.var 0) (.var 1))
        let v : MTm := .lam (.lam (.app (.ann (.lam (.var 0)) (.pi (.var 1) (.var 2))) (.var 0)))
        let g0 : Globals ZeroOneMany := {}
        let d := Decl.withMarks g0 { name := "k", levelParams := ["u"], type := ty.toTerm, value := some v.toTerm }
        -- unmarked it is rejected: the inner λ is at a type in `Sort (imax u u)`, which may be 0
        if let .ok _ := addDecl g0 { name := "k", levelParams := ["u"], type := ty.toTerm, value := some v.toTerm } then
          throw (IO.userError "the unmarked level-generic term was accepted")
        let g ← match addDecl g0 d with
          | .ok g => pure g
          | .error e => throw (IO.userError s!"the marked term is rejected: {e}")
        let inst (l : Nat) (A a : Term ZeroOneMany) : Val ZeroOneMany :=
          whnf (eval g [] (.app (.app (.const "k" [Level.ofNat l]) A) a))
        -- at `u := 1` it computes; at `u := 0` the whole of `k` is a proof (of
        -- `(A : Prop) → A → A`): suspended, and applying it only grows its spine
        unless (inst 1 (.enum ["a", "b"]) (.tag ["a", "b"] 1)) matches .tag _ 1 do throw (IO.userError "k.{1} did not compute")
        unless (inst 0 (.unit 0) .tt) matches .neutral (.prf ..) #[.app _, .app _] do throw (IO.userError "k.{0} was evaluated")
        let kernel ← IO.FS.readFile "selfhost/Kernel.wiz"
        let main := "def kTy : Tm := sortsTy " ++ ty.toWiz ++ "\ndef kV : Tm := markClosed " ++ v.toWiz ++ " kTy\n" ++
          "def kAt (l : Nat) (A a : Tm) : Val := whnf (eval .nil (.app (.app (.const \"k\" (.cons \"u\" .nil) (.cons (.lnum l) .nil) kV kTy) A) a))\n" ++
          "def shape : Val → String\n  | .vtag _ _ => \"tag\"\n  | .vne (.hprf _ _) (.sapp (.sapp .snil _) _) => \"suspended\"\n  | _ => \"other\"\n" ++
          "def okD (v : Tm) : String := match checkDecl kTy (.some (sortsClosed v kTy)) with\n  | .ok _ _ => \"ok\"\n  | .err _ => \"error\"\n" ++
          "def main : IO Unit := do\n  IO.println (okD " ++ v.toWiz ++ ");\n  IO.println (okD kV);\n" ++
          "  IO.println (shape (kAt 1 (.enum 2) (.tag 2 1)));\n  IO.println (shape (kAt 0 .ptrue .star))\n"
        selfhostCompileRun (kernel ++ "\n" ++ main) "error\nok\ntag\nsuspended\n" },
    { name := "the Wiz kernel checks declarations at symbolic levels like the Lean kernel", run := fun _ => do
        let kernel ← IO.FS.readFile "selfhost/Kernel.wiz"
        let decls := MTm.declSamples ++ MTm.levelPuzzles 200
        let expected := decls.map leanDeclVerdict
        unless (expected.filter (· == "ok")).length ≥ 60 do throw (IO.userError "too few valid declarations")
        unless (expected.filter (· == "error")).length ≥ 30 do throw (IO.userError "too few invalid declarations")
        let decl := "def wellTyped (ty0 : Tm) (v0 : Option Tm) : Bool :=\n  let ty := sortsTy ty0;\n  match inferUniv (TCtx.noMarkers empty) ty with\n  | .err _ => .false\n  | .ok _ _ => match v0 with\n    | .none => .true\n    | .some v => match check (TCtx.noMarkers empty) (sortsClosed v ty) (eval .nil ty) with\n      | .ok _ _ => .true\n      | .err _ => .false\n" ++
          "def declVerdict (ty0 : Tm) (v0 : Option Tm) : String := match wellTyped ty0 v0 with\n  | .false => \"error\"\n  | .true =>\n    let ty := markTy empty ty0;\n    match checkDecl ty (match v0 with\n      | .some v => .some (markClosed v ty)\n      | .none => .none) with\n    | .ok _ _ => \"ok\"\n    | .err _ => \"error\"\n"
        let calls := decls.map fun (_, v, ty) =>
          s!"(declVerdict {ty.toWiz} {match v with | some v => s!"(.some {v.toWiz})" | none => ".none"})"
        let main := s!"def main : IO Unit := printAll {wizList calls}\n"
        let printAll := "def printAll : List String → IO Unit\n  | .nil => IO.pure ()\n  | .cons s ss => do\n    IO.println s;\n    printAll ss\n"
        selfhostCompileRun (kernel ++ "\n" ++ decl ++ printAll ++ main) ("\n".intercalate expected ++ "\n") },
    -- D1: regularity is off in both kernels; with it on, the Wiz kernel loops too
    -- (L-2) the kernel checks the value of a `let` at 0 as an erased position, so the
    -- backend must not compile it (the frontend doesn't produce `letq` today)
    { name := "Backend.wiz erases the value of a let at 0, and keeps it at 1 and ω", run := fun _ => do
        -- the backend test does not need the CLI driver (which expects the generated
        -- parser tables and toolchain constants): checker + Backend only
        let src ← (Selfhost.frontendFiles ++ ["selfhost/Backend.wiz"]).mapM (fun (f : String) => IO.FS.readFile f)
        let show1 (q : String) := s!"(match eraseCheck .nil empty (.letq {q} (.enum 2) (.tag 2 0) (.tag 2 1)) (.venum 2) with\n    | .ok e => showE e\n    | .err m => String.append \"error: \" m)"
        let prog := "import IO\nimport Std\n" ++ "\n".intercalate (src.map Selfhost.strip) ++ "\n" ++
          s!"def main : IO Unit := do\n  IO.println {show1 ".qz"};\n  IO.println {show1 ".qo"};\n  IO.println {show1 ".qw"}\n"
        let kept := "(let " ++ "#0" ++ "; "
        selfhostRunWith prog fun out => do
          match out.splitOn "\n" with
          | z :: o :: w :: _ =>
            unless z.startsWith "(let ◾; " do throw (IO.userError s!"a let at 0 keeps its value: {z}")
            unless !o.startsWith "(let ◾; " && o.startsWith "(let " && o == w do
              throw (IO.userError s!"unexpected erasure at 1 / ω: {o} / {w} (expected like {kept}…)")
          | _ => throw (IO.userError s!"unexpected output: {out}") },
    { name := "D1 (Abel–Coquand): both kernels check the let-encoded program, with regularity on too (P2: its let-bound proofs are marked, and never evaluated)", run := fun _ => do
        let kernel ← IO.FS.readFile "selfhost/Kernel.wiz"
        let control := MTm.abelCoquand false
        unless leanVerdict control != "error" do throw (IO.userError "the Lean kernel rejects the control")
        selfhostCompileRun (kernel ++ "\n" ++ wizVerdict ++ s!"def main : IO Unit := IO.println (markedVerdict {control.toWiz})\n")
          (leanVerdict control ++ "\n")
        let loop := MTm.abelCoquand true
        -- without regularity (the default) both kernels check it
        let expected := leanVerdict loop
        unless expected != "error" do throw (IO.userError "the Lean kernel without regularity rejects it")
        selfhostCompileRun (kernel ++ "\n" ++ wizVerdict ++ s!"def main : IO Unit := IO.println (markedVerdict {loop.toWiz})\n") (expected ++ "\n")
        -- unmarked, both kernels reject it: its `let`-bound proofs are λs (the marker is
        -- required, not a convention of the elaborator)
        checkEq "error" (leanVerdict loop (mark := false))
        selfhostCompileRun (kernel ++ "\n" ++ wizVerdict ++ s!"def main : IO Unit := IO.println (rawVerdict {loop.toWiz})\n") "error\n"
        -- with regularity (`kernelRegularity`; `--regularity full` in the Lean kernel) the
        -- program used to loop in the Wiz kernel: `Omega := delta omega` was evaluated by
        -- the `let`. Marked, `delta` is a suspended proof, and `delta omega` only grows its
        -- spine: both kernels answer.
        let off := "def kernelRegularity : Bool := .false"
        unless (kernel.splitOn off).length == 2 do throw (IO.userError "kernelRegularity not found")
        let withReg := kernel.replace off "def kernelRegularity : Bool := .true"
        selfhostCompileRun (withReg ++ "\n" ++ wizVerdict ++ s!"def main : IO Unit := IO.println (markedVerdict {loop.toWiz})\n") (expected ++ "\n")
        let g : Globals ZeroOneMany := { leanGlobals () with regularity := .full }
        match infer (R := ZeroOneMany) { globals := g } (Mark.infer (R := ZeroOneMany) { globals := g } loop.toTerm).1 with
        | .ok _ => pure ()
        | .error e => throw (IO.userError s!"the Lean kernel with full regularity rejects it: {e}") }

  ]

/-- The audit's stub: a file that pretends to be the self-hosted compiler (or checker) and
writes its input to standard output. A case in `selfhost` that passes with this in place
does not run the pipeline. -/
def echoStub (dir : System.FilePath) : IO System.FilePath := do
  let p := dir / "echo-stub"
  IO.FS.writeFile p ("#!/bin/sh\n" ++
    "for f in input.wiz \"$1\"; do\n" ++
    "  if [ -f \"$f\" ]; then cat \"$f\"; exit 0; fi\n" ++
    "done\n" ++
    "exit 0\n")
  let c ← IO.Process.output { cmd := "chmod", args := #["+x", p.toString] }
  unless c.exitCode == 0 do throw (IO.userError s!"chmod failed: {c.stderr}")
  pure p

/-- The cases that run the **Lean host** toolchain only: they compile Wiz sources with the
Lean compiler, or they are in-process probes of the Lean kernel (their "and both kernels
agree below" counterpart is the `selfhost` case that runs the Wiz program). They are not
evidence about the self-hosted pipeline, so they live in their own group; a case that
reaches `selfhostCompiler`/`selfhostChecker` belongs to `selfhost` instead. -/
def selfHostHostGroup : Group where
  name := "selfhost-host"
  exercise := "Stages 12b–14q (Lean host only)"
  cases := [
    { name := "the host frontend elaborates the self-hosted checker and compiler (a fast guard)", run := fun _ =>
        selfhostHostGuard },
    { name := "the additive match (T.casesOnA) runs, compiled by the Lean compiler (21v)", run := fun _ =>
        ioRun linearMatchProgram "3\n5\n6\n" },
    { name := "Kernel.wiz quantity terms: the same variable is the same quantity, and a Σ at a stuck non-variable quantity is rejected, as in the Lean kernel (21x, review probes 7a, 15b)", run := fun _ => do
        -- (`MTm` has no `Qty` terms; the Lean kernel's verdicts are in
        -- wiz-notes/fieldq-review-probes: 7a accepted, 15b rejected by `qtyPoly`)
        let kernel ← IO.FS.readFile "selfhost/Kernel.wiz"
        -- (mandatory sorts: the sorts pass fills the `Π`s' holes, as the frontend runs it)
        let verdict := "def piW (a b : Tm) : Tm := .pi .qw .lhole .lhole a b\n" ++
          "def verdict (t : Tm) : String := match infer empty (sortsInfer t) with\n  | .ok _ _ => \"ok\"\n  | .err _ => \"error\"\n"
        let dq := "(.ann (.darg (.var 0) (.unit (ln 1)) (.lam (.dret .star))) (.descr (ln 0) (.unit (ln 1))))"
        let p7a := s!"(.ann (.lam (.lam (.letq .qz (.eqTy (.unit (ln 1)) (.unit (ln 1))) (.fst (.var 0)) .star))) (piW .qty (piW (.eq (.descr (ln 0) (.unit (ln 1))) {dq} {dq}) (.unit (ln 1)))))"
        let p15b := "(.ann (.lam (.con (.pair .star (.pair .star .star)))) (piW (piW (.unit (ln 1)) .qty) (.mu (ln 0) (.unit (ln 1)) " ++
          "(.app (.ann (.lam (.darg (.var 0) (.unit (ln 1)) (.lam (.dret .star)))) (piW .qty (.descr (ln 0) (.unit (ln 1))))) (.app (.var 0) .star)) .star)))"
        ioRun (kernel ++ "\n" ++ verdict ++ s!"def main : IO Unit := do\n  IO.println (verdict {p7a});\n  IO.println (verdict {p15b})\n")
          "ok\nerror\n" },
    -- The anti-vacuity case: the pipeline group must fail when its compiler/checker is a
    -- stub that echoes `input.wiz`. It runs each case of `selfhost` in a child process
    -- with `WIZ_SELFHOST_COMPILER`/`WIZ_SELFHOST_CHECKER` set (the override in
    -- `Tests/Elab.lean`), so a new case that forgets to invoke the pipeline fails here.
    { name := "an echoing stub compiler and checker fail every =selfhost case (the pipeline group is not vacuous)", run := fun _ => do
        let dir ← IO.FS.createTempDir
        let stub ← echoStub dir
        let self ← IO.appPath
        let env : Array (String × Option String) :=
          #[("WIZ_SELFHOST_COMPILER", some stub.toString), ("WIZ_SELFHOST_CHECKER", some stub.toString)]
        let flags := (← flagsRef.get).toArray
        let mut passed := #[]
        for c in selfHostGroup.cases, i in [0:selfHostGroup.cases.length] do
          let out ← IO.Process.output
            { cmd := "timeout", args := #["900", self.toString, "--run-case", "selfhost", toString i] ++ flags, env }
          -- (a case that skipped did not demonstrate the pipeline, but it did not pass
          -- either: only an exit 0 without a `skipped` note is a vacuous case; both the
          -- note and the older printed `(skipped: …)` form count)
          let skipped := (out.stdout.splitOn "\n").any fun l =>
            l.startsWith (noteMarker ++ "skipped ") || l.trimAscii.toString.startsWith "(skipped: "
          if out.exitCode == 0 && !skipped then passed := passed.push s!"{i}: {c.name}"
        unless passed.isEmpty do
          throw (IO.userError s!"{passed.size} of {selfHostGroup.cases.length} =selfhost cases pass with a stub compiler/checker that echoes its input; they do not test the pipeline:\n{"\n".intercalate passed.toList}")
        note s!"all {selfHostGroup.cases.length} =selfhost cases failed with the echo stub" },
    { name := "selfhost/Tables.wiz is current (regenerate with `lake build genSelfhostTables`)", run := fun _ => do
        -- the checked-in file is what the selfhost builds read; a grammar change that
        -- does not regenerate it is a stale compiler, so fail here (CI runs this shard
        -- when `Wiz/Parser/*` changes)
        let file ← IO.FS.readFile "selfhost/Tables.wiz"
        unless file == Selfhost.tablesFile do
          throw (IO.userError s!"selfhost/Tables.wiz is stale: run `lake build genSelfhostTables` and commit it (file {file.length} bytes, the tables now {Selfhost.tablesFile.length})") },
    { name := "both kernels compare propositions by equivalence (and agree on it below)", run := fun _ => do
        -- the domains' equation is an equivalence, not `False`
        match MTm.propShapes.map leanVerdict with
        | ["error", ok] => unless ok != "error" do throw (IO.userError "the equivalence was rejected")
        | vs => throw (IO.userError s!"unexpected verdicts {vs}") },
    { name := "Size = Size is stuck, not False (and both kernels agree on it below)", run := fun _ => do
        match MTm.sizeEq.map leanVerdict with
        | ["error", "error", "error", a, b] =>
          unless a == "EqTy(Size, Size)" && b == "EqTy(Size<(∞), Size<(∞))" do
            throw (IO.userError s!"unexpected types {a}, {b}")
        | vs => throw (IO.userError s!"unexpected verdicts {vs}") },
    { name := "projections need an unrestricted pair; positions at 0 are erased; eliminators use their scrutinee ω times (R1; and both kernels agree on it below)", run := fun _ => do
        for (t, ok) in MTm.projRule ++ MTm.elimRule ++ MTm.usageRule ++ MTm.linearCaseRule do
          let v := leanVerdict t
          unless (v != "error") == ok do
            throw (IO.userError s!"expected {if ok then "accepted" else "rejected"}, got {v}: {MTm.pretty 0 t}") },
    { name := "the size of μ and ν is checked (and both kernels agree on it below)", run := fun _ => do
        let vs := MTm.sizeArgs.map leanVerdict
        unless vs.take 2 == ["error", "error"] && (vs.drop 2).all (· != "error") do
          throw (IO.userError s!"unexpected verdicts {vs}") },
    { name := "guarded μ/ν descriptions: μ X. X is rejected, Nat/List/tree and a stream are accepted (and both kernels agree below)", run := fun _ => do
        for (t, ok) in MTm.muSize do
          let v := leanVerdict t
          unless (v != "error") == ok do
            throw (IO.userError s!"expected {if ok then "accepted" else "rejected"}, got {v}: {MTm.pretty 0 t}") },
    { name := "∞ is not below itself (and both kernels agree on it below)", run := fun _ => do
        let vs := MTm.sizeInf.map leanVerdict
        unless vs.take 5 == List.replicate 5 "error" && (vs.drop 5).all (· != "error") do
          throw (IO.userError s!"unexpected verdicts {vs}") },
    { name := "F6: literal quantities that differ make types unequal (and both kernels agree on it below)", run := fun _ => do
        let vs := MTm.qtyApart.map leanVerdict
        unless vs.take 2 |>.all (· != "error") do throw (IO.userError s!"unexpected verdicts {vs}")
        unless vs[2]? == some "error" && vs[3]? != some "error" do throw (IO.userError s!"unexpected verdicts {vs}") },
    { name := "F3 (audit): the eliminators check the index type's level (and both kernels agree on it below)", run := fun _ => do
        let vs := MTm.elimLevels.map leanVerdict
        let names := ["ind", "sfix", "scase", "coit", "scofix"]
        for n in names, k in [0:5] do
          unless vs[k]? == some "error" do
            throw (IO.userError s!"{n} with an index type one level too high was accepted: {vs[k]?}")
          unless vs[5 + k]? == some "error" do
            throw (IO.userError s!"{n} with an index type one level too low was accepted: {vs[5 + k]?}")
          unless vs[10 + k]? != some "error" && vs[15 + k]? != some "error" do
            throw (IO.userError s!"{n} with a well-levelled index type was rejected: {vs[10 + k]?}, {vs[15 + k]?}")
        unless vs.drop 20 == ["error", "error"] do throw (IO.userError s!"unexpected verdicts {vs.drop 20}") },
    { name := "transp is rejected at a proposition, as eq and refl are (and both kernels agree on it below)", run := fun _ => do
        let vs := MTm.transpProp.map leanVerdict
        unless vs.take 2 == ["error", "error"] && (vs.drop 2).all (· != "error") && vs.length == 4 do
          throw (IO.userError s!"unexpected verdicts {vs}") },
    { name := "Q4: a small description field is rejected, a lifted one works (and both kernels agree on it below)", run := fun _ => do
        let vs := MTm.smallField.map leanVerdict
        let body := (vs.drop 4).dropLast
        unless vs.take 4 == List.replicate 4 "error" && body.all (· != "error") && vs.getLast? == some "error" do
          throw (IO.userError s!"unexpected verdicts {vs}")
        -- `getS D'` is a type (it computes to `ULift True`), and a boxed proof unboxes to `True`
        unless vs[5]? == some "U0" && vs[9]? == some "True" do
          throw (IO.userError s!"unexpected types {vs}") },
    { name := "P2 with #126: a level-generic structurally recursive definition's derived equations agree with its value (checkImplAgrees), at levels 0 and 1", run := fun _ => do
        -- its marker is `prf.{u}` at a symbolic level: evaluated, not suspended, so the
        -- agreement check goes through the recursion as for data; at `u := 0` it is a proof
        ok ("inductive N where\n  | z\n  | s (n : N)\n" ++
          "def natRec.{u} (P : N → Sort u) (z : P .z) (s : (n : N) → P n → P (.s n)) : (n : N) → P n\n" ++
          "  | .z => z\n  | .s n => s n (natRec P z s n)\n" ++
          "def allT (n : N) : True := natRec.{0} (fun _ => True) () (fun _ h => h) n\n" ++
          "def two : N := natRec.{1} (fun _ => N) .z (fun _ m => .s m) (.s (.s .z))\n" ++
          "#reduce two") [".s (.s .z)"]
        -- the derived equations are what the kernel checked against the value
        let s := runFrontend (R := ZeroOneMany) ("inductive N where\n  | z\n  | s (n : N)\n" ++
          "def natRec.{u} (P : N → Sort u) (z : P .z) (s : (n : N) → P n → P (.s n)) : (n : N) → P n\n" ++
          "  | .z => z\n  | .s n => s n (natRec P z s n)\n")
        match s.globals.find? "natRec" with
        | some d => unless d.derivedEquations do throw (IO.userError "natRec has no derived equations: the test does not reach checkImplAgrees")
        | none => throw (IO.userError "natRec was not declared") },

    { name := "(30f) the self-hosted frontend: a superclass is an instance-implicit parameter (A10)", run := fun _ =>
        selfhostCheckFile superclassParam superclassParamExpected },
    { name := "(30f) the self-hosted backend: a class with a superclass parameter compiles and runs (A10)", run := fun _ =>
        selfhostCompileRun superclassProgram "5\n" }

  ]

builtin_initialize registerGroup selfHostGroup
builtin_initialize registerGroup selfHostHostGroup

end Tests.Elab
