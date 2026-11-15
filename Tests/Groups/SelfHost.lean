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
   (.dhrec c c c c, 4, 0), (.delim w c c c c c c, 6, 1), (.mu w c c c c (some ("h", [w], [c])), 5, 2),
   (.con c, 1, 0), (.ind w c c w c c c c, 6, 2), (.nu w c c c c (some ("h", [w], [c])), 5, 2), (.out c, 1, 0),
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
toolchain's `gcCflags`/`gcLdflags`), run it, and compare its output. -/
def selfhostCompileRun (file expected : String) (flags : Array String := #[]) (progArgs : Array String := #[])
    (opt : String := "-O2") (smallStack : Bool := false) : IO Unit := do
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
    checkEq expected run.stdout

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

/-- (21l) A program with foreign functions gives the same output compiled by the Lean
compiler and by the self-hosted one (with the collector unless `gc := false`, and with
reference counting, which also checks that every object was freed). -/
def ffiAgrees (src expected : String) (gc : Bool := true) : IO Unit := do
  ioRun src expected
  if gc then selfhostCompileRun src expected
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
  ("def imp {n : Nat} (x : Nat) : Nat := n\n", false),
  ("def er (0 x : Nat) : Nat := x\n", false),
  ("def bad2 (2 x : Nat) : Nat := x\n", false),
  ("def l1bad (x : Nat) : Nat := let 1 y := x; Nat.add y y\n", false),
  ("def flbad2 : (y : Nat) → Nat := fun (1 y : Nat) => y\n", false),
  ("def useAx2 (1 y : Nat) : Nat := Nat.add (lin1 y) y\n", false),
  ("def mk {w : Nat} : Pt w := Pt.mk w\n", false),
  ("def toW (1 x : Nat) : Nat := Nat.succ x\n", false),
  ("def l0 (x : Nat) : Nat := let 0 y := x; y\n", false),
  ("def linTwice (1 z : Nat) : Nat := lin z (fun y => Nat.add y y)\n", false)]

/-- (stage 21x) Constructor fields with quantities (`Desc.arg q S D`) and implicit
constructor fields (at 0, filled in at the call, not named by patterns): the same
verdicts in both frontends. -/
def fieldQtyHeader : String :=
  "axiom Tok : Type\naxiom use : (1 t : Tok) → Nat\n" ++
  "inductive E0 where\n  | mk (0 n : Nat) (m : Nat)\n" ++
  "inductive L1 where\n  | mk (1 t : Tok)\n" ++
  "inductive W where\n  | mk (ω n : Nat)\n" ++
  "inductive V (A : Type) : Nat → Type where\n  | nil : V A Nat.zero\n" ++
  "  | cons {n : Nat} (a : A) (rest : V A n) : V A (Nat.succ n)\n" ++
  "structure S0 where\n  0 n : Nat\n  m : Nat\n" ++
  "structure P1 where\n  1 a : Tok\n  b : Nat\n"
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
  -- an implicit field: at 0, inserted at the call, not named by a pattern
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
  ("inductive Q2 where\n  | mk (2 n : Nat)\n", false)]

/-- (stage 21x) Field quantities and implicit fields, compiled and run. -/
def fieldQtyProgram : String :=
  "import Prelude\n" ++
  "inductive E0 where\n  | mk (0 n : Nat) (m : Nat)\n" ++
  "inductive V (A : Type) : Nat → Type where\n  | nil : V A Nat.zero\n" ++
  "  | cons {n : Nat} (a : A) (rest : V A n) : V A (Nat.succ n)\n" ++
  "inductive L1 where\n  | mk (1 n : Nat)\n" ++
  "def getM : E0 → Nat\n  | .mk _ m => m\n" ++
  "def vsum {n : Nat} : V Nat n → Nat\n  | .nil => 0\n  | .cons a r => Nat.add a (vsum r)\n" ++
  "def unL : L1 → Nat\n  | .mk n => n\n" ++
  "def main : IO Unit := do\n  IO.println (Nat.toString (getM (E0.mk 3 4)));\n" ++
  "  IO.println (Nat.toString (vsum (V.cons 1 (V.cons 2 V.nil))));\n" ++
  "  IO.println (Nat.toString (unL (L1.mk 9)))\n"

/-- (stage 21m, K1) The pinned differences, `(declaration, Lean accepts, self-hosted
accepts)` (docs/CoreSpec.md §15): the Lean frontend takes a `match` on a linear scrutinee
apart with `T.casesOn1` (the case at 1), the self-hosted frontend's match is the case at
ω, which uses the scrutinee ω times. (Constructor field quantities and implicit fields
were differences until 21x; a linear variable used once in each branch of a `match`
until 21v: `linearMatchDecls`.) -/
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
  if tc.gcCflags.isEmpty then IO.println "    (skipped: no garbage collector, --gc-cflags)"; return
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


def selfHostGroup : Group where
  name := "selfhost"
  exercise := "Stages 12b–14q"
  cases := [
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
        ioRun prog ("\n".intercalate expected ++ "\n") },
    { name := "the parser in Wiz agrees with the Lean parser", run := fun _ => do
        let lexSrc ← IO.FS.readFile "selfhost/Lex.wiz"
        let parseSrc ← IO.FS.readFile "selfhost/Parse.wiz"
        let t := Builtin.tables
        let expected := parseDiffCorpus.map fun (c, i) => leanParse t c i
        let calls := parseDiffCorpus.map fun (c, i) => s!"(parse cats tokens {wizLit c} {wizLit i})"
        let prog := lexSrc ++ "\n" ++ parseSrc ++ "\n" ++ wizTables t ++
          s!"def tokens : List String := {wizList (t.tokens.toList.map wizLit)}\n" ++
          s!"def main : IO Unit := printAll {wizList calls}\n"
        ioRun prog ("\n".intercalate expected ++ "\n") },
    { name := "selfhost/Tables.wiz is current (regenerate with `lake build genSelfhostTables`)", run := fun _ => do
        -- the checked-in file is what the selfhost builds read; a grammar change that
        -- does not regenerate it is a stale compiler, so fail here (CI runs this shard
        -- when `Wiz/Parser/*` changes)
        let file ← IO.FS.readFile "selfhost/Tables.wiz"
        unless file == Selfhost.tablesFile do
          throw (IO.userError s!"selfhost/Tables.wiz is stale: run `lake build genSelfhostTables` and commit it (file {file.length} bytes, the tables now {Selfhost.tablesFile.length})") },
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
        ioRun prog ("\n".intercalate expected ++ "\n") },
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
        ioRun (kernel ++ "\n" ++ defs ++ main) ("(x0 : U0) → (x1 : x0) → x0\n(x0 : U0) → (x1 : x0) → x0\n" ++
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
        ioRun (kernel ++ "\n" ++ probe) ("d's declaration, at every level: ok\nF's declaration: ok\nthe proof of d.{0}: ok\n" ++
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
        ioRun prog (computed ++ computed ++ "U0\n") },
    -- Y4: `Kernel.wiz` compares two constants by name, so a name has one declaration
    { name := "a name is declared once: a second declaration is an error (it proved an empty type inhabited)", run := fun _ =>
        selfhostCheckFile dupNames dupNamesExpected },
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
        ioRun prog ("(x0 : U0) → (x1 : x0) → x0\nU3\n(x0 : U0) → U0\n" ++
          "error: cannot infer the type of a λ; add a type ascription\nscope error: unknown identifier y\n" ++
          "(x0 : (x0 : U0) → U0) → (x1 : U0) → U0\nparse " ++ leanParse t "term" bad ++ "\n") },
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
          s!"error: unknown identifier Bad\nerror: type mismatch: expected Nat, got U1\n") },
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
    { name := "constructors by their names (.c) and @f, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\ninductive List (A : Type) where\n  | nil\n  | cons (head : A) (tail : List A)\ndef two : Nat := .succ (.succ .zero)\n#reduce two\ndef xs : List Nat := .cons .zero (.cons two .nil)\n#reduce xs\ndef id {A : Type} (x : A) : A := x\n#reduce @id Nat .zero\ndef add : Nat → Nat → Nat\n  | .zero, n => n\n  | .succ m, n => .succ (add m n)\n#reduce add two two\ndef map {A B : Type} (f : A → B) : List A → List B\n  | .nil => .nil\n  | .cons h t => .cons (f h) (map f t)\n#reduce map (add two) xs\ndef bad : Nat := .nil\n"
          "Nat : U0\nList : (x0 : U0) → U0\ntwo : Nat\ncon((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt))))\nxs : (List Nat)\ncon((#1, (con((#0, (tt, tt))), (con((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (con((#0, (tt, tt))), (tt, tt))))), (tt, tt)))))\nid : (x0 :0 U0) → (x1 : x0) → x0\ncon((#0, (tt, tt)))\nadd : (x0 : Nat) → (x1 : Nat) → Nat\ncon((#1, (con((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt))))\nmap : (x0 :0 U0) → (x1 :0 U0) → (x2 : (x2 : x0) → x1) → (x3 : (List x0)) → (List x1)\ncon((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (con((#1, (con((#1, (con((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (con((#0, (tt, tt))), (tt, tt))))), (tt, tt)))))\nerror: unknown identifier Nat.nil\n" },
    { name := "partial definitions and mutual blocks, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\ninductive Bool where\n  | false\n  | true\npartial def loop (n : Nat) : Nat := loop (.succ n)\n#check loop\nmutual\ndef isEven : Nat → Bool\n  | .zero => .true\n  | .succ n => isOdd n\ndef isOdd : Nat → Bool\n  | .zero => .false\n  | .succ n => isEven n\nend\n#check isOdd\npartial def bad (n : Nat) : Nat := Type\n"
          "Nat : U0\nBool : U0\nloop : (x0 : Nat) → Nat\n(x0 : Nat) → Nat\nisEven : (x0 : Nat) → Bool\nisOdd : (x0 : Nat) → Bool\n(x0 : Nat) → Bool\nerror: type mismatch: expected Nat, got U1\n" },
    { name := "indexed families, checked in Wiz", run := fun _ =>
        selfhostCheckFile "inductive Nat where\n  | zero\n  | succ (n : Nat)\ninductive Vec (A : Type) : Nat → Type where\n  | nil : Vec A Nat.zero\n  | cons (n : Nat) (a : A) (v : Vec A n) : Vec A (Nat.succ n)\n#check Vec.cons\ndef v2 : Vec Nat (.succ (.succ .zero)) := Vec.cons (.succ .zero) .zero (Vec.cons .zero (.succ .zero) Vec.nil)\n#reduce v2\ndef len {A : Type} {n : Nat} (v : Vec A n) : Nat := match v with\n  | .nil => Nat.zero\n  | .cons _ _ t => Nat.succ (len t)\n#reduce len v2\ndef head {A : Type} {n : Nat} (d : A) (v : Vec A n) : A := match v with\n  | .cons _ a _ => a\n  | _ => d\n#reduce head (.succ (.succ .zero)) v2\ndef bad : Vec Nat .zero := Vec.cons .zero .zero Vec.nil\n"
          "Nat : U0\nVec : (x0 : U0) → (x1 : Nat) → U0\n(x0 :0 U0) → (x1 : Nat) → (x2 : x0) → (x3 : ((Vec x0) x1)) → ((Vec x0) (Nat.succ x1))\nv2 : ((Vec Nat) (Nat.succ (Nat.succ Nat.zero)))\ncon((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (con((#0, (tt, tt))), (con((#1, (con((#0, (tt, tt))), (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (con((#0, (refl(Nat, Nat.zero), tt))), (refl(Nat, (Nat.succ con((#0, (tt, tt))))), tt)))))), (refl(Nat, (Nat.succ con((#1, (con((#0, (tt, tt))), (tt, tt)))))), tt))))))\nlen : (x0 :0 U0) → (x1 :0 Nat) → (x2 : ((Vec x0) x1)) → Nat\ncon((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt))))\nhead : (x0 :0 U0) → (x1 :0 Nat) → (x2 : x0) → (x3 : ((Vec x0) x1)) → x0\ncon((#0, (tt, tt)))\nerror: type mismatch: expected ((Vec Nat) Nat.zero), got ((Vec ?m0) (Nat.succ Nat.zero))\n" },
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
          "leaf : Syntax\nkindOf : (x0 : Syntax) → String\ncon((#1, (con((#1, (con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt)))), (tt, tt)))), (tt, tt))))\nargCount : (x0 :0 Bool) → (x1 : (SyntaxF x0)) → Nat\ncon((#1, (tt, tt)))\nCat : U0\nfind : (x0 : (List Cat)) → (x1 : String) → (Option Cat)\nm : (StrMap Nat)\n" },
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
          "con((#1, (tt, tt)))\ncon((#1, (tt, tt)))\nN.toNat : (x0 :0 Nat) → (x1 : (N x0)) → Nat\ncon((#1, (tt, tt)))\n" ++
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
    { name := "the self-hosted frontend: constructor field quantities (0, 1, ω) and implicit fields, as in the Lean frontend (21x)", run := fun _ =>
        selfhostAgrees fieldQtyHeader fieldQtyDecls },
    { name := "constructor field quantities and implicit fields: the Lean and the self-hosted compilers agree (21x)", run := fun _ => do
        ioRun (fieldQtyProgram.replace "import Prelude" "import IO") "4\n3\n9\n"
        selfhostCompileRun fieldQtyProgram "4\n3\n9\n"
        selfhostCompileRun fieldQtyProgram "4\n3\n9\n" (flags := #["--rc"]) },
    { name := "the self-hosted frontend: quantities, the pinned differences (21m, K1)", run := fun _ =>
        selfhostVerdicts quantityHeader quantityDiffs },
    { name := "a linear variable used once in each branch of a match: both frontends accept it (21v)", run := fun _ =>
        selfhostAgrees linearMatchHeader linearMatchDecls },
    { name := "the additive match (T.casesOnA) runs, compiled by the Lean compiler (21v)", run := fun _ =>
        ioRun linearMatchProgram "3\n5\n6\n" },
    { name := "the self-hosted frontend: Σ types, pairs, projections and ∀, as in the Lean frontend (21u)", run := fun _ =>
        selfhostAgrees "" sigmaDecls },
    { name := "the self-hosted backend: quantities erase and run, with either collector (21m)", run := fun _ => do
        selfhostCompileRun quantityProgram "6\n5\n9\n"
        selfhostCompileRun quantityProgram "6\n5\n9\n" (flags := #["--rc"]) },
    { name := "the self-hosted frontend: private declarations, constructors and fields, as in one Lean module (21n)", run := fun _ =>
        selfhostAgrees "" privateDecls },
    { name := "the self-hosted frontend: an unknown command is an error naming it (21n)", run := fun _ =>
        selfhostCheckFile "import Prelude\ndef f : Nat := 1\nattribute [macro f] f\nattribute [tactic f] f\ndef g : Nat := f\n"
          "f : Nat\nerror: unsupported command command.attrMacro\nerror: unsupported command command.attrTactic\ng : Nat\n" },
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
          "static inline unsigned long hdr_mul(unsigned long a, unsigned long b) { return a * b; }\n"
        let prog := "import IO\nimport_c \"h.h\" (pure)\n" ++
          "glue twice (n : Nat) : Nat := \"return hdr_add(n, n);\"\n" ++
          "glue square (n : Nat) : Nat := \"return hdr_mul(n, n);\"\n" ++
          "def main : IO Unit := do\n  IO.println (Nat.toString (C.hdr_add 20 22));\n" ++
          "  IO.println (Nat.toString (twice 21));\n  IO.println (Nat.toString (square 7))"
        selfhostLinkRun [("main.wiz", prog), ("h.h", header)] "42\n42\n49\n"
        selfhostLinkRun [("main.wiz", prog), ("h.h", header)] "42\n42\n49\n" (flags := #["--rc"]) },
    { name := "native representation: implemented_by mk/get on a sealed constructor (stage 30)", run := fun _ => do
        let prog := "import IO\n" ++
          "sealed inductive WA where\n  | private mk (xs : List Nat)\n" ++
          "def WA.mkImpl (xs : List Nat) : WA := .mk xs\n" ++
          "def WA.getImpl (a : WA) : List Nat := match a with\n  | .mk xs => xs\n" ++
          "attribute [implemented_by WA.mkImpl WA.getImpl] WA.mk\n" ++
          "def WA.ofList (xs : List Nat) : WA := .mk xs\n" ++
          "def WA.toList (a : WA) : List Nat := WA.getImpl a\n" ++
          "extern \"wa_id\" WA.ofListNative : List Nat → WA\n" ++
          "extern \"wa_id\" WA.toListNative : WA → List Nat\n" ++
          "attribute [implemented_by WA.ofListNative] WA.ofList\n" ++
          "attribute [implemented_by WA.toListNative] WA.toList\n" ++
          "def main : IO Unit := IO.println (Nat.toString (List.length (WA.toList (WA.ofList (List.cons 1 (List.cons 2 (List.cons 3 .nil)))))))"
        let csrc := "typedef unsigned long wiz_val;\nwiz_val wa_id(wiz_val x) { return x; }\n"
        selfhostLinkRun [("main.wiz", prog ++ "\nlink_c \"c/wa.c\"\n"), ("c/wa.c", csrc)] "3\n"
        selfhostLinkRun [("main.wiz", prog ++ "\nlink_c \"c/wa.c\"\n"), ("c/wa.c", csrc)] "3\n" (flags := #["--rc"]) },
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
    { name := "the self-hosted frontend: structure update, plain and nested, as in the Lean frontend (13i, 13p)", run := fun _ =>
        selfhostSameNats (updHeader ++ updProgram) updCases },
    { name := "the self-hosted frontend: structure update verdicts, as in the Lean frontend (13i, 13p)", run := fun _ =>
        selfhostAgrees updHeader updDecls },
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
        let some out ← selfhostOutputPeak ("import Prelude\n" ++ strip lex ++ "\n" ++ strip parseHead) 512
          | pure ()
        for l in out.splitOn "\n" do
          if l.startsWith "error" || l.startsWith "parse error" then throw (IO.userError l) },
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
        ioRun (kernel ++ "\n" ++ verdict ++ printAll ++ main) ("\n".intercalate expected ++ "\n") },
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
          "def sameVal (a b : Val) : Bool := tmEq (quoteM .false 0 a) (quoteM .false 0 b)\n" ++
          "def ab (sp : Spine) : Spine := .sabsurd sp (.venum 2)\n" ++
          "def main : IO Unit := do\n" ++
          "  IO.println (b2s (sameVal (.vne pf (.sfst .snil)) (.vne pf (.ssnd .snil))));\n" ++
          "  IO.println (b2s (sameVal (.vne pf (.sapp (ab .snil) (.vtag 2 0))) (.vne pf (.sapp (ab .snil) (.vtag 2 1)))));\n" ++
          "  IO.println (b2s (sameVal (.vne pf (.sapp (ab (.sfst .snil)) (.vtag 2 0))) (.vne pf (.sapp (ab (.ssnd .snil)) (.vtag 2 0)))));\n" ++
          "  IO.println (b2s (sameVal (.vne rf (.sfst .snil)) (.vne pf (.ssnd .snil))));\n" ++
          "  IO.println (b2s (sameVal (.vne rf (ab .snil)) (.vne pf (ab (.sfst .snil)))));\n" ++
          "  IO.println (b2s (conv empty (.venum 2) (.vne pf (ab .snil)) (.vne (.hrefl (.venum 2) (.vtag 2 0)) (ab .snil))));\n" ++
          "  IO.println (b2s (conv empty (.venum 2) (.vne pf (.sfst .snil)) (.vne (.hrefl (.venum 2) (.vtag 2 0)) (.sfst .snil))))\n"
        ioRun (kernel ++ "\n" ++ main) "true\nfalse\ntrue\ntrue\ntrue\ntrue\ntrue\n" },
    { name := "every constructor of Term is covered by the traversals (S1: a missed one proved False)", run := fun _ => do
        let samples := termSamples (.var 5) (.param "pw")
        -- a sample for every constructor
        let names := (samples.map (termCtor ·.1)).eraseDups
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
        ioRun (kernel ++ "\n" ++ main) "true\nfalse\nfalse\nfalse\ntrue\ntrue\n" },
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
        ioRun (kernel ++ "\n" ++ okV ++ printAll ++ s!"def main : IO Unit := printAll {wizList calls}\n")
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
        ioRun (kernel ++ "\n" ++ wizVerdict ++ okV ++ printAll ++ s!"def main : IO Unit := printAll {wizList calls}\n")
          ("\n".intercalate (samples.map fun (_, _, ok) => show' ok) ++ "\n")
        -- and with `kernelInertConv := .false` the value comparisons are still accepted by
        -- the prop gate; only the type controls (`ty`, `tv`) are rejected
        let on := "def kernelInertConv : Bool := .true"
        unless (kernel.splitOn on).length == 2 do throw (IO.userError "kernelInertConv not found")
        let groundK := kernel.replace on "def kernelInertConv : Bool := .false"
        ioRun (groundK ++ "\n" ++ wizVerdict ++ okV ++ printAll ++ s!"def main : IO Unit := printAll {wizList calls}\n")
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
        ioRun (kernel ++ "\n" ++ main) "internal error: a Π's domain without its sort (the sorts pass did not fill it)\nstuck\nstuck\nstuck\npair\nlam\n" },
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
        ioRun (kernel ++ "\n" ++ wizVerdict ++ printAll ++ s!"def main : IO Unit := printAll {wizList calls}\n") "True\nTrue\nTrue\n" },
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
        ioRun (kernel ++ "\n" ++ wizVerdict ++ main)
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
        ioRun (kernel ++ "\n" ++ main) (String.join (cases.map fun _ => "ok\nok\n") ++ "lam\n") },
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
        ioRun (kernel ++ "\n" ++ main) "error\nok\n" },
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
        ioRun (kernel ++ "\n" ++ main) "error\nok\ntag\nsuspended\n" },
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
        ioRun (kernel ++ "\n" ++ decl ++ printAll ++ main) ("\n".intercalate expected ++ "\n") },
    -- D1: regularity is off in both kernels; with it on, the Wiz kernel loops too
    -- (L-2) the kernel checks the value of a `let` at 0 as an erased position, so the
    -- backend must not compile it (the frontend doesn't produce `letq` today)
    { name := "Backend.wiz erases the value of a let at 0, and keeps it at 1 and ω", run := fun _ => do
        -- the backend test does not need the CLI driver (which expects the generated
        -- parser tables and toolchain constants): checker + Backend only
        let src ← (Selfhost.frontendFiles ++ ["selfhost/Backend.wiz"]).mapM (fun (f : String) => IO.FS.readFile f)
        let show1 (q : String) := s!"(match eraseCheck empty (.letq {q} (.enum 2) (.tag 2 0) (.tag 2 1)) (.venum 2) with\n    | .ok e => showE e\n    | .err m => String.append \"error: \" m)"
        let prog := "import IO\nimport Std\n" ++ "\n".intercalate (src.map Selfhost.strip) ++ "\n" ++
          s!"def main : IO Unit := do\n  IO.println {show1 ".qz"};\n  IO.println {show1 ".qo"};\n  IO.println {show1 ".qw"}\n"
        let kept := "(let " ++ "#0" ++ "; "
        ioRunWith prog fun out => do
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
        ioRun (kernel ++ "\n" ++ wizVerdict ++ s!"def main : IO Unit := IO.println (markedVerdict {control.toWiz})\n")
          (leanVerdict control ++ "\n")
        let loop := MTm.abelCoquand true
        -- without regularity (the default) both kernels check it
        let expected := leanVerdict loop
        unless expected != "error" do throw (IO.userError "the Lean kernel without regularity rejects it")
        ioRun (kernel ++ "\n" ++ wizVerdict ++ s!"def main : IO Unit := IO.println (markedVerdict {loop.toWiz})\n") (expected ++ "\n")
        -- unmarked, both kernels reject it: its `let`-bound proofs are λs (the marker is
        -- required, not a convention of the elaborator)
        checkEq "error" (leanVerdict loop (mark := false))
        ioRun (kernel ++ "\n" ++ wizVerdict ++ s!"def main : IO Unit := IO.println (rawVerdict {loop.toWiz})\n") "error\n"
        -- with regularity (`kernelRegularity`; `--regularity full` in the Lean kernel) the
        -- program used to loop in the Wiz kernel: `Omega := delta omega` was evaluated by
        -- the `let`. Marked, `delta` is a suspended proof, and `delta omega` only grows its
        -- spine: both kernels answer.
        let off := "def kernelRegularity : Bool := .false"
        unless (kernel.splitOn off).length == 2 do throw (IO.userError "kernelRegularity not found")
        let withReg := kernel.replace off "def kernelRegularity : Bool := .true"
        ioRun (withReg ++ "\n" ++ wizVerdict ++ s!"def main : IO Unit := IO.println (markedVerdict {loop.toWiz})\n") (expected ++ "\n")
        let g : Globals ZeroOneMany := { leanGlobals () with regularity := .full }
        match infer (R := ZeroOneMany) { globals := g } (Mark.infer (R := ZeroOneMany) { globals := g } loop.toTerm).1 with
        | .ok _ => pure ()
        | .error e => throw (IO.userError s!"the Lean kernel with full regularity rejects it: {e}") },
    -- (A14) modules: `import M` loads `M.wiz` (a `-I` root, then the working directory)
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
    { name := "modules: the cache key includes the module graph", run := fun _ => do
        let root := "import Prelude\nimport B\ndef two : Nat := one\n"
        let files1 := [("B.wiz", "import Prelude\ndef one : Nat := 1\n"), ("input.wiz", root)]
        let files2 := [("B.wiz", "import Prelude\ndef one : Nat := 2\n"), ("input.wiz", root)]
        let some k1 ← selfhostModuleOutput files1 #["--key"] | return
        let some k1' ← selfhostModuleOutput files1 #["--key"] | return
        let some k2 ← selfhostModuleOutput files2 #["--key"] | return
        unless k1 == k1' do throw (IO.userError s!"the key is not stable: {k1} / {k1'}")
        if k1 == k2 then throw (IO.userError s!"the key ignores a module's text: {k1}") },
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
          "transEq : (x0 :0 U0) → (x1 :0 x0) → (x2 :0 x0) → (x3 : Nat) → (x4 : Eq(x0, x1, x2)) → " ++
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
          checkEq ("bad.wiz:2:1: error: the data type's universe must be a declared universe parameter, not u (declare one: `inductive T.{u}`)\n") out.stderr }
  ]

builtin_initialize registerGroup selfHostGroup

end Tests.Elab
