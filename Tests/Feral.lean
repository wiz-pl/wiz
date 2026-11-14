import Wiz
import Tests.Harness
import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

/-!
# Feral: the surface language (lib/Feral.wiz), docs/stages/22-numbers.md, 22j

* every program of `drafts/feral/surface` lowers to Wiz that checks, and its `#eval`s give
  what its hand-lowered counterpart in `drafts/feral/lowered` gives;
* every program of `drafts/feral/rejected/surface` is rejected **both ways**: by the front
  end's region-carrying checker, at the Feral source line with the rustc error class its
  header names, and by the kernel on the lowering of the same program (`#unchecked
  feral`). A disagreement between the two verdicts is a failure.
-/

namespace Tests.Feral

/-- `lib/` plus the runtime stand-ins of `drafts/feral/lib`. -/
def loader : IO (Name → Option String) := do
  let lib ← Tests.Elab.libLoader
  let core ← IO.FS.readFile "drafts/feral/lib/FeralCore.wiz"
  pure fun n => if n == "FeralCore" then some core else lib n

def frontend (src : String) : IO (CommandState ZeroOneMany) := do
  pure (runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := ← loader })

def errorsOf (s : CommandState ZeroOneMany) (src : String) : List String :=
  (s.messages.filter (·.severity == .error)).toList.map (·.render src)

def infosOf (s : CommandState ZeroOneMany) : List String :=
  (s.messages.filter (·.severity == .info)).toList.map (·.text)

def has (s frag : String) : Bool := (s.splitOn frag).length > 1

/-- A surface program is accepted (the front end and then the kernel on what it lowers
to), and every `#eval` of it is one of the results of the hand-lowered program. -/
def accepted (name : String) : IO Unit := do
  let src ← IO.FS.readFile s!"drafts/feral/surface/{name}.wiz"
  let s ← frontend src
  let errs := errorsOf s src
  unless errs.isEmpty do throw (IO.userError s!"the surface program is not accepted:\n{"\n".intercalate errs}")
  let got := infosOf s
  check (!got.isEmpty) "the surface program evaluates nothing"
  let hand ← IO.FS.readFile s!"drafts/feral/lowered/{name}.wiz"
  let h ← frontend hand
  let herrs := errorsOf h hand
  unless herrs.isEmpty do throw (IO.userError s!"the hand-lowered program does not check:\n{"\n".intercalate herrs}")
  let want := infosOf h
  for g in got do
    unless want.contains g do
      throw (IO.userError s!"the surface program gives {g}, which the hand-lowered one does not ({want})")

/-- The `-- expect: FRAGMENT at LINE` line of a rejected program. -/
def expectation (src : String) : IO (String × Nat) := do
  let some l := (src.splitOn "\n").find? (has · "-- expect: ") | throw (IO.userError "no `-- expect:` line")
  match ((l.splitOn "-- expect: ")[1]!).splitOn " at " with
  | [frag, line] => pure (frag, line.trimAscii.toString.toNat!)
  | _ => throw (IO.userError s!"malformed expectation: {l}")

/-- A rejected program, both ways. -/
def rejected (name : String) : IO Unit := do
  let src ← IO.FS.readFile s!"drafts/feral/rejected/surface/{name}.wiz"
  let (frag, line) ← expectation src
  -- the front end's verdict, at the Feral source
  let s ← frontend src
  let errs := errorsOf s src
  check (!errs.isEmpty) "the front end accepts a program that must be rejected"
  check (errs.all (!has · "generated source")) s!"the front end missed it (the kernel rejected the lowering):\n{errs}"
  let first := errs.head!
  check (has first frag) s!"the error does not name `{frag}`:\n{first}"
  check (first.startsWith s!"{line}:") s!"the error is not at line {line}:\n{first}"
  -- the kernel's verdict, on the lowering of the same program
  let un := src.replace "\nferal\n" "\n#unchecked feral\n"
  check (un != src) "no `feral` block to lower unchecked"
  let u ← frontend un
  let uerrs := errorsOf u un
  check ((infosOf u).any (has · frag)) s!"#unchecked does not report the front end's verdict ({frag}): {infosOf u}"
  check (uerrs.any (has · "the generated source was rejected"))
    s!"the two verdicts differ: the front end rejects the program, the kernel accepts its lowering ({uerrs})"
  -- and the hand-written lowering of drafts/feral/rejected is still rejected
  let hand ← IO.FS.readFile s!"drafts/feral/rejected/{name}.wiz"
  let h ← frontend hand
  check (!(errorsOf h hand).isEmpty) "the hand-lowered program is accepted"

def firstError (src : String) : IO String := do
  let s ← frontend src
  match errorsOf s src with
  | e :: _ => pure e
  | [] => throw (IO.userError "accepted, but an error was expected")

def pre : String := "import FeralCore\nimport Feral\n"

/-- Elaborate as the language server does (recording what hovers read). -/
def frontendInfo (src : String) : IO (CommandState ZeroOneMany) := do
  pure (runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := ← loader, termInfo := true })

/-- The character offset of the `k`th occurrence of `needle` in `src`, plus `delta`. -/
def offOf (src needle : String) (delta : Nat := 0) (k : Nat := 0) : Nat :=
  ((src.splitOn needle).take (k + 1)).foldl (· + ·.length) 0 + needle.length * k + delta

/-- The text of `src` in a range. -/
def textAt (src : String) (i : SourceInfo) : String :=
  String.ofList ((src.toList.drop i.start).take (i.stop - i.start))

/-- What a hover at `off` shows: the type, and the source text it is about. -/
def hoverText (s : CommandState ZeroOneMany) (src : String) (off : Nat) : String :=
  match Query.identAt s off with
  | some (.ident i _ _ names ty) => s!"{textAt src i} : {ty.pretty names (some s.globals)}"
  | _ => "none"

/-- Every identifier the info tree has inside the `feral` block (for failure messages). -/
def identsIn (s : CommandState ZeroOneMany) (src : String) : String :=
  let from_ := offOf src "\nferal\n"
  "\n".intercalate (s.infos.toList.filterMap fun
    | .ident i n _ names ty => if i.start ≥ from_ && i.start < offOf src "\nend\n" then
        some s!"{i.start}-{i.stop} `{textAt src i}` {n} : {ty.pretty names (some s.globals)}" else none
    | _ => none)

/-- A program for the position tests (hovers, go to definition). -/
def posSrc : String := pre ++ "feral\n  fn double (n : U64) : U64 := n + n\n" ++
  "  fn bump {'a} (y : &'a mut U64) : Unit := { *y := *y + 1 }\n" ++
  "  fn f (x : U64) : U64 := {\n    let mut v := Vec.new;\n    let r := &mut v;\n    r.push x;\n" ++
  "    let mut a := x;\n    bump (&mut a);\n    double (v.len) + a\n  }\nend\n" ++
  "#eval Result.map U64.toNat (f (U64.lit 3))\n"

def surfaceNames : List String :=
  ["01_swap", "02_push", "03_get_mut", "04_reverse", "05_bst", "06_count", "07_disjoint", "08_first_mut",
   "09_bsearch", "10_regions", "11_list", "12_pick"]

def rejectedNames : List String :=
  ["E0499_two_mut", "E0502_use_while_mut", "E0515_return_local", "E0515_return_mut", "E0597_not_long_enough",
   "E0597_store_short", "lifetime_bound_missing", "lifetime_bound_missing_mut", "outlives_wrong_way"]

def group : Group where
  name := "feral"
  parallel := true
  exercise := "lib/Feral.wiz (the Feral surface language)"
  cases :=
    surfaceNames.map (fun n => { name := s!"surface/{n} lowers, checks, and behaves like lowered/{n}", run := fun _ => accepted n }) ++
    rejectedNames.map (fun n => { name := s!"rejected/{n}: rejected by the front end and by the kernel", run := fun _ => rejected n }) ++ [
    { name := "every program of drafts/feral/surface and rejected/surface is tested", run := fun _ => do
        let listed (dir : String) : IO (List String) := do
          let es ← System.FilePath.readDir dir
          pure ((es.toList.filter (·.path.extension == some "wiz")).map (·.path.fileStem.getD "")).mergeSort
        checkEq (toString surfaceNames.mergeSort) (toString (← listed "drafts/feral/surface"))
        checkEq (toString rejectedNames.mergeSort) (toString (← listed "drafts/feral/rejected/surface")) },
    { name := "hand-written Wiz against lib/Region.wiz: a forged handle and a lengthened borrow are rejected", run := fun _ => do
        for n in ["forge_handle", "lengthen_borrow"] do
          let src ← IO.FS.readFile s!"drafts/feral/rejected/{n}.wiz"
          check (!(errorsOf (← frontend src) src).isEmpty) s!"{n} is accepted" },
    { name := "linear mode (M4b-1): a join and an error path hand the handle back", run := fun _ => do
        let src := pre ++ "feral\n  fn bump {'a} (x : &'a mut U64) (c : Bool) : Unit := {\n    if c then { *x := *x + 1 } else { () };\n    *x := *x + 1\n  }\n  fn twice (n : U64) : U64 := {\n    let mut v := n;\n    bump (&mut v) (U64.lt n 5);\n    v\n  }\nend\n#eval Result.map (fun (u : U64) => u.val) (twice (U64.lit 3))\n#eval Result.map (fun (u : U64) => u.val) (twice (U64.lit 7))\n"
        let s ← frontend src
        checkEq "[]" (toString (errorsOf s src))
        checkEq "[.ok 5, .ok 8]" (toString (infosOf s))
        let l ← frontend (src.replace "\nferal\n" "\n#lower feral\n")
        check ((infosOf l).any (has · "Result1 Unit (Uniq ρa U64)")) s!"{infosOf l}" },
    { name := "linear mode (M4b-3c): returned borrows (Mut, Borrowed), an error exit releases live borrows, field borrows by Uniq.zoom", run := fun _ => do
        -- a returned borrow is a `Mut` in `Borrowed.ok`; `Borrowed.err` hands the lender back
        let w ← frontend (pre ++ "#lower feral\n  fn f {'a} (v : &'a mut Vec U64) (i : USize) : &'a mut U64 := &mut v[i]\nend\n")
        check ((infosOf w).any (has · "Borrowed (Mut ρa U64 (Vec U64)) (Uniq ρa (Vec U64))")) s!"{infosOf w}"
        -- two lenders; an overflow while the borrow lives: the error path releases it first
        let a := pre ++ "feral\n  fn pick {'a 'b} {'a : 'b} (c : Bool) (x : &'a mut U64) (y : &'b mut U64) : &'b mut U64 :=\n    if c then x else y\n" ++
          "  fn go (n : U64) : U64 × U64 := {\n    let mut a : U64 := n;\n    let mut b : U64 := 2;\n    *pick true (&mut a) (&mut b) += 10;\n    (a, b)\n  }\nend\n" ++
          "#eval Result.map (fun (r : U64 × U64) => (r.1.val, r.2.val)) (go (U64.lit 1))\n" ++
          "#eval Result.map (fun (r : U64 × U64) => (r.1.val, r.2.val)) (go (U64.lit 18446744073709551610))\n"
        let s ← frontend a
        checkEq "[]" (toString (errorsOf s a))
        checkEq "[.ok (11, 2), .err .overflow]" (toString (infosOf s))
        let l ← frontend (a.replace "\nferal\n" "\n#lower feral\n")
        check ((infosOf l).any (has · "Mut.alongside")) s!"{infosOf l}"
        -- (the borrow is finished twice: where it ends, and on the overflow's error path)
        check ((infosOf l).any (fun i => (i.splitOn "let 1 (a_r0, b_r2) := Mut.finish v_9;").length == 3)) s!"{infosOf l}"
        -- `f (&mut s.f)`: a zoom on a handle, on a borrowed local, and beside another handle (zoomIn)
        let z := pre ++ "feral\n  struct P where\n    a : U64\n    b : U64\n  fn bump2 (x : &mut U64) (y : &mut U64) : Unit := { *x += 1; *y += 2 }\n" ++
          "  fn g (p : &mut P) (q : &mut U64) : Unit := { bump2 (&mut p.a) q; *q += 1 }\n" ++
          "  fn go (p0 : P) : U64 := {\n    let mut p := p0;\n    let mut q : U64 := 5;\n    bump2 (&mut p.b) (&mut q);\n    g (&mut p) (&mut q);\n    p.a + p.b + q\n  }\nend\n" ++
          "#eval Result.map U64.toNat (go (P.mk (U64.lit 1) (U64.lit 2)))\n"
        let t ← frontend z
        checkEq "[]" (toString (errorsOf t z))
        checkEq "[.ok 15]" (toString (infosOf t))
        let lz ← frontend (z.replace "\nferal\n" "\n#lower feral\n")
        check ((infosOf lz).any (has · "@Uniq.zoomIn")) s!"{infosOf lz}"
        check ((infosOf lz).any (has · "@Uniq.zoom ")) s!"{infosOf lz}"
        -- two fields of one struct in one call: not yet (the `let` form, L11, does it)
        let e ← firstError (z.replace "bump2 (&mut p.a) q" "bump2 (&mut p.a) (&mut p.b)")
        check (has e "not supported yet: two fields of `p`") e },
    { name := "linear mode (M4b-2): for and while loops take and hand back their handles; a method on a &mut (push)", run := fun _ => do
        let a := pre ++ "feral\n  fn bump_n {'a} (x : &'a mut U64) (n : U64) : Unit := {\n    for i in 0 .. n do {\n      *x := *x + 1\n    }\n  }\n  fn halve {'a} (x : &'a mut U64) : Unit := {\n    while 1 < *x do {\n      *x := *x - 1\n    }\n  }\n  fn go (n : U64) : U64 × U64 := {\n    let mut a := 0;\n    let mut b := 9;\n    bump_n (&mut a) n;\n    halve (&mut b);\n    (a, b)\n  }\nend\n#eval Result.map (fun (p : U64 × U64) => (p.1.val, p.2.val)) (go (U64.lit 4))\n"
        let s ← frontend a
        checkEq "[]" (toString (errorsOf s a))
        checkEq "[.ok (4, 1)]" (toString (infosOf s))
        let b := pre ++ "feral\n  fn fill {'a} (v : &'a mut Vec U64) (n : U64) : Unit := {\n    for i in 0 .. n do {\n      v.push i\n    }\n  }\n  fn make (n : U64) : Vec U64 := {\n    let mut v := Vec.new;\n    fill (&mut v) n;\n    v\n  }\nend\n#eval Result.map (fun (v : Vec U64) => List.length v.items) (make (U64.lit 5))\n"
        let t ← frontend b
        checkEq "[]" (toString (errorsOf t b))
        checkEq "[.ok 5]" (toString (infosOf t))
        let l ← frontend (b.replace "\nferal\n" "\n#lower feral\n")
        check ((infosOf l).any (has · "Vec.push v i")) s!"{infosOf l}" },
    { name := "linear mode (M4b-3a): `return` from inside a loop and a join hands the handles back", run := fun _ => do
        let a := pre ++ "feral\n  -- add 1 up to n times, stopping early at 10\n  fn bump_to {'a} (x : &'a mut U64) (n : U64) : Bool := {\n    for i in 0 .. n do {\n      if 9 < *x then { return true } else { () };\n      *x := *x + 1\n    };\n    false\n  }\n  fn go (n : U64) : U64 × Bool := {\n    let mut a := 5;\n    let hit := bump_to (&mut a) n;\n    (a, hit)\n  }\nend\n#eval Result.map (fun (p : U64 × Bool) => (p.1.val, p.2)) (go (U64.lit 3))\n#eval Result.map (fun (p : U64 × Bool) => (p.1.val, p.2)) (go (U64.lit 20))\n"
        let s ← frontend a
        checkEq "[]" (toString (errorsOf s a))
        checkEq "[.ok (8, .false), .ok (10, .true)]" (toString (infosOf s))
        let l ← frontend (a.replace "\nferal\n" "\n#lower feral\n")
        check ((infosOf l).any (has · "Result1 ((Flow Unit) Bool) (Uniq ρa U64)")) s!"{infosOf l}" },
    { name := "linear mode (M4b-3b): shared borrows and indexing beside live handles (Shr.borrowIn, Uniq.shareIn)", run := fun _ => do
        let a := pre ++ "feral\n  fn total {'a} (v : &'a Vec U64) : U64 := {\n    let mut s := 0;\n    for i in 0 .. v.len do {\n      s := s + v[i]\n    };\n    s\n  }\n  -- push the sum of a shared vector onto a mutable one, and read it back by index\n  fn push_total {'a 'b} (dst : &'a mut Vec U64) (src : &'b Vec U64) : U64 := {\n    let t := total src;\n    dst.push t;\n    dst[0]\n  }\n  fn go () : U64 := {\n    let mut d := Vec.new;\n    let mut s := Vec.new;\n    s.push 3;\n    s.push 4;\n    let r := push_total (&mut d) (&s);\n    r\n  }\nend\n#eval Result.map (fun (u : U64) => u.val) go\n"
        let s ← frontend a
        checkEq "[]" (toString (errorsOf s a))
        checkEq "[.ok 7]" (toString (infosOf s))
        let b := pre ++ "feral\n  fn copy_len {'a 'b} (a : &'a mut Vec U64) (b : &'b mut Vec U64) : Unit := {\n    b.push a.len;\n    a.push b.len\n  }\n  fn go () : U64 × U64 := {\n    let mut x := Vec.new;\n    let mut y := Vec.new;\n    x.push 9;\n    copy_len (&mut x) (&mut y);\n    (x.len, y.len)\n  }\nend\n#eval Result.map (fun (p : U64 × U64) => (p.1.val, p.2.val)) go\n"
        let t ← frontend b
        checkEq "[]" (toString (errorsOf t b))
        checkEq "[.ok (2, 1)]" (toString (infosOf t))
        let l ← frontend (b.replace "\nferal\n" "\n#lower feral\n")
        check ((infosOf l).any (has · "@Uniq.shareIn")) s!"{infosOf l}" },
    { name := "examples/resources.wiz: Feral's swap on heap cells, verified with the x-tactics through lib/HeapBorrow.wiz", run := fun _ => do
        let src ← IO.FS.readFile "examples/resources.wiz"
        let s ← frontend src
        checkEq "[]" (toString (errorsOf s src))
        checkEq ("[.ok (2, 1), .some ((), .cons .none (.cons (.some (20, ())) (.cons (.some (10, ())) " ++
          "(.cons (.some (30, ())) .nil))))]") (toString (infosOf s))
        -- the heap specification of the identity is not one of swap's
        let bad := src ++ "\ndef bad (p q : Nat) (a b : U64) :\n" ++
          "    Triple ((p ↦ a) ⋆ (q ↦ b)) (swapCells p q) (fun _ => (p ↦ a) ⋆ (q ↦ b)) := by\n" ++
          "  xgo\n"
        let e ← firstError bad
        check (((e.splitOn ":")[0]!).toNat! > 69) s!"the error is not in the added definition: {e}" },
    { name := "spec items: a function's specification as a Wiz proposition (result, old, final)", run := fun _ => do
        let fn := "  fn swap {'a 'b} (x : &'a mut U64) (y : &'b mut U64) : Unit := {\n    let t := *x;\n    *x := *y;\n    *y := t\n  }\n"
        let s ← frontend (pre ++ "#lower feral\n" ++ fn ++ "  spec swap ensures (final x = old y) ensures (final y = old x)\nend\n")
        check ((infosOf s).any (has · ("def swap.Spec (x : U64) (y : U64) : Prop :=\n" ++
          "  Result.Holds (fun (r : ((Unit × U64) × U64)) => (r.2 = y) × (r.1.2 = x)) (\n" ++
          "    Uniq.borrow Region.static x (fun ρ1 h1 l1 x =>\n" ++
          "      Uniq.borrowIn ρ1 y x (fun ρ2 h2 l2 x y =>  swap x y)))")))
          s!"{infosOf s}"
        -- a true specification is proved, a false one is not (linear handles: the spec is
        -- stated on the arguments' values)
        let ok := pre ++ "feral\n" ++ fn ++ "  spec swap ensures (final x = old y) ensures (final y = old x)\nend\n" ++
          "def swap_ok (a b : U64) : swap.Spec a b := (rfl, rfl)\n"
        checkEq "[]" (toString (errorsOf (← frontend ok) ok))
        let e ← firstError (pre ++ "feral\n" ++ fn ++ "  spec swap ensures (final x = old x)\nend\n" ++
          "def swap_bad (a b : U64) : swap.Spec a b := (rfl, rfl)\n")
        check (has e "rfl") e
        -- requires, result
        let r := pre ++ "feral\n  fn add1 (a : U64) : U64 := a + 1\n  spec add1 requires (Nat.lt a.val 10 = .true) ensures (result.val = Nat.succ a.val)\nend\n" ++
          "#check @add1.Spec\n"
        let rs ← frontend r
        checkEq "[]" (toString (errorsOf rs r))
        let e ← firstError (pre ++ "feral\n  spec nope ensures (True)\nend\n")
        check (has e "no function `nope`") e },
    { name := "#lower shows the generated Wiz, item by item", run := fun _ => do
        let src := pre ++ "#lower feral\n  fn swap {'a 'b} (x : &'a mut U64) (y : &'b mut U64) : Unit := {\n" ++
          "    let t := *x;\n    *x := *y;\n    *y := t\n  }\nend\n"
        let s ← frontend src
        checkEq "[]" (toString (errorsOf s src))
        checkEq ("[def swap {ρa ρb : Region} (1 x : (Uniq ρa U64)) (1 y : (Uniq ρb U64)) : Result1 Unit ((1 _ : (Uniq ρa U64)) × (Uniq ρb U64)) :=\n" ++
          "  let 1 (d_2, x) := Uniq.peek x;\n  let t := d_2;\n  let 1 (d_5, y) := Uniq.peek y;\n  let 1 x := Uniq.write x d_5;\n" ++
          "  let 1 y := Uniq.write y t;\n  Result1.ok (()) (x, y)\n]") (toString (infosOf s)) },
    { name := "errors point into the block: the line and column of the offending expression", run := fun _ => do
        let e ← firstError (pre ++ "feral\n  fn f (x : U64) : U64 := {\n    let y := x;\n    y := 3;\n    y\n  }\nend\n")
        check (e.startsWith "6:5: " && has e "E0384") e
        let e ← firstError (pre ++ "feral\n  fn f (x : U64) : Bool :=\n    x + 1\nend\n")
        check (e.startsWith "5:5: " && has e "type mismatch: expected Bool, found U64") e
        let e ← firstError (pre ++ "feral\n  fn f (x : U64) : U64 := g x\nend\n")
        check (has e "unknown identifier `g`") e },
    { name := "the lender is unusable while a named borrow of it lives (E0499, E0502, E0506)", run := fun _ => do
        let body (stmts : String) := pre ++ "feral\n  fn f () : U64 := {\n    let mut v := Vec.new;\n    let r := &mut v;\n" ++ stmts ++ "    r.push 2;\n    0\n  }\nend\n"
        let e ← firstError (body "    v.push 1;\n")
        check (e.startsWith "7:" && has e "E0499") e
        let e ← firstError (body "    let n := v.len;\n")
        check (e.startsWith "7:" && has e "E0502") e
        let e ← firstError (body "    v := Vec.new;\n")
        check (e.startsWith "7:" && has e "E0506") e
        -- and after the borrow's last use the lender is back
        let ok := pre ++ "feral\n  fn f () : U64 := {\n    let mut v := Vec.new;\n    let r := &mut v;\n    r.push 2;\n    v.push 1;\n    v.len\n  }\nend\n" ++
          "#eval Result.map U64.toNat f\n"
        let s ← frontend ok
        checkEq "[]" (toString (errorsOf s ok))
        checkEq "[.ok 2]" (toString (infosOf s)) },
    { name := "a shared borrow: the lender can be read, not mutated, while it lives (E0502)", run := fun _ => do
        let body (stmts : String) := pre ++ "feral\n  fn f () : U64 := {\n    let mut a : U64 := 1;\n    let r := &a;\n" ++ stmts ++ "    *r + a\n  }\nend\n"
        let ok := body "" ++ "#eval Result.map U64.toNat f\n"
        let s ← frontend ok
        checkEq "[]" (toString (errorsOf s ok))
        checkEq "[.ok 2]" (toString (infosOf s))
        let e ← firstError (body "    let w := &mut a;\n")
        check (e.startsWith "7:" && has e "E0502") e },
    { name := "one local mutably borrowed twice in a call is rejected by the front end and, with linear handles, by the kernel", run := fun _ => do
        -- The front end reports E0499. Lowered anyway (#unchecked), the program passes one
        -- handle twice. This used to be a KNOWN GAP (handles were ω values); in linear mode
        -- (cohesion M4b-1, `Uniq` on linear-case stage 2) the kernel rejects it too.
        let src := pre ++ "feral\n  fn swap {'a 'b} (x : &'a mut U64) (y : &'b mut U64) : Unit := {\n    let t := *x;\n    *x := *y;\n    *y := t\n  }\n" ++
          "  fn bad () : U64 := {\n    let mut a : U64 := 1;\n    swap (&mut a) (&mut a);\n    a\n  }\nend\n"
        let e ← firstError src
        check (e.startsWith "11:" && has e "E0499") e
        let un := src.replace "\nferal\n" "\n#unchecked feral\n"
        let u ← frontend un
        check ((infosOf u).any (has · "E0499")) "no verdict from the front end"
        check ((errorsOf u un).any (has · "the generated source was rejected")) s!"the kernel accepts the lowering: {errorsOf u un}" },
    { name := "positions inside a block: hovers on variables, calls, borrows and binders", run := fun _ => do
        let s ← frontendInfo posSrc
        checkEq "[]" (toString (errorsOf s posSrc))
        checkEq "[.ok 6]" (toString (infosOf s))
        let at_ (needle : String) (delta : Nat := 0) (k : Nat := 0) := hoverText s posSrc (offOf posSrc needle delta k)
        let checkEq (want got : String) : IO Unit := check (want == got) s!"expected {want}\n      got {got}\n{identsIn s posSrc}"
        let starts (want got : String) : IO Unit := check (got.startsWith want) s!"expected {want}…\n      got {got}\n{identsIn s posSrc}"
        -- a variable (the second `n` of `n + n`), parameters, a `let`
        checkEq "n : U64" (at_ "n + n" 4)
        checkEq "n : U64" (at_ "(n : U64)" 1)
        checkEq "x : U64" (at_ "push x" 5)
        checkEq "a : U64" (at_ "let mut a" 8)
        starts "y : Uniq ρa U64" (at_ "(y :" 1)
        -- a call, the function it names, an operator, a method call
        checkEq "double : U64 → Result U64" (at_ "double (v.len)" 1)
        checkEq "double (v.len) : U64" (at_ "double (v.len)" 7)
        checkEq "+ : U64 → U64 → Result U64" (at_ "n + n" 2)
        checkEq "double (v.len) + a : U64" (at_ ") + a" 1)
        -- a `&mut` argument (its handle) and a named borrow (this block is linear now:
        -- its `&mut`s, a `push` and `len` are inside the linear fragment)
        starts "(&mut a) : Uniq ρ" (at_ "&mut a" 1)
        starts "r : Uniq ρ" (at_ "let r" 4)
        -- (a method call on a variable is one identifier: the receiver's handle shows)
        starts "r.push : Uniq ρ" (at_ "r.push" 0) },
    { name := "positions inside a block: go to definition, errors at the sub-expression", run := fun _ => do
        let s ← frontendInfo posSrc
        -- `double` in `f` goes to `fn double`, not to the whole block
        match Query.definitionAt s (offOf posSrc "double (v.len)" 1) with
        | some (n, i, m) =>
          checkEq "double" (toString n)
          checkEq "" m
          check ((textAt posSrc i).startsWith "fn double (n : U64)") s!"jumps to {textAt posSrc i}"
          check (!(textAt posSrc i).contains "fn f") s!"jumps to {textAt posSrc i}"
        | none => throw (IO.userError "no definition for `double`")
        -- the kernel's verdict on an unchecked lowering is at the expression it is about
        -- (E0499_two_mut: `r2.push 2` gets the handle of a borrow of the token, line 13)
        let src ← IO.FS.readFile "drafts/feral/rejected/surface/E0499_two_mut.wiz"
        let un := src.replace "\nferal\n" "\n#unchecked feral\n"
        let errs := errorsOf (← frontend un) un
        check (errs.any fun e => !has e "generated source" && e.startsWith "13:5: ") (toString errs) },
    { name := "command macros: errors, info and generated source at a node of the input (Syntax.errorAt …)", run := fun _ => do
        let src := "import Prelude\nsyntax (name := three) \"three!\" ident ident ident : command\n" ++
          "def threeMacro : CommandMacro := fun stx => MacroM.pure (.cons (Syntax.errorAt (.cons 2 .nil) \"second\")\n" ++
          "  (.cons (Syntax.infoAt (.cons 3 .nil) \"third\") (.cons (Syntax.sourceAt (.cons 1 .nil) \"def one : Nat := 1\\ndef uno : Nat := one\") .nil)))\n" ++
          "attribute [macro command.three] threeMacro\nthree! a\n  b\n  c\n#eval uno\n"
        let s ← frontend src
        checkEq "[7:3: error: second, 8:3: info: third, 9:1: info: 1]" (toString (s.messages.toList.map (·.render src)))
        -- generated source that does not check is reported at the node, with the text
        let bad := src.replace "def one : Nat := 1" "def one : Nat := zzz"
        let b ← frontend bad
        check ((errorsOf b bad).any (fun e => e.startsWith "6:8: " && has e "the generated source was rejected")) (toString (errorsOf b bad)) }
  ]

def groups : List Group :=
  group ::
  []

end Tests.Feral
