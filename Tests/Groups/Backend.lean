import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

def backendGroup : Group where
  name := "backend"
  exercise := "Exercise 8.1"
  cases := [
    { name := "numbers through the IR", run := fun _ =>
        okLib "import Prelude\n#run 100 * 100 + 1" ["10001"] },
    { name := "recursion, without leaks", run := fun _ =>
        okLib "import Prelude\ndef fact : Nat → Nat\n  | .zero => 1\n  | .succ n => (.succ n) * fact n\n#run fact 10" ["3628800"] },
    { name := "lists and strings", run := fun _ =>
        okLib "import Prelude\n#run List.append (.cons (1 : Nat) .nil) (.cons 2 .nil)\n#run String.append \"ab\" \"cd\""
          [".cons 1 (.cons 2 .nil)", "\"abcd\""] },
    { name := "closures capture their variables", run := fun _ =>
        okLib "import Prelude\ndef adder (n : Nat) : Nat → Nat := fun x => x + n\ndef twice (f : Nat → Nat) (x : Nat) : Nat := f (f x)\n#run twice (adder 10) 1"
          ["21"] },
    { name := "codata is lazy", run := fun _ =>
        okLib (streamPrelude ++ "#run (nats .zero).tail.tail.head") [".succ (.succ .zero)"] },
    { name := "codata built by cocon (register) and coit (mealy)", run := fun _ =>
        okLib (streamPrelude ++ registerSrc ++ "#run (register Nat.zero (mealy (fun (n : Nat) (x : Nat) => (.succ n, n)) .zero (nats .zero))).tail.tail.head")
          [".succ .zero"] },
    { name := "sized recursion", run := fun _ =>
        okLib (runPrelude ++ "#run fib (.succ (.succ (.succ (.succ (.succ .zero)))))")
          [".succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))"] },
    { name := "memoised codata, without leaks (also dropped part-way)", run := fun _ =>
        okLib (memoStreamSrc ++ "#run main") ["14946"] },
    { name := "infinitary data", run := fun _ =>
        okLib (treePrelude ++ "#run Tree.depthAt (.node (fun i => .node (fun j => .leaf))) 3") ["3"] },
    { name := "type class dictionaries", run := fun _ =>
        okLib (classPrelude ++ "#run (Inhabited.default : List (List Nat))") [".cons (.cons 0 .nil) .nil"] },
    { name := "the IR, with reference counting (Exercise 8.1)", run := fun _ =>
        okLib "import Prelude\ndef twice (f : Nat → Nat) (x : Nat) : Nat := f (f x)\n#ir twice"
          ["def twice x0 x1 :=\n  dup x0\n  let x2 := ap x0 x1\n  let x3 := ap x0 x2\n  ret x3"] },
    { name := "reuse: a dead cell is reused for a new one (Exercise 8.3)", run := fun _ => do
        let prelude ← IO.FS.readFile "lib/Prelude.wiz"
        let src := "import Prelude\ndef inc : List Nat → List Nat\n  | .nil => .nil\n  | .cons x xs => .cons (x + 1) (inc xs)\n#ir inc\n#run inc (.cons 1 (.cons 2 .nil))"
        let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := fun _ => some prelude }
        let texts := s.messages.toList.map (·.text)
        check (texts.any fun t => (t.splitOn "reuse").length > 1) s!"no reuse in {texts}"
        check (texts.contains ".cons 2 (.cons 3 .nil)") s!"wrong result: {texts}" },
    { name := "unused parameters are borrowed (the caller drops them)", run := fun _ =>
        okLib "import Prelude\ndef k (x y : List Nat) : List Nat := x\n#ir k"
          ["def k x0 @&x1 :=\n  ret x0"] },
    { name := "constant folding and known constructors in the IR (15c)", run := fun _ => do
        let s := runFrontend (R := ZeroOneMany) (foldSrc ++ "#ir known\n#ir isTen\n#ir again\n#run main\n") { loader := ← preludeLoader }
        match (s.messages.toList.filter (·.severity == .info)).map (·.text) with
        | [known, isTen, again, run] =>
          -- a match on a constructor built in place: its field, plus one
          check ((known.splitOn "case").length == 1 && (known.splitOn ":= 6\n").length == 2) known
          -- in the `true` branch `n` is `10`, so `n + 1` is `11`
          check ((isTen.splitOn ":= 11\n").length == 2 && (isTen.splitOn "nat.add").length == 1) isTen
          -- the second match on the same list is gone
          checkEq 2 (again.splitOn "case").length
          checkEq foldExpected run
        | ms => throw (IO.userError s!"unexpected messages {ms}") },
    { name := "a self tail call is a jump to a join point (15f)", run := fun _ => do
        let src := "import Prelude\npartial def count (n acc : Nat) : Nat := match n with\n  | .zero => acc\n" ++
          "  | .succ m => count m (acc + 1)\n#ir count\n#run count 100000 0\n"
        let s := runFrontend (R := ZeroOneMany) src { loader := ← preludeLoader }
        match (s.messages.toList.filter (·.severity == .info)).map (·.text) with
        | [ir, run] =>
          check ((ir.splitOn "join").length > 1 && (ir.splitOn "jmp").length > 2) ir
          checkEq "100000" run
        | ms => throw (IO.userError s!"unexpected messages {ms}") },
    { name := "numerals at 2^31 … 2^64+1 and 10^30, interpreted and through the IR (15g)", run := fun _ =>
        okLib (bigLitSrc ++ "#eval main\n#run main\n") [bigLitExpected, bigLitExpected] },
    { name := "Bool.and/Bool.or calls are cases: the search is a loop that stops (15h)", run := fun _ => do
        let s := runFrontend (R := ZeroOneMany) (caseShapeSrc ++ "#ir mem\n#ir allLt\n#ir pick\n#run rest\n") { loader := ← preludeLoader }
        let errs := (s.messages.filter (·.severity == .error)).map (·.text)
        unless errs.isEmpty do throw (IO.userError s!"unexpected errors: {errs}")
        match (s.messages.toList.filter (·.severity == .info)).map (·.text) with
        | [mem, allLt, pick, run] =>
          for ir in [mem, allLt] do
            -- no call of `Bool.or`/`Bool.and`: a case on the test, and the recursion a jump
            check ((ir.splitOn "Bool.or x").length == 1 && (ir.splitOn "Bool.and x").length == 1) ir
            check ((ir.splitOn "case").length == 3 && (ir.splitOn "jmp").length == 3) ir
          -- the default is computed in the `none` branch only
          check ((pick.splitOn "orElse").length == 1) pick
          match pick.splitOn "case" with
          | [before, after] => check ((before.splitOn "range").length == 1 && (after.splitOn "range").length == 2) pick
          | _ => throw (IO.userError pick)
          -- (`#run` is the IR's interpreter: the arguments that never return are not computed)
          checkEq caseShapeRest run
        | ms => throw (IO.userError s!"unexpected messages {ms}") },
    { name := "allocations of a short-circuiting search, before and after (15h)", run := fun _ => do
        let s := runFrontend (R := ZeroOneMany) caseShapeSrc { loader := ← preludeLoader }
        let allocs (n : Name) (caseShapes : Bool) : IO Nat := match (do
            let code ← (compileReachable s.globals s.builtins [n] (caseShapes := caseShapes)).mapError toString
            let decls ← IR.lowerProgram code (.global n)
            let (_, a) ← IR.runProgram (IR.optimizeProgram decls)
            pure a : Except String Nat) with
          | .ok a => pure a
          | .error e => throw (IO.userError s!"{n}: {e}")
        -- a search in a list that exists already: the same cells (but a loop, and it stops)
        checkEq [1000, 1000] [← allocs "s1" false, ← allocs "s1" true]
        -- the next level of the search is built only when the test failed
        checkEq [101, 4] [← allocs "s2" false, ← allocs "s2" true]
        -- the second list is not built when the first test fails
        checkEq [2000, 1000] [← allocs "s3" false, ← allocs "s3" true]
        -- the default of `orElse` is not computed for `some`; and (HD9's inlining) `pick`
        -- and `orElse` are inlined into `s4`, whose `case` on the known `.some 4` then
        -- picks its branch, so the `.some` cell isn't built either
        checkEq [151, 100] [← allocs "s4" false, ← allocs "s4" true] },
    { name := "closed definitions that do work are cached (CAFs, 15i); aliases, erased ones and the entry are not", run := fun _ => do
        let s := runFrontend (R := ZeroOneMany) cafSrc { loader := ← preludeLoader }
        let (decls, _) ← match Build.irProgram s "main" with
          | .ok r => pure r
          | .error e => throw (IO.userError e)
        let cafs := IR.cafs decls
        for n in ["table", "diverge", "failing", "lazySum", "big", "ones"] do
          check (cafs.contains n) s!"{n} is not cached"
        -- `tab` is `table` again, `four` and `Tab` are erased, `addTen` is a function
        for n in ["tab", "four", "Tab", "addTen", "wiz.entry", "range", "loop"] do
          check (!cafs.contains n) s!"{n} is cached" }
  ]

builtin_initialize registerGroup backendGroup

end Tests.Elab
