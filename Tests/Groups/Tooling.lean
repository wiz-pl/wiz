import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- This test driver's sibling `wiz`. -/
def wizExe : IO String := do
  pure (← IO.FS.realPath ((← IO.appPath).parent.getD "." / "wiz")).toString

/-- Run `wiz` and collect its output (`env` overrides, inherited environment otherwise). -/
def runWiz (args : List String) (env : Array (String × Option String) := #[]) :
    IO (UInt32 × String × String) := do
  let out ← IO.Process.output { cmd := ← wizExe, args := args.toArray, env }
  pure (out.exitCode, out.stdout, out.stderr)

/-- Run `wiz repl` with `input` on a pipe; returns its exit code and output. -/
def runRepl (input : String) (args : List String := []) : IO (UInt32 × String × String) := do
  let child ← IO.Process.spawn { cmd := ← wizExe, args := #["repl"] ++ args.toArray,
                                  stdin := .piped, stdout := .piped, stderr := .piped }
  let (stdin, child) ← child.takeStdin
  let out ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let err ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
  stdin.putStr input
  stdin.flush
  let code ← child.wait
  pure (code, ← IO.ofExcept out.get, ← IO.ofExcept err.get)

def toolingGroup : Group where
  name := "tooling"
  exercise := "Stage 11"
  cases := [
    { name := "queries: an edit re-elaborates only what follows it", run := fun _ => do
        let prelude ← IO.FS.readFile "lib/Prelude.wiz"
        let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, loader := fun m => if m == "Prelude" then some prelude else none }
        let v1 := "import Prelude\ndef a : Nat := 1\ndef b : Nat := a + 1\ndef c : Nat := b + 1\n"
        let (s1, eng) := Query.elaborate {} v1 init
        checkEq 4 eng.elaborated
        let v2 := v1.replace "b + 1" "b + 2"
        let (s2, eng) := Query.elaborate eng v2 init
        checkEq 5 eng.elaborated
        check (s1.messages.isEmpty && s2.messages.isEmpty) "unexpected messages"
        -- the same text again: everything is reused
        let (_, eng) := Query.elaborate eng v2 init
        checkEq 5 eng.elaborated },
    { name := "queries: hover, definition, completion", run := fun _ => do
        let prelude ← IO.FS.readFile "lib/Prelude.wiz"
        let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, loader := fun m => if m == "Prelude" then some prelude else none }
        let src := "import Prelude\ndef double (n : Nat) : Nat := n + n\ndef four : Nat := double 2\n"
        let (s, _) := Query.elaborate {} src init
        let off := (src.splitOn "double 2")[0]!.length
        checkEq "(some (double, Nat → Nat))" (toString (Query.hoverAt s off))
        match Query.definitionAt s off with
        | some (n, info, m) => checkEq "double 15 \"\"" s!"{n} {info.start} {repr m}"
        | none => throw (IO.userError "no definition")
        let pre := src ++ "def x : Nat := dou"
        let (s', _) := Query.elaborate {} pre init
        checkEq "#[double]" (toString (Query.completionsAt s' pre pre.length)) },
    { name := "the shared cache gives the same results", run := fun _ => do
        let prelude ← IO.FS.readFile "lib/Prelude.wiz"
        let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, loader := fun m => if m == "Prelude" then some prelude else none }
        let src := "import Prelude\ninductive T where\n  | a\n  | b (t : T)\ndef size : T → Nat\n  | .a => 1\n  | .b t => size t + 1\n#eval size (.b (.b .a))\ndef bad : Nat := true\n"
        let plain := runFrontend src init
        let dir ← IO.FS.createTempDir
        let (cold, h1) ← Cache.elaborateCached (some dir) [] src init 0
        let (warm, h2) ← Cache.elaborateCached (some dir) [] src init 0
        checkEq 0 h1
        check (h2 > 0) "nothing came from the cache"
        let msgs (st : CommandState ZeroOneMany) := toString (st.messages.toList.map (·.render src))
        checkEq (msgs plain) (msgs cold)
        checkEq (msgs plain) (msgs warm)
        checkEq plain.globals.order.size warm.globals.order.size },
    { name := "another build of wiz misses the shared cache (its binary is in the key)", run := fun _ => do
        let prelude ← IO.FS.readFile "lib/Prelude.wiz"
        let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, loader := fun m => if m == "Prelude" then some prelude else none }
        let src := "import Prelude\ndef two : Nat := 1 + 1\n#eval two\n"
        let dir ← IO.FS.createTempDir
        let (_, h1) ← Cache.elaborateCached (some dir) [] src init 0 (binary := some 1)
        let (_, h2) ← Cache.elaborateCached (some dir) [] src init 0 (binary := some 1)
        let (_, h3) ← Cache.elaborateCached (some dir) [] src init 0 (binary := some 2)
        checkEq 0 h1
        check (h2 > 0) "the same binary got nothing from the cache"
        checkEq 0 h3
        -- by default, the key is this test driver's own hash, remembered by its stamp
        let me ← Cache.binaryId (some dir)
        checkEq me (← Cache.binaryId (some dir))
        checkEq me (hash (← IO.FS.readBinFile (← IO.appPath)))
        let (_, h4) ← Cache.elaborateCached (some dir) [] src init 0
        let (_, h5) ← Cache.elaborateCached (some dir) [] src init 0 (binary := some me)
        checkEq 0 h4
        check (h5 > 0) "the default is not this binary's hash" },
    { name := "terms survive the cache's format", run := fun _ => do
        let prelude ← IO.FS.readFile "lib/Prelude.wiz"
        let st := runFrontend (R := ZeroOneMany) "import Prelude" { trustedModule := Tests.libModule, loader := fun _ => some prelude }
        for n in ["List.append", "Nat.rec", "SyntaxF.casesOn", "Tac.rec", "Monad.bind"] do
          let some d := st.globals.find? n | throw (IO.userError s!"no {n}")
          let text := (Cache.term d.type).render
          match (Cache.Sx.parse text).bind (Cache.dterm (R := ZeroOneMany)) with
          | some t => check (t == d.type) s!"{n}: the type changed in the round trip"
          | none => throw (IO.userError s!"{n}: could not read back {text.take 200}") },
    { name := "the language server answers requests", run := fun _ => do
        let prelude ← IO.FS.readFile "lib/Prelude.wiz"
        let srv : LSP.Server := { libs := ({} : Std.HashMap String (String × String)).insert "Prelude" ("lib/Prelude.wiz", prelude), trusted := ["Prelude"] }
        let req (s : String) : Lean.Json := (Lean.Json.parse s).toOption.get!
        let (srv, out) := LSP.handle srv (req "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{}}")
        check ((out[0]!.compress.splitOn "hoverProvider").length > 1) "no capabilities"
        let (srv, out) := LSP.handle srv (req ("{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{\"textDocument\":" ++
          "{\"uri\":\"file:///t.wiz\",\"text\":\"import Prelude\\ndef ok : Nat := 1\\ndef bad : Nat := true\\n\"}}}"))
        check ((out[0]!.compress.splitOn "unknown identifier").length > 1) s!"no diagnostic: {out[0]!.compress}"
        let (_, out) := LSP.handle srv (req ("{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"textDocument/hover\",\"params\":" ++
          "{\"textDocument\":{\"uri\":\"file:///t.wiz\"},\"position\":{\"line\":1,\"character\":9}}}"))
        check ((out[0]!.compress.splitOn "Nat : Type").length > 1) s!"no hover: {out[0]!.compress}" },
    { name := "wiz repl: definitions persist, #eval prints, an error does not stop the session", run := fun _ => do
        let input := "def answer : Nat := 41 + 1\n#eval answer\n#check answer\ndef bad : Nat := true\n#eval answer + 1\n:quit\n"
        let (code, out, err) := ← runRepl input
        checkEq 0 code
        for frag in ["42", "answer : Nat", "43"] do
          check ((out.splitOn frag).length > 1) s!"no '{frag}' in the session:\n{out}\n{err}"
        check ((err.splitOn ": error:").length > 1) s!"the error was not reported:\n{err}" },
    { name := "wiz repl: a pipe (no tty) reads one command per line and EOF exits", run := fun _ => do
        -- `:quit` is not needed: the end of the file is the end of the session
        let dir ← IO.FS.createTempDir
        let script := dir / "session.wiz"
        IO.FS.writeFile script "def x : Nat := 7\n#eval x + 1\n"
        let child ← IO.Process.spawn { cmd := "sh", args := #["-c", s!"exec \"{← wizExe}\" repl < \"{script}\""],
                                        stdout := .piped, stderr := .piped }
        let out ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
        let err ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
        let code ← child.wait
        let out := ← IO.ofExcept out.get
        let err := ← IO.ofExcept err.get
        checkEq 0 code
        check ((out.splitOn "8").length > 1) s!"no result in the piped session:\n{out}\n{err}"
        check ((out.splitOn "wiz> ").length == 1) s!"a prompt was printed to a pipe:\n{out}" },
    { name := "wiz repl: :type prints a type and :load adds a file's definitions", run := fun _ => do
        let dir ← IO.FS.createTempDir
        let file := dir / "Loaded.wiz"
        -- the second definition is an error: its file's messages are prefixed, the
        -- session goes on, and the good definition stays in scope
        IO.FS.writeFile file "def three : Nat := 1 + 2\ndef bad : Nat := true\n"
        let missing := dir / "missing.wiz"
        let (code, out, err) := ← runRepl
          s!"def two : Nat := 1 + 1\n:type two\n:load {file}\n#check three\n#eval three + 1\n:load {missing}\n#check two\n:quit\n"
        checkEq 0 code
        check ((out.splitOn "two : Nat").length > 1) s!"`:type` printed nothing:\n{out}\n{err}"
        check ((out.splitOn "three : Nat").length > 1) s!"the loaded definition is not in scope:\n{out}\n{err}"
        check ((out.splitOn "1:1: info: 4").length > 1) s!"`:load` broke the session:\n{out}\n{err}"
        check ((err.splitOn s!"{file}:2:").length > 1) s!"no error with the loaded file's path:\n{err}"
        check ((err.splitOn "cannot read").length > 1) s!"a missing file was not reported:\n{err}" },
    { name := "wiz test-driver: the driver's --list, a group, and a clear error without the driver", run := fun _ => do
        let self ← IO.appPath
        let (code, out, err) := ← runWiz ["test-driver", "--list"] #[("WIZ_TESTS", some self.toString)]
        checkEq 0 code
        check ((out.splitOn "tooling").length > 1) s!"no tooling group in --list:\n{out}\n{err}"
        -- the cheapest group, through the wrapper: each case is one child process
        let (code, out, err) := ← runWiz ["test-driver", "=rig", "--jobs", "2"] #[("WIZ_TESTS", some self.toString)]
        checkEq 0 code
        check ((out.splitOn "── rig").length > 1 && (out.splitOn "0 failed").length > 1) s!"not the rig group's result:\n{out}\n{err}"
        let missing := "/nonexistent/wiz-tests"
        let (code, out, err) := ← runWiz ["test-driver", "--list"] #[("WIZ_TESTS", some missing)]
        checkEq 2 code
        check ((err.splitOn "no test driver").length > 1) s!"no clear error:\n{out}\n{err}" }
  ]

builtin_initialize registerGroup toolingGroup

end Tests.Elab
