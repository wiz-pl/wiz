import Tests.Elab
import Grail.Elab

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
    { name := "a root file's manifest is its own (same headers, different text)", run := fun _ => do
        let prelude ← IO.FS.readFile "lib/Prelude.wiz"
        let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, module := "", loader := fun m => if m == "Prelude" then some prelude else none }
        let dir ← IO.FS.createTempDir
        let s1 := "import Prelude\ndef one : Nat := 1\n"
        let s2 := "import Prelude\ndef two : Nat := 2\n"
        let (_, h1) ← Cache.elaborateCached (some dir) [] s1 init 0 (verify := .warn)
        let (_, h2) ← Cache.elaborateCached (some dir) [] s2 init 0 (verify := .warn)
        let (_, h3) ← Cache.elaborateCached (some dir) [] s1 init 0 (verify := .warn)
        let (_, h4) ← Cache.elaborateCached (some dir) [] s2 init 0 (verify := .warn)
        -- (a cold run still counts its imported modules' replay as hits: 283 for the
        -- Prelude here, so the check is that the roots hit more than the module alone)
        check (h3 > h1 && h4 > h2) s!"a root file's entries were lost: {h1}/{h3}, {h2}/{h4}"
        -- (the root pseudo-module's manifest is keyed by the file's text too: before that,
        -- both files shared one manifest, which grew with every root checked and could
        -- lose a concurrent writer's entries -- a fresh file then missed on every run)
        let mdir := dir / "manifest.d"
        let mut roots := 0
        for e in ← mdir.readDir do
          unless e.fileName.endsWith ".wizmf" do continue
          let text ← IO.FS.readFile e.path
          if (((text.take 160).toString).splitOn "(module \"\")").length > 1 then roots := roots + 1
        checkEq 2 roots },
    { name := "a fresh file hits on the second check; an edit is a miss", run := fun _ => do
        let dir ← IO.FS.createTempDir
        let file := dir / "fresh.wiz"
        let cache := (dir / "cache").toString
        IO.FS.writeFile file "import Prelude\ndef one : Nat := 1\ndef two : Nat := one + 1\n"
        let wiz ← wizExe
        let hits (err : String) : Nat :=
          match err.splitOn " manifests, " with
          | _ :: s :: _ => match s.splitOn " entries" with
            | h :: _ => (h.trimAscii.toString.toNat?).getD 0
            | [] => 0
          | _ => 0
        -- (a hit writes no `.wizc`; a miss puts one, so the count is the hit/miss signal
        -- even though imported modules contribute to the stats' hit count)
        let cacheDir : System.FilePath := cache
        let entries : IO Nat := do
          if !(← cacheDir.isDir) then return 0
          let mut n := 0
          for e in ← cacheDir.readDir do
            if e.fileName.endsWith ".wizc" then n := n + 1
          pure n
        let checkIt (verify : List String) : IO (UInt32 × String) := do
          let out ← IO.Process.output { cmd := wiz, args := #["check", file.toString, "--cache", cache, "--cache-verify-stats"] ++ verify.toArray }
          pure (out.exitCode, out.stderr)
        let (c1, e1) ← checkIt []
        checkEq 0 c1
        let h1 := hits e1
        let n1 ← entries
        let (c2, e2) ← checkIt []
        checkEq 0 c2
        check (hits e2 > h1) s!"the second check of a fresh file did not add its hits ({h1} -> {hits e2}):\n{e2}"
        checkEq n1 (← entries)
        let h2 := hits e2
        -- (an edit re-elaborates its changed command: one new entry and one fewer hit; the
        -- pointer to the previous text's manifest keeps `one` warm -- without it, two
        -- commands would be re-elaborated)
        IO.FS.writeFile file "import Prelude\ndef one : Nat := 1\ndef two : Nat := one + 2\n"
        let (c3, e3) ← checkIt []
        checkEq 0 c3
        let n3 ← entries
        checkEq (n1 + 1) n3
        checkEq (hits e3 + 1) h2
        let (c4, e4) ← checkIt []
        checkEq 0 c4
        check (hits e4 > 0) s!"the second check after an edit missed:\n{e4}"
        checkEq h2 (hits e4)
        checkEq n3 (← entries)
        -- (`--cache-verify strict` uses the manifests the `warn` runs wrote)
        let (c5, e5) ← checkIt ["--cache-verify", "strict"]
        checkEq 0 c5
        check (hits e5 > 0) s!"strict did not serve the manifested entries:\n{e5}"
        -- (`off` is the old unverified lookup: the same verdict, and it writes no manifest)
        let (c6, _) ← checkIt ["--cache-verify", "off"]
        checkEq 0 c6
        let (c7, e7) ← checkIt []
        checkEq 0 c7
        check (hits e7 > 0) s!"a warn run after off did not hit:\n{e7}" },
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
    { name := "a long list literal caches in linear time (its expansion is not reprinted exponentially)", run := fun _ => do
        let wiz := ((← IO.appPath).parent.getD ".") / "wiz"
        -- one cold check of a `k`-element list literal through a fresh cache
        let checkLiteral (k : Nat) : IO Unit := do
          let dir ← IO.FS.createTempDir
          let names := (List.range k).map fun i => s!"name{i}"
          let src := "import Prelude\nstructure M where\n  name : String\ndef mk (n : String) : M := M.mk n\n" ++
            "def mapM {A B : Type} (f : A → B) : List A → List B\n  | .nil => .nil\n  | .cons x xs => .cons (f x) (mapM f xs)\n" ++
            "def xs : List M :=\n  mapM mk [ " ++ ", ".intercalate (names.map fun n => s!"\"{n}\"") ++ " ]\n"
          let file := dir / "long-list.wiz"
          IO.FS.writeFile file src
          try
            let out ← IO.Process.output { cmd := "timeout", args :=
              #["60", wiz.toString, "check", "--cache", (dir / "cache").toString, file.toString] }
            unless out.exitCode == 0 do
              throw (IO.userError s!"checking a {k}-element list literal through the cache failed (exit {out.exitCode}): {out.stdout}{out.stderr}")
          finally
            IO.FS.removeDirAll dir
        -- (finding in reviews/2026-11-17-test-audit.md:35: one size and `ms < 15000`
        -- passes a quadratic implementation; the ratio at 40 and 80 is the claim)
        let _ ← checkScaling "long list literal" checkLiteral 40 3 },
    { name := "terms survive the cache's format", run := fun _ => do
        let prelude ← IO.FS.readFile "lib/Prelude.wiz"
        let st := runFrontend (R := ZeroOneMany) "import Prelude" { trustedModule := Tests.libModule, loader := fun _ => some prelude }
        for n in ["List.append", "Nat.rec", "SyntaxF.casesOn", "Tac.rec", "Monad.bind"] do
          let some d := st.globals.find? n | throw (IO.userError s!"no {n}")
          let text := (Cache.term d.type).render
          match (Cache.Sx.parse text).bind (Cache.dterm (R := ZeroOneMany)) with
          | some t => check (t == d.type) s!"{n}: the type changed in the round trip"
          | none => throw (IO.userError s!"{n}: could not read back {text.take 200}") },
    { name := "the cache's format rejects a malformed escape instead of decoding it (F27)", run := fun _ => do
        let atom (s : String) : Option String :=
          match Cache.Sx.parse s with
          | some (.a v) => some v
          | _ => none
        -- valid escapes still decode, in either case
        checkEq (some "A") (atom "\"\\x41\"")
        checkEq (some "J") (atom "\"\\x4a\"")
        checkEq (some "→") (atom "\"\\u{2192}\"")
        -- quoted atoms round-trip: a space forces quoting, a control character an escape
        checkEq (some "a b") (atom (Cache.Sx.render (.a "a b")))
        checkEq (some "a\x01b") (atom (Cache.Sx.render (.a "a\x01b")))
        -- a malformed escape is a parse failure, not an arbitrary character
        for bad in ["\"\\xZZ\"", "\"\\x4g\"", "\"\\u{zz}\"", "\"\\u{}\"", "\"\\u{110000}\""] do
          check (Cache.Sx.parse bad).isNone s!"accepted the malformed escape {bad}" },
    { name := "the language server answers requests", run := fun _ => do
        let prelude ← IO.FS.readFile "lib/Prelude.wiz"
        let srv : LSP.Server := { libs := ({} : Std.HashMap String (String × String)).insert "Prelude" ("lib/Prelude.wiz", prelude), trusted := ["Prelude"] }
        let req (s : String) : Lean.Json := (Lean.Json.parse s).toOption.get!
        let (srv, out) ← LSP.handle srv (req "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{}}")
        check ((out[0]!.compress.splitOn "hoverProvider").length > 1) "no capabilities"
        let (srv, out) ← LSP.handle srv (req ("{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{\"textDocument\":" ++
          "{\"uri\":\"file:///t.wiz\",\"text\":\"import Prelude\\ndef ok : Nat := 1\\ndef bad : Nat := true\\n\"}}}"))
        check ((out[0]!.compress.splitOn "unknown identifier").length > 1) s!"no diagnostic: {out[0]!.compress}"
        let (_, out) ← LSP.handle srv (req ("{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"textDocument/hover\",\"params\":" ++
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
    { name := "wiz repl: --prelude imports a module before the first input (-I, -p, missing)", run := fun _ => do
        let dir ← IO.FS.createTempDir
        -- a prelude module is an ordinary module: it imports the Prelude itself
        IO.FS.writeFile (dir / "Pre.wiz") "import Prelude\ndef preValue : Nat := 40 + 2\n"
        -- `--prelude M` (with `-I DIR`) is an implicit `import M` before the session
        let (code, out, err) := ← runRepl "#eval preValue + 1\n#check preValue\n:quit\n"
          ["-I", dir.toString, "--prelude", "Pre"]
        checkEq 0 code
        check ((out.splitOn "43").length > 1) s!"the prelude's value is not in scope:\n{out}\n{err}"
        check ((out.splitOn "preValue : Nat").length > 1) s!"the prelude's definition is not in scope:\n{out}\n{err}"
        -- `-p` is the short form
        let (code, out, err) := ← runRepl "#eval preValue\n:quit\n" ["-I", dir.toString, "-p", "Pre"]
        checkEq 0 code
        check ((out.splitOn "42").length > 1) s!"`-p` did not import the module:\n{out}\n{err}"
        -- a missing module is an error at startup, before any input is read
        let (code, out, err) := ← runRepl "#eval 1\n" ["--prelude", "NoSuchPrelude"]
        checkEq 2 code
        check ((err.splitOn "unknown module NoSuchPrelude").length > 1)
          s!"no clear missing-module error:\n{out}\n{err}"
        check ((out.splitOn "1").length == 1) s!"the session ran anyway:\n{out}\n{err}" },
    { name := "wiz parse --imports lists the header, and parse reports an import after a declaration", run := fun _ => do
        let dir ← IO.FS.createTempDir
        let file := dir / "deps.wiz"
        IO.FS.writeFile file "-- a comment\nimport Prelude\n/- block -/\nimport Logic\ndef x : Nat := 1\nimport Text\n"
        -- the dependency fact: header only, one module per line
        let (code, out, err) := ← runWiz ["parse", "--imports", file.toString]
        checkEq 0 code
        checkEq "Prelude\nLogic\n" out
        checkEq "" err
        -- `wiz parse` reports the order violation (and still prints the trees)
        let (code, _, err) := ← runWiz ["parse", file.toString]
        checkEq 1 code
        check ((err.splitOn "imports must precede declarations").length > 1) s!"no order error:\n{err}" },
    { name := "wiz run and REPL :run remove their temporary directories (F11)", run := fun _ => do
        let tc ← toolchain
        -- a TMPDIR of our own: every temporary directory a child makes lands there
        let tmp ← IO.FS.createTempDir
        let dir ← IO.FS.createTempDir
        try
          let file := dir / "prog.wiz"
          -- the `import_c` header is preprocessed in a temporary directory of its own
          IO.FS.writeFile file "import Prelude\nimport_c \"stddef.h\"\ndef main : Nat := 40 + 2\n"
          let env : Array (String × Option String) := #[("TMPDIR", some tmp.toString)]
          let (code, out, err) := ← runWiz (tc.toFlags ++ ["run", file.toString]) env
          if code != 0 then
            if ["gmp", "No such file", "not preprocessed", "cannot find", "could not execute"].any (fun s => ((out ++ err).splitOn s).length > 1) then
              skip "no toolchain"
              return
            throw (IO.userError s!"wiz run failed ({code}):\n{out}\n{err}")
          check ((out.splitOn "42").length > 1) s!"no result:\n{out}\n{err}"
          -- a second run must not leave a second directory either
          let (code, out, err) := ← runWiz (tc.toFlags ++ ["run", file.toString]) env
          checkEq 0 code
          check ((out.splitOn "42").length > 1) s!"no result:\n{out}\n{err}"
          -- `:run` twice in one session (and the session's preprocessed headers)
          let script := dir / "session.wiz"
          IO.FS.writeFile script "def main : Nat := 40 + 2\n:run main\n:run main\n"
          let (code, out, err) := ← runWiz (tc.toFlags ++ ["repl", "--script", script.toString]) env
          checkEq 0 code
          check ((out.splitOn "42").length > 2) s!"the session's :run printed nothing:\n{out}\n{err}"
          let left := (← tmp.readDir).map (·.fileName)
          check left.isEmpty s!"temporary directories were left behind: {left.toList}"
        finally
          IO.FS.removeDirAll tmp
          IO.FS.removeDirAll dir },
    { name := "import_c: a header name with a newline or `>` is rejected, not spliced (F09)", run := fun _ => do
        let tc ← toolchain
        -- `string.h` first, then a directive that *succeeds*: if it reached `cc`, the
        -- preprocessed text would hold stdio's declarations and `C.printf` would bind
        let injected := "string.h>\n#include <stdio.h>\n#define wiz_injected "
        let rejected (what : String) (r : Except String Unit) : IO Unit :=
          match r with
          | .ok () => throw (IO.userError s!"{what} accepted the spliced header")
          | .error e => do
            check ((e.splitOn "not a valid C header name").length > 1)
              s!"{what}: no clear rejection: {e}"
            check ((e.splitOn "stdio").length == 1)
              s!"{what}: the offending header was echoed into the error: {e}"
        let viaBuild ← try
            let _ ← Build.preprocessHeaders tc s!"import_c \"{injected}\"\n"
            pure (.ok () : Except String Unit)
          catch e => pure (.error (toString e))
        rejected "Build.preprocessHeaders" viaBuild
        -- Grail's reader runs the same scan; it must reject the name too
        let viaGrail ← try
            let _ ← Grail.preprocessHeaders tc [s!"import_c \"{injected}\"\n"]
            pure (.ok () : Except String Unit)
          catch e => pure (.error (toString e))
        rejected "Grail.preprocessHeaders" viaGrail
        -- and through the command: an error, and the injected include never bound anything
        let dir ← IO.FS.createTempDir
        try
          let file := dir / "bad.wiz"
          IO.FS.writeFile file ("import IO\nimport_c \"string.h>\n#include <stdio.h>\n#define wiz_injected \"\n" ++
            "def main : IO Unit := do\n  IO.println (Nat.toString (C.printf \"x\"))\n")
          let (code, out, err) ← runWiz (tc.toFlags ++ ["check", file.toString])
          check (code != 0) s!"the injected header checked (exit {code}):\n{out}\n{err}"
          check ((err.splitOn "not a valid C header name").length > 1)
            s!"no clear error:\n{out}\n{err}"
          check ((out.splitOn "C.printf").length == 1)
            s!"the check reported the injected binding:\n{out}"
        finally
          IO.FS.removeDirAll dir },
    { name := "import_c: a failing preprocessor is an error, not a silently dropped header (F09)", run := fun _ => do
        let tc ← toolchain
        let missing := "wiz_no_such_header_f09.h"
        let viaBuild ← try
            let _ ← Build.preprocessHeaders tc s!"import_c \"{missing}\"\n"
            pure (none : Option String)
          catch e => pure (some (toString e))
        let some e := viaBuild | throw (IO.userError "a header the compiler could not read was dropped")
        if ((e.splitOn "could not execute").length > 1) then
          -- no `cc` on this machine: not this case's failure
          skip "no toolchain"
          return
        check ((e.splitOn "-E failed").length > 1) s!"the compiler's failure is not reported: {e}"
        check ((e.splitOn missing).length > 1) s!"the error does not name the header: {e}"
        -- the same through `wiz check`: the compiler's failure, not "not preprocessed"
        let dir ← IO.FS.createTempDir
        try
          let file := dir / "missing.wiz"
          IO.FS.writeFile file s!"import IO\nimport_c \"{missing}\"\ndef main : IO Unit := IO.println \"x\"\n"
          let (code, out, err) ← runWiz (tc.toFlags ++ ["check", file.toString])
          check (code != 0) s!"a missing header checked (exit {code})"
          check ((err.splitOn missing).length > 1) s!"the error does not name the header:\n{out}\n{err}"
          check ((err.splitOn "was not preprocessed").length == 1)
            s!"the old silent-skip message is still used:\n{out}\n{err}"
        finally
          IO.FS.removeDirAll dir },
    { name := "split objects: the key is a SHA-256 of every input, and each one changes it (F36)", run := fun _ => do
        let base : Build.SplitObject :=
          { cc := "cc", flags := #["-O2", "-w", "-c"], env := #[("CPATH", none)],
            text := "wiz_val wiz_f(void) { return 1; }", header := "wiz_val wiz_f(void);" }
        let k := Build.splitObjectKey base
        checkEq 64 k.length
        check (k.toList.all fun c => (48 ≤ c.toNat && c.toNat ≤ 57) || (97 ≤ c.toNat && c.toNat ≤ 102))
          s!"not a SHA-256 hex digest: {k}"
        let changes : List (String × Build.SplitObject) :=
          [("the compiler", { base with cc := "clang" }),
           ("the flags", { base with flags := base.flags.push "-g" }),
           ("the include environment", { base with env := #[("CPATH", some "/include")] }),
           ("the environment list", { base with env := base.env.push ("C_INCLUDE_PATH", none) }),
           ("the unit's text", { base with text := base.text ++ "\n" }),
           ("the header", { base with header := base.header ++ "\n" })]
        for (what, changed) in changes do
          check (Build.splitObjectKey changed != k) s!"changing {what} did not change the key" },
    { name := "a split build reuses its objects, and a changed program, compiler or flag misses (F36)", run := fun _ => do
        let tc ← toolchain
        let dir ← IO.FS.createTempDir
        try
          let log : System.FilePath := dir / "cc.log"
          -- A recording stub `cc`: it logs the invocation and creates the `-o` output, so
          -- the cache decisions (stamp + object present) are exercised without needing a
          -- C toolchain or its GMP store paths on this node.
          let stub (name : String) : IO String := do
            let p := dir / name
            IO.FS.writeFile p ("#!/bin/sh\n" ++
              s!"printf '%s\\n' \"$*\" >> '{log}'\n" ++
              "out=\"\"\nprev=\"\"\n" ++
              "for a in \"$@\"; do\n  if [ \"$prev\" = \"-o\" ]; then out=\"$a\"; fi\n  prev=\"$a\"\ndone\n" ++
              "[ -n \"$out\" ] && : > \"$out\"\nexit 0\n")
            let c ← IO.Process.output { cmd := "chmod", args := #["+x", p.toString] }
            unless c.exitCode == 0 do throw (IO.userError s!"chmod failed: {c.stderr}")
            pure p.toString
          let compiles : IO Nat := do
            if !(← log.pathExists) then return 0
            let lines := (← IO.FS.readFile log).splitOn "\n"
            pure (lines.filter fun l => (l.splitOn " ").contains "-c").length
          let src : System.FilePath := dir / "prog.wiz"
          let out : System.FilePath := dir / "prog"
          let source (k : Nat) : String :=
            "import IO\ndef twice (n : Nat) : Nat := n + n\n" ++
            s!"def main : IO Unit := IO.println (Nat.toString (twice {k}))\n"
          IO.FS.writeFile src (source 21)
          let cc1 ← stub "cc1.sh"
          let cc2 ← stub "cc2.sh"
          let build (cc : String) (extra : List String) : IO (UInt32 × String × String) :=
            runWiz (tc.toFlags ++ ["--cc", cc,
              "--cflags", " ".intercalate (tc.cflags ++ extra),
              "build", src.toString, "-o", out.toString, "--split", "2"])
          let first ← build cc1 []
          let n1 ← compiles
          unless first.1 == 0 && n1 ≥ 3 do
            -- the program did not elaborate into a split build: not this case's claim
            skip "no split build"
            return
          -- the same inputs: every unit's stamp and object are reused
          let again ← build cc1 []
          checkEq 0 again.1
          checkEq n1 (← compiles)
          -- a changed program is a miss
          IO.FS.writeFile src (source 22)
          let edited ← build cc1 []
          checkEq 0 edited.1
          let n2 ← compiles
          check (n2 > n1) s!"a changed program reused every object ({n1} -> {n2})"
          -- a changed compiler is a miss (same flags, same text)
          let other ← build cc2 []
          checkEq 0 other.1
          let n3 ← compiles
          check (n3 > n2) s!"a changed compiler reused every object ({n2} -> {n3})"
          -- a changed flag is a miss
          let flagged ← build cc2 ["-g"]
          checkEq 0 flagged.1
          let n4 ← compiles
          check (n4 > n3) s!"a changed --cflags reused every object ({n3} -> {n4})"
        finally
          IO.FS.removeDirAll dir },
    { name := "wiz test-driver: the driver's --list, a group, and a clear error without the driver", run := fun _ => do
        let self ← IO.appPath
        let (code, out, err) := ← runWiz ["test-driver", "--driver", self.toString, "--list"] #[]
        checkEq 0 code
        check ((out.splitOn "tooling").length > 1) s!"no tooling group in --list:\n{out}\n{err}"
        -- the cheapest group, through the wrapper: each case is one child process
        let (code, out, err) := ← runWiz ["test-driver", "=rig", s!"--driver={self}", "--jobs", "2"] #[]
        checkEq 0 code
        check ((out.splitOn "── rig").length > 1 && (out.splitOn "0 failed").length > 1) s!"not the rig group's result:\n{out}\n{err}"
        let missing := "/nonexistent/wiz-tests"
        let (code, out, err) := ← runWiz ["test-driver", "--driver", missing, "--list"] #[]
        checkEq 2 code
        check ((err.splitOn "no test driver").length > 1) s!"no clear error:\n{out}\n{err}" }
  ]

builtin_initialize registerGroup toolingGroup

end Tests.Elab
