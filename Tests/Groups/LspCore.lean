import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- Build and run `main` through C with every library importable (`lib/` and its
subdirectories, so `import Lsp.Core` resolves), and compare its standard output. -/
def lspCoreRun (src : String) (expected : String) : IO Unit := do
  let headers ← Build.preprocessHeaders (← toolchain) src
  let s := runFrontend (R := ZeroOneMany) src
    { trustedModule := Tests.libModule, loader := ← libLoader, cHeaders := (headers[·]?) }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  let dir ← IO.FS.createTempDir
  match ← Build.runGlobal (← toolchain) s "main" dir false (timeout := some 120) with
  | .ok v => checkEq expected v
  | .error e =>
    if ["gmp.h", "llc:", "No such file"].any fun m => (e.splitOn m).length > 1 then skip "no toolchain"
    else throw (IO.userError e)

/-- The scripted sessions of lib/Lsp/Core.wiz with the fake elaborator (lib/Lsp/Fake.wiz),
run on lib/Lsp/Loop.wiz's virtual clock (10 ms per command, 200 ms debounce): events in,
messages out, byte for byte. Compiled rather than `#eval`ed: the kernel evaluator does
not share `let`-bound pairs, so a loop that threads state through pairs is exponential
there (a 22-step pair loop takes about a minute). -/
def lspCoreSrc : String := r##"import IO
import Lsp.Loop
import Lsp.Fake
def u : String := "file:///a.wiz"
def v : String := "file:///b.wiz"
def init : List (Nat × String) := [(0, Lsp.Send.initialize 1 .false), (0, Lsp.Send.initialized)]
def run (title : String) (cfg : Lsp.Config) (script : List (Nat × String)) : String :=
  String.intercalate "\n" (.cons (String.append "== " title) (Lsp.transcript Lsp.fake cfg 10 (List.append init script)))
def cfg : Lsp.Config := Lsp.Config.default
def text4 : String := "def a\ncheck b\ncheck a\ngoal x | y\n"
def main : IO Unit := IO.println (String.intercalate "\n" [
  String.append "split " (String.intercalate " " (List.map (fun p => String.join [Nat.repr p.1, "-", Nat.repr p.2]) (Lsp.splitAll "def a\ncheck a\n  -- still check\n\n-- c\ngoal x\n"))),
  run "open, diagnostics, a request waits behind the frontier" cfg
    [(0, Lsp.Send.didOpen u 1 text4),
     (5, Lsp.Send.position 2 "wiz/plainGoal" u 3 2),
     (5, Lsp.Send.position 3 "textDocument/hover" u 0 5),
     (50, Lsp.Send.position 4 "wiz/plainTermGoal" u 2 7),
     (50, Lsp.Send.position 5 "wiz/plainTermGoal" u 1 7)],
  run "prefix reuse: an edit in the last command re-elaborates one command" cfg
    [(0, Lsp.Send.didOpen u 1 text4),
     (100, Lsp.Send.didChange u 2 "def a\ncheck b\ncheck a\ngoal x | z\n"),
     (400, Lsp.Send.position 6 "textDocument/hover" u 0 4)],
  run "prefix reuse: an edit in the first command re-elaborates all four" cfg
    [(0, Lsp.Send.didOpen u 1 text4),
     (100, Lsp.Send.didChange u 2 "def b\ncheck b\ncheck a\ngoal x | y\n")],
  run "an identical text reuses everything; appending re-elaborates the last command" cfg
    [(0, Lsp.Send.didOpen u 1 text4),
     (100, Lsp.Send.didChange u 2 text4),
     (400, Lsp.Send.didChange u 3 (String.append text4 "check a\n"))],
  run "an edit mid-elaboration: stale work dropped, waiting request ContentModified, debounce" cfg
    [(0, Lsp.Send.didOpen u 1 text4),
     (5, Lsp.Send.position 7 "wiz/plainGoal" u 3 0),
     (15, Lsp.Send.didChange u 2 "def a\ncheck a\n"),
     (16, Lsp.Send.position 8 "wiz/plainTermGoal" u 1 6)],
  run "cancel: a waiting request is answered RequestCancelled, an answered one is ignored" cfg
    [(0, Lsp.Send.didOpen u 1 text4),
     (0, Lsp.Send.position 9 "wiz/plainGoal" u 3 0),
     (0, Lsp.Send.position 10 "textDocument/hover" u 0 4),
     (12, Lsp.Send.cancel 9),
     (13, Lsp.Send.cancel 10)],
  run "two documents take turns, one command each" (Lsp.Config.mk 0 .false "fake")
    [(0, Lsp.Send.didOpen u 1 "def a\ndef b\ndef c\n"),
     (0, Lsp.Send.didOpen v 1 "check a\ncheck b\n")],
  run "a document a request waits on goes first; wiz/elaborated when asked" (Lsp.Config.mk 0 .false "fake")
    [(0, Lsp.Send.initialize 11 .true),
     (0, Lsp.Send.didOpen u 1 "def a\ndef b\ndef c\n"),
     (0, Lsp.Send.didOpen v 1 "check a\ncheck b\n"),
     (0, Lsp.Send.position 12 "wiz/plainTermGoal" v 1 6)],
  run "UTF-16 positions: a character outside the BMP counts two" cfg
    [(0, Lsp.Send.didOpen u 1 "fail 😀😀\ndef λx\ncheck λx\n"),
     (100, Lsp.Send.position 13 "textDocument/hover" u 1 5),
     (100, Lsp.Send.position 14 "wiz/plainTermGoal" u 2 7)],
  run "errors: unknown and interactive methods, unknown document, bad JSON, close, shutdown, exit" cfg
    [(0, Lsp.Send.position 15 "wiz/interactiveGoals" u 0 0),
     (0, Lsp.Send.position 16 "wiz/plainGoal" "file:///none.wiz" 0 0),
     (0, "{not json"),
     (0, Lsp.Send.didOpen u 1 text4),
     (0, Lsp.Send.position 17 "wiz/plainGoal" u 3 0),
     (1, Lsp.Send.didClose u),
     (2, Lsp.Send.shutdown 18),
     (3, Lsp.Send.exit),
     (4, Lsp.Send.didOpen v 1 "def z\n")],
  String.intercalate "\n" (.cons "== before initialize" (Loop.transcript (Lsp.runScript Lsp.fake cfg 10 100
    [(0, Lsp.Send.position 19 "wiz/plainGoal" u 0 0), (0, Lsp.Send.didOpen u 1 "def a\n")])))])
"##

/-- What `lspCoreSrc` prints. -/
def lspCoreOut : String := r##"split 0-6 6-32 37-44
== open, diagnostics, a request waits behind the frontier
t=0 {"jsonrpc":"2.0","id":1,"result":{"capabilities":{"textDocumentSync":1,"positionEncoding":"utf-16","hoverProvider":true,"experimental":{"wizInfoview":{"version":"0.1","methods":["wiz/plainGoal","wiz/plainTermGoal"]}}},"serverInfo":{"name":"wiz-lsp-core","version":"0.1"}}}
t=10 {"jsonrpc":"2.0","id":3,"result":{"contents":{"kind":"plaintext","value":"a : def #1"},"range":{"start":{"line":0,"character":4},"end":{"line":0,"character":5}}}}
t=30 {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file:///a.wiz","version":1,"diagnostics":[{"range":{"start":{"line":1,"character":6},"end":{"line":1,"character":7}},"severity":1,"source":"wiz","message":"unknown identifier 'b'"},{"range":{"start":{"line":2,"character":6},"end":{"line":2,"character":7}},"severity":3,"source":"wiz","message":"a : def #1"}]}}
t=30 {"jsonrpc":"2.0","id":2,"result":{"goals":["x","y"],"rendered":"x\n\ny"}}
t=50 {"jsonrpc":"2.0","id":4,"result":{"goal":"a","range":{"start":{"line":2,"character":6},"end":{"line":2,"character":7}}}}
t=50 {"jsonrpc":"2.0","id":5,"result":null}
steps=4
== prefix reuse: an edit in the last command re-elaborates one command
t=0 {"jsonrpc":"2.0","id":1,"result":{"capabilities":{"textDocumentSync":1,"positionEncoding":"utf-16","hoverProvider":true,"experimental":{"wizInfoview":{"version":"0.1","methods":["wiz/plainGoal","wiz/plainTermGoal"]}}},"serverInfo":{"name":"wiz-lsp-core","version":"0.1"}}}
t=30 {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file:///a.wiz","version":1,"diagnostics":[{"range":{"start":{"line":1,"character":6},"end":{"line":1,"character":7}},"severity":1,"source":"wiz","message":"unknown identifier 'b'"},{"range":{"start":{"line":2,"character":6},"end":{"line":2,"character":7}},"severity":3,"source":"wiz","message":"a : def #1"}]}}
t=300 {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file:///a.wiz","version":2,"diagnostics":[{"range":{"start":{"line":1,"character":6},"end":{"line":1,"character":7}},"severity":1,"source":"wiz","message":"unknown identifier 'b'"},{"range":{"start":{"line":2,"character":6},"end":{"line":2,"character":7}},"severity":3,"source":"wiz","message":"a : def #1"}]}}
t=400 {"jsonrpc":"2.0","id":6,"result":{"contents":{"kind":"plaintext","value":"a : def #1"},"range":{"start":{"line":0,"character":4},"end":{"line":0,"character":5}}}}
steps=5
== prefix reuse: an edit in the first command re-elaborates all four
t=0 {"jsonrpc":"2.0","id":1,"result":{"capabilities":{"textDocumentSync":1,"positionEncoding":"utf-16","hoverProvider":true,"experimental":{"wizInfoview":{"version":"0.1","methods":["wiz/plainGoal","wiz/plainTermGoal"]}}},"serverInfo":{"name":"wiz-lsp-core","version":"0.1"}}}
t=30 {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file:///a.wiz","version":1,"diagnostics":[{"range":{"start":{"line":1,"character":6},"end":{"line":1,"character":7}},"severity":1,"source":"wiz","message":"unknown identifier 'b'"},{"range":{"start":{"line":2,"character":6},"end":{"line":2,"character":7}},"severity":3,"source":"wiz","message":"a : def #1"}]}}
t=330 {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file:///a.wiz","version":2,"diagnostics":[{"range":{"start":{"line":1,"character":6},"end":{"line":1,"character":7}},"severity":3,"source":"wiz","message":"b : def #1"},{"range":{"start":{"line":2,"character":6},"end":{"line":2,"character":7}},"severity":1,"source":"wiz","message":"unknown identifier 'a'"}]}}
steps=8
== an identical text reuses everything; appending re-elaborates the last command
t=0 {"jsonrpc":"2.0","id":1,"result":{"capabilities":{"textDocumentSync":1,"positionEncoding":"utf-16","hoverProvider":true,"experimental":{"wizInfoview":{"version":"0.1","methods":["wiz/plainGoal","wiz/plainTermGoal"]}}},"serverInfo":{"name":"wiz-lsp-core","version":"0.1"}}}
t=30 {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file:///a.wiz","version":1,"diagnostics":[{"range":{"start":{"line":1,"character":6},"end":{"line":1,"character":7}},"severity":1,"source":"wiz","message":"unknown identifier 'b'"},{"range":{"start":{"line":2,"character":6},"end":{"line":2,"character":7}},"severity":3,"source":"wiz","message":"a : def #1"}]}}
t=300 {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file:///a.wiz","version":2,"diagnostics":[{"range":{"start":{"line":1,"character":6},"end":{"line":1,"character":7}},"severity":1,"source":"wiz","message":"unknown identifier 'b'"},{"range":{"start":{"line":2,"character":6},"end":{"line":2,"character":7}},"severity":3,"source":"wiz","message":"a : def #1"}]}}
t=610 {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file:///a.wiz","version":3,"diagnostics":[{"range":{"start":{"line":1,"character":6},"end":{"line":1,"character":7}},"severity":1,"source":"wiz","message":"unknown identifier 'b'"},{"range":{"start":{"line":2,"character":6},"end":{"line":2,"character":7}},"severity":3,"source":"wiz","message":"a : def #1"},{"range":{"start":{"line":4,"character":6},"end":{"line":4,"character":7}},"severity":3,"source":"wiz","message":"a : def #1"}]}}
steps=7
== an edit mid-elaboration: stale work dropped, waiting request ContentModified, debounce
t=0 {"jsonrpc":"2.0","id":1,"result":{"capabilities":{"textDocumentSync":1,"positionEncoding":"utf-16","hoverProvider":true,"experimental":{"wizInfoview":{"version":"0.1","methods":["wiz/plainGoal","wiz/plainTermGoal"]}}},"serverInfo":{"name":"wiz-lsp-core","version":"0.1"}}}
t=20 {"jsonrpc":"2.0","id":7,"error":{"code":-32801,"message":"the document changed"}}
t=220 {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file:///a.wiz","version":2,"diagnostics":[{"range":{"start":{"line":1,"character":6},"end":{"line":1,"character":7}},"severity":3,"source":"wiz","message":"a : def #1"}]}}
t=220 {"jsonrpc":"2.0","id":8,"result":{"goal":"a","range":{"start":{"line":1,"character":6},"end":{"line":1,"character":7}}}}
steps=3
== cancel: a waiting request is answered RequestCancelled, an answered one is ignored
t=0 {"jsonrpc":"2.0","id":1,"result":{"capabilities":{"textDocumentSync":1,"positionEncoding":"utf-16","hoverProvider":true,"experimental":{"wizInfoview":{"version":"0.1","methods":["wiz/plainGoal","wiz/plainTermGoal"]}}},"serverInfo":{"name":"wiz-lsp-core","version":"0.1"}}}
t=0 {"jsonrpc":"2.0","id":10,"result":{"contents":{"kind":"plaintext","value":"a : def #1"},"range":{"start":{"line":0,"character":4},"end":{"line":0,"character":5}}}}
t=20 {"jsonrpc":"2.0","id":9,"error":{"code":-32800,"message":"cancelled"}}
t=30 {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file:///a.wiz","version":1,"diagnostics":[{"range":{"start":{"line":1,"character":6},"end":{"line":1,"character":7}},"severity":1,"source":"wiz","message":"unknown identifier 'b'"},{"range":{"start":{"line":2,"character":6},"end":{"line":2,"character":7}},"severity":3,"source":"wiz","message":"a : def #1"}]}}
steps=4
== two documents take turns, one command each
t=0 {"jsonrpc":"2.0","id":1,"result":{"capabilities":{"textDocumentSync":1,"positionEncoding":"utf-16","hoverProvider":true,"experimental":{"wizInfoview":{"version":"0.1","methods":["wiz/plainGoal","wiz/plainTermGoal"]}}},"serverInfo":{"name":"fake","version":"0.1"}}}
t=30 {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file:///b.wiz","version":1,"diagnostics":[{"range":{"start":{"line":0,"character":6},"end":{"line":0,"character":7}},"severity":1,"source":"wiz","message":"unknown identifier 'a'"},{"range":{"start":{"line":1,"character":6},"end":{"line":1,"character":7}},"severity":1,"source":"wiz","message":"unknown identifier 'b'"}]}}
t=40 {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file:///a.wiz","version":1,"diagnostics":[]}}
steps=5
== a document a request waits on goes first; wiz/elaborated when asked
t=0 {"jsonrpc":"2.0","id":1,"result":{"capabilities":{"textDocumentSync":1,"positionEncoding":"utf-16","hoverProvider":true,"experimental":{"wizInfoview":{"version":"0.1","methods":["wiz/plainGoal","wiz/plainTermGoal"]}}},"serverInfo":{"name":"fake","version":"0.1"}}}
t=0 {"jsonrpc":"2.0","id":11,"result":{"capabilities":{"textDocumentSync":1,"positionEncoding":"utf-16","hoverProvider":true,"experimental":{"wizInfoview":{"version":"0.1","methods":["wiz/plainGoal","wiz/plainTermGoal"]}}},"serverInfo":{"name":"fake","version":"0.1"}}}
t=10 {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file:///b.wiz","version":1,"diagnostics":[{"range":{"start":{"line":0,"character":6},"end":{"line":0,"character":7}},"severity":1,"source":"wiz","message":"unknown identifier 'a'"},{"range":{"start":{"line":1,"character":6},"end":{"line":1,"character":7}},"severity":1,"source":"wiz","message":"unknown identifier 'b'"}]}}
t=10 {"jsonrpc":"2.0","method":"wiz/elaborated","params":{"uri":"file:///b.wiz","version":1,"session":2}}
t=10 {"jsonrpc":"2.0","id":12,"result":null}
t=40 {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file:///a.wiz","version":1,"diagnostics":[]}}
t=40 {"jsonrpc":"2.0","method":"wiz/elaborated","params":{"uri":"file:///a.wiz","version":1,"session":1}}
steps=5
== UTF-16 positions: a character outside the BMP counts two
t=0 {"jsonrpc":"2.0","id":1,"result":{"capabilities":{"textDocumentSync":1,"positionEncoding":"utf-16","hoverProvider":true,"experimental":{"wizInfoview":{"version":"0.1","methods":["wiz/plainGoal","wiz/plainTermGoal"]}}},"serverInfo":{"name":"wiz-lsp-core","version":"0.1"}}}
t=20 {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file:///a.wiz","version":1,"diagnostics":[{"range":{"start":{"line":0,"character":0},"end":{"line":0,"character":4}},"severity":2,"source":"wiz","message":"😀😀"},{"range":{"start":{"line":2,"character":6},"end":{"line":2,"character":8}},"severity":3,"source":"wiz","message":"λx : def #1"}]}}
t=100 {"jsonrpc":"2.0","id":13,"result":{"contents":{"kind":"plaintext","value":"λx : def #1"},"range":{"start":{"line":1,"character":4},"end":{"line":1,"character":6}}}}
t=100 {"jsonrpc":"2.0","id":14,"result":{"goal":"λx","range":{"start":{"line":2,"character":6},"end":{"line":2,"character":8}}}}
steps=3
== errors: unknown and interactive methods, unknown document, bad JSON, close, shutdown, exit
t=0 {"jsonrpc":"2.0","id":1,"result":{"capabilities":{"textDocumentSync":1,"positionEncoding":"utf-16","hoverProvider":true,"experimental":{"wizInfoview":{"version":"0.1","methods":["wiz/plainGoal","wiz/plainTermGoal"]}}},"serverInfo":{"name":"wiz-lsp-core","version":"0.1"}}}
t=0 {"jsonrpc":"2.0","id":15,"error":{"code":-32601,"message":"method not found: wiz/interactiveGoals"}}
t=0 {"jsonrpc":"2.0","id":16,"error":{"code":-32602,"message":"document not open: file:///none.wiz"}}
t=0 {"jsonrpc":"2.0","id":null,"error":{"code":-32700,"message":"parse error: expected a key at offset 1"}}
t=10 {"jsonrpc":"2.0","id":17,"error":{"code":-32801,"message":"the document changed"}}
t=10 {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file:///a.wiz","diagnostics":[]}}
t=10 {"jsonrpc":"2.0","id":18,"result":null}
steps=1
== before initialize
t=0 {"jsonrpc":"2.0","id":19,"error":{"code":-32002,"message":"the server is not initialized"}}
"##

/-- The native driver (lib/Lsp/Stdio.wiz) on a pipe: five framed messages and a frame
without `Content-Length` (skipped), then the end of the input; the driver finishes the
due work and returns. The output is framed (`Content-Length`, CR LF). -/
def lspStdioSrc : String := r##"import Lsp.Stdio
import Lsp.Fake
def u : String := "file:///a.wiz"
def frames : List String := [Lsp.Send.initialize 1 .false, Lsp.Send.initialized,
  Lsp.Send.didOpen u 1 "def a\ncheck λ\ncheck a\n", Lsp.Send.position 2 "textDocument/hover" u 0 4,
  Lsp.Send.position 3 "wiz/plainTermGoal" u 2 6]
def writeFrames (w : Fd) : List String → EIO Unit
  | .nil => EIO.pure ()
  | .cons f fs => do
    Fd.write w (Lsp.Stdio.frame f);
    writeFrames w fs
def main : IO Unit := EIO.toIO (do
  p ← Fd.pipe;
  writeFrames p.2 frames;
  Fd.write p.2 (Bytes.ofUtf8 "Content-Type: x\r\n\r\n");
  Fd.close p.2;
  out ← EIO.lift Fd.stdout;
  s ← Lsp.Stdio.run Lsp.loopOf p.1 out (Lsp.Core.init Lsp.fake (Lsp.Config.mk 0 .false "stdio")) Bytes.empty .false;
  Fd.writeUtf8 out (String.join ["\nsteps=", Nat.repr s.steps, "\n"]))
"##

/-- One frame, as `Lsp.Stdio.frame` writes it: `Content-Length` (given literally here,
so a wrong length still fails the case) and its body, the header's two lines ending CR LF
as the protocol's framing requires. -/
def lspStdioFrame (n : Nat) (body : String) : String :=
  String.join ["Content-Length: ", Nat.repr n, "\r\n\r\n", body]

/-- What `lspStdioSrc` prints: the four frames and `steps=3`. This expectation was first
one raw literal, so the blank line after each header held LF; the case then failed on the
separator alone, because the driver writes the protocol's `\r\n` (a terminal shows the two
alike). The driver is right -- a frame is `Content-Length: N\r\n\r\n` and N UTF-8 bytes --
so the expectation spells the separator out. The lengths stay literal, so a wrong one
still fails, and the bodies are raw literals (one line each) for a byte-exact compare. -/
def lspStdioOut : String :=
  String.join [
    lspStdioFrame 265 r##"{"jsonrpc":"2.0","id":1,"result":{"capabilities":{"textDocumentSync":1,"positionEncoding":"utf-16","hoverProvider":true,"experimental":{"wizInfoview":{"version":"0.1","methods":["wiz/plainGoal","wiz/plainTermGoal"]}}},"serverInfo":{"name":"stdio","version":"0.1"}}}"##,
    lspStdioFrame 162 r##"{"jsonrpc":"2.0","id":2,"result":{"contents":{"kind":"plaintext","value":"a : def #1"},"range":{"start":{"line":0,"character":4},"end":{"line":0,"character":5}}}}"##,
    lspStdioFrame 388 r##"{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file:///a.wiz","version":1,"diagnostics":[{"range":{"start":{"line":1,"character":6},"end":{"line":1,"character":7}},"severity":1,"source":"wiz","message":"unknown identifier 'λ'"},{"range":{"start":{"line":2,"character":6},"end":{"line":2,"character":7}},"severity":3,"source":"wiz","message":"a : def #1"}]}}"##,
    lspStdioFrame 120 r##"{"jsonrpc":"2.0","id":3,"result":{"goal":"a","range":{"start":{"line":2,"character":6},"end":{"line":2,"character":7}}}}"##,
    "\nsteps=3\n"]

/-- `lib/Lsp/*.wiz` (concurrency plan E1/E2): the pure language-server core, its pure
event loop and its stdio driver. -/
def lspCoreGroup : Group where
  name := "lsp-core"
  exercise := "lib/Lsp/Core.wiz, Loop.wiz, Fake.wiz, Stdio.wiz (concurrency plan E1/E2)"
  cases := [
    { name := "the library modules check", run := fun _ =>
        okLibs "import Lsp.Core\nimport Lsp.Loop\nimport Lsp.Fake\nimport Lsp.Stdio\n" },
    { name := "positions: commands, code points and UTF-16 columns (#eval)", run := fun _ =>
        okLibs "import Lsp.Fake\n#eval Lsp.splitAll \"def a\\ncheck a\\n  -- still check\\ngoal x\\n\"\n#eval Lsp.posOf (String.chars \"ab\\nc😀d\") 6\n#eval Lsp.offsetOf (String.chars \"ab\\nc😀d\") 1 3\n#eval Lsp.offsetOf (String.chars \"ab\\nc😀d\") 0 9\n"
          [".cons (0, 6) (.cons (6, 31) (.cons (31, 38) .nil))", "(1, 4)", "5", "2"] },
    { name := "scripted sessions: diagnostics, waiting requests, prefix reuse, cancellation, errors", run := fun _ =>
        lspCoreRun lspCoreSrc lspCoreOut },
    { name := "the stdio driver over a pipe: framing, end of input", run := fun _ =>
        lspCoreRun lspStdioSrc lspStdioOut }
  ]

builtin_initialize registerGroup lspCoreGroup

end Tests.Elab
