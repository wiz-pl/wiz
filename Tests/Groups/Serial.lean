import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- A `Serial` program (lib/Serial.wiz links lib/serial.c), on both backends. -/
def serialRun (body : List String) (expected : String) (defs : String := "") : IO Unit := do
  let src := "import Serial\n" ++ sysBytesShow ++ defs ++ "def main : IO Unit := EIO.toIO (do\n" ++
    ";\n".intercalate (body.map ("  " ++ ·)) ++ ")\n"
  linkRun [("main.wiz", src)] expected
  linkRun [("main.wiz", src)] expected (llvm := true)

def serialTryAll : String := r#"def tryAll (t : Fd) : List SerialConfig → EIO String
  | .nil => EIO.pure ""
  | .cons c cs => do
    Serial.configure t c;
    s ← Serial.settings t;
    rest ← tryAll t cs;
    EIO.pure (String.append (yesNo (SerialSettings.matches s c)) rest)
def bauds : List Baud → List SerialConfig
  | .nil => .nil
  | .cons b bs => .cons (SerialConfig.raw8N1 b) (bauds bs)
"#

def serialGroup : Group where
  name := "serial"
  exercise := "Stage 9k"
  cases := [
    { name := "a pseudo-terminal: every byte value both ways, raw settings read back", run := fun _ =>
        serialRun ["pty ← Pty.open", "let all := Bytes.range 256",
          "t ← Serial.open pty.path (SerialConfig.raw8N1 .b115200)",
          "s ← Serial.settings t", "say (yesNo (SerialSettings.matches s (SerialConfig.raw8N1 .b115200)))",
          "say (yesNo s.raw)", "say (Nat.toString s.minBytes)",
          "Fd.write t all", "Fd.write t all",
          "h ← Fd.readExactlyWithin pty.controller 512 (Duration.seconds 5)",
          "say (gotShow (Bytes.append all all) h)",
          "Fd.write pty.controller all", "Serial.drain pty.controller",
          "k ← Fd.readExactlyWithin t 256 (Duration.seconds 5)", "say (gotShow all k)",
          "Fd.close t", "e ← Fd.readWithin pty.controller 10 (Duration.seconds 5)",
          r#"say (match e with | .ready .none => "end" | .ready (.some _) => "data?" | .timedOut => "timed out")"#,
          "Fd.close pty.controller"]
          "yes\nyes\n1\nall yes\nall yes\nend\n" },
    { name := "a terminal that does not answer in time", run := fun _ =>
        serialRun ["pty ← Pty.open",
          "t ← Serial.open pty.path (SerialConfig.raw8N1 .b9600)",
          "t0 ← EIO.lift Clock.monotonic",
          "q ← Fd.readExactlyWithin t 3 (Duration.millis 300)", "t1 ← EIO.lift Clock.monotonic",
          "say (gotShow Bytes.empty q)", "say (yesNo (Duration.lt (Duration.millis 250) (Duration.sub t1 t0)))",
          "Fd.write pty.controller (Bytes.ofUtf8 \"ab\")",
          "r ← Fd.readExactlyWithin t 3 (Duration.millis 300)", "say (gotShow Bytes.empty r)",
          "Fd.write pty.controller (Bytes.ofUtf8 \"stale\")", "Serial.discard t .input",
          "w ← Fd.readWithin t 10 (Duration.millis 100)",
          r#"say (match w with | .timedOut => "nothing left" | .ready _ => "data?")"#,
          "Fd.close t", "Fd.close pty.controller"]
          "timeout after 0\nyes\ntimeout after 2\nnothing left\n" },
    { name := "settings: every rate, stop bits and flow control read back; errors", run := fun _ =>
        serialRun ["pty ← Pty.open", "t ← Fd.open pty.path .readWrite OpenFlags.device",
          "s0 ← Serial.settings t", "say (yesNo s0.raw)",
          "r ← tryAll t (List.append (bauds Baud.all) (.cons (SerialConfig.mk .b9600 .eight .none .two .none) (.cons (SerialConfig.mk .b57600 .eight .none .one .rtsCts) (.cons (SerialConfig.mk .b19200 .eight .none .two .xonXoff) .nil))))",
          "say r", "s ← Serial.settings t",
          r#"say (match s.baud with | .some b => Nat.toString (Baud.bitsPerSecond b) | .none => "?")"#,
          "say (Nat.toString s.stopBits)", "say (yesNo s.xonXoff)",
          r#"say (match Baud.ofBitsPerSecond 115200 with | .some b => Nat.toString (Baud.toIndex b) | .none => "?")"#,
          r#"say (match Baud.ofBitsPerSecond 115201 with | .some b => "?" | .none => "not standard")"#,
          "q ← EIO.lift (Serial.configure t (SerialConfig.mk .b9600 .seven .even .one .none))",
          r#"say (match q with | .ok _ => "7E1 kept?" | .error m => m)"#,
          "p ← Fd.pipe", "e ← EIO.lift (Serial.configure p.1 (SerialConfig.raw8N1 .b9600))",
          r#"say (match e with | .ok _ => "?" | .error m => m)"#,
          "a ← EIO.lift (Serial.isTty t)", "b ← EIO.lift (Serial.isTty p.2)",
          "say (String.append (yesNo a) (yesNo b))",
          r#"n ← EIO.lift (Serial.open "/nonexistent/tty" (SerialConfig.raw8N1 .b9600))"#,
          r#"say (match n with | .ok _ => "?" | .error m => m)"#,
          "Fd.close t", "Fd.close pty.controller"]
          ("no\nyesyesyesyesyesyesyesyesyesyesyesyesyesyesyesyesyes\n19200\n2\nyes\n7\nnot standard\n" ++
           "configure terminal: the device did not keep these settings (a pseudo-terminal is always 8 data bits without parity)\n" ++
           "configure terminal: Inappropriate ioctl for device\nyesno\n/nonexistent/tty: No such file or directory\n")
          serialTryAll }
  ]

builtin_initialize registerGroup serialGroup

end Tests.Elab
