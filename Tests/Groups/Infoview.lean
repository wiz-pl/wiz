import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-! ## 11m–n: JSON and the infoview's layout (lib/Json.wiz, lib/Infoview.wiz) -/

/-- Elaborate with `Prelude`, `Json` and `Infoview` importable; no errors, and these infos. -/
def okInfoview (input : String) (infos : List String := []) : IO Unit := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let json ← IO.FS.readFile "lib/Json.wiz"
  let iv ← IO.FS.readFile "lib/Infoview.wiz"
  let tagged ← IO.FS.readFile "lib/Tagged.wiz"
  let textLib ← IO.FS.readFile "lib/Text.wiz"
  let loader : Name → Option String := fun m =>
    if m == "Prelude" then some prelude else if m == "Json" then some json
    else if m == "Infoview" then some iv else if m == "Tagged" then some tagged
    else if m == "Text" then some textLib else none
  let s := runFrontend (R := ZeroOneMany) input { loader, trustedModule := Tests.libModule }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render input
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  checkEq (repr infos).pretty (repr (s.messages.toList.map (·.text))).pretty

def jsonPrelude : String := r#"import Json
def parsed (s : String) : String := match Json.parse s with
  | .ok j => Json.render j
  | .error e => e
"#

/-- Goals built by hand (`A : Type`, `f : Nat → Nat → Nat → Nat` ⊢ `Nat → A`). -/
def goalPrelude : String := r#"import Infoview
def nat (r : Nat) : TT := .tag r "const" "Nat" (.text "Nat")
def arrow (r : Nat) (a b : TT) : TT := .tag r "pi" "" (.append (.cons a (.cons (.text " → ") (.cons b .nil))))
def hA : Hyp := .mk (.cons "A" .nil) (.tag 1 "sort" "" (.text "Type")) .none
def hf : Hyp := .mk (.cons "f" .nil) (arrow 2 (nat 3) (arrow 4 (nat 5) (arrow 6 (nat 7) (nat 8)))) .none
def g : Goal := .mk "" (.cons hA (.cons hf .nil)) (arrow 9 (nat 10) (.tag 11 "var" "A" (.text "A")))
def v : View := View.ofState 80 (.some (.cons g .nil)) .none
def esc (s : String) : List Char := .cons (Char.mk 27) (String.chars s)
"#

def infoviewGroup : Group where
  name := "infoview"
  exercise := "lib/Json.wiz, lib/Infoview.wiz (stages 11m, 11n)"
  cases := [
    { name := "JSON: printing escapes quotes, newlines; integers keep their sign", run := fun _ =>
        okInfoview (jsonPrelude ++ r#"#eval Json.render (Json.mkArr (.cons (.int .true 42) (.cons (.str "a\"b\nλ") (.cons .null .nil))))"#)
          [r#""[-42,\"a\\\"b\\nλ\",null]""#] },
    { name := "JSON: parse and print again (numbers, escapes, surrogate pairs, empty containers)", run := fun _ =>
        okInfoview (jsonPrelude ++ r#"#eval parsed " {\"a\": [1, -2, 3.5e10, -0.25E-3, true, null, {}], \"b\": \"\\u03bb\\ud83d\\ude00\\/\\t\", \"c\": []} ""#)
          [r#""{\"a\":[1,-2,3.5e10,-0.25E-3,true,null,{}],\"b\":\"λ😀/\\t\",\"c\":[]}""#] },
    { name := "JSON: ASCII output escapes non-ASCII, as surrogate pairs above U+FFFF", run := fun _ =>
        okInfoview (jsonPrelude ++ r#"#eval match Json.parse "\"\\u03bb\\ud83d\\ude00\\u0001\"" with
  | .ok j => Json.renderAscii j
  | .error e => e
#eval parsed "\"\\ud800x\"""#)
          [r#""\"\\u03bb\\ud83d\\ude00\\u0001\"""#, r#""\"�x\"""#] },
    { name := "JSON: errors say what and where", run := fun _ =>
        okInfoview (jsonPrelude ++ "#eval parsed \"[1, 2,]\"\n#eval parsed \"01\"\n#eval parsed \"[1] 2\"\n#eval parsed \"\\\"abc\"\n#eval parsed \"1.e5\"")
          [r#""unexpected character at offset 6""#, r#""bad number at offset 0""#, r#""trailing characters at offset 4""#,
           r#""unterminated string at offset 4""#, r#""bad number at offset 1""#] },
    { name := "JSON: paths into objects; decimal printing", run := fun _ =>
        okInfoview (jsonPrelude ++ r#"def path (s : String) : Option Json := match Json.parse s with
  | .ok j => Json.getPath j (.cons "x" (.cons "y" .nil))
  | .error _ => .none
#eval path "{\"x\": {\"y\": 7}}"
#eval Nat.repr 1234567890123"#)
          [".some (.int .false 7)", r#""1234567890123""#] },
    { name := "tagged text from JSON (the protocol's shape)", run := fun _ =>
        okInfoview (goalPrelude ++ r#"#eval match Json.parse "{\"tag\": [{\"ref\": 4, \"kind\": \"const\", \"name\": \"Nat\"}, {\"append\": [{\"text\": \"N\"}, {\"text\": \"at\"}]}]}" with
  | .ok j => TT.toString (TT.ofJson j)
  | .error e => e"#) [r#""Nat""#] },
    { name := "goals laid out, and wrapped with a hanging indent", run := fun _ =>
        okInfoview (goalPrelude ++ "#eval Infoview.plainLines (View.lines v)\n" ++
          "#eval Infoview.plainLines (View.lines (View.ofState 16 (.some (.cons g .nil)) (.some (.mk \"\" .nil (nat 12)))))")
          [r#".cons "Tactic state" (.cons "A : Type" (.cons "f : Nat → Nat → Nat → Nat" (.cons "⊢ Nat → A" .nil)))"#,
           r#".cons "Tactic state" (.cons "A : Type" (.cons "f : Nat → Nat →" (.cons "    Nat → Nat" (.cons "⊢ Nat → A" (.cons "" (.cons "Expected type" (.cons "⊢ Nat" .nil)))))))"#] },
    { name := "the messages of the tactic at the cursor (trace, trace_state), under the goals", run := fun _ =>
        okInfoview (goalPrelude ++ "#eval Infoview.plainLines (View.lines (View.ofTacState 30 (.some (.mk (.cons g .nil) (.cons \"hello\" (.cons \"n : Nat\\n⊢ Nat\" .nil)))) .none))\n" ++
          "#eval Infoview.htmlTacState 0 (.some (.mk .nil (.cons \"a<b\" .nil))) .none\n" ++
          "def msgsOf : TacView → List String\n  | .mk _ ms => ms\n" ++
          "#eval match Json.parse \"{\\\"goals\\\": [], \\\"messages\\\": [\\\"one\\\", \\\"two\\\"]}\" with\n  | .ok j => msgsOf (TacView.ofJson j)\n  | .error e => List.cons e List.nil")
          [r#".cons "Tactic state" (.cons "A : Type" (.cons "f : Nat → Nat → Nat → Nat" (.cons "⊢ Nat → A" (.cons "" (.cons "Messages" (.cons "hello" (.cons "" (.cons "n : Nat" (.cons "⊢ Nat" .nil)))))))))"#,
           r#""<h3>Tactic state</h3><div class=\"no-goals\">No goals</div><h3>Messages</h3><pre class=\"message\">a&lt;b</pre>""#,
           r#".cons "one" (.cons "two" .nil)"#] },
    { name := "11w: what else is at the cursor (wiz/interactiveInfo): sections, as text and HTML", run := fun _ =>
        okInfoview (goalPrelude ++ r#"def items : List InfoItem := .cons (.mk "syntax" "syntax term.twice" "syntax \"twice\" term : term" .none)
  (.cons (.mk "expansion" "expanded by macro rule" "Nat.add a\nb" .none)
  (.cons (.mk "instance" "instance i" "i" (.some (nat 1)))
  (.cons (.mk "declaration" "four" "" (.some (nat 2))) .nil)))
#eval Infoview.plainLines (View.lines (View.ofInfo 40 .none .none items))
#eval Infoview.plainLines (View.lines (View.ofInfo 40 (.some (.mk .nil .nil)) .none (.cons (.mk "message" "info" "3" .none) .nil)))
#eval Infoview.htmlInfo 0 .none .none (.cons (.mk "declaration" "x<y" "" (.some (nat 1))) .nil)
#eval match Json.parse "{\"items\": [{\"kind\": \"import\", \"title\": \"import M\", \"text\": \"lib/M.wiz\", \"type\": null}], \"session\": 1}" with
  | .ok j => List.length (Items.ofJson j)
  | .error _ => 0"#)
          [r#".cons "Syntax" (.cons "syntax term.twice" (.cons "  syntax \"twice\" term : term" (.cons "expanded by macro rule" (.cons "  Nat.add a" (.cons "  b" (.cons "" (.cons "Instances" (.cons "i : Nat" (.cons "" (.cons "Declarations" (.cons "four : Nat" .nil)))))))))))"#,
           r#".cons "Tactic state" (.cons "No goals" (.cons "" (.cons "Messages" (.cons "info" (.cons "  3" .nil)))))"#,
           r#""<h3>Declarations</h3><div class=\"item\"><span class=\"names\">x&lt;y</span> : <span class=\"tt k-const\" data-ref=\"1\" data-idx=\"0\" title=\"Nat\">Nat</span></div>""#,
           "1"] },
    { name := "terminal lines: SGR colours by kind, the selection in reverse video", run := fun _ =>
        okInfoview (goalPrelude ++ "#eval Infoview.ansiLines 3 (View.lines (View.ofState 80 (.some .nil) (.some (.mk \"h\" .nil (arrow 1 (nat 2) (nat 3))))))")
          [r#".cons "\x1b[0;1;4mTactic state\x1b[0m" (.cons "\x1b[0;1;32mNo goals\x1b[0m" (.cons "\x1b[0m" (.cons "\x1b[0;1;4mExpected type\x1b[0m" (.cons "\x1b[0;1;4mcase h\x1b[0m" (.cons "\x1b[0;1;35m⊢\x1b[0m \x1b[0;34mNat\x1b[0m \x1b[0m→\x1b[0m \x1b[0;34;7mNat\x1b[0m" .nil)))))"#] },
    { name := "HTML: data-ref and data-idx on every subterm, text escaped", run := fun _ =>
        okInfoview (goalPrelude ++ "#eval Infoview.htmlState 2 .none (.some (.mk \"\" (.cons (.mk (.cons \"x\" .nil) (nat 1) .none) .nil) (.tag 2 \"var\" \"x<y\" (.text \"a&b\"))))")
          [r#""<h3>Expected type</h3><div class=\"goal\"><div class=\"hyp\"><span class=\"names\">x</span> : <span class=\"tt k-const\" data-ref=\"1\" data-idx=\"0\" title=\"Nat\">Nat</span></div><div class=\"target\"><span class=\"turnstile\">⊢</span> <span class=\"tt k-var sel\" data-ref=\"2\" data-idx=\"1\" title=\"x&lt;y\">a&amp;b</span></div></div>""#] },
    { name := "navigation: out, into, previous (wrapping), out at the top", run := fun _ =>
        okInfoview (goalPrelude ++ "#eval View.navigate v 4 .out\n#eval View.navigate v 2 .into\n#eval View.navigate v 0 .prev\n#eval View.navigate v 1 .out")
          ["2", "3", "11", "1"] },
    { name := "framing: Content-Length counts UTF-8 bytes; a partial message waits", run := fun _ =>
        okInfoview (goalPrelude ++ r#"#eval Rpc.frame "{\"a\":\"λ\"}"
#eval Rpc.unframe (String.chars (String.append (Rpc.frame "{\"a\":\"λ\"}") "Content-Le"))
#eval Rpc.unframe (String.chars (String.append "Content-Length: 12" (String.mk (.cons (Char.mk 13) (.cons (Char.mk 10) (.cons (Char.mk 13) (.cons (Char.mk 10) (String.chars "{\"a\":\"λ\"}"))))))))"#)
          [r#""Content-Length: 10\x0d\n\x0d\n{\"a\":\"λ\"}""#,
           r#".some ("{\"a\":\"λ\"}", .cons (.mk 67) (.cons (.mk 111) (.cons (.mk 110) (.cons (.mk 116) (.cons (.mk 101) (.cons (.mk 110) (.cons (.mk 116) (.cons (.mk 45) (.cons (.mk 76) (.cons (.mk 101) .nil))))))))))"#,
           ".none"] },
    { name := "keys: arrows, SGR mouse reports, page keys; terminal widths", run := fun _ =>
        okInfoview (goalPrelude ++ "#eval Key.decode (List.append (esc \"[A\") (List.append (String.chars \"\\tq\") (List.append (esc \"[<0;5;3M\") (esc \"[6~\"))))\n" ++
          "#eval Infoview.width (String.chars \"aλ😀́b\")")
          [".cons .up (.cons (.char 9) (.cons (.char 113) (.cons (.mouse 0 5 3 .true) (.cons .pageDown .nil))))", "5"] },
    { name := "the terminal infoview against a stub server, as text and in a pty (infoview/test.sh)", run := fun _ => do
        let tc ← toolchain
        let env := #[("WIZ_CFLAGS", some (" ".intercalate tc.cflags)), ("WIZ_LDFLAGS", some (" ".intercalate tc.ldflags))]
        let out ← IO.Process.output { cmd := "sh", args := #["infoview/test.sh"], env := env }
        unless out.exitCode == 0 do
          if ((out.stdout ++ out.stderr).splitOn "gmp.h").length > 1 then skip "no toolchain"
          else throw (IO.userError s!"infoview/test.sh failed:\n{out.stdout}{out.stderr}") }
  ]

builtin_initialize registerGroup infoviewGroup

end Tests.Elab
