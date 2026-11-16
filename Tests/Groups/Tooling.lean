import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

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
    { name := "22m: the target is part of the cache key (--target/--ptr-bits/--endian)", run := fun _ => do
        let t0 : Toolchain := {}
        let t1 : Toolchain := { t0 with target := "aarch64-unknown-linux-gnu" }
        let t2 : Toolchain := { t0 with ptrBits := 32 }
        let t3 : Toolchain := { t0 with endian := "big" }
        check (t0.id != t1.id && t0.id != t2.id && t0.id != t3.id) "the target is not in the toolchain id"
        check (t0.targetId != t1.targetId && t0.targetId != t2.targetId && t0.targetId != t3.targetId)
          "the target id does not change"
        -- the flags set the fields, and round-trip
        let (t, rest) := t0.parseFlags ["--target", "aarch64-unknown-linux-gnu", "--ptr-bits", "32",
          "--endian", "big", "check", "f.wiz"]
        checkEq ["check", "f.wiz"] rest
        checkEq "aarch64-unknown-linux-gnu" t.target
        checkEq 32 t.ptrBits
        checkEq "big" t.endian
        check (t.toFlags.contains "--target" && (t.toFlags.contains "32") && (t.toFlags.contains "big"))
          s!"the flags do not round-trip: {t.toFlags}"
        check (((t.render).splitOn "target aarch64-unknown-linux-gnu").length > 1) "render has no target"
        check ((t0.set "ptr-bits" "48").isNone) "a 48-bit pointer width was accepted"
        -- two targets in one cache directory do not share entries
        let prelude ← IO.FS.readFile "lib/Prelude.wiz"
        let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, loader := fun m => if m == "Prelude" then some prelude else none }
        let src := "import Prelude\ndef two : Nat := 1 + 1\n#eval two\n"
        let dir ← IO.FS.createTempDir
        let (_, h1) ← Cache.elaborateCached (some dir) [] src init 0 (toolchain := t0.id)
        let (_, h2) ← Cache.elaborateCached (some dir) [] src init 0 (toolchain := t0.id)
        let (_, h3) ← Cache.elaborateCached (some dir) [] src init 0 (toolchain := t1.id)
        checkEq 0 h1
        check (h2 > 0) "the same target got nothing from the cache"
        checkEq 0 h3 },
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
        check ((out[0]!.compress.splitOn "Nat : Type").length > 1) s!"no hover: {out[0]!.compress}" }
  ]

builtin_initialize registerGroup toolingGroup

end Tests.Elab
