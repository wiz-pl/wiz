import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- `lib/Json.wiz` (stage 11m): the printer and the parser, pure, so `#eval` runs them.
The output is fixed byte for byte: the tests here are the regression net for the
`Nat.div`/`Nat.mod` hex escapes and for lib/Text.wiz's helpers. -/
def jsonGroup : Group where
  name := "json"
  exercise := "lib/Json.wiz (stage 11m)"
  parallel := true
  cases := [
    { name := "a non-trivial document renders byte for byte (integers, decimals, escapes, λ and 😀)", run := fun _ =>
        let src := r#"import Json
def doc : Json := Json.mkObj (.cons ("id", Json.ofNat 1234567890123) (.cons ("ok", .bool .true)
  (.cons ("xs", Json.mkArr (.cons (.int .true 2) (.cons (.int .false 0) (.cons (.dec "-0.25E-3") (.cons (.dec "3.5e10") .nil)))))
  (.cons ("s", .str "λ😀\n\t\"\\") (.cons ("o", Json.mkObj (.cons ("k", .null) .nil))
  (.cons ("e", Json.mkArr .nil) (.cons ("z", .int .true 0) .nil)))))))
def rt (s : String) : String := match Json.parse s with
  | .ok j => Json.render j
  | .error e => e
#eval Json.render doc
#eval Json.renderAscii doc
#eval rt (Json.render doc)
"#
        okLibs src [r#""{\"id\":1234567890123,\"ok\":true,\"xs\":[-2,0,-0.25E-3,3.5e10],\"s\":\"λ😀\\n\\t\\\"\\\\\",\"o\":{\"k\":null},\"e\":[],\"z\":0}""#,
     r#""{\"id\":1234567890123,\"ok\":true,\"xs\":[-2,0,-0.25E-3,3.5e10],\"s\":\"\\u03bb\\ud83d\\ude00\\n\\t\\\"\\\\\",\"o\":{\"k\":null},\"e\":[],\"z\":0}""#,
     r#""{\"id\":1234567890123,\"ok\":true,\"xs\":[-2,0,-0.25E-3,3.5e10],\"s\":\"λ😀\\n\\t\\\"\\\\\",\"o\":{\"k\":null},\"e\":[],\"z\":0}""#] },
    { name := "the four hex digits of \\u escapes: 4095, 4096 and 65535 render in place", run := fun _ =>
        let src := r#"import Json
#eval Json.render (Json.mkArr (.cons (Json.ofNat 4095) (.cons (Json.ofNat 4096) (.cons (Json.ofNat 65535) .nil))))
#eval match Json.parse "\"\\uFFFF\\u0000\\u0010\\u0100\\u1000\\ud800\\udc00\\udbff\\udfff\"" with
  | .ok j => Json.renderAscii j
  | .error e => e
"#
        okLibs src [r#""[4095,4096,65535]""#,
     r#""\"\\uffff\\u0000\\u0010\\u0100\\u1000\\ud800\\udc00\\udbff\\udfff\"""#] },
    { name := "parse and render again: a mixed document and deep nesting", run := fun _ =>
        let src := r#"import Json
def rt (s : String) : String := match Json.parse s with
  | .ok j => Json.render j
  | .error e => e
#eval rt "{\"a\": [1, -2, 3.5e10, -0.25E-3, true, null, {}], \"b\": \"\\u03bb\\ud83d\\ude00\\/\\t\", \"c\": []}"
#eval rt " { \"deep\": [[[[{\"n\": 1}]]]] } "
"#
        okLibs src [r#""{\"a\":[1,-2,3.5e10,-0.25E-3,true,null,{}],\"b\":\"λ😀/\\t\",\"c\":[]}""#,
     r#""{\"deep\":[[[[{\"n\":1}]]]]}""#] }
  ]

builtin_initialize registerGroup jsonGroup

end Tests.Elab
