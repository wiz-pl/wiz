import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- `lib/Args.wiz` (the CLI parser): pure, so `#eval` runs it. One case pins every rule
of the module's documentation, including the exact usage messages. -/
def argsGroup : Group where
  name := "args"
  exercise := "lib/Args.wiz (CLI parser)"
  parallel := true
  cases := [
    { name := "long, short, clustered, --, positionals, subcommands and every error message", run := fun _ =>
        okLibs (r#"import Args
import Text

def spec : Args.Spec :=
  Args.Spec.mk
    [ Args.Flag.arg "mem" "m"
    , Args.Flag.on "verbose" "v"
    , Args.Flag.on "all" "a"
    , Args.Flag.on "brief" "b"
    , Args.Flag.arg "color" "" ]
    ["build", "check", "run"]

def val (r : Except Args.Usage Args.Parsed) (name : String) : String :=
  match r with
  | .ok p => match Args.Parsed.value p name with
    | .some v => v
    | .none => "(unset)"
  | .error u => "!" ++ Args.Usage.message u

def flag (r : Except Args.Usage Args.Parsed) (name : String) : String :=
  match r with
  | .ok p => match Args.Parsed.has p name with
    | .true => "yes"
    | .false => "no"
  | .error u => "!" ++ Args.Usage.message u

def cmd (r : Except Args.Usage Args.Parsed) : String :=
  match r with
  | .ok p => match p.command with
    | .some c => c
    | .none => "(none)"
  | .error u => "!" ++ Args.Usage.message u

def pos (r : Except Args.Usage Args.Parsed) : String :=
  match r with
  | .ok p => String.intercalate "," p.positionals
  | .error u => "!" ++ Args.Usage.message u

def msg (r : Except Args.Usage Args.Parsed) : String :=
  match r with
  | .ok _ => "ok"
  | .error u => Args.Usage.message u

def valueCount (r : Except Args.Usage Args.Parsed) (name : String) : String :=
  match r with
  | .ok p => Nat.repr (List.length (List.filter (fun kv => String.eq kv.1 name) p.values))
  | .error u => "!" ++ Args.Usage.message u

def switchCount (r : Except Args.Usage Args.Parsed) (name : String) : String :=
  match r with
  | .ok p => Nat.repr (List.length (List.filter (fun s => String.eq s name) p.switches))
  | .error u => "!" ++ Args.Usage.message u

-- long flags, both forms; a value may contain '='
#eval val (Args.parse spec ["--mem", "6G"]) "mem"
#eval val (Args.parse spec ["--mem=6G"]) "mem"
#eval val (Args.parse spec ["--mem=a=b"]) "mem"
-- short flags, both forms, and a long-only flag
#eval val (Args.parse spec ["-m", "4G"]) "mem"
#eval val (Args.parse spec ["-m4G"]) "mem"
#eval val (Args.parse spec ["--color", "red"]) "color"
-- clustered switches, and a value flag taking the rest of the cluster
#eval flag (Args.parse spec ["-ab"]) "all"
#eval flag (Args.parse spec ["-ab"]) "brief"
#eval flag (Args.parse spec ["-vab"]) "verbose"
#eval val (Args.parse spec ["-vm6G"]) "mem"
#eval flag (Args.parse spec ["-vm6G"]) "verbose"
-- `--` terminates flags; the same text is positional
#eval pos (Args.parse spec ["build", "--", "--mem", "x"])
#eval val (Args.parse spec ["build", "--", "--mem", "x"]) "mem"
-- positionals in order, the first one the subcommand; flags may follow them
#eval cmd (Args.parse spec ["build", "one", "two"])
#eval pos (Args.parse spec ["build", "one", "two"])
#eval cmd (Args.parse spec ["--mem=1G", "run", "x"])
#eval pos (Args.parse spec ["--mem=1G", "run", "x"])
#eval pos (Args.parse spec ["build", "-"])
#eval val (Args.parse spec ["build", "x", "--mem", "6G"]) "mem"
#eval pos (Args.parse spec ["build", "x", "--mem", "6G"])
-- a value flag takes the next argument unconditionally (as grailOpts does)
#eval val (Args.parse spec ["--mem", "--fast"]) "mem"
-- the exact usage errors
#eval msg (Args.parse spec ["--bogus"])
#eval msg (Args.parse spec ["-abx"])
#eval msg (Args.parse spec ["--mem"])
#eval msg (Args.parse spec ["-m"])
#eval msg (Args.parse spec ["--all=yes"])
#eval msg (Args.parse spec ["frobnicate"])
-- repeated flags: the last value wins, and is stored once; switches idempotent
#eval val (Args.parse spec ["--mem", "1G", "-m", "8G"]) "mem"
#eval valueCount (Args.parse spec ["--mem", "1G", "-m", "8G"]) "mem"
#eval switchCount (Args.parse spec ["-a", "--all"]) "all"
"#)
        [r#""6G""#, r#""6G""#, r#""a=b""#, r#""4G""#, r#""4G""#, r#""red""#,
         r#""yes""#, r#""yes""#, r#""yes""#, r#""6G""#, r#""yes""#,
         r#""--mem,x""#, r#""(unset)""#,
         r#""build""#, r#""one,two""#, r#""run""#, r#""x""#, r#""-""#,
         r#""6G""#, r#""x""#,
         r#""--fast""#,
         r#""unknown flag: --bogus""#, r#""unknown flag: -x""#,
         r#""flag needs a value: --mem""#, r#""flag needs a value: -m""#,
         r#""flag takes no value: --all""#, r#""unknown command: frobnicate""#,
         r#""8G""#, r#""1""#, r#""1""#] }
  ]

builtin_initialize registerGroup argsGroup

end Tests.Elab
