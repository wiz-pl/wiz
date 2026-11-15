import Tests.Elab

open Wiz

-- The closed terms of the example are normally evaluated at start-up; that would
-- execute unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- The N-master circuit's Verilog through yosys (`check -assert`, `synth_ice40`) when
yosys is on PATH; a design with an unmapped cell or a combinational loop fails here. -/
def hdlArbNSynthesis : IO Unit := do
  let ys ← (do let o ← IO.Process.output { cmd := "yosys", args := #["-V"] }; pure (o.exitCode == 0)) <|> pure false
  unless ys do skip "no yosys"; return
  let src ← IO.FS.readFile "examples/hdl-arb-n.wiz"
  let body := "import Hdl.Core\nimport Hdl.Bus\n" ++ src ++
    "\n#eval Verilog.emit (Circuit.netlist \"arbn2\" (Bus.arbNC 2 8 8))\n" ++
    "#eval Verilog.emit (Circuit.netlist \"arbn3\" (Bus.arbNC 3 8 8))\n" ++
    "#eval Verilog.emit (Circuit.netlist \"arbn4\" (Bus.arbNC 4 8 8))\n"
  let s := runFrontend (R := ZeroOneMany) body { trustedModule := Tests.libModule, loader := ← libLoader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render body
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors: {"\n".intercalate errs.toList}")
  let texts := s.messages.toList.map (·.text)
  let unq (t : String) : String := ((t.drop 1).dropEnd 1).replace "\\n" "\n" |>.replace "\\\"" "\""
  IO.FS.withTempDir fun dir => do
    for t in texts, top in ["arbn2", "arbn3", "arbn4"] do
      IO.FS.writeFile (dir / s!"{top}.v") (unq t)
      let o ← IO.Process.output { cmd := "yosys", args := #["-q", "-p",
        s!"read_verilog {top}.v; check -assert; synth_ice40 -top {top}; tee -q -o {top}.stat stat"], cwd := dir }
      unless o.exitCode == 0 do throw (IO.userError s!"yosys fails on {top}.v:\n{o.stderr}")

/-- The protocol laws of `Hdl.Bus`: valid/ready stability, arbiter mutual exclusion and
progress, decode/route correctness, RAM read-after-write/address stability, and the
`Bus.ReqW` byte strobes. The example checks a Boolean form of each law on generated
inputs and compares the value simulation, `Netlist.simulate` and `Circuit.simFast`.
"Tested, not proved" for everything except the lemmas `Hdl.BusLaw` proves. The N-master
circuit case also checks the synthesisable `Bus.arbNC` against `Bus.arbNStep` and runs
yosys on its Verilog when the tool is available. -/
def hdlBusLawGroup : Group where
  name := "bus-law"
  exercise := "HDL libraries: Hdl.BusLaw (valid/ready laws, arbiter, route, RAM, byte enables)"
  cases := [
    { name := "Hdl.Bus law: stability, arbiter exclusion/progress, route, RAM read-after-write and strobes", run := fun _ => do
        cRunLibs (← IO.FS.readFile "examples/hdl-bus-law.wiz")
          ("route: all laws yes, value = simulate = simFast yes, 4608 inputs\n" ++
           "arb mutex yes, answers only requests yes, stable under stall yes, windows yes, generated matches yes, value = simulate = simFast yes\n" ++
           "arb fast grants 2 1 2 1 2 1 2 1 2 1 2 1 2 1 2 1 yes, hold grants 4 4 4 4 3 4 yes\n" ++
           "n-master pick n=1..4 yes\n" ++
           "n-master step law n=3 yes\n" ++
           "n-master fair n=3, 32 starts yes\n" ++
           "ram read-after-write yes, answered after 2 yes, value = simulate = simFast yes\n" ++
           "ramw strobes yes, value = simulate = simFast yes\n" ++
           "well formed yes\n") },
    { name := "Hdl.Bus N-master circuit: value = Netlist.simulate = simFast for n=2,3,4; value = arbNStep; netlist ownership/progress; yosys when available", run := fun _ => do
        cRunLibs (← IO.FS.readFile "examples/hdl-arb-n.wiz")
          ("n-master circuit selector n=1..4 yes\n" ++
           "n=2 circuit: value = simulate = simFast yes, value = arbNStep yes, netlist law yes, well formed yes, 64 cycles\n" ++
           "n=3 circuit: value = simulate = simFast yes, value = arbNStep yes, netlist law yes, well formed yes, 64 cycles\n" ++
           "n=4 circuit: value = simulate = simFast yes, value = arbNStep yes, netlist law yes, well formed yes, 64 cycles\n" ++
           "n=3 circuit fair, 32 starts yes\n")
        hdlArbNSynthesis }
  ]

builtin_initialize registerGroup hdlBusLawGroup
