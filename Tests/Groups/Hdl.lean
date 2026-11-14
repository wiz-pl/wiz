import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- A user-declared `ShareLet` (no HDL library): the hook fires on a `let` in check mode
with no explicit quantity, and only when an instance exists. -/
def shareLetHook : String := "import Prelude
structure W where
  n : Nat
class ShareLet (A B : Type) where
  share : A → (A → B) → B
instance : ShareLet W W where
  share := fun x f => f (W.mk (x.n + 100))
def t1 : W := let y := W.mk 1; y
def t2 : W := let ω y := W.mk 1; y
def t3 : Nat := let y := 1; y
#eval t1.n
#eval t2.n
#eval t3
"

/-- Circuits whose Verilog the `hdl` group looks at: a counter (non-zero initial value), a
64-bit state (an initial value above 2^32) and a circuit with an input and a pair state. -/
def hdlVerilogSrc : String := "import Hdl.Core
def u8 : HwTy := HwTy.bits 8
def c1 : Circuit (HwTy.bits 1) u8 := Circuit.mk u8 (BitVec.ofNat 8 250) (fun s u => Hw.pair (Hw.add s (Hw.lit 8 1)) s)
def v1 : String := Verilog.emit (Circuit.netlist \"counter\" c1)
def u64 : HwTy := HwTy.bits 64
def c2 : Circuit u8 u64 := Circuit.mk u64 (BitVec.ofNat 64 13835062455471964160) (fun s x => Hw.pair (Hw.add s (Hw.lit 64 1)) s)
def v2 : String := Verilog.emit (Circuit.netlist \"wide\" c2)
def c3 : Circuit u8 u8 := Circuit.mk (HwTy.prod u8 u8) (BitVec.ofNat 8 1, BitVec.ofNat 8 2)
  (fun s x => Hw.pair (Hw.pair x (Hw.fst s)) (Hw.mux (Hw.ult x (Hw.snd s)) (Hw.fst s) (Hw.sub x (Hw.snd s))))
def v3 : String := Verilog.emit (Circuit.netlist \"pairs\" c3)
"

/-- The memories of examples/hdl-mem.wiz through Icarus (the RAM's test bench) and yosys
(block RAM inferred for the RAM and a 256-word ROM), each when it is on PATH. -/
def hdlMemTools : IO Unit := do
    let has (c : String) : IO Bool := (do let o ← IO.Process.output { cmd := c, args := #["-V"] }; pure (o.exitCode == 0)) <|> pure false
    let iv ← has "iverilog"
    let ys ← (do let o ← IO.Process.output { cmd := "yosys", args := #["-V"] }; pure (o.exitCode == 0)) <|> pure false
    unless iv || ys do skip "no iverilog, no yosys"; return
    let src ← IO.FS.readFile "examples/hdl-mem.wiz"
    let s := runFrontend (R := ZeroOneMany) (src ++ "\n#eval vRom\n#eval tbRam\n#eval vecRam\n" ++
        "def big : HwTy.El (HwTy.mem 8 8) := fun (a : BitVec 8) => BitVec.ofNat 8 (Nat.mul a.toNat 3)\n" ++
        "def bigC : Circuit (HwTy.bits 8) B8 := Circuit.mk B8 (BitVec.ofNat 8 0) (fun s a => Hw.pair (Hw.memRead (Hw.const (HwTy.mem 8 8) big) a) s)\n" ++
        "#eval Verilog.emit (Circuit.netlist \"rom\" bigC)\n")
      { trustedModule := Tests.libModule, loader := ← libLoader }
    let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render ""
    unless errs.isEmpty do throw (IO.userError s!"unexpected errors: {errs}")
    let texts := (s.messages.toList.map (·.text)).drop 4
    let unq (t : String) : String := ((t.drop 1).dropRight 1).replace "\\n" "\n" |>.replace "\\\"" "\""
    IO.FS.withTempDir fun dir => do
      let names := ["ram.v", "rom.v", "tb.v", "ram.vec", "rom256.v"]
      for t in texts, nm in names do IO.FS.writeFile (dir / nm) (unq t)
      if iv then
        let o ← IO.Process.output { cmd := "iverilog", args := #["-g2005", "-o", (dir / "tb.vvp").toString, (dir / "tb.v").toString, (dir / "ram.v").toString], cwd := dir }
        unless o.exitCode == 0 do throw (IO.userError s!"iverilog rejects the RAM bench:\n{o.stderr}")
        let r ← IO.Process.output { cmd := "vvp", args := #["-n", (dir / "tb.vvp").toString], cwd := dir }
        unless (r.stdout.splitOn "PASS ram: 7 cycles").length > 1 do throw (IO.userError s!"RAM bench: {r.stdout}{r.stderr}")
      if ys then
        for (f, top) in [("ram.v", "ram"), ("rom256.v", "rom")] do
          let o ← IO.Process.output { cmd := "yosys", args := #["-q", "-p", s!"read_verilog {f}; synth_ice40 -top {top}; tee -o stat.txt stat"], cwd := dir }
          unless o.exitCode == 0 do throw (IO.userError s!"yosys fails on {f}:\n{o.stderr}")
          let st ← IO.FS.readFile (dir / "stat.txt")
          unless (st.splitOn "SB_RAM40_4K").length > 1 do throw (IO.userError s!"no block RAM inferred for {f}:\n{st}")

/-- examples/hdl-arty.wiz through the front end: its eight `#eval` texts (four about the
board's pin constraints, then four Verilog modules). -/
def hdlArtyTexts : IO (List String) := do
    let src ← IO.FS.readFile "examples/hdl-arty.wiz"
    let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := ← libLoader }
    let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
    unless errs.isEmpty do throw (IO.userError s!"unexpected errors: {errs}")
    pure (s.messages.toList.map (·.text))

/-- The pin constraints of examples/hdl-arty.wiz: the "\"set_property -dict { PACKAGE_PIN E3 IOSTANDARD LVCMOS33 } [get_ports { clk }]\\ncreate_clock -period 10.000 -name clk [get_ports { clk }]\\nset_property -dict { PACKAGE_PIN D9 IOSTANDARD LVCMOS33 } [get_ports { btn[0] }]\\nset_property -dict { PACKAGE_PIN C9 IOSTANDARD LVCMOS33 } [get_ports { btn[1] }]\\nset_property -dict { PACKAGE_PIN B9 IOSTANDARD LVCMOS33 } [get_ports { btn[2] }]\\nset_property -dict { PACKAGE_PIN B8 IOSTANDARD LVCMOS33 } [get_ports { btn[3] }]\\nset_property -dict { PACKAGE_PIN A9 IOSTANDARD LVCMOS33 } [get_ports { uart_rx }]\\nset_property -dict { PACKAGE_PIN H5 IOSTANDARD LVCMOS33 } [get_ports { led[0] }]\\nset_property -dict { PACKAGE_PIN J5 IOSTANDARD LVCMOS33 } [get_ports { led[1] }]\\nset_property -dict { PACKAGE_PIN T9 IOSTANDARD LVCMOS33 } [get_ports { led[2] }]\\nset_property -dict { PACKAGE_PIN T10 IOSTANDARD LVCMOS33 } [get_ports { led[3] }]\\nset_property -dict { PACKAGE_PIN D10 IOSTANDARD LVCMOS33 } [get_ports { uart_tx }]\\n\"" of a design on the Arty A7, the
problems of a board that does not fit it, the two devices. -/
def hdlArtyXdc : IO Unit := do
    let texts ← hdlArtyTexts
    checkEq (repr (["\"set_property -dict { PACKAGE_PIN E3 IOSTANDARD LVCMOS33 } [get_ports {clk}]\\ncreate_clock -period 10.000 [get_ports {clk}]\\nset_property -dict { PACKAGE_PIN D9 IOSTANDARD LVCMOS33 } [get_ports {btn[0]}]\\nset_property -dict { PACKAGE_PIN C9 IOSTANDARD LVCMOS33 } [get_ports {btn[1]}]\\nset_property -dict { PACKAGE_PIN B9 IOSTANDARD LVCMOS33 } [get_ports {btn[2]}]\\nset_property -dict { PACKAGE_PIN B8 IOSTANDARD LVCMOS33 } [get_ports {btn[3]}]\\nset_property -dict { PACKAGE_PIN A9 IOSTANDARD LVCMOS33 } [get_ports {uart_rx}]\\nset_property -dict { PACKAGE_PIN H5 IOSTANDARD LVCMOS33 } [get_ports {led[0]}]\\nset_property -dict { PACKAGE_PIN J5 IOSTANDARD LVCMOS33 } [get_ports {led[1]}]\\nset_property -dict { PACKAGE_PIN T9 IOSTANDARD LVCMOS33 } [get_ports {led[2]}]\\nset_property -dict { PACKAGE_PIN T10 IOSTANDARD LVCMOS33 } [get_ports {led[3]}]\\nset_property -dict { PACKAGE_PIN D10 IOSTANDARD LVCMOS33 } [get_ports {uart_tx}]\\n\"",
      ".nil",
      ".cons \"no pin for port btn\" (.cons \"no pin for port uart_rx\" (.cons \"port led has 4 bits, the board's led 2\" (.cons \"no pin for port uart_tx\" .nil)))",
      ".cons (\"xc7a35ticsg324-1L\", \"xc7a35tcsg324-1\") (.cons (\"xc7a100tcsg324-1\", \"xc7a100tcsg324-1\") .nil)"] : List String)).pretty
      (repr (texts.take 4)).pretty

/-- yosys's synth_xilinx on the Verilog of examples/hdl-arty.wiz: the RAMs become a
RAMB18E1 and a RAMB36E1, the ROM a RAMB18E1, the multiply a DSP48E1 (when yosys is on
PATH). -/
def hdlArtyTools : IO Unit := do
    let ys ← (do let o ← IO.Process.output { cmd := "yosys", args := #["-V"] }; pure (o.exitCode == 0)) <|> pure false
    unless ys do skip "no yosys"; return
    let texts := (← hdlArtyTexts).drop 4
    let unq (t : String) : String := ((t.drop 1).dropRight 1).replace "\\n" "\n" |>.replace "\\\"" "\""
    IO.FS.withTempDir fun dir => do
      let cases := [("ram18", "RAMB18E1"), ("ram36", "RAMB36E1"), ("rom", "RAMB18E1"), ("mul", "DSP48E1")]
      for t in texts, (top, cell) in cases do
        IO.FS.writeFile (dir / s!"{top}.v") (unq t)
        let o ← IO.Process.output { cmd := "yosys", args := #["-q", "-p", s!"read_verilog {top}.v; synth_xilinx -family xc7 -top {top}; tee -q -o {top}.stat stat"], cwd := dir }
        unless o.exitCode == 0 do throw (IO.userError s!"yosys fails on {top}.v:\n{o.stderr}")
        let st ← IO.FS.readFile (dir / s!"{top}.stat")
        unless (st.splitOn cell).length > 1 do throw (IO.userError s!"no {cell} for {top}:\n{st}")

/-- examples/hdl-prim.wiz through the front end: its seven `#eval` texts. -/
def hdlPrimTexts : IO (List String) := do
    let src ← IO.FS.readFile "examples/hdl-prim.wiz"
    let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := ← libLoader }
    let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
    unless errs.isEmpty do throw (IO.userError s!"unexpected errors: {errs}")
    pure (s.messages.toList.map (·.text))

def hdlUnq (t : String) : String := ((t.drop 1).dropRight 1).replace "\\n" "\n" |>.replace "\\\"" "\""

/-- Primitive instances (H14 P1): the Verilog of a PLL-wrapped OSERDESE2/IOBUF/ODDR/OBUF
design, the refusal to simulate cells without a model, a buffer simulated by its model,
and the kind errors. -/
def hdlPrimCheck : IO Unit := do
    let texts ← hdlPrimTexts
    unless texts.length == 7 do throw (IO.userError s!"expected 7 texts, got {texts.length}: {texts}")
    let v := hdlUnq texts[0]!
    for frag in ["module serial_core(input clk, input [0:0] sys4x, input [7:0] d, output [0:0] ck, output [0:0] q, inout [0:0] dq, output [0:0] back);",
        "OSERDESE2 #(.DATA_RATE_OQ(\"DDR\"), .DATA_RATE_TQ(\"BUF\"), .DATA_WIDTH(8), .TRISTATE_WIDTH(1), .SERDES_MODE(\"MASTER\"))",
        ".CLK(sys4x), .CLKDIV(clk), .D1(", ".OCE(1'd1), .RST(1'd0), .T1(r), .TCE(1'd1), .OQ(", "IOBUF u", ".IO(dq));", "ODDR #(.DDR_CLK_EDGE(\"SAME_EDGE\"), .INIT(1'b0), .SRTYPE(\"SYNC\"))", ".O(ck));",
        "module serial(input clk, input [7:0] d, output [0:0] ck, output [0:0] q, inout [0:0] dq, output [0:0] back);",
        "PLLE2_BASE #(.CLKIN1_PERIOD(10.0), .CLKFBOUT_MULT(8), .DIVCLK_DIVIDE(1), .CLKOUT0_DIVIDE(8), .CLKOUT0_PHASE(0.0), .CLKOUT1_DIVIDE(2), .CLKOUT1_PHASE(0.0)) clocking (.CLKIN1(clk), .RST(1'b0), .PWRDWN(1'b0), .CLKFBOUT(ck_CLKFBOUT), .CLKFBIN(ck_CLKFBOUT), .CLKOUT0(ck_CLKOUT0), .CLKOUT1(ck_CLKOUT1));",
        "BUFG bufg_CLKOUT0 (.I(ck_CLKOUT0), .O(ck_CLKOUT0_g));",
        "serial_core core (.clk(ck_CLKOUT0_g), .sys4x(ck_CLKOUT1_g), .d(d), .ck(ck), .q(q), .dq(dq), .back(back));"] do
      unless (v.splitOn frag).length > 1 do throw (IO.userError s!"missing from the Verilog: {frag}\n{v}")
    if (v.splitOn "assign dq").length > 1 then throw (IO.userError s!"a pad is assigned:\n{v}")
    checkEq (repr ([".cons \"OSERDESE2 (node 14) has no behavioural model\" (.cons \"ODDR (node 21) has no behavioural model\" .nil)",
      ".error \"simulation refused: OSERDESE2 (node 14) has no behavioural model; ODDR (node 21) has no behavioural model\"",
      ".nil",
      "\"module blink(input clk, input [0:0] x, output [0:0] led, inout [0:0] pin, output [0:0] seen);\\n  reg [0:0] r; initial r = 1'd0;\\n  wire [0:0] n2 = ~x;\\n  wire [0:0] n4;\\n  wire [0:0] n6 = ~r;\\n  IOBUF u3 (.I(r), .T(n2), .O(n4), .IO(pin));\\n  OBUF u7 (.I(r), .O(led));\\n  always @(posedge clk) r <= n6;\\n  assign seen = n4;\\nendmodule\\n\"",
      ".ok (.cons (.mk 0 (), .mk 0 (), .mk 0 ()) (.cons (.mk 1 (), .mk 1 (), .mk 0 ()) (.cons (.mk 0 (), .mk 0 (), .mk 0 ()) (.cons (.mk 1 (), .mk 1 (), .mk 1 ()) .nil))))",
      ".cons \"ODDR port C wants a clock, not a data signal (node 2)\" (.cons \"a clock (input sys4x) is used as data by register r\" (.cons \"output y_1 is a data signal but gets a pad (OBUF.O)\" .nil))"] : List String)).pretty
      (repr (texts.drop 1)).pretty

/-- yosys's synth_xilinx keeps the primitives of examples/hdl-prim.wiz as cells:
PLLE2_BASE, BUFG, OSERDESE2, IOBUF, ODDR, OBUF (when yosys is on PATH). -/
def hdlPrimTools : IO Unit := do
    let ys ← (do let o ← IO.Process.output { cmd := "yosys", args := #["-V"] }; pure (o.exitCode == 0)) <|> pure false
    unless ys do skip "no yosys"; return
    let v := hdlUnq (← hdlPrimTexts)[0]!
    IO.FS.withTempDir fun dir => do
      IO.FS.writeFile (dir / "serial.v") v
      let o ← IO.Process.output { cmd := "yosys", args := #["-q", "-p", "read_verilog serial.v; synth_xilinx -family xc7 -top serial; tee -q -o serial.stat stat"], cwd := dir }
      unless o.exitCode == 0 do throw (IO.userError s!"yosys fails on serial.v:\n{o.stderr}")
      let st ← IO.FS.readFile (dir / "serial.stat")
      for cell in ["PLLE2_BASE", "BUFG", "OSERDESE2", "IOBUF", "ODDR", "OBUF"] do
        unless (st.splitOn cell).length > 1 do throw (IO.userError s!"no {cell} in serial:\n{st}")
      if (o.stderr.splitOn "has no driver").length > 1 then throw (IO.userError s!"undriven wire:\n{o.stderr}")

def hdlGroup : Group where
  name := "hdl"
  exercise := "HDL stage S0 (hdl-plan H14)"
  cases := [
    { name := "S2: operators on signals: same Verilog as the Hw operations, numerals at the width, if as a mux, printed back", run := fun _ => do
        -- the three designs agree with their Hw-operation twins (Verilog text); the counter
        -- wraps at 10; shifts by 3, 0, 8 places; the counter's Verilog; three terms printed
        -- in notation; `if` on a Bool, a dependent `if b then rfl else rfl`, Nat bitwise
        okLibs (← IO.FS.readFile "examples/hdl-operators.wiz")
          ["(.true, .true, .true)",
           ".cons 0 (.cons 1 (.cons 2 (.cons 3 (.cons 4 (.cons 5 (.cons 6 (.cons 7 (.cons 8 (.cons 9 (.cons 0 (.cons 1 .nil)))))))))))",
           "((72, 25), (201, 201), 0, 0)",
           "\"module count(input clk, input [0:0] x, output [3:0] y);\\n  reg [3:0] r; initial r = 4'd0;\\n  wire [0:0] n3 = r == 4'd9;\\n  wire [3:0] n6 = r + 4'd1;\\n  wire [3:0] n7 = n3 ? 4'd0 : n6;\\n  always @(posedge clk) r <= n7;\\n  assign y = r;\\nendmodule\\n\"",
           "fun c x y => if c then x + 1 &&& ~~~y else x <<< 2 ||| y >>> 3 : Wire Bit → Wire B8 → Wire B8 → Wire B8",
           "fun x y => x === y ||| x <ᵤ 3 : Wire B8 → Wire B8 → Wire HwTy.bit",
           "fun c x => if c then x else 0 : Wire Bit → Wire B8 → Wire B8",
           "(1, 24, 14)"] },
    { name := "S4: shifts by a signal, signed comparisons, && and || on bits, deriving BitPack, registers with reset and enable", run := fun _ => do
        -- examples/hdl-gaps.wiz: the values against lib/BitVec.wiz (every 8-bit value),
        -- netlist simulations = values (shifter, comparisons, gates, a phase register, a
        -- bundle in one register, the registers with rst/en), operator twins' Verilog,
        -- printing, enum and bundle encodings, the reset/enable Verilog
        okLibs (← IO.FS.readFile "examples/hdl-gaps.wiz")
          ["(.true, .true)",
           "(.true, 12)",
           "(.true, .true)",
           "\"module shifts(input clk, input [7:0] x_0, input [3:0] x_1, output [7:0] y_0, output [7:0] y_1, output [7:0] y_2, output [7:0] y_3);\\n  wire [7:0] n3 = x_0 << x_1;\\n  wire [7:0] n4 = x_0 >> x_1;\\n  wire [7:0] n5 = $signed(x_0) >>> x_1;\\n  wire [0:0] n6 = x_0[7:7];\\n  wire [2:0] n9 = n6 ? 3'd7 : 3'd0;\\n  wire [10:0] n10 = {n9, x_0};\\n  wire [7:0] n11 = n10[10:3];\\n  assign y_0 = n3;\\n  assign y_1 = n4;\\n  assign y_2 = n5;\\n  assign y_3 = n11;\\nendmodule\\n\"",
           "fun x s => x <<< s ||| x >>> s ^^^ x >>>ₛ s ^^^ x >>>ₛ 2 : Wire B8 → Wire B3 → Wire (.bits 8)",
           "fun x y => x <ₛ y ||| x ≥ₛ 2 : Wire B8 → Wire B8 → Wire HwTy.bit",
           "(.true, .true)",
           "fun a b => a &&& b ||| b : Wire Bit → Wire Bit → Wire Bit",
           "(.false, .true)",
           "(2, .cons 0 (.cons 1 (.cons 2 (.cons 3 .nil))), 7, 5)",
           "83",
           ".true",
           "(.true, .cons 9 (.cons 0 (.cons 0 (.cons 1 (.cons 1 (.cons 2 (.cons 3 (.cons 0 (.cons 0 (.cons 0 (.cons 1 (.cons 1 (.cons 2 (.cons 3 (.cons 0 (.cons 1 (.cons 2 (.cons 3 (.cons 0 (.cons 1 (.cons 2 .nil)))))))))))))))))))))",
           "(.true, .cons 10 (.cons 83 (.cons 0 (.cons 95 (.cons 9 (.cons 120 (.cons 5 (.cons 81 (.cons 108 (.cons 56 (.cons 115 (.cons 60 (.cons 104 .nil)))))))))))))",
           "\"module phase(input clk, input [0:0] x, output [1:0] y);\\n  reg [1:0] r; initial r = 2'd0;\\n  wire [0:0] n3 = r == 2'd3;\\n  wire [1:0] n6 = r + 2'd1;\\n  wire [1:0] n7 = n3 ? 2'd0 : n6;\\n  wire [1:0] n8 = x ? n7 : r;\\n  always @(posedge clk) r <= n8;\\n  assign y = r;\\nendmodule\\n\"",
           "((.true, .cons 4 (.cons 42 (.cons 42 (.cons 174 (.cons 174 (.cons 174 (.cons 174 (.cons 174 (.cons 174 (.cons 174 (.cons 174 (.cons 174 (.cons 116 (.cons 116 (.cons 116 (.cons 116 (.cons 116 (.cons 116 (.cons 116 (.cons 116 (.cons 116 (.cons 116 (.cons 87 (.cons 87 (.cons 87 (.cons 87 (.cons 42 (.cons 203 (.cons 203 (.cons 203 (.cons 203 (.cons 203 (.cons 203 (.cons 203 (.cons 203 (.cons 203 (.cons 203 (.cons 203 (.cons 58 (.cons 58 (.cons 58 .nil))))))))))))))))))))))))))))))))))))))))), (.true, .cons 5 (.cons 0 (.cons 0 (.cons 174 (.cons 174 (.cons 174 (.cons 174 (.cons 174 (.cons 174 (.cons 174 (.cons 174 (.cons 174 (.cons 34 (.cons 34 (.cons 34 (.cons 34 (.cons 34 (.cons 34 (.cons 34 (.cons 34 (.cons 34 (.cons 34 (.cons 121 (.cons 121 (.cons 121 (.cons 121 (.cons 0 (.cons 203 (.cons 203 (.cons 203 (.cons 203 (.cons 203 (.cons 203 (.cons 203 (.cons 203 (.cons 203 (.cons 203 (.cons 203 (.cons 5 (.cons 5 (.cons 63 .nil))))))))))))))))))))))))))))))))))))))))), .true, .true)",
           ".true",
           "\"module reg_(input clk, input [0:0] rst, input [0:0] en, input [7:0] x, output [7:0] y);\\n  reg [7:0] r; initial r = 8'd42;\\n  always @(posedge clk) if (rst) r <= 8'd42; else if (en) r <= x;\\n  assign y = r;\\nendmodule\\n\""] },
    { name := "S2: if on a condition that is no signal takes the ordinary path (its messages)", run := fun _ => do
        failsLibs "import Prelude\ndef f (n : Nat) : Nat := if n then 1 else 2" "constructor"
        failsLibs "import Prelude\ndef f (A : Type) (a : A) : Nat := if a then 1 else 2" "cannot match on a value of type A"
        okLibs "import Prelude\ndef f (b : Bool) : (if b then 1 else 1) = 1 := if b then rfl else rfl\n#check fun (b : Bool) (x : Nat) => if b then x + 1 else 0"
          ["fun b x => if b then x + 1 else 0 : Bool → Nat → Nat"] },
    { name := "auto-share: a let becomes ShareLet.share when an instance exists", run := fun _ =>
        okLibs shareLetHook ["101", "1", "1"] },
    { name := "L2 examples: hash-consed netlists are no bigger, three simulations agree; the doubling chain is linear", run := fun _ => do
        -- r1–r4: (nodes hash-consed, nodes naive), then the value simulation and the netlist
        -- simulations (hash-consed, naive). q1: the chain at k = 20 (nodes, adders, builder
        -- work). q2: the chain at k = 3 simulated. q3: the chain without sharing (`let ω`) at
        -- k = 10 (nodes, work, naive nodes). Last: (x + y) * (y + x) has one adder.
        okLibs (← IO.FS.readFile "examples/hdl.wiz") ["((4, 4), .cons 0 (.cons 1 (.cons 2 (.cons 3 (.cons 4 (.cons 5 .nil))))), .cons 0 (.cons 1 (.cons 2 (.cons 3 (.cons 4 (.cons 5 .nil))))), .cons 0 (.cons 1 (.cons 2 (.cons 3 (.cons 4 (.cons 5 .nil))))))", "((7, 7), .cons 250 (.cons 251 (.cons 252 (.cons 253 (.cons 254 (.cons 255 .nil))))), .cons 250 (.cons 251 (.cons 252 (.cons 253 (.cons 254 (.cons 255 .nil))))), .cons 250 (.cons 251 (.cons 252 (.cons 253 (.cons 254 (.cons 255 .nil))))))", "((28, 35), .cons 1 (.cons 1 (.cons 2 (.cons 1 (.cons 3 (.cons 3 .nil))))), .cons 1 (.cons 1 (.cons 2 (.cons 1 (.cons 3 (.cons 3 .nil))))), .cons 1 (.cons 1 (.cons 2 (.cons 1 (.cons 3 (.cons 3 .nil))))))", "((8, 9), .cons 1 (.cons 4 (.cons 9 (.cons 15 (.cons 216 (.cons 162 .nil))))), .cons 1 (.cons 4 (.cons 9 (.cons 15 (.cons 216 (.cons 162 .nil))))), .cons 1 (.cons 4 (.cons 9 (.cons 15 (.cons 216 (.cons 162 .nil))))))", "(22, 20, 22)", "(.cons 8 (.cons 16 (.cons 24 (.cons 32 (.cons 64 (.cons 56 .nil))))), .cons 8 (.cons 16 (.cons 24 (.cons 32 (.cons 64 (.cons 56 .nil))))))", "(11, 2047, 2047)", "4"] },
    { name := "auto-share elaborates an object let to ShareLet.share; an erased or meta let stays a let", run := fun _ =>
        okLibs ("import Hdl.Core\ndef f {r : HwTy → Type} [Hw r] (x : r (HwTy.bits 8)) : r (HwTy.bits 8) := let y := Hw.add x x; Hw.add y y\n" ++
          "def g {r : HwTy → Type} [Hw r] (x : r (HwTy.bits 8)) (k : Nat) : r (HwTy.bits 8) := let j := Nat.succ k; Hw.lit 8 j\n#erase f\n#erase g")
          ["f := (λr. (λinst✝. (λx. (((((ShareLet.share ◾) ◾) ((((instShareLetRARB ◾) #1) ⟨0 8⟩) ⟨0 8⟩)) (((((Hw.add ◾) #1) 8) #0) #0)) (λy. (((((Hw.add ◾) #2) 8) #0) #0))))))",
           "g := (λr. (λinst✝. (λx. (λk. (let j := (Nat.succ #0); ((((Hw.lit ◾) #3) 8) #0))))))"] },
    { name := "traces: a circuit's run along a trace (lib/Trace.wiz); the finite simulation is its prefix", run := fun _ =>
        okLibs ("import Hdl.Core\ndef u8 : HwTy := HwTy.bits 8\n" ++
          "def ctr : Circuit (HwTy.bits 1) u8 := Circuit.mk u8 (BitVec.ofNat 8 250) (fun s u => Hw.pair (Hw.add s (Hw.lit 8 1)) s)\n" ++
          "def xs : Trace (BitVec 1) := Trace.const (BitVec.ofNat 1 0)\n" ++
          "def t3 : Circuit.trace ctr xs 3 = BitVec.ofNat 8 253 := rfl\n" ++
          "def pre (n : Nat) (ys : Trace (BitVec 1)) : Circuit.run ctr (Trace.take n ys) = Trace.take n (Circuit.trace ctr ys) := Circuit.run_take ctr n ys\n" ++
          "#eval Hdl.map BitVec.toNat (Trace.take 8 (Circuit.trace ctr xs))\n")
          [".cons 250 (.cons 251 (.cons 252 (.cons 253 (.cons 254 (.cons 255 (.cons 0 (.cons 1 .nil)))))))"] },
    { name := "Arty A7 (lib/Hdl/Arty.wiz): pin constraints (XDC) from the board's table, what does not fit, the two devices", run := fun _ => hdlArtyXdc },
    { name := "H14 P1: primitive instances: Verilog of an OSERDESE2/IOBUF/ODDR/OBUF design under a PLL wrapper, refusal without models, buffer models, kind errors", run := fun _ => hdlPrimCheck },
    { name := "H14 P1: yosys synth_xilinx keeps PLLE2_BASE, BUFG, OSERDESE2, IOBUF, ODDR, OBUF (skipped without yosys)", run := fun _ => hdlPrimTools },
    { name := "Xilinx 7-series: yosys synth_xilinx maps two RAMs, a 1024-byte ROM and a multiply to RAMB18E1, RAMB36E1 and DSP48E1 (skipped without yosys)", run := fun _ => hdlArtyTools },
    { name := "optics: deriving Lens on structures and bundles (laws, independence by rfl); a step zoomed into a field, the frame rule", run := fun _ => do
        okLibs (← IO.FS.readFile "examples/hdl-optic.wiz")
          ["(.cons 1 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 1 (.cons 0 .nil))))))))))), .true)"]
        okLibs ("import OpticDerive\nstructure P where\n  x : Nat\n  y : Bool\n  z : Nat\n  deriving Lens\n" ++
          "structure Q (A : Type) (n : Nat) where\n  a : A\n  b : List A\n  deriving Lens\n" ++
          "def t1 : Lens.get P.yL (P.mk 1 .true 3) = .true := rfl\n" ++
          "def t2 : Lens.set P.zL (P.mk 1 .true 3) 7 = P.mk 1 .true 7 := rfl\n" ++
          "def t3 : Lens.Indep P.xL P.zL := P.x_z_indep\n" ++
          "def t4 : Lens.set (@Q.bL Nat 3) (Q.mk 1 .nil) (.cons 2 .nil) = Q.mk 1 (.cons 2 .nil) := rfl\n" ++
          "def t5 {A : Type} {n : Nat} : Lens.Lawful (@Q.aL A n) := Q.aL_lawful\n#eval Lens.get P.zL (Lens.set P.xL (P.mk 1 .true 3) 9)\n") ["3"] },
    { name := "docs/hardware.md's example: a circuit refines a specification; a temporal property of every run; simulation agrees", run := fun _ => do
        okLibs (← IO.FS.readFile "examples/hardware-tour.wiz") ["(.cons 2 (.cons 0 (.cons 0 (.cons 1 (.cons 2 (.cons 0 .nil))))), .true)"] },
    { name := "memories: RAM with a registered read, ROM, enable and reset; values = netlist; read/write lemmas; misuse reported; Verilog arrays", run := fun _ => do
        okLibs (← IO.FS.readFile "examples/hdl-mem.wiz")
          ["(.cons 0 (.cons 0 (.cons 42 (.cons 99 (.cons 13 (.cons 99 (.cons 0 .nil)))))), .true)",
           "(.cons 0 (.cons 9 (.cons 225 (.cons 0 (.cons 49 .nil)))), .true)",
           "(.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 42 .nil)))), .true)",
           ".cons \"a choice between two different memories (a memory can only be written, not chosen)\" .nil",
           "\"module ram(input clk, input [0:0] we, input [3:0] waddr, input [7:0] wdata, input [3:0] raddr, output [7:0] y);\\n  reg [7:0] q; initial q = 8'd0;\\n  reg [7:0] cells [0:15];\\n  initial begin\\n    cells[0] = 8'd0;\\n    cells[1] = 8'd0;\\n    cells[2] = 8'd0;\\n    cells[3] = 8'd0;\\n    cells[4] = 8'd0;\\n    cells[5] = 8'd0;\\n    cells[6] = 8'd0;\\n    cells[7] = 8'd0;\\n    cells[8] = 8'd0;\\n    cells[9] = 8'd0;\\n    cells[10] = 8'd0;\\n    cells[11] = 8'd0;\\n    cells[12] = 8'd0;\\n    cells[13] = 8'd0;\\n    cells[14] = 8'd0;\\n    cells[15] = 8'd0;\\n  end\\n  wire [7:0] n5 = cells[raddr];\\n  always @(posedge clk) q <= n5;\\n  always @(posedge clk) begin\\n    if (we) cells[waddr] <= wdata;\\n  end\\n  assign y = q;\\nendmodule\\n\""] },
    { name := "memories in Verilog: Icarus replays the RAM's test bench; yosys maps RAM and a 256-word ROM to SB_RAM40_4K (skipped without the tools)", run := fun _ => hdlMemTools },
    { name := "bits: one-bit laws by case split (Hdl.Bits); control logic written with gates proved with symbolic inputs; the Boolean bridge", run := fun _ => do
        okLibs (← IO.FS.readFile "examples/hdl-bits.wiz") ["1"] },
    { name := "Verilog: declarations before use (regs, wires, then the updates), sized initial values", run := fun _ =>
        okLibs (hdlVerilogSrc ++ "#eval v1\n")
          ["\"module counter(input clk, input [0:0] x, output [7:0] y);\\n  reg [7:0] r; initial r = 8'd250;\\n  wire [7:0] n3 = r + 8'd1;\\n  always @(posedge clk) r <= n3;\\n  assign y = r;\\nendmodule\\n\""] },
    { name := "C1: clock domains: a clk2 circuit emits input clk2 and posedge clk2; Hw.clockOf drives a primitive", run := fun _ => do
        -- `n2.clocks` is the named domain; its Verilog names the port and the always block
        -- after it; an ODDR clocked by `Hw.clockOf d2` connects `.C(clk2)`.
        okLibs ("import Hdl.Core\nimport Hdl.Prim\n" ++
          "def u8 : HwTy := HwTy.bits 8\n" ++
          "def c1 : Circuit (HwTy.bits 1) u8 := Circuit.mk u8 (BitVec.ofNat 8 250) (fun s u => Hw.pair (Hw.add s (Hw.lit 8 1)) s)\n" ++
          "def d2 : ClockDomain := ClockDomain.named \"clk2\"\n" ++
          "def n2 : Netlist := Circuit.netlistIn d2 \"dom2\" c1\n" ++
          "#eval Hdl.map (fun (d : ClockDomain) => (d.name, d.periodPs)) n2.clocks\n" ++
          "#eval Verilog.emit n2\n" ++
          "def oddrP : Prim (HwTy.prod HwTy.clock (HwTy.prod HwTy.bit HwTy.bit)) HwTy.bit :=\n" ++
          "  Prim.decl \"ODDR\" .nil (.cons \"C\" (.cons \"D1\" (.cons \"D2\" .nil))) (.cons \"Q\" .nil) .none\n" ++
          "def primC : Circuit (HwTy.bits 8) HwTy.bit :=\n" ++
          "  Circuit.mk (HwTy.bits 8) (BitVec.ofNat 8 0)\n" ++
          "    (fun s x => Hw.pair s (Hw.prim oddrP (Hw.pair (Hw.clockOf d2) (Hw.pair (Hw.lit 1 0) (Hw.lit 1 1)))))\n" ++
          "#eval Verilog.emit (Circuit.netlistIn d2 \"dom3\" primC)\n")
          [".cons (\"clk2\", 0) .nil",
           "\"module dom2(input clk2, input [0:0] x, output [7:0] y);\\n  reg [7:0] r; initial r = 8'd250;\\n  wire [7:0] n3 = r + 8'd1;\\n  always @(posedge clk2) r <= n3;\\n  assign y = r;\\nendmodule\\n\"",
           "\"module dom3(input clk2, input [7:0] x, output [0:0] y);\\n  reg [7:0] r; initial r = 8'd0;\\n  wire [0:0] n6;\\n  ODDR u5 (.C(clk2), .D1(1'd0), .D2(1'd1), .Q(n6));\\n  always @(posedge clk2) r <= r;\\n  assign y = n6;\\nendmodule\\n\""] },
    { name := "C2/C3: clock domains: a synchronised crossing accepted, an unsynchronised one rejected; Multi parts and wires; Clocking.domains; XDC/PCF periods; BUFG output domain; runners refuse two clocks", run := fun _ => do
        -- examples/hdl-cdc.wiz: the C2 raw-netlist checks (a two-domain top with and without
        -- Cdc.sync2, the sync clocked by its own source domain, a clock input used as data,
        -- a one-domain circuit, a circuit that tries to smuggle a second domain in), then
        -- C3: the same design as two Multi parts with a link (rejected) and Cdc.wire
        -- (accepted), its core and PLL-wrapper Verilog, a pin-sourced second clock, XDC and
        -- PCF constraints from ClockDomain.periodPs, a BUFG output as a synchroniser's
        -- clock (Prim.withOutDom), and the multi-clock simulation refusal
        okLibs (← IO.FS.readFile "examples/hdl-cdc.wiz")
          [".nil",
           "\"module cross(input clk, input clk2, output [0:0] y);\\n  reg [0:0] r; initial r = 1'd0;\\n  reg [0:0] s; initial s = 1'd0;\\n  wire [0:0] n3;\\n  wiz_sync2 u2 (.clk(clk2), .d(r), .q(n3));\\n  always @(posedge clk) r <= r;\\n  always @(posedge clk2) s <= n3;\\n  assign y = s;\\nendmodule\\n\"",
           ".cons \"a clk signal (register r) is used by clk2 logic (register s): no synchroniser\" .nil",
           ".cons \"a clk signal (register r) is used by clk2 logic (register s): no synchroniser\" .nil",
           ".cons \"synchroniser wiz_sync2 (node 2): its data is in its clock's own domain clk, not another one\" (.cons \"a clk signal (wiz_sync2.q) is used by clk2 logic (register s): no synchroniser\" .nil)",
           ".cons \"a clock (input ck) is used as data by register r\" .nil",
           ".nil",
           ".nil",
           "\"module counter(input clk, output [7:0] y);\\n  reg [7:0] r; initial r = 8'd0;\\n  wire [7:0] n3 = r + 8'd1;\\n  always @(posedge clk) r <= n3;\\n  assign y = r;\\nendmodule\\n\"",
           ".cons \"a clk2 signal (wiz_sync2.q) is used by clk logic (register r): no synchroniser\" (.cons \"the clock net at node 2 is on clock domain clk2, which the netlist does not declare (clk)\" .nil)",
           ".error \"simulation refused: 2 clock domains (clk, clk2): multi-clock simulation needs an event schedule; wiz_sync2 (node 2) has no behavioural model\"",
           ".cons \"a clk signal (register tx_r) is used by clk2 logic (register rx_r): no synchroniser\" .nil",
           ".nil",
           "\"module cross(input clk, input clk2, input [0:0] go, output [0:0] q);\\n  reg [0:0] tx_r; initial tx_r = 1'd0;\\n  reg [0:0] rx_r; initial rx_r = 1'd0;\\n  wire [0:0] n4;\\n  wiz_sync2 u3 (.clk(clk2), .d(tx_r), .q(n4));\\n  always @(posedge clk) tx_r <= go;\\n  always @(posedge clk2) rx_r <= n4;\\n  assign q = rx_r;\\nendmodule\\n\"",
           "\"module cross_core(input clk, input clk2, input [0:0] go, output [0:0] q);\\n  reg [0:0] tx_r; initial tx_r = 1'd0;\\n  reg [0:0] rx_r; initial rx_r = 1'd0;\\n  wire [0:0] n4;\\n  wiz_sync2 u3 (.clk(clk2), .d(tx_r), .q(n4));\\n  always @(posedge clk) tx_r <= go;\\n  always @(posedge clk2) rx_r <= n4;\\n  assign q = rx_r;\\nendmodule\\nmodule cross(input clk, input [0:0] go, output [0:0] q);\\n  wire ck_CLKFBOUT;\\n  wire ck_CLKOUT0;\\n  wire ck_CLKOUT1;\\n  PLLE2_BASE #(.CLKIN1_PERIOD(10.0), .CLKFBOUT_MULT(8), .DIVCLK_DIVIDE(1), .CLKOUT0_DIVIDE(8), .CLKOUT0_PHASE(0.0), .CLKOUT1_DIVIDE(2), .CLKOUT1_PHASE(0.0)) clocking (.CLKIN1(clk), .RST(1'b0), .PWRDWN(1'b0), .CLKFBOUT(ck_CLKFBOUT), .CLKFBIN(ck_CLKFBOUT), .CLKOUT0(ck_CLKOUT0), .CLKOUT1(ck_CLKOUT1));\\n  wire ck_CLKOUT0_g;\\n  BUFG bufg_CLKOUT0 (.I(ck_CLKOUT0), .O(ck_CLKOUT0_g));\\n  wire ck_CLKOUT1_g;\\n  BUFG bufg_CLKOUT1 (.I(ck_CLKOUT1), .O(ck_CLKOUT1_g));\\n  cross_core core (.clk(ck_CLKOUT0_g), .clk2(ck_CLKOUT1_g), .go(go), .q(q));\\nendmodule\\n\"",
           "\"module cross_core(input clk, input clk2, input [0:0] go, output [0:0] q);\\n  reg [0:0] tx_r; initial tx_r = 1'd0;\\n  reg [0:0] rx_r; initial rx_r = 1'd0;\\n  wire [0:0] n4;\\n  wiz_sync2 u3 (.clk(clk2), .d(tx_r), .q(n4));\\n  always @(posedge clk) tx_r <= go;\\n  always @(posedge clk2) rx_r <= n4;\\n  assign q = rx_r;\\nendmodule\\nmodule cross(input clk, input [0:0] go, input clk2, output [0:0] q);\\n  wire ck_CLKFBOUT;\\n  wire ck_CLKOUT0;\\n  PLLE2_BASE clocking (.CLKIN1(clk), .CLKFBOUT(ck_CLKFBOUT), .CLKFBIN(ck_CLKFBOUT), .CLKOUT0(ck_CLKOUT0));\\n  wire ck_CLKOUT0_g;\\n  BUFG bufg_CLKOUT0 (.I(ck_CLKOUT0), .O(ck_CLKOUT0_g));\\n  cross_core core (.clk(ck_CLKOUT0_g), .clk2(clk2), .go(go), .q(q));\\nendmodule\\n\"",
           "\"set_property -dict { PACKAGE_PIN E3 IOSTANDARD LVCMOS33 } [get_ports {clk}]\\ncreate_clock -period 10.000 [get_ports {clk}]\\ncreate_clock -period 2.500 [get_ports {clk2}]\\nset_property -dict { PACKAGE_PIN F3 IOSTANDARD LVCMOS33 } [get_ports {clk2}]\\nset_property -dict { PACKAGE_PIN D9 IOSTANDARD LVCMOS33 } [get_ports {go}]\\nset_property -dict { PACKAGE_PIN D10 IOSTANDARD LVCMOS33 } [get_ports {q}]\\n\"",
           ".nil",
           "\"set_io clk 21\\nset_io go 1\\nset_io q 2\\nset_frequency clk 100\\nset_frequency clk2 400\\n\"",
           ".cons \"synchroniser wiz_sync2 (node 5): its data is in its clock's own domain clk2, not another one\" .nil",
           ".nil",
           "\"module cross(input clk, input clk2, input [0:0] go, output [0:0] q);\\n  reg [0:0] tx_r; initial tx_r = 1'd0;\\n  reg [0:0] rx_r; initial rx_r = 1'd0;\\n  wire [0:0] n4;\\n  wire [0:0] n6;\\n  BUFG u3 (.I(clk2), .O(n4));\\n  wiz_sync2 u5 (.clk(n4), .d(tx_r), .q(n6));\\n  always @(posedge clk) tx_r <= go;\\n  always @(posedge clk2) rx_r <= n6;\\n  assign q = rx_r;\\nendmodule\\n\"",
           ".error \"simulation refused: 2 clock domains (clk, clk2): multi-clock simulation needs an event schedule; wiz_sync2 (node 3) has no behavioural model\""] },
    { name := "S1: bundles, composition, reset and enable at random cycles; netlist simulation = values; names, test bench, PCF, VCD", run := fun _ => do
        -- t1–t6: (agreement of the netlist simulations with `Circuit.run`, the netlist size
        -- and the outputs) for the bundled counter, a delay chain, `par`, a feedback loop,
        -- two instances, and reset and enable driven at random cycles; then the counter's
        -- Verilog (named ports and registers, `if (rst) … else if (en)`), pin constraints,
        -- the problems of a bad pin list, a waveform, and the sizes of a list of designs
        okLibs (← IO.FS.readFile "examples/hdl-compose.wiz")
          ["(.true, .cons 17 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 2 (.cons 4 (.cons 6 (.cons 8 (.cons 8 (.cons 10 (.cons 10 (.cons 10 (.cons 12 (.cons 14 (.cons 14 (.cons 14 (.cons 16 (.cons 19 (.cons 16 (.cons 14 (.cons 12 (.cons 12 (.cons 12 (.cons 12 (.cons 10 (.cons 8 (.cons 6 (.cons 6 (.cons 4 (.cons 2 .nil)))))))))))))))))))))))))))))))",
           "(.true, .cons 5 (.cons 9 (.cons 7 (.cons 0 (.cons 0 (.cons 140 (.cons 173 (.cons 172 (.cons 30 (.cons 11 (.cons 226 (.cons 250 (.cons 211 .nil)))))))))))))",
           "(.true, .cons 9 (.cons 2389 (.cons 1798 (.cons 150 (.cons 40 (.cons 17709 (.cons 24795 (.cons 35041 (.cons 43032 .nil)))))))))",
           "(.true, .cons 4 (.cons 1 (.cons 1 (.cons 26 (.cons 128 (.cons 123 (.cons 250 (.cons 41 (.cons 185 .nil)))))))))",
           "(.true, .cons 29 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 .nil)))))))))))))))))))))))))))))))))))))))))",
           "(.true, .cons 19 (.cons 0 (.cons 0 (.cons 0 (.cons 2 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 2 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 2 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 2 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 2 (.cons 2 (.cons 0 (.cons 0 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 2 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))",
           "\"module counter(input clk, input [0:0] rst, input [0:0] en, input [0:0] go, output [3:0] leds, output [0:0] top);\\n  reg [3:0] count; initial count = 4'd0;\\n  reg [0:0] up; initial up = 1'd1;\\n  wire [3:0] n6 = count + 4'd1;\\n  wire [3:0] n7 = count - 4'd1;\\n  wire [3:0] n8 = up ? n6 : n7;\\n  wire [3:0] next = go ? n8 : count;\\n  wire [0:0] n11 = next == 4'd9;\\n  wire [0:0] n13 = next == 4'd0;\\n  wire [0:0] n16 = n13 ? 1'd1 : up;\\n  wire [0:0] n17 = n11 ? 1'd0 : n16;\\n  wire [0:0] n18 = count == 4'd9;\\n  always @(posedge clk) if (rst) count <= 4'd0; else if (en) count <= next;\\n  always @(posedge clk) if (rst) up <= 1'd1; else if (en) up <= n17;\\n  assign leds = count;\\n  assign top = n18;\\nendmodule\\n\"",
           "\"set_io clk 21\\nset_io rst 1\\nset_io en 2\\nset_io go 3\\nset_io leds[0] 99\\nset_io leds[1] 98\\nset_io leds[2] 97\\nset_io leds[3] 96\\nset_io top 95\\nset_frequency clk 100\\n\"",
           ".cons \"no pin for port rst\" (.cons \"no pin for port en\" (.cons \"port leds has 4 bits, one pin given\" (.cons \"no pin for port top\" (.cons \"pin for no port: led\" .nil))))",
           "\"$timescale 1ns $end\\n$scope module counter $end\\n$var wire 1 ! clk $end\\n$var wire 1 \\\" go $end\\n$var wire 4 # leds $end\\n$var wire 1 $ top $end\\n$var wire 4 % count $end\\n$var wire 1 & up $end\\n$upscope $end\\n$enddefinitions $end\\n#0\\n0!\\n0\\\"\\nb0000 #\\n0$\\nb0000 %\\n1&\\n#1\\n1!\\n#2\\n0!\\n#3\\n1!\\n#4\\n0!\\n#5\\n1!\\n#6\\n0!\\n1\\\"\\n#7\\n1!\\n#8\\n\"",
           ".cons 17 (.cons 5 (.cons 4 .nil))"] },
    { name := "H14 T: temporal properties (UART idle-high and delivery for ever, valid/ready refinement, stability, liveness)", run := fun _ => do
        okLibs (← IO.FS.readFile "examples/hdl-temporal.wiz") },
    { name := "H14 T: temporal notation □ ◇ ○ ~> |-> |=>, printed back; `|=>` leaves `fun`/`match` alone (13o)", run := fun _ => do
        okLibs ("import Hdl.Temporal\n" ++
          "def p (a b : TL Nat) : TL Nat := □ (a ~> ◇ b)\n#check p\n#check fun (a b : TL Nat) => TL.always (TL.leadsTo a (TL.eventually b))\n" ++
          "#check fun (a b : TL Nat) => a |-> ○ b\n#check fun (a b : TL Nat) => a |=> b |-> a\n" ++
          "def q (n : Nat) : Nat := match n with\n  |.zero=>1\n  | .succ k => k\ndef r : Nat → Nat := fun x=>x\n#eval q 0")
          ["p : TL Nat → TL Nat → TL Nat", "fun a b => □ (a ~> ◇ b) : TL Nat → TL Nat → TL Nat",
           "fun a b => a |-> ○ b : TL Nat → TL Nat → TL Nat", "fun a b => a |=> b |-> a : TL Nat → TL Nat → TL Nat", "1"] },
    { name := "Verilog: Icarus Verilog accepts the emitted modules (skipped without iverilog on PATH)", run := fun _ => do
        let found ← (do let o ← IO.Process.output { cmd := "iverilog", args := #["-V"] }; pure (o.exitCode == 0)) <|> pure false
        unless found do skip "no iverilog"; return
        let s := runFrontend (R := ZeroOneMany) (hdlVerilogSrc ++ "#eval v1\n#eval v2\n#eval v3\n")
          { trustedModule := Tests.libModule, loader := ← libLoader }
        let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render ""
        unless errs.isEmpty do throw (IO.userError s!"unexpected errors: {errs}")
        IO.FS.withTempDir fun dir => do
          for m in s.messages.toList, i in [0:3] do
            -- the message is the string as `#eval` prints it: quoted, newlines escaped
            let text := ((m.text.drop 1).dropRight 1).replace "\\n" "\n"
            let file := dir / s!"m{i}.v"
            IO.FS.writeFile file text
            let o ← IO.Process.output { cmd := "iverilog", args := #["-g2005", "-o", (dir / "out.vvp").toString, file.toString] }
            unless o.exitCode == 0 do throw (IO.userError s!"iverilog rejects module {i}:\n{o.stderr}\n{text}")
        -- the composed circuits, and the generated test bench replaying the counter with
        -- reset and enable at random cycles against its value simulation
        let src ← IO.FS.readFile "examples/hdl-compose.wiz"
        let s := runFrontend (R := ZeroOneMany) (src ++ "\n#eval vCounter\n#eval vTwo\n#eval vPipe\n#eval tbCounter\n#eval vecCounter\n")
          { trustedModule := Tests.libModule, loader := ← libLoader }
        let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render ""
        unless errs.isEmpty do throw (IO.userError s!"unexpected errors: {errs}")
        let texts := (s.messages.toList.map (·.text)).drop 11
        let unq (t : String) : String := ((t.drop 1).dropRight 1).replace "\\n" "\n" |>.replace "\\\"" "\""
        IO.FS.withTempDir fun dir => do
          let names := ["counter.v", "two.v", "pipe.v", "tb.v", "counter.vec"]
          for t in texts, nm in names do IO.FS.writeFile (dir / nm) (unq t)
          for nm in ["two.v", "pipe.v"] do
            let o ← IO.Process.output { cmd := "iverilog", args := #["-g2005", "-o", (dir / "x.vvp").toString, (dir / nm).toString] }
            unless o.exitCode == 0 do throw (IO.userError s!"iverilog rejects {nm}:\n{o.stderr}")
          let o ← IO.Process.output { cmd := "iverilog", args := #["-g2005", "-o", (dir / "tb.vvp").toString, (dir / "tb.v").toString, (dir / "counter.v").toString], cwd := dir }
          unless o.exitCode == 0 do throw (IO.userError s!"iverilog rejects the test bench:\n{o.stderr}")
          let r ← IO.Process.output { cmd := "vvp", args := #["-n", (dir / "tb.vvp").toString], cwd := dir }
          unless (r.stdout.splitOn "PASS counter: 60 cycles").length > 1 do
            throw (IO.userError s!"test bench: {r.stdout}{r.stderr}")
        -- (H14 S4) the shifts by a signal and the signed comparisons: Icarus Verilog
        -- replays their value simulations
        let src ← IO.FS.readFile "examples/hdl-gaps.wiz"
        let s := runFrontend (R := ZeroOneMany) (src ++ "\n#eval vShift\n#eval tbShift\n#eval vecShift\n#eval vCmp\n#eval tbCmp\n#eval vecCmp\n")
          { trustedModule := Tests.libModule, loader := ← libLoader }
        let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render ""
        unless errs.isEmpty do throw (IO.userError s!"unexpected errors: {errs}")
        let all := s.messages.toList.map (·.text)
        let texts := all.drop (all.length - 6)
        IO.FS.withTempDir fun dir => do
          let names := ["shifts.v", "tbs.v", "shifts.vec", "cmps.v", "tbc.v", "cmps.vec"]
          for t in texts, nm in names do IO.FS.writeFile (dir / nm) (unq t)
          for (tb, m, pass) in [("tbs.v", "shifts.v", "PASS shifts: 200 cycles"), ("tbc.v", "cmps.v", "PASS cmps: 200 cycles")] do
            let o ← IO.Process.output { cmd := "iverilog", args := #["-g2005", "-o", (dir / "t.vvp").toString, (dir / tb).toString, (dir / m).toString], cwd := dir }
            unless o.exitCode == 0 do throw (IO.userError s!"iverilog rejects {m}:\n{o.stderr}")
            let r ← IO.Process.output { cmd := "vvp", args := #["-n", (dir / "t.vvp").toString], cwd := dir }
            unless (r.stdout.splitOn pass).length > 1 do
              throw (IO.userError s!"test bench {m}: {r.stdout}{r.stderr}") },
    { name := "fast netlist simulation (Hdl.Sim, compiled): = Netlist.simulate = Circuit.run, cycle for cycle; not well formed falls back", run := fun _ => do
        -- examples/hdl-sim.wiz: every netlist operation (shifts by a signal too), 70-bit widths, reset and enable, a
        -- table tree, composition, memories (two write ports, read-during-write, a ROM,
        -- out-of-range addresses); 3000 random cycles each, hash-consed and naive netlists
        cRunLibs (← IO.FS.readFile "examples/hdl-sim.wiz")
          ("alu: yes, 3000 cycles, well formed yes, checksum 840993931\n" ++
           "alu with reset and enable: yes, 3000 cycles, well formed yes, checksum 86608463\n" ++
           "piped: yes, 3000 cycles, well formed yes, checksum 623585979\n" ++
           "memories: yes, 3000 cycles, well formed yes, checksum 380888474\n" ++
           "memories, raw out-of-range values: simFast = simulate: yes\n" ++
           "shifter: yes, 3000 cycles, well formed yes, checksum 331396695\n" ++
           "not well formed: yes, simFast = simulate: yes\n") }
  ]

builtin_initialize registerGroup hdlGroup

end Tests.Elab
