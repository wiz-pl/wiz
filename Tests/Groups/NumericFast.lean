import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-!
# Numeric and data-structure fast paths (audit W3)

Regression tests for the helpers changed on `agent/numeric-fast`:

* `HTrie.hashBits`/`HTrie.find`/`HTrie.insert` (lib/Hdl/Core.wiz): the hash's bits are
  computed once per key and threaded through the levels (no `Nat.testBit h d` per node);
  the netlist of a known design is unchanged, and colliding keys share a bucket;
* `Json.natChars`/`Json.u4` (lib/Json.wiz): native `Nat.div`/`Nat.mod`, no hand-rolled
  `Json.divMod`;
* `Ring.Key.cmp`/`Ring.Key.cmp_eq` (lib/Ring.wiz): native `Nat.beq`/`Nat.lt` rather than
  `Nat.cmp`; `nat_ring!` still proves identities and the proofs stay axiom-free.
-/

def numericFastHdl : String := "import Hdl.Core
def u8 : HwTy := HwTy.bits 8
def c1 : Circuit (HwTy.bits 1) u8 := Circuit.mk u8 (BitVec.ofNat 8 250) (fun s u => Hw.pair (Hw.add s (Hw.lit 8 1)) s)
def sq (n : Nat) : Nat := Nat.mul n n
def build : Nat → HTrie Nat → HTrie Nat
  | .zero, t => HTrie.putN 0 0 t
  | .succ n, t => build n (HTrie.putN (Nat.succ n) (sq (Nat.succ n)) t)
def check : Nat → HTrie Nat → Bool
  | .zero, t => match HTrie.getN 0 t with
    | .some v => Nat.beq v 0
    | .none => .false
  | .succ n, t => Bool.and (match HTrie.getN (Nat.succ n) t with
      | .some v => Nat.beq v (sq (Nat.succ n))
      | .none => .false) (check n t)
def keyA : List Nat := .cons 1 .nil
def keyB : List Nat := .cons 2 .nil
def tA : HTrie Nat := HTrie.insert keyA 1 HTrie.tip (HTrie.hashBits 7)
def tAB : HTrie Nat := HTrie.insert keyB 2 tA (HTrie.hashBits 7)
#eval check 100 (build 100 HTrie.tip)
#eval List.length (HTrie.hashBits 12345)
#eval HTrie.find keyA tAB (HTrie.hashBits 7)
#eval HTrie.find keyB tAB (HTrie.hashBits 7)
#eval List.length (Circuit.netlist \"counter\" c1).nodes
#eval Verilog.emit (Circuit.netlist \"counter\" c1)
"

def numericFastJson : String := "import Json
def emoji : String := .mk (List.cons (Json.chr 0x1F600) .nil)
#eval Json.render (Json.ofNat 123456789012345678901234567890)
#eval Json.renderAscii (Json.mkStr emoji)
#eval Json.render (Json.mkArr (List.cons (Json.ofNat 42) (List.cons (Json.mkStr \"λ\") .nil)))
"

def numericFastRing : String := "import Ring
def ordN (o : Ordering) : Nat := match o with
  | .lt => 0
  | .eq => 1
  | .gt => 2
def t (a b c : Nat) : (a + b) * (a + c) = a * a + a * c + b * a + b * c :=
  nat_ring! (a + b) * (a + c) = a * a + a * c + b * a + b * c
#eval ordN (Ring.Key.cmp (List.cons 1 (List.cons 2 .nil)) (List.cons 1 (List.cons 3 .nil)))
#eval ordN (Ring.Key.cmp (List.cons 2 .nil) (List.cons 2 .nil))
#eval ordN (Ring.Key.cmp (List.cons 3 .nil) (List.cons 2 .nil))
#eval ordN (Ring.Key.cmp .nil (List.cons 1 .nil))
#eval ordN (Ring.Key.cmp (List.cons 1 .nil) .nil)
#print axioms Ring.Key.cmpCons_eq
#print axioms Ring.Key.cmp_eq
#print axioms NatPoly.eval_add
#print axioms t
"

def numericFastRingShared : String := "import IntRing
import Rat
def ti (a b : Int) : (a - b) * (a + b) = a * a - b * b := int_ring! (a - b) * (a + b) = a * a - b * b
def tq (p q : Q) : (p + q) * (p + q) ≈ p * p + 2 * p * q + q * q :=
  q_ring! (p + q) * (p + q) ≈ p * p + 2 * p * q + q * q
#print axioms ti
#print axioms tq
"

def numericFastGroup : Group where
  name := "numeric-fast"
  exercise := "Audit W3 (numeric/data fast paths)"
  cases := [
    { name := "HTrie: threaded hash bits, maps round-trip, colliding buckets, the netlist is unchanged", run := fun _ =>
        okLibs numericFastHdl
          [".true", "20", ".some 1", ".some 2", "4",
           "\"module counter(input clk, input [0:0] x, output [7:0] y);\\n  reg [7:0] r; initial r = 8'd250;\\n  wire [7:0] n3 = r + 8'd1;\\n  always @(posedge clk) r <= n3;\\n  assign y = r;\\nendmodule\\n\""] },
    { name := "Json: decimals and \\u escapes use the native division", run := fun _ =>
        okLibs numericFastJson
          ["\"123456789012345678901234567890\"", "\"\\\"\\\\ud83d\\\\ude00\\\"\"", "\"[42,\\\"λ\\\"]\""] },
    { name := "Ring: key comparison is native, nat_ring! still proves, no axioms", run := fun _ =>
        okLibs numericFastRing
          ["0", "1", "2", "0", "2",
           "'Ring.Key.cmpCons_eq' does not depend on any axioms",
           "'Ring.Key.cmp_eq' does not depend on any axioms",
           "'NatPoly.eval_add' does not depend on any axioms",
           "'t' does not depend on any axioms"] },
    { name := "Ring's key comparison is shared: int_ring! and q_ring! still prove, no axioms", run := fun _ =>
        okLibs numericFastRingShared
          ["'ti' does not depend on any axioms", "'tq' does not depend on any axioms"] }
  ]

builtin_initialize registerGroup numericFastGroup

end Tests.Elab
