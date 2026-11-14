import Wiz
import Tests.Harness
import Tests.Elab

/-!
# S5: the abstract-interpretation core (`lib/Scry/Ai*.wiz`)

The hand-built CFGs in `lib/Scry/AiExamples.wiz` exercise the parts of stage S5 that do
not need Wil:

* a loop that needs widening, and one narrowing pass that makes its post-fixpoint
  precise enough for the checker to accept;
* a constant/interval proof (`z = x * y`, so `z = 6`);
* a nullness alarm and an out-of-bounds alarm;
* an overflow alarm;
* a post-fixpoint the checker must reject (an unsound edge);
* the domain operations (join, widen, narrow, width wrap-around).

Every case elaborates a small Wiz program with `lib/` importable and compares the
`#eval` texts, so the values are computed by the Wiz evaluator (the model), not by Lean.
-/

set_option compiler.extract_closed false

open Wiz

namespace Tests.ScryAi

open Tests
open Tests.Elab (okLibs)

/-- The widening case: the widened post-fixpoint is `Top` at the loop head and is
rejected; after `narrowOnce` the body is `[0, 999]` and the checker accepts. -/
def wideningSrc : String := "import Scry.AiExamples

#eval Interval.isTop (AiEx.valueAt AiEx.loopCfg AiEx.loopInv 1 0).itv
#eval accepts AiEx.m16 AiEx.loopCfg AiEx.loopInv
#eval Interval.hiOpt (AiEx.valueAt AiEx.loopCfg AiEx.loopInvNarrow 2 0).itv
#eval accepts AiEx.m16 AiEx.loopCfg AiEx.loopInvNarrow
"

/-- The constant proof: `x := 2; y := 3; z := x * y`. -/
def constSrc : String := "import Scry.AiExamples

#eval accepts AiEx.m8 AiEx.constCfg AiEx.constInv
#eval Interval.hiOpt (AiEx.valueAt AiEx.constCfg AiEx.constInv 3 2).itv
"

/-- Nullness: the null dereference alarms, a safe array load does not. -/
def nullSrc : String := "import Scry.AiExamples

#eval Alarm.has (Alarm.nullDeref 1) (check AiEx.m8 AiEx.nullCfg AiEx.nullInv)
#eval alarmCount (check AiEx.m8 AiEx.nullCfg AiEx.nullInv)
#eval List.isEmpty (check AiEx.m8 AiEx.safeArrayCfg AiEx.safeArrayInv)
"

/-- Out of bounds: `p[8]` on an array of length 4. -/
def oobSrc : String := "import Scry.AiExamples

#eval Alarm.has (Alarm.outOfBounds 1 8 4) (check AiEx.m8 AiEx.oobCfg AiEx.oobInv)
"

/-- Overflow: `x + 1` with `x` unknown at 8 bits. -/
def ovfSrc : String := "import Scry.AiExamples

#eval Alarm.has (Alarm.overflow 0 \"add\") (check AiEx.m8 AiEx.ovfCfg AiEx.ovfInv)
"

/-- An unsound post-fixpoint: `z = 5` where the transfer gives `z = 6`; the checker
reports `unsoundEdge 2 3` and does not accept. -/
def unsoundSrc : String := "import Scry.AiExamples

#eval accepts AiEx.m8 AiEx.constCfg AiEx.constBadInv
#eval Alarm.has (Alarm.unsoundEdge 2 3) (check AiEx.m8 AiEx.constCfg AiEx.constBadInv)
"

/-- The domain operations, independent of the CFG. -/
def latticeSrc : String := "import Scry.AiExamples

#eval Interval.le (Interval.join (Interval.range 0 2) (Interval.range 5 7)) (Interval.range 0 7)
#eval Interval.contains (Interval.join (Interval.range 0 2) (Interval.range 5 7)) 6
#eval Interval.isTop (Interval.widen (Interval.range 0 2) (Interval.range 0 3))
#eval Interval.hiOpt (Interval.narrow (Interval.range 0 9) (Interval.range 0 7))
"

/-- Machine widths: a sum that wraps becomes `Top`, a safe one stays a point, and
unsigned subtraction that would underflow is `Top`. -/
def widthSrc : String := "import Scry.AiExamples

#eval Interval.isTop (AExpr.eval AiEx.m8 [] (AExpr.add (AExpr.lit 250) (AExpr.lit 10))).itv
#eval Interval.hiOpt (AExpr.eval AiEx.m8 [] (AExpr.add (AExpr.lit 2) (AExpr.lit 3))).itv
#eval Interval.isTop (AExpr.eval AiEx.m8 [] (AExpr.sub (AExpr.lit 5) (AExpr.lit 9))).itv
"


-- ## The Wil path (`lib/Scry/AiWil*.wiz`)

/-- Constant/interval proof over `Wil.Stmt`s: `x := 2; y := 3; z := x * y` in three
blocks, with `WCfg.ofFunc` deriving the edges from the Wil terminators. -/
def wilConstSrc : String := "import Scry.AiWilExamples

#eval acceptsW AiWEx.m8u AiWEx.constCfg AiWEx.constInv
#eval Interval.hiOpt (AiWEx.valueAt AiWEx.constCfg AiWEx.constInv 3 2).uItv
"

/-- The Wil loop needs widening; the widened post-fixpoint is rejected because `i + 1`
may overflow, one narrowing pass (with the `< 10` guard refinement) accepts. -/
def wilLoopSrc : String := "import Scry.AiWilExamples

#eval Interval.isTop (AiWEx.valueAt AiWEx.loopCfg AiWEx.loopInv 1 0).uItv
#eval acceptsW AiWEx.m8u AiWEx.loopCfg AiWEx.loopInv
#eval Interval.hiOpt (AiWEx.valueAt AiWEx.loopCfg AiWEx.loopInvNarrow 2 0).uItv
#eval acceptsW AiWEx.m8u AiWEx.loopCfg AiWEx.loopInvNarrow
"

/-- Nullness from Wil's `.nul`, exact and symbolic lengths: an in-bounds load is safe, a
`p[8]` on length 4 alarms, and a symbolic `atLeast 0` length proves nothing (soundly). -/
def wilMemorySrc : String := "import Scry.AiWilExamples

#eval Alarm.has (Alarm.nullDeref 0) (checkW AiWEx.m8u AiWEx.nullCfg AiWEx.nullInv)
#eval List.isEmpty (checkW AiWEx.m8u AiWEx.safeArrayCfg AiWEx.safeArrayInv)
#eval Alarm.has (Alarm.outOfBounds 1 8 4) (checkW AiWEx.m8u AiWEx.oobCfg AiWEx.oobInv)
#eval List.isEmpty (checkW AiWEx.m8u AiWEx.symSafeCfg AiWEx.symSafeInv)
#eval Alarm.has (Alarm.outOfBoundsSym 1 0 0) (checkW AiWEx.m8u AiWEx.symTopCfg AiWEx.symTopInv)
"

/-- Overflow: unsigned keeps the conservative alarm; signed alarms only under the
undefined-behaviour policy, while the `.wrap` policy treats it as defined. -/
def wilOverflowSrc : String := "import Scry.AiWilExamples

#eval Alarm.has (Alarm.overflow 0 \"add\") (checkW AiWEx.m8u AiWEx.ovfU8Cfg AiWEx.ovfU8Inv)
#eval Alarm.has (Alarm.overflow 0 \"add\") (checkW AiWEx.m8s AiWEx.ovfS8Cfg AiWEx.ovfS8Inv)
#eval List.isEmpty (checkW AiWEx.m8w AiWEx.ovfS8Cfg AiWEx.ovfS8WrapInv)
#eval List.isEmpty (checkW AiWEx.m8s AiWEx.safeS8Cfg AiWEx.safeS8Inv)
"

/-- The Wil checker rejects an unsound post-fixpoint (`z = 5` where the edge gives 6). -/
def wilUnsoundSrc : String := "import Scry.AiWilExamples

#eval acceptsW AiWEx.m8u AiWEx.constCfg AiWEx.constBadInv
#eval Alarm.has (Alarm.unsoundEdge 2 3) (checkW AiWEx.m8u AiWEx.constCfg AiWEx.constBadInv)
"

/-- Signed interval algebra: exact signed ranges, an out-of-range sum and a product
become `Top`, and signed constants compute. -/
def signedSrc : String := "import Scry.AiWilExamples

#eval SInterval.loOpt (SInterval.add AiWEx.m8s (SInterval.range (-3) 10) (SInterval.range 1 2))
#eval SInterval.hiOpt (SInterval.add AiWEx.m8s (SInterval.range (-3) 10) (SInterval.range 1 2))
#eval SInterval.isTop (SInterval.add AiWEx.m8s (SInterval.range 120 120) (SInterval.range 10 10))
#eval SInterval.isTop (SInterval.mul AiWEx.m8s (SInterval.range (-100) (-100)) (SInterval.range 2 2))
#eval SConst.beq (SConst.addC AiWEx.m8s (SConst.known (-3)) (SConst.known 1)) (SConst.known (-2))
"

/-- The γ instance is the pointwise product, and the small literal CFG's certificate is
checked by the kernel: `AiWEx.litAccepted` is `rfl`. -/
def gammaReflSrc : String := "import Scry.AiWilExamples

#eval Value.gamma (Value.ofNat 3) (VState.mk 3 Bool.false)
#eval acceptsW AiWEx.m8u AiWEx.litCfg AiWEx.litInv
#eval Nat.beq (WState.at AiWEx.litCfg AiWEx.litInv 1).length 2
"

/-- The γ laws of `Scry.AiLaws` are proved: their `#print axioms` is clean (no
`castRefl`, no `native_refl`, no `sorry`). -/
def lawsSrc : String := "import Scry.AiLaws

#print axioms Interval.contains_mono
#print axioms Interval.contains_join
#print axioms Const.gamma_mono
#print axioms Const.gamma_join_sound
#print axioms Null.gamma_mono
#print axioms Null.gamma_join_sound
#print axioms Value.gamma_norm
#print axioms Value.gamma_mono
#print axioms Value.gamma_join_sound
#print axioms Env.gamma_join_sound
#print axioms Env.gamma_mono
"

/-- The Wil-facing γ laws (`Scry.AiWLaws`) are proved too, including the signed
intervals (the Boolean `Int.le` order theory), so all of them are unconditional. -/
def wilLawsSrc : String := "import Scry.AiWLaws

#print axioms SInterval.contains_mono
#print axioms SInterval.contains_join
#print axioms SConst.gamma_mono
#print axioms SConst.gamma_join_sound
#print axioms NumV.gamma_mono
#print axioms NumV.gamma_join_sound
#print axioms WValue.gamma_norm
#print axioms WValue.gamma_mono
#print axioms WValue.gamma_join_sound
#print axioms WEnv.gamma_join_sound
#print axioms WEnv.gamma_mono
"

/-- The checker's edge side is proved (`Scry.AiWSound.checkW_sound`): acceptance gives
every `cfg.edges` post-fixpoint condition. -/
def soundSrc : String := "import Scry.AiWSound

#print axioms checkW_sound
"

/-- `cRunLibs`, but a missing C compiler is a skip (this host has no `cc`; CI does). -/
def compiledOrSkip (src expected : String) (llvm : Bool) : IO Unit := do
  try
    Elab.cRunLibs src expected (llvm := llvm)
  catch e =>
    let msg := toString e
    if (msg.splitOn "could not execute external process").length > 1 then
      skip s!"no C toolchain ({msg})"
    else
      throw e

/-- The same example compiled to C and LLVM (`examples/scry-ai-wil.wiz`, digest 111111). -/
def wilCompiled : IO Unit := do
  let src ← IO.FS.readFile "examples/scry-ai-wil.wiz"
  compiledOrSkip src "111111" false
  compiledOrSkip src "111111" true

def scryGroup : Group where
  name := "scry-ai"
  exercise := "S5 (code-analysis-design §4.6, §5.3)"
  cases := [
    { name := "widening: the loop reaches a post-fixpoint; one narrowing pass lets the checker accept",
      run := fun _ => okLibs wideningSrc [".true", ".false", ".some 999", ".true"] },
    { name := "constant/interval proof: z := x * y with x = 2, y = 3 gives z = 6 and no alarm",
      run := fun _ => okLibs constSrc [".true", ".some 6"] },
    { name := "nullness: a null dereference alarms, a safe array load does not",
      run := fun _ => okLibs nullSrc [".true", "1", ".true"] },
    { name := "out of bounds: p[8] on a fresh array of length 4 alarms",
      run := fun _ => okLibs oobSrc [".true"] },
    { name := "overflow: x + 1 with x unknown at 8 bits alarms",
      run := fun _ => okLibs ovfSrc [".true"] },
    { name := "an unsound post-fixpoint is rejected (unsoundEdge 2 3)",
      run := fun _ => okLibs unsoundSrc [".false", ".true"] },
    { name := "lattice: join, contains, widen and narrow",
      run := fun _ => okLibs latticeSrc [".true", ".true", ".true", ".some 7"] },
    { name := "widths: wrap-around and underflow become Top, a safe sum stays exact",
      run := fun _ => okLibs widthSrc [".true", ".some 5", ".true"] },
    { name := "Wil constants: x := 2; y := 3; z := x * y proves z = 6 (WCfg.ofFunc)",
      run := fun _ => okLibs wilConstSrc [".true", ".some 6"] },
    { name := "Wil loop: widening reaches Top and is rejected; one narrowing pass accepts",
      run := fun _ => okLibs wilLoopSrc [".true", ".false", ".some 9", ".true"] },
    { name := "Wil memory: null, exact and symbolic lengths, safe and out-of-bounds loads",
      run := fun _ => okLibs wilMemorySrc [".true", ".true", ".true", ".true", ".true"] },
    { name := "Wil overflow: unsigned and signed UB alarm; signed wrap does not",
      run := fun _ => okLibs wilOverflowSrc [".true", ".true", ".true", ".true"] },
    { name := "Wil unsound: a post-fixpoint claiming z = 5 is rejected (unsoundEdge 2 3)",
      run := fun _ => okLibs wilUnsoundSrc [".false", ".true"] },
    { name := "signed intervals: exact sums, out-of-range add/mul become Top",
      run := fun _ => okLibs signedSrc [".some -2", ".some 12", ".true", ".true", ".true"] },
    { name := "gamma/refl: the product gamma and a kernel-checked certificate on a small Wil CFG",
      run := fun _ => okLibs gammaReflSrc ["()", ".true", ".true"] },
    { name := "gamma laws: interval/const/null/value/env monotonicity and joins are proved (no axioms)",
      run := fun _ => okLibs lawsSrc [
        "'Interval.contains_mono' does not depend on any axioms",
        "'Interval.contains_join' does not depend on any axioms",
        "'Const.gamma_mono' does not depend on any axioms",
        "'Const.gamma_join_sound' does not depend on any axioms",
        "'Null.gamma_mono' does not depend on any axioms",
        "'Null.gamma_join_sound' does not depend on any axioms",
        "'Value.gamma_norm' does not depend on any axioms",
        "'Value.gamma_mono' does not depend on any axioms",
        "'Value.gamma_join_sound' does not depend on any axioms",
        "'Env.gamma_join_sound' does not depend on any axioms",
        "'Env.gamma_mono' does not depend on any axioms"] },
    { name := "Wil gamma laws: signed intervals, SConst/NumV/WValue/WEnv laws are proved",
      run := fun _ => okLibs wilLawsSrc [
        "'SInterval.contains_mono' does not depend on any axioms",
        "'SInterval.contains_join' does not depend on any axioms",
        "'SConst.gamma_mono' does not depend on any axioms",
        "'SConst.gamma_join_sound' does not depend on any axioms",
        "'NumV.gamma_mono' does not depend on any axioms",
        "'NumV.gamma_join_sound' does not depend on any axioms",
        "'WValue.gamma_norm' does not depend on any axioms",
        "'WValue.gamma_mono' does not depend on any axioms",
        "'WValue.gamma_join_sound' does not depend on any axioms",
        "'WEnv.gamma_join_sound' does not depend on any axioms",
        "'WEnv.gamma_mono' does not depend on any axioms"] },
    { name := "checker soundness: acceptance implies every CFG edge's post-fixpoint (checkW_sound)",
      run := fun _ => okLibs soundSrc ["'checkW_sound' does not depend on any axioms"] },
    { name := "the Wil checker compiled to C and LLVM (digest 111111)",
      run := fun _ => wilCompiled }
  ]

builtin_initialize registerGroup scryGroup

end Tests.ScryAi
