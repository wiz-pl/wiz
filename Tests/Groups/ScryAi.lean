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
      run := fun _ => okLibs widthSrc [".true", ".some 5", ".true"] }
  ]

builtin_initialize registerGroup scryGroup

end Tests.ScryAi
