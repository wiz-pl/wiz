import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- `lib/Plot.wiz`: exact rational data, linear and log scales, 1/2/5 × 10^k ticks and
deterministic SVG. The tick cases are properties (inside the domain, increasing,
multiples of a nice step); the four SVGs are byte-for-byte goldens in `Tests/data/plot/`,
so a diff there means the library changed the picture (or stopped being deterministic).

The Wiz sources and their expected outputs are top-level definitions: a raw string
inside a structure literal followed by another argument is a Lean parser gap, not a
Wiz one. -/
def plotTicksSrc : String := r#"import Plot
import Text

partial def inc : List Plot.Tick → Bool
  | .nil => .true
  | .cons _ .nil => .true
  | .cons a (.cons b rest) => Bool.and (Plot.qLt a.value b.value) (inc (.cons b rest))

def inside (b : Plot.Bounds) (t : Plot.Tick) : Bool :=
  Bool.and (Plot.qLe b.lo t.value) (Plot.qLe t.value b.hi)

def niceMant (m : Nat) : Bool :=
  Bool.or (Nat.beq m 1) (Bool.or (Nat.beq m 2) (Nat.beq m 5))

def multQ (step v : Q) : Bool :=
  Int.beq (Int.mod (Int.mul v.num step.den) (Int.mul v.den step.num)) 0

def mult (s : Plot.Step) (t : Plot.Tick) : Bool := multQ s.value t.value

def nrOk (lo hi : Q) : Bool :=
  let p := Plot.padBounds lo hi;
  let b := Plot.niceRange lo hi 6;
  let s := Plot.niceStep (Q.sub p.hi p.lo) 6;
  Bool.and (Bool.and (Plot.qLt b.lo b.hi)
      (Bool.and (Plot.qLe b.lo p.lo) (Plot.qLe p.hi b.hi)))
    (Bool.and (multQ s.value b.lo) (multQ s.value b.hi))

def okDomain (lo hi : Q) : Bool :=
  let b := Plot.padBounds lo hi;
  let s := Plot.niceStep (Q.sub b.hi b.lo) 6;
  let ts := Plot.ticksWith b s 6;
  let n := List.length ts;
  Bool.and (niceMant s.mant)
    (Bool.and (Bool.and (Nat.le 3 n) (Nat.le n 9))
      (Bool.and (List.all (inside b) ts) (Bool.and (inc ts) (List.all (mult s) ts))))

#eval List.map (fun p => okDomain p.1 p.2) [
  ((0 : Q), (1 : Q)), (0, Plot.frac 7 3), (5, 5), (-5, 5), (0, Plot.frac 1 1000000000),
  (999999, 1000001), (Plot.fracInt (-12345) 100, Plot.fracInt 6789 100)]
#eval nrOk 0 1
#eval nrOk (Plot.fracInt (-7) 3) (Plot.frac 22 7)
"#

def plotTicksExpected : List String := [
  ".cons .true (.cons .true (.cons .true (.cons .true (.cons .true (.cons .true (.cons .true .nil))))))",
  ".true", ".true"]

def plotDomainsSrc : String := r#"import Plot

def between (b : Plot.Bounds) (v : Q) : Bool :=
  Bool.and (Plot.qLt b.lo v) (Plot.qLt v b.hi)

def logLo (vs : List Q) (v : Q) : Bool := Plot.qEq (Plot.logBoundsOf vs).lo v
def logHi (vs : List Q) (v : Q) : Bool := Plot.qEq (Plot.logBoundsOf vs).hi v

#eval between (Plot.boundsOf [5] .false) 5
#eval between (Plot.boundsOf [0] .false) 0
#eval between (Plot.boundsOf [Plot.frac 1 1000000000000] .false) (Plot.frac 1 1000000000000)
#eval between (Plot.boundsOf [0, 10] .true) 0
#eval between (Plot.boundsOf [0, 10] .false) 0
#eval logLo [-3, 0, 5, 50] 1
#eval logHi [-3, 0, 5, 50] 100
#eval logLo [0] 1
#eval logHi [0] 10
#eval logLo [Plot.frac 1 1000000000, Plot.frac 1 1000000000] (Plot.frac 1 1000000000)
#eval logHi [Plot.frac 1 1000000000, Plot.frac 1 1000000000] (Plot.frac 1 100000000)
"#

def plotDomainsExpected : List String := [
  ".true", ".true", ".true", ".true", ".true", ".true",
  ".true", ".true", ".true", ".true", ".true"]

def plotLogSrc : String := r#"import Plot
import Text

partial def inc : List Plot.Tick → Bool
  | .nil => .true
  | .cons _ .nil => .true
  | .cons a (.cons b rest) => Bool.and (Plot.qLt a.value b.value) (inc (.cons b rest))

def inside (b : Plot.Bounds) (t : Plot.Tick) : Bool :=
  Bool.and (Plot.qLe b.lo t.value) (Plot.qLe t.value b.hi)

def mantOk (t : Plot.Tick) : Bool :=
  Bool.or (Int.beq t.mant 1) (Bool.or (Int.beq t.mant 2) (Int.beq t.mant 5))

def okLog (lo hi : Q) : Bool :=
  let b := Plot.logBoundsOf [lo, hi];
  let ts := Plot.logTicks b 6;
  Bool.and (List.all (fun t => Bool.and (inside b t) (mantOk t)) ts) (inc ts)

#eval List.map (fun p => okLog p.1 p.2) [
  ((1 : Q), (10 : Q)), (1, 100), (Plot.frac 1 1000, 3), (Plot.frac 1 1000000000, Plot.frac 9 1000000000)]
#eval List.length (Plot.logTicks (Plot.logBoundsOf [(1 : Q), 10]) 6)
#eval List.length (Plot.logTicks (Plot.logBoundsOf [(1 : Q), 100]) 6)
#eval List.map (fun t => Plot.showDec t.mant t.exp) (Plot.logTicks (Plot.logBoundsOf [(1 : Q), 10]) 6)
"#

def plotLogExpected : List String := [
  ".cons .true (.cons .true (.cons .true (.cons .true .nil)))", "4", "3",
  ".cons \"1\" (.cons \"2\" (.cons \"5\" (.cons \"10\" .nil)))"]

def plotRoundSrc : String := r#"import Plot
#eval Plot.qRound (Plot.frac 1 2)
#eval Plot.qRound (Plot.fracInt (-1) 2)
#eval Plot.qRound (Plot.frac 3 2)
#eval Plot.qRound (Plot.fracInt (-3) 2)
#eval Plot.showDec 2 (-1)
#eval Plot.showDec 1 3
#eval Plot.showDec 125 (-2)
#eval Plot.showDec (-1) 0
#eval Plot.showQ (Plot.frac 1 3)
"#

def plotRoundExpected : List String := [
  "1", "-1", "2", "-2", "\"0.2\"", "\"1000\"", "\"1.25\"", "\"-1\"", "\"0.333333333333\""]

def plotGoldenSrc : String := r#"import IO
import Plot

def lineData : Plot.Frame := Plot.frame [
  Plot.line "revenue" [Plot.pt 0 3, Plot.pt 1 5, Plot.pt 2 4, Plot.pt 3 8]]

def scatterData : Plot.Frame := Plot.frame [
  Plot.scatter "samples" [Plot.pt 0 1, Plot.pt 1 4, Plot.pt 2 2, Plot.pt 3 6]]

def barData : Plot.Frame := Plot.frame [
  Plot.bar "delta" [Plot.pt 0 3, Plot.pt 1 (-1), Plot.pt 2 2, Plot.pt 3 5]]

def histogramData : Plot.Frame := Plot.frame [
  Plot.bar "count" [Plot.ptNat 0 2, Plot.ptNat 1 7, Plot.ptNat 2 5, Plot.ptNat 3 9,
    Plot.ptNat 4 3, Plot.ptNat 5 1]]

def lineChart : Plot.Chart :=
  Plot.labels "x" "y" (Plot.chart "Line" lineData)
def scatterChart : Plot.Chart :=
  Plot.labels "x" "y" (Plot.size 320 240 (Plot.chart "Scatter" scatterData))
def barChart : Plot.Chart :=
  Plot.labels "x" "y" (Plot.size 320 240 (Plot.chart "Bar" barData))
def histogramChart : Plot.Chart :=
  Plot.labels "bin" "count" (Plot.size 320 240 (Plot.chart "Histogram" histogramData))

def main : IO Unit := do
  IO.print (Plot.svg lineChart);
  IO.print "\n@@\n";
  IO.print (Plot.svg scatterChart);
  IO.print "\n@@\n";
  IO.print (Plot.svg barChart);
  IO.print "\n@@\n";
  IO.print (Plot.svg histogramChart);
  IO.print "\n@@\n";
  IO.print (Plot.svg lineChart);
  IO.print "\n@@\n";
  IO.print (Plot.svg lineChart)
"#

def plotGroup : Group where
  name := "plot"
  exercise := "lib/Plot.wiz"
  parallel := true
  cases := [
    { name := "linear ticks: 1/2/5 step, inside the domain, increasing, integer multiples (awkward domains)", run := fun _ =>
        okLibs plotTicksSrc plotTicksExpected },
    { name := "domains: one point, all-equal, zero, tiny magnitudes, bars include zero; log drops ≤ 0", run := fun _ =>
        okLibs plotDomainsSrc plotDomainsExpected },
    { name := "log ticks: 1/2/5 mantissas, inside the domain, increasing; wide domains use decades", run := fun _ =>
        okLibs plotLogSrc plotLogExpected },
    { name := "rounding and decimal text are pinned (halves away from zero, exact tick labels)", run := fun _ =>
        okLibs plotRoundSrc plotRoundExpected },
    { name := "golden SVGs: line, scatter, bar, histogram (byte for byte, twice the same)", run := fun _ => do
        let line ← IO.FS.readFile "Tests/data/plot/line.svg"
        let scatter ← IO.FS.readFile "Tests/data/plot/scatter.svg"
        let bar ← IO.FS.readFile "Tests/data/plot/bar.svg"
        let histogram ← IO.FS.readFile "Tests/data/plot/histogram.svg"
        let expected := String.intercalate "\n@@\n"
          [line, scatter, bar, histogram, line, line]
        cRunLibs plotGoldenSrc expected },
    { name := "examples/plot.wiz regenerates the figure docs/libraries.md shows (docs/assets/plot-example.svg)", run := fun _ => do
        cRunLibs (← IO.FS.readFile "examples/plot.wiz")
          (← IO.FS.readFile "docs/assets/plot-example.svg") }
  ]

builtin_initialize registerGroup plotGroup

end Tests.Elab
