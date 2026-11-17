import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- `lib/TestRun/*.wiz` (stage 33): the test runner's pure core. Every case is a Wiz
program whose `#eval`s print a transcript: selection, plans, records and goldens, and the
scheduler fed scripted events on a virtual clock (`Sched.runScript`, `Sched.simulate`),
with no process at all. The expected outputs were produced by `wiz check` on master's
toolchain and checked by hand (docs/stages/33-test-runner.md). -/
def testRunGroup : Group where
  name := "testrun"
  exercise := "lib/TestRun (stage 33)"
  cases := [
    { name := "admission (33c): fits, alone, waits; admit_le, release_le, release_take and OkPool.admit use no axioms", run := fun _ =>
        okLibs r##"import TestRun.Budget
import Text
def show (o : Option Grant) : String := match o with
  | .some g => String.join ["held ", Nat.repr g.held, ", reserved ", Nat.repr g.pool.reserved, "/", Nat.repr g.pool.budget, ", running ", Nat.repr g.pool.running]
  | .none => "waits"
def p : Pool := Pool.take (Pool.new 1000 2) 600
#eval show (Pool.admit (Pool.new 1000 2) 300)
#eval show (Pool.admit (Pool.new 1000 2) 5000)
#eval show (Pool.admit p 400)
#eval show (Pool.admit p 500)
#eval show (Pool.admit (Pool.take p 100) 50)
#eval (Pool.release (Pool.take p 250) 250).reserved
#print axioms Budget.admit_le
#print axioms Budget.release_le
#print axioms Budget.release_take
#print axioms OkPool.admit
"##
          [r##""held 300, reserved 300/1000, running 1""##,
           r##""held 1000, reserved 1000/1000, running 1""##,
           r##""held 400, reserved 1000/1000, running 2""##,
           r##""waits""##,
           r##""waits""##,
           r##"600"##,
           r##"'Budget.admit_le' does not depend on any axioms"##,
           r##"'Budget.release_le' does not depend on any axioms"##,
           r##"'Budget.release_take' does not depend on any axioms"##,
           r##"'OkPool.admit' does not depend on any axioms"##] },
    { name := "ids (33a): slugs, the 64-character cut, -2/-3 on repeats, golden ids", run := fun _ =>
        okLibs r##"import TestRun.Id
#eval TestRun.slug "Direct induction hypotheses agree with the template on every Desc"
#eval TestRun.slug "  λ-calculus: `id id` reduces!  "
#eval TestRun.slug "a very long name that goes on and on and on, past the sixty-four character limit of slugs"
#eval TestRun.ids "json" ["parse x", "Parse X", "render", "parse  x"]
#eval TestRun.goldenId "wiz-rv" "tests/long.wiz"
"##
          [r##""direct-induction-hypotheses-agree-with-the-template-on-every-des""##,
           r##""calculus-id-id-reduces""##,
           r##""a-very-long-name-that-goes-on-and-on-and-on-past-the-sixty-four""##,
           r##".cons "json/parse-x" (.cons "json/parse-x-2" (.cons "json/render" (.cons "json/parse-x-3" .nil)))"##,
           r##""wiz-rv:tests/long.wiz""##] },
    { name := "globs (33a): *, ?, ** and **/ (no directory included)", run := fun _ =>
        okLibs r##"import TestRun.Id
#eval TestRun.glob "tests/**/*.wiz" "tests/rv/a.wiz"
#eval TestRun.glob "tests/**/*.wiz" "tests/a.wiz"
#eval TestRun.glob "tests/**/*.wiz" "tests/rv/arch/b.wiz"
#eval TestRun.glob "tests/*.wiz" "tests/rv/a.wiz"
#eval TestRun.glob "tests/rv/**" "tests/rv/x/y.wiz"
#eval TestRun.glob "t?sts/a.wiz" "tests/a.wiz"
#eval TestRun.glob "t?sts/a.wiz" "t/sts/a.wiz"
#eval TestRun.glob "tests/a.wiz" "tests/a.wizz"
#eval TestRun.glob "**" ""
"##
          [r##".true"##,
           r##".true"##,
           r##".true"##,
           r##".false"##,
           r##".true"##,
           r##".true"##,
           r##".false"##,
           r##".false"##,
           r##".true"##] },
    { name := "selection (33a): every selector form, filters, and the errors (a flag, nothing matched, bad indices)", run := fun _ =>
        okLibs r##"import TestRun.Id
def tagged (c : CaseInfo) (tags : List String) (shard : String) (part : Nat) : CaseInfo :=
  CaseInfo.mk c.id c.group c.index c.name c.path tags shard part
def cs : List CaseInfo := [
  tagged (CaseInfo.lean "json" 0 "parse a document" "json/parse-a-document") .nil "library" 1,
  tagged (CaseInfo.lean "json" 1 "render escapes" "json/render-escapes") ["slow"] "library" 2,
  tagged (CaseInfo.lean "jsonx" 0 "extra" "jsonx/extra") .nil "library" 2,
  tagged (CaseInfo.golden "rv" 0 "tests/rv/a.wiz") ["hdl", "slow"] "rv" 0]
def ids (r : Except String (List CaseInfo)) : String := match r with
  | .ok l => String.intercalate " " (List.map (fun c => c.id) l)
  | .error e => String.join ["error: ", e]
def sel (ss : List String) : String := ids (TestRun.select (SelCtx.mk ["jsonx/extra"] .nil) ss cs)
#eval sel []
#eval sel ["=json"]
#eval sel ["json"]
#eval sel ["=json#1"]
#eval sel ["=json/render-escapes"]
#eval sel ["tests/**"]
#eval sel ["~render"]
#eval sel ["+slow"]
#eval sel ["json", "-slow"]
#eval sel ["json", "!=jsonx"]
#eval sel ["@shard:library/2"]
#eval sel ["@failed"]
#eval sel ["@changed"]
#eval sel ["=nope"]
#eval sel ["--jobs"]
#eval sel ["=json#x"]
#eval sel ["@shard:"]
#eval sel ["@later"]
"##
          [r##""json/parse-a-document json/render-escapes jsonx/extra rv:tests/rv/a.wiz""##,
           r##""json/parse-a-document json/render-escapes""##,
           r##""json/parse-a-document json/render-escapes jsonx/extra""##,
           r##""json/render-escapes""##,
           r##""json/render-escapes""##,
           r##""rv:tests/rv/a.wiz""##,
           r##""json/render-escapes""##,
           r##""json/render-escapes rv:tests/rv/a.wiz""##,
           r##""json/parse-a-document jsonx/extra""##,
           r##""json/parse-a-document json/render-escapes""##,
           r##""json/render-escapes jsonx/extra""##,
           r##""jsonx/extra""##,
           r##""""##,
           r##""error: selector =nope matches no test""##,
           r##""error: unknown flag --jobs""##,
           r##""error: selector =json#x: case indices are numbers (=G#3,7)""##,
           r##""error: selector @shard: matches no test""##,
           r##""error: selector @later: unknown (@shard:NAME[/k], @failed, @changed)""##] },
    { name := "the plan (33b): declared/learned/default limits, drift, scaling, LPT order and packing by fixture", run := fun _ =>
        okLibs r##"import TestRun.Plan
def showL (l : Limits) : String := String.join [Nat.repr (l.timeoutMs / 1000), "s ", Nat.repr l.memMib, "M ", Source.name l.source]
def info (id : String) : CaseInfo := CaseInfo.lean "g" 0 id id
#eval showL (Limits.learn (Learned.mk 2000 400 5))
#eval showL (Limits.learn (Learned.mk 90000 3600 5))
#eval showL (Limits.resolve .run .none .none .none)
#eval showL (Limits.resolve .check (.some 900000) .none (.some (Learned.mk 2000 100 3)))
#eval showL (Limits.resolve .lean .none (.some 6144) (.some (Learned.mk 2000 100 3)))
#eval showL (Limits.scale 2500 (Kind.defaults .fixture))
#eval Limits.drift (.some 300) (.some (Learned.mk 1000 400 3))
#eval Limits.drift (.some 3000) (.some (Learned.mk 1000 400 3))
def mk (id : String) (est : Nat) (fx : List String) : Case :=
  Case.mk (info id) .lean (Kind.defaults .lean) est fx
def ids (cs : List Case) : String := String.intercalate " " (List.map (fun c => c.info.id) cs)
#eval ids (Plan.order [mk "a" 10 [], mk "b" 50 [], Case.make (info "checker") .fixture .none .none .none [], mk "c" 50 [], mk "d" 30 []])
def shard : List Case := [mk "a" 10 [], mk "b" 50 ["checker"], mk "c" 40 ["checker"], mk "d" 60 [], mk "e" 20 [], mk "f" 35 []]
#eval String.intercalate " | " (List.map (fun p => String.join [Nat.repr p.load, ": ", ids p.cases]) (Plan.pack 2 shard))
#eval String.intercalate " | " (List.map (fun p => String.join [Nat.repr p.load, ": ", ids p.cases]) (Plan.pack 3 shard))
#eval Plan.count (Plan.pack 4 shard)
#eval TestRun.sortBy Nat.lt [5, 3, 9, 1, 3, 7, 0, 2, 8]
"##
          [r##""60s 564M learned""##,
           r##""360s 4564M learned""##,
           r##""300s 1536M default""##,
           r##""900s 256M learned""##,
           r##""60s 6144M declared""##,
           r##""4500s 5120M default""##,
           r##".some "declares 300 MiB but its runs need 564 MiB""##,
           r##".none"##,
           r##""checker b c d a""##,
           r##""110: b c e | 105: d f a""##,
           r##""90: b c | 60: d | 65: f e a""##,
           r##"6"##,
           r##".cons 0 (.cons 1 (.cons 2 (.cons 3 (.cons 3 (.cons 5 (.cons 7 (.cons 8 (.cons 9 .nil))))))))"##] },
    { name := "records (33e): log lines per status, the timings superset, the summary, the baseline from new and old lines", run := fun _ =>
        okLibs r##"import TestRun.Report
def r (st : Status) (detail : String) : Rec :=
  Rec.mk "library-3" (CaseInfo.lean "scry-taint" 4 "a \"quoted\" case" "scry-taint/a-quoted-case") 81204 st 2 412
    (Limits.mk 300000 1024 .learned) "cgroup" 3100 ["uses checker"] detail
#eval Rec.jsonl (r .pass "")
#eval Rec.line (r .pass "")
#eval Rec.line (r .fail "boom\nsecond line")
#eval Rec.line (r .skip "no toolchain")
#eval Rec.line (r .timeout "")
#eval Rec.line (r .oom "")
#eval Rec.line (r .flaky "")
#eval Rec.line (r .cached "")
#eval Tally.line (Tally.ofRecs [r .pass "", r .fail "", r .flaky "", r .skip "", r .timeout "", r .interrupted ""])
#eval TestRun.showMs 7
#eval TestRun.parseMs "81.2"
#eval TestRun.percentile 95 [40, 10, 30, 20]
#eval TestRun.percentile 50 [40, 10, 30, 20]
def lines : List String := [
  Rec.jsonl (r .pass ""),
  "{\"shard\": \"library-3\", \"group\": \"scry-taint\", \"index\": 4, \"case\": \"a \\\"quoted\\\" case\", \"seconds\": 79.5, \"ok\": true, \"notes\": []}",
  "{\"shard\": \"library-3\", \"group\": \"scry-taint\", \"index\": 5, \"case\": \"other\", \"seconds\": 12, \"ok\": false, \"notes\": []}",
  "not json"]
#eval String.intercalate " " (List.map (fun e => Json.render (Report.entryJson e)) (Report.learn (Report.samples lines)))
"##
          [r##""{\"shard\":\"library-3\",\"group\":\"scry-taint\",\"index\":4,\"case\":\"a \\\"quoted\\\" case\",\"id\":\"scry-taint/a-quoted-case\",\"seconds\":81.204,\"ok\":true,\"notes\":[\"uses checker\"],\"status\":\"pass\",\"attempt\":2,\"peak_mib\":412,\"limit\":{\"timeout\":300.000,\"mem_mib\":1024,\"source\":\"learned\"},\"enforce\":\"cgroup\",\"queued_s\":3.100}""##,
           r##""  ✓ a \"quoted\" case (81.204 s)""##,
           r##""  ✗ a \"quoted\" case (81.204 s)\n      boom\n      second line""##,
           r##""  ⊘ a \"quoted\" case (81.204 s)\n      skipped (no toolchain)""##,
           r##""  ✗ a \"quoted\" case (81.204 s)\n      timed out after 300.000 s (learned limit)""##,
           r##""  ✗ a \"quoted\" case (81.204 s)\n      over its memory budget (peak 412 MiB of 1024 MiB, learned)""##,
           r##""  ✓ a \"quoted\" case (81.204 s)\n      flaky: passed on attempt 2""##,
           r##""  ✓ a \"quoted\" case (cached)""##,
           r##""1 passed, 2 failed, 1 skipped, 1 flaky, 1 interrupted""##,
           r##""0.007""##,
           r##".some 81200"##,
           r##"40"##,
           r##"20"##,
           r##""{\"id\":\"scry-taint/a-quoted-case\",\"p95_s\":81.204,\"p95_peak_mib\":412,\"runs\":2}""##] },
    { name := "goldens (33f): header words and their errors, the first difference, verdicts, normalisation, --update", run := fun _ =>
        okLibs r##"import TestRun.Golden
def opt (o : Option Nat) : String := match o with
  | .some n => Nat.repr n
  | .none => "-"
def show (r : Except String Header) : String := match r with
  | .ok h => String.join [GKind.name h.kind, (match h.kind with
      | .skip w => String.join [" (", w, ")"]
      | _ => ""), " timeout=", opt h.timeoutS, " build=", opt h.buildTimeoutS, " mem=", opt h.memMib,
      " tags=", String.intercalate "," h.tags, " args=", String.intercalate " " h.args,
      match h.explicit with
      | .true => ""
      | .false => " (implicit)"]
  | .error e => String.join ["error: ", e]
#eval show (Golden.parseHeader "-- test: run timeout 900 mem 5G tags slow,hdl")
#eval show (Golden.parseHeader "-- test: check build-timeout 60 mem 512M")
#eval show (Golden.parseHeader "-- test: run args -n 3 --fast")
#eval show (Golden.parseHeader "-- test: skip needs  a flag")
#eval show (Golden.headerOf "import Foo\n#eval 1")
#eval show (Golden.parseHeader "-- test: run timeout 0")
#eval show (Golden.parseHeader "-- test: run timeout soon")
#eval show (Golden.parseHeader "-- test: run mem lots")
#eval show (Golden.parseHeader "-- test: run timeout")
#eval show (Golden.parseHeader "-- test: run colour red")
#eval show (Golden.parseHeader "-- test: bogus")
#eval Golden.firstDifference "a\nb" "a\nc"
#eval Golden.firstDifference "a" "a\nc"
#eval Golden.firstDifference "same" "same"
def v (x : Verdict) : String := match x with
  | .same => "same"
  | .missing m => String.join ["missing: ", m]
  | .differ m => String.join ["differ: ", m]
#eval v (Golden.compare (Header.plain .run .true) "t/a.expected" (.some "1\n2") "1\n2")
#eval v (Golden.compare (Header.plain .run .true) "t/a.expected" .none "1")
#eval v (Golden.compare (Header.plain .check .false) "t/a.expected" (.some "x") "y")
#eval Golden.normalize [("/home/u/pkg", "$PKG"), ("/nix/store/", "$STORE/")] "/home/u/pkg/a.wiz:1:1: error: /nix/store/abc-wiz"
#eval Golden.mayUpdate .true .false
#eval Golden.mayUpdate .false .false
#eval Golden.mayUpdate .true .true
#eval Golden.expectedPath "tests/rv/a.wiz"
"##
          [r##""run timeout=900 build=- mem=5120 tags=slow,hdl args=""##,
           r##""check timeout=- build=60 mem=512 tags= args=""##,
           r##""run timeout=- build=- mem=- tags= args=-n 3 --fast""##,
           r##""skip (needs  a flag) timeout=- build=- mem=- tags= args=""##,
           r##""check timeout=- build=- mem=- tags= args= (implicit)""##,
           r##""error: timeout must be positive""##,
           r##""error: timeout wants a number of seconds, not soon""##,
           r##""error: mem wants a size (512M, 5G), not lots""##,
           r##""error: option timeout wants a value""##,
           r##""error: unknown option colour (timeout SECS, build-timeout SECS, mem SIZE, tags A,B, args …)""##,
           r##""error: unknown test kind bogus (check, run, skip REASON; check and run may take options)""##,
           r##""line 2:\n      expected: b\n      actual:   c""##,
           r##""line 2:\n      expected: <end>\n      actual:   c""##,
           r##""(the same)""##,
           r##""same""##,
           r##""missing: no t/a.expected (write it with --update)""##,
           r##""differ: output differs from t/a.expected, line 1:\n      expected: x\n      actual:   y\n      (no `-- test:` line, so this was a `check` test: the expected output is the messages of checking the file; for what `main` prints, make `-- test: run` the first line)""##,
           r##""$PKG/a.wiz:1:1: error: $STORE/abc-wiz""##,
           r##".true"##,
           r##".false"##,
           r##".false"##,
           r##""tests/rv/a.expected""##] },
    { name := "scheduler (33d): memory packing on a virtual clock, a retried failure, a case bigger than the budget alone", run := fun _ =>
        okLibs r##"import TestRun.Sched
def cfg : Cfg := Cfg.mk "lib" 4 5000 1 "cgroup"
def mk (id : String) (mem tmo : Nat) (src : Source) : Case :=
  Case.mk (CaseInfo.lean "g" 0 id (String.join ["g/", id])) .lean (Limits.mk tmo mem src) 0 .nil
-- budget 1000 MiB, 3 jobs: b (500) waits for a (600); c and d pass it; c fails once and is retried.
def cs : List Case := [mk "a" 600 60000 .declared, mk "b" 500 60000 .declared, mk "c" 300 60000 .declared, mk "d" 100 60000 .declared]
def beh (slot a : Nat) : Nat × Res := match slot with
  | 0 => (5000, Res.of 0 500)
  | 1 => (3000, Res.of 0 400)
  | 2 => (2000, Res.of 1 200)
  | _ => (1000, Res.of 0 50)
def sim : S × List String := Sched.simulate cfg 1000 3 cs beh
#eval String.intercalate "\n" sim.2
#eval Sched.summary sim.1
#eval Sched.finished sim.1
-- a case bigger than the budget runs alone; nothing starts beside it
def big : List Case := [mk "huge" 4000 60000 .declared, mk "x" 100 60000 .declared]
#eval String.intercalate "\n" (Sched.simulate cfg 1000 3 big (fun s _ => (1000 * (s + 1), Res.of 0 10))).2
"##
          [r##""@0 run 0 #1 60.000s 600M\n@0 run 2 #1 60.000s 300M\n@0 run 3 #1 60.000s 100M\n@1000 print   ✓ d (1.000 s)\n@1000 record g/d pass #1\n@1000 res=900/1000 run=2\n@2000 print   ✗ c (2.000 s)\n      exit code 1\n      retrying (attempt 2)\n@2000 record g/c fail #1\n@2000 run 2 #2 60.000s 300M\n@2000 res=900/1000 run=2\n@4000 print   ✗ c (2.000 s)\n      exit code 1\n@4000 record g/c fail #2\n@4000 res=600/1000 run=1\n@5000 print   ✓ a (5.000 s)\n@5000 record g/a pass #1\n@5000 run 1 #1 60.000s 500M\n@5000 res=500/1000 run=1\n@8000 print   ✓ b (3.000 s)\n@8000 record g/b pass #1\n@8000 res=0/1000 run=0""##,
           r##""3 passed, 1 failed, 0 skipped""##,
           r##".true"##,
           r##""@0 run 0 #1 60.000s 4000M\n@1000 print   ✓ huge (1.000 s)\n@1000 record g/huge pass #1\n@1000 run 1 #1 60.000s 100M\n@1000 res=100/1000 run=1\n@3000 print   ✓ x (2.000 s)\n@3000 record g/x pass #1\n@3000 res=0/1000 run=0""##] },
    { name := "scheduler (33d): at most maxBypass cases pass the head, then it drains; the pressure gate", run := fun _ =>
        okLibs r##"import TestRun.Sched
def mk (id : String) (mem : Nat) : Case :=
  Case.mk (CaseInfo.lean "g" 0 id (String.join ["g/", id])) .lean (Limits.mk 60000 mem .declared) 0 .nil
-- head h (800) waits behind r (400): at most 2 small cases pass it, then the runner drains.
def cfg : Cfg := Cfg.mk "lib" 2 5000 0 "poll"
def cs : List Case := [mk "r" 400 , mk "h" 800, mk "s1" 100, mk "s2" 100, mk "s3" 100, mk "s4" 100]
def beh (slot a : Nat) : Nat × Res := match slot with
  | 0 => (10000, Res.of 0 300)
  | 1 => (1000, Res.of 0 700)
  | _ => (1000, Res.of 0 50)
#eval String.intercalate "\n" (Sched.simulate cfg 1000 4 cs beh).2
-- the pressure gate: while it is closed nothing starts, even with room
#eval String.intercalate "\n" (Sched.runScript cfg 1000 1 [mk "a" 100, mk "b" 100]
  [(10, Event.pressure .false), (20, Event.exited 0 (Res.of 0 10)), (30, Event.pressure .true),
   (40, Event.exited 1 (Res.of 0 10))]).2
"##
          [r##""@0 run 0 #1 60.000s 400M\n@0 run 2 #1 60.000s 100M\n@0 run 3 #1 60.000s 100M\n@1000 print   ✓ s1 (1.000 s)\n@1000 record g/s1 pass #1\n@1000 res=500/1000 run=2\n@1000 print   ✓ s2 (1.000 s)\n@1000 record g/s2 pass #1\n@1000 res=400/1000 run=1\n@10000 print   ✓ r (10.000 s)\n@10000 record g/r pass #1\n@10000 run 1 #1 60.000s 800M\n@10000 run 4 #1 60.000s 100M\n@10000 run 5 #1 60.000s 100M\n@10000 res=1000/1000 run=3\n@11000 print   ✓ h (1.000 s)\n@11000 record g/h pass #1\n@11000 res=200/1000 run=2\n@11000 print   ✓ s3 (1.000 s)\n@11000 record g/s3 pass #1\n@11000 res=100/1000 run=1\n@11000 print   ✓ s4 (1.000 s)\n@11000 record g/s4 pass #1\n@11000 res=0/1000 run=0""##,
           r##""@0 run 0 #1 60.000s 100M\n@20 print   ✓ a (0.020 s)\n@20 record g/a pass #1\n@30 run 1 #1 60.000s 100M\n@40 print   ✓ b (0.010 s)\n@40 record g/b pass #1""##] },
    { name := "scheduler (33d): timeout (kill 15, then 9), a learned OOM retried alone (drift), a declared one not; skip and failure", run := fun _ =>
        okLibs r##"import TestRun.Sched
def mk (id : String) (mem tmo : Nat) (src : Source) : Case :=
  Case.mk (CaseInfo.lean "g" 0 id (String.join ["g/", id])) .lean (Limits.mk tmo mem src) 0 .nil
def cfg : Cfg := Cfg.mk "lib" 4 5000 0 "cgroup"
-- a timeout: kill 15 at the deadline, kill 9 after the grace, then the exit is a timeout
def t1 : S × List String := Sched.runScript cfg 1000 2 [mk "slow" 100 30000 .declared]
  [(1000, Event.started 0), (31000, Event.tick), (36000, Event.tick), (36500, Event.exited 0 (Res.of 137 80))]
#eval String.intercalate "\n" t1.2
#eval Sched.wake (Sched.runScript cfg 1000 2 [mk "slow" 100 30000 .declared] [(1000, Event.started 0)]).1
-- a learned budget that is too small: retried alone with the whole budget, noted as drift
def oomRes : Res := Res.mk 137 .true 700 .none .nil ""
def t2 : S × List String := Sched.runScript cfg 1000 2 [mk "golem" 300 60000 .learned, mk "other" 300 60000 .declared]
  [(4000, Event.exited 0 oomRes), (5000, Event.exited 1 (Res.of 0 10)), (9000, Event.exited 0 (Res.of 0 900))]
#eval String.intercalate "\n" t2.2
#eval String.intercalate "\n" (List.map Rec.jsonl (Sched.results t2.1))
-- a declared budget that is too small is not retried
#eval String.intercalate "\n" (Sched.runScript cfg 1000 2 [mk "decl" 300 60000 .declared] [(4000, Event.exited 0 oomRes)]).2
-- a skip and a failure with output
def skipRes : Res := Res.mk 0 .false 5 (.some "no toolchain") .nil ""
#eval String.intercalate "\n" (Sched.runScript cfg 1000 2 [mk "s" 100 60000 .declared, mk "f" 100 60000 .declared]
  [(10, Event.exited 0 skipRes), (20, Event.exited 1 (Res.mk 1 .false 5 .none ["uses checker"] "expected 3\ngot 4"))]).2
"##
          [r##""@0 run 0 #1 30.000s 100M\n@31000 kill 0 15\n@36000 kill 0 9\n@36500 print   ✗ slow (35.500 s)\n      timed out after 30.000 s (declared limit)\n@36500 record g/slow timeout #1""##,
           r##".some 31000"##,
           r##""@0 run 0 #1 60.000s 300M\n@0 run 1 #1 60.000s 300M\n@4000 print   ✗ golem (4.000 s)\n      over its memory budget (peak 700 MiB of 300 MiB, learned)\n      retrying (attempt 2)\n@4000 record g/golem oom #1\n@5000 print   ✓ other (5.000 s)\n@5000 record g/other pass #1\n@5000 run 0 #2 60.000s 1000M\n@9000 print   ✓ golem (4.000 s)\n@9000 record g/golem pass #2""##,
           r##""{\"shard\":\"lib\",\"group\":\"g\",\"index\":0,\"case\":\"other\",\"id\":\"g/other\",\"seconds\":5.000,\"ok\":true,\"notes\":[],\"status\":\"pass\",\"attempt\":1,\"peak_mib\":10,\"limit\":{\"timeout\":60.000,\"mem_mib\":300,\"source\":\"declared\"},\"enforce\":\"cgroup\",\"queued_s\":0.000}\n{\"shard\":\"lib\",\"group\":\"g\",\"index\":0,\"case\":\"golem\",\"id\":\"g/golem\",\"seconds\":4.000,\"ok\":true,\"notes\":[\"drift: passed alone after its learned budget ran out\"],\"status\":\"pass\",\"attempt\":2,\"peak_mib\":900,\"limit\":{\"timeout\":60.000,\"mem_mib\":1000,\"source\":\"learned\"},\"enforce\":\"cgroup\",\"queued_s\":1.000}""##,
           r##""@0 run 0 #1 60.000s 300M\n@4000 print   ✗ decl (4.000 s)\n      over its memory budget (peak 700 MiB of 300 MiB, declared)\n@4000 record g/decl oom #1""##,
           r##""@0 run 0 #1 60.000s 100M\n@0 run 1 #1 60.000s 100M\n@10 print   ⊘ s (0.010 s)\n      skipped (no toolchain)\n@10 record g/s skip #1\n@20 print   ✗ f (0.020 s)\n      expected 3\n      got 4\n@20 record g/f fail #1""##] },
    { name := "scheduler (33d): a pass on a retry is flaky; an interrupt kills the running cases and starts nothing; reserved_le", run := fun _ =>
        okLibs r##"import TestRun.Sched
def mk (id : String) : Case :=
  Case.mk (CaseInfo.lean "g" 0 id (String.join ["g/", id])) .lean (Limits.mk 60000 100 .declared) 0 .nil
-- one retry: a failure that passes the second time is flaky, never pass
def cfg : Cfg := Cfg.mk "lib" 4 5000 1 "none"
def t : S × List String := Sched.runScript cfg 1000 1 [mk "wobbly", mk "steady"]
  [(100, Event.exited 0 (Res.of 1 10)), (200, Event.exited 1 (Res.of 0 10)), (300, Event.exited 0 (Res.of 0 10))]
#eval String.intercalate "\n" t.2
#eval Sched.summary t.1
-- an interrupt: the running cases are killed (15, then 9 after the grace), nothing more starts
def u : S × List String := Sched.runScript cfg 1000 2 [mk "a", mk "b", mk "c"]
  [(100, Event.interrupt), (5100, Event.tick), (5200, Event.exited 0 (Res.of 137 10)), (5300, Event.exited 1 (Res.of 143 10))]
#eval String.intercalate "\n" u.2
#eval Sched.summary u.1
#eval Sched.finished u.1
#print axioms Sched.reserved_le
"##
          [r##""@0 run 0 #1 60.000s 100M\n@100 print   ✗ wobbly (0.100 s)\n      exit code 1\n      retrying (attempt 2)\n@100 record g/wobbly fail #1\n@100 run 1 #1 60.000s 100M\n@200 print   ✓ steady (0.100 s)\n@200 record g/steady pass #1\n@200 run 0 #2 60.000s 100M\n@300 print   ✓ wobbly (0.100 s)\n      flaky: passed on attempt 2\n@300 record g/wobbly flaky #2""##,
           r##""1 passed, 0 failed, 0 skipped, 1 flaky""##,
           r##""@0 run 0 #1 60.000s 100M\n@0 run 1 #1 60.000s 100M\n@100 print interrupted: stopping\n@100 kill 0 15\n@100 kill 1 15\n@5100 kill 0 9\n@5100 kill 1 9\n@5200 print   ⊘ a (5.200 s)\n      interrupted\n@5200 record g/a interrupted #1\n@5300 print   ⊘ b (5.300 s)\n      interrupted\n@5300 record g/b interrupted #1""##,
           r##""0 passed, 0 failed, 0 skipped, 2 interrupted, 1 not started""##,
           r##".true"##,
           r##"'Sched.reserved_le' does not depend on any axioms"##] },
    { name := "an OkPool over its budget does not check: the invariant is in the type", run := fun _ =>
        failsLibs r##"import TestRun.Budget
def bad : OkPool := OkPool.mk (Pool.mk 10 20 0 1) rfl
"## "not definitionally equal" }
  ]

builtin_initialize registerGroup testRunGroup

end Tests.Elab
