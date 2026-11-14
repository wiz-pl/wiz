# Stage 15: performance for self-hosting

## 15a: lazy unfolding

`memo : (Unit → A) → Unit → A` (Prelude, `builtin memo`) is a memoised suspension. To
the kernel and the interpreters it is the identity; compiled code makes it a thunk
object (`WIZ_TAG_THUNK`) that `wiz_apply` runs at most once, keeping the result. The
Wiz kernel's glued values now hold their unfolding as `Unit → Val` built with `memo`, as
the Lean kernel's `Val.unfold` holds a `Thunk`: a global is unfolded only when `whnf`
looks through it, and once. Checking a term that mentions a large global 300 times
(without needing its value) went from 206 s to 1 s.

(`whnf` recurses into the forced unfolding: structural recursion through a function
field. For a mutual family, that field's induction hypothesis wants the index equation
after the field's argument; the recursive call now supplies it, as `fun h => ih h
proof`.)

## 15b: the self-hosted pipeline, measured

A benchmark checks a file of 300 definitions (and one of 3000) with the self-hosted
pipeline compiled to C, against the Lean-hosted `wiz check`. At first the self-hosted
one took 1.5 s (and 32 s, so quadratic) against 0.08 s (0.68 s). Profiling the compiled
program with `gprof` (`WIZ_CFLAGS=-pg`):

* the parser spent nearly all its time reading tokens, each read trying every token of
  the table: the context now keeps the table by first character (`tokenBuckets`), and
  a candidate no longer shares the memo table with the live state;
* globals were variables of the typing context, so every command rebuilt it, and every
  usage vector and name lookup grew with the number of globals: they are now the
  kernel's constants (checked in the empty context, unfolded lazily since 15a), found
  by name in a `StrMap` (`Scope`), and kept in an `Array`.

Now 0.25 s (2.4 s): linear, within 3–4× of the Lean-hosted checker. The profile is flat;
the largest share left is reference counting (about 1.4 billion `inc`/`dec` for the
3000 definitions). Two things tried and left out:

* *borrow inference* as a pass around `insertRC` (parameters never consumed are
  borrowed; calls and boxed wrappers fixed up afterwards) removed only 4% of the
  `inc`s, and cost 12% more allocations, since a borrowed cell can't be reused. The
  gain needs borrowed *projections* and reuse-aware inference inside `insertRC`
  itself;
* `ap` of a known partial application: closures are applied only about a million
  times here.

Next: fewer index equations for mutual families (elaboration time and code size).

### 15c: known constructors and constant folding

`Wiz/Compiler/Simp.lean` simplifies every function of the IR right after lowering
(before constants are hoisted and before reference counting). A native operation on
numbers whose arguments are literals is computed at compile time, with the kernel's own
semantics (`natNative?`: `3 - 5 = 0`, `n / 0 = 0`, `n % 0 = n`); `nat.beq`/`nat.blt` of
literals, or of a variable with itself, are the `Bool` tags. A `case` on a variable known
to be a constructor (built in the same function), a literal, or already tested by an
enclosing `case` is replaced by the branch, and a projection of a known constructor is
its field. A branch also learns from its test: in the `true` branch of
`case (nat.beq n 10)`, `n` is `10`. What becomes unused is removed by `elimDead`, which
now counts operations on numbers, tests and tags as pure. `#ir` shows the folded form;
`#run`, C and LLVM agree (group `c`/`llvm`: "constant folding and known constructors").

### 15d: the self-hosted C at `-O2`

Stage 2 of the bootstrap (`scripts/fixpoint.sh`, grail's `stage2` target) and the
self-hosted compile-and-run tests compile the self-hosted backend's C with `-O2`
instead of `-O1`, like `wiz build`.

### 15e: dead code in the self-hosted backend

The reference counting mode compiles a `let`'s body first, so it knows whether the
variable is live: a dead `let` whose value has no effects (variables, globals, numbers,
objects and projections of such, closures, suspensions; no applications) is not
compiled at all. Before, it was computed and released at once.

### 15f: self tail calls are loops

A function that calls itself in tail position runs in constant stack, whatever the C
compiler does (tested at `-O0` on a 1 MB stack, 10 million iterations). In the Lean
compiler (`Decl.loopify`), `f ps` whose body has `let r := f as; ret r` (in a branch, a
join point's body, …) becomes `join J(ps') := body[ps ↦ ps', f as ↦ jmp J as]; jmp J ps`; join
points are labels and `goto`s in C and branches in LLVM, and borrow inference (8e)
treats the join point's parameters like the function's. In the self-hosted backend (`markSelf`),
such a call becomes `wiz.self`: the arguments are computed, the parameters reassigned
and control goes back to the label `top_` at the function's start (in the garbage
collected mode, out of the statement expressions; that mode now pushes applications
into `case`s too, as reference counting did, so a match builds no closure and the calls
in its branches are in tail position). Under reference counting a borrowed
parameter must be passed a borrowed parameter (else the argument would be released
after the call): otherwise the call stays a call. In the garbage collected mode a call
under a match on a computed value (`match Nat.beq … with`) is not yet in tail position:
the match's payload is a suspended `let`, and its branches are closures (under reference
counting lets are strict, and it is a loop).

### 15g: big numerals

A numeral like `1000000000` in a file compiled by the self-hosted compiler crashed the
compiler (a stack overflow), when that compiler was the one built by the Lean
`wiz build`. The self-hosted kernel has no number literals: its frontend elaborates a
numeral to a binary term, `2 * (n / 2)` plus one if `n` is odd (`binNat`), and it
halved `n` with `halfNat`, a recursion on `succ (succ j)`: `n / 2` frames deep. It now
uses `Nat.div`, a native operation in both compilers; the term was always logarithmic.

What each compiler does with a numeral:

* **The Lean compiler** keeps it as a literal from the elaborator to the IR
  (`Term.natLit`, `ETerm.natLit`, `Expr.lit`), and the backends emit a constant: below
  `2^62` an immediate, from `2^62` a GMP number built once from its digits
  (`wiz_nat_lit`). Nothing recurses on the value. One bug on the way: the LLVM backend
  named the global holding the digits with a counter per function, so a module with
  two such literals in two functions defined `@lit.1.str` twice and `llc` rejected it;
  the global is now named after the number.
* **The self-hosted compiler.** Its numbers are 63-bit words whose arithmetic wraps
  (a limit of that runtime, not changed here), so a numeral from `2^63` could only be
  its value modulo `2^63` (`2^64 + 1` would be `1`). It is now an error in the frontend
  ("the numeral does not fit in 63 bits"), decided on the digits: when the compiler
  runs on words itself, the value has wrapped before anyone can look at it.
* **The self-hosted compiler stops at a frontend error.** Its driver
  (`Selfhost.compilerSource`) printed the frontend's messages as comments at the top
  of the C and went on: a definition with an error was just missing, and the program
  compiled anyway if nothing used it. Now, if any line of the frontend's output starts
  with `error`, the errors go to standard error, no C is printed, and the exit code is
  1. For this the self-hosted prelude and `selfhost/rt.c` have two more natives, with
  the names and types of `lib/Sys.wiz`: `IO.ePrintln : String → IO Unit` and
  `Process.exit : Nat → IO Unit`.
* **Folded constants.** The backend recognises the binary term and emits `BOX(n)` (`natConst`, which also
  folds `+` and `*` of constants): it now wraps like the runtime does. Built by the Lean
  compiler its own numbers are unbounded, and a folded product could print a constant
  like `BOX(18446744073709551616UL)`, which gcc truncates with a warning and other C
  compilers reject (and stage 1 and stage 2 would print different C).

Tests: numerals at `2^31`, `2^32`, `2^62 - 1`, `2^62`, `2^63`, `2^64`, `2^64 + 1` and
`10^30` with `#eval`, `#run`, C and LLVM (groups `backend`, `c`, `llvm`); with the
self-hosted compiler (group `selfhost`), numerals up to `2^63 - 1` compiled and run
with both collectors, the error from `2^63`, and the compiler's exit code and
standard error for a program with errors.

### 15h: case-shaped calls (`Bool.and` and `Bool.or` short-circuit)

Application is call by value in compiled code: `Bool.and a b` computed `b` before
looking at `a`. So `p x && all p xs` (written with `Bool.and`) walked the whole list
after the answer was known, and the recursive call was not a tail call. The kernel's
evaluator never did that (it is lazy).

A definition is **case-shaped** when its erased code is `λ x₁ … xₙ. case s [b₀, …]`
with a scrutinee and branches built only from the parameters, constants, objects,
projections and tags (no application, no binder; at most 16 nodes), after substituting
the `let`s a compiled `match` makes for fields. `Bool.and`, `Bool.or`, `Bool.not`, a
`getD` or `orElse` on `Option` are. A call with all `n` arguments is compiled as the
`case` itself (`ETerm.caseInline` in `Wiz/Compiler/Inline.lean`, run on every reachable
definition by `compileReachableE`, before lowering):

* an argument whose parameter the scrutinee uses, or that more than one branch uses, is
  computed first, as before;
* an argument whose parameter one branch uses is computed in that branch;
* an argument whose parameter no branch uses is not computed.

A partial application (`foldB Bool.and`, a fold given the function) still calls the definition.

Why this is sound: the language is pure, so when an argument is evaluated cannot be
observed, only whether the program returns. The result is the same whenever the
call-by-value program returned. A program that did not return because of such an
argument (a `partial` definition that loops, an absurd case) now returns when the
branch taken doesn't use it, which is what the kernel's evaluator does with the same
term. An argument of type `IO A` is a value (a function of the world): not building it
performs nothing, and performing it was never part of evaluating the call.

The passes after it see ordinary `case`s: constant folding (15c) removes the `case`
when the test is known, the recursive call in a branch is a tail call and becomes a
loop (15f), and borrow inference and reuse (8e, 8f) run on the result.

    def mem (n : Nat) : List Nat → Bool
      | .nil => .false
      | .cons x xs => Bool.or (Nat.beq x n) (mem n xs)

    def mem @&x0 @&x1 :=
      join j1(x13 x14) :=
          case x14 of
          | 0 => let x6 := Bool.false; ret x6
          | 1 =>
              let x8 := proj 0 x14
              let x9 := proj 1 x14
              let x10 := prim nat.beq x8 x13
              case x10 of
              | 0 => jmp j1 x13 x9
              | 1 => let x12 := Bool.true; ret x12
      jmp j1 x0 x1

Allocations in the checked-heap interpreter, without and with the pass
(`compileReachable … (caseShapes := false)` turns it off; the programs are
`caseShapeSrc` in `Tests/Elab.lean`):

| program | before | after |
|---|---|---|
| `mem 3 (range 1000)`: a search in a list that exists | 1000 | 1000 (the same cells; a loop that stops at the fourth) |
| `reach 8 100 [1]`: each level `Bool.or (mem n xs) (reach … (double xs))` | 101 | 4 |
| `Bool.and (mem 2000 (range 1000)) (mem 5 (range 1000))` | 2000 | 1000 |
| `orElse (.some 4) (List.length (range 50 xs))`, `xs` of 100 elements | 151 | 101 |

Tests: group `backend` (the IR of `mem`, `allLt` and a user function; the counts
above), groups `c` and `llvm` (a second argument that never returns; ten million steps
of `Bool.or (Nat.beq i n) (upFrom n (i + 1))` on a 1 MB stack at `-O0`).

The self-hosted backend does the same for its own input (small case-shaped functions
inlined with lazy arguments); `&&` and `||` as macros
that expand to matches need neither.


### 15i: closed definitions are computed once (CAFs)

A top-level definition without parameters after erasure, such as a table
`def Fx.fontT : RomT := RomT.build 7 Fx.font`, compiled to a function that computed its
body again at every use: in the value simulation of the OLED demo that rebuilt the font
and program ROMs every simulated cycle. Now, as for GHC's and Lean's *constant applicative
forms*, both native backends (C and LLVM) compute such a value **on its first use** and
keep it for the rest of the run:

* `IR.cafs` (`Wiz/Compiler/IR.lean`) picks the definitions without parameters whose body
  does work (allocates or calls a function with parameters). Not cached: `wiz.entry`, the
  closures of exported functions, the wrappers of foreign functions, and bodies that only
  return a scalar or another constant (`def tab := table`). The hoisted literal constants
  of 20f (`wiz.const.k`) are now just CAFs, cached by LLVM too.
* The function reads a slot (one atomic load) and returns the value; while the slot is
  empty it calls `wiz_caf_init` (`runtime/`), which runs the body, makes the result
  **immortal** (rc 0: never counted, never freed, not a leak) and publishes it with a
  compare-and-swap. Threads may race to build it: the first wins, a loser's copy stays
  immortal and unused.
* Lazily, never at startup: a definition used only in a branch that is never taken is
  never computed, even one that diverges or fails (an axiom). A definition that uses itself
  while it is being built builds itself again, as before: it loops exactly when it looped
  before.
* An `IO A` is a function of the world: its value is a closure (or the definition has the
  world as a parameter), so caching it doesn't run it; it runs at each use. Erased
  definitions (proofs, types) are not compiled at all, and function values (a partial
  application) are cached as closures.
* `wiz_immortal` now walks every kind of object (closures, suspensions, arrays, maps,
  numbers …), with an explicit stack (a constant may be a long list), instead of only
  constructors. An immortal memoised suspension (inside a constant, so visible to every
  thread) is forced under the suspension lock, like one shared between threads, and its
  value made immortal.

The cost is the GHC one: a constant that is large and used once stays in memory until the
program ends, and an immortal value is never unique, so it is copied, not updated in place.

Benchmark: `examples/closed-table-bench.wiz` (a 256-entry table and a ROM tree built from
it, read in a loop; `wiz-tools/bench/closed-table`). Informal, 100000 lookups:
8.1 s with the table rebuilt at each use, 0.08 s cached.

Tests: groups `backend` (which definitions are cached), `c` and `llvm` (a table in a
loop, a diverging and a failing constant in an untaken branch, a memoised suspension, a
big number, erased definitions, self-referential codata, no leaks; an `IO` constant run
four times), `conc` (eight threads first using a table and a suspension in it at once).

### 15j: shared projection prefixes

A structure (and a Σ) nests to the right, `(f₀, (f₁, (f₂, …)))`, so field `k` is `k`
projections `.2` and a `.1`, whether it is written `s.f` or bound by a `match`. A
function that reads every field of a wide structure did n²/2 projections: a bundle's
`pack`, a step function over a wide state (wiz-rv's 20-field core state, the iCEstick IR
blaster's 19 fields).

* **Lean compiler.** The IR simplifier (`Simp.lean`, right after lowering) remembers
  the projections bound on the path from the function's start, `(field, object) ↦
  variable`, and renames a projection computed again to the first one. Each step of a
  chain is its own binding, so `x.2.2.2.1` and `x.2.2.2.2.1` share `x.2`, `x.2.2` and
  `x.2.2.2`, and reading every field is linear. Only what dominates is shared: a `case`
  branch sees what was bound before the `case`, not what a sibling branch bound; a join
  point's body starts afresh; a `lazySet` (an observed lazy cell is overwritten) forgets
  everything. A projection still borrows from its object, so reference counting is
  unchanged in kind: the field of an owned object is `dup`ed once instead of once per
  read. No representation changes.
* **Self-hosted backend.** It compiles terms, not ANF, so the prefixes are planned per
  region (`csePlan`): at a function's body, a `case` branch and a `λ`'s body, each prefix
  `x.2…` of a variable bound outside used twice, once on the region's straight-line path
  (so it is evaluated there anyway), becomes a C local, `qx_1 = fld(x, 1)`, `qx_2 =
  fld(qx_1, 1)`, … (a `let` does the same for its own variable), and every path from `x`
  reads from the longest local. Only `.2`s are shared: `fld(·, 1)` is total and never
  forces a hypothesis. Under reference counting the locals are borrowed from `x` (no
  `inc`): every use of one is still a use of `x`, which therefore lives as long, and the
  locals are declared only when `x` is still alive (used in the region, or borrowed).

Tests: `scaling` (reading every field of 32- and 64-field structures takes one projection
per field and per tail), `c` and `llvm` (a root consumed before the last read through its
prefix, an in-place update of the root's cell while fields read through the prefix are
live, a join point, codata between observations; the IR interpreter checks every
reference), `selfhost` (the same in both modes; the C of a wide read has its locals).

### 15k: parallelism in the build pipeline

Where the time goes in `wiz build FILE -o OUT` (one compilation unit, all of it
single-threaded) and in `grail build` (a graph of jobs, `-j N` processes at a time):

| stage | threads | note |
|---|---|---|
| module closure read, `cc -E` per `import_c` header, elaboration through the per-command cache | 1 | command order *is* the cache key chain; module keys depend only on text |
| erasure (`Erase.compileReachable`) | 1 | reachability worklist |
| lowering, simplification, constant hoisting | 1 | per declaration, one pass, output sorted |
| borrow inference | 1 | whole-program greatest fixed point |
| dead code, RC, reuse, drop specialisation per declaration | 1 | independent once borrows are known |
| C emission | 1 | one string, declaration order |
| `cc -O2` (compiles `link_c` sources too) | 1 process | LLVM: `cc`, `llc`, `cc` in sequence |
| grail jobs: `check F`, `build F`, `ir F`, `obj`, `link`, `test`, selfhost steps | up to `-j N` | each a supervised process; default `min(cores, 4)`; selfhost is a serial chain |

Lake builds independent Lean modules in parallel (its own job pool, shared artifact
cache) but never parallelises inside a module, so the frontend and backend passes
above are serial in `wiz`/`grail` themselves.

Probes (heavy, shared machine; approximate), `grail build std` (59 checks; cold
unless said):

| jobs | cold | warm cache | up to date |
|---|---|---|---|
| `-j1` | 174.1 s | | |
| `-j4` | 55.7 s | 22.6 s | 1.27 s |
| `-j8` | 44.0 s | | |

So the existing job graph scales 3.1× at `-j4` and 4.0× at `-j8`: the checks form a
depth-limited import DAG, and the marginal gain of 8 over 4 is small. Graph
construction and per-node key computation for 59 nodes cost 1.3 s, so the serial
scheduler is not a bottleneck. The warm-cache build spends 22.6 s replaying the
modules' commands from their per-command cache files (one `.wizc` per command) in 59
separate processes: each job re-reads the closure and re-preprocesses headers.

The old `grail build` graph had `check F -> ir F -> c F` for an executable, three
jobs and three processes. `ir` and `c` each re-ran the whole IR pipeline, not just
elaboration. 23g now runs one `build F` job that checks F and writes its IR, C and
link text (`ir F` remains for a file that is already checked as a module). Measured
on the self-hosted compiler (`grail build selfhost-compiler -j4`, 641 KB generated
source): **262.3 s -> 160.7 s (1.63×)**; six small examples at `-j1`: 19.8 -> 14.9 s.
For the same source, `wiz check` is 34.1 s and `wiz build --cc true` (elaboration +
IR + C, no C compiler) is 70.4 s, so the IR pipeline is ~36 s that the old graph ran
once per `ir`/`c` job. The full `wiz build` of that file is 157.3 s: elaboration
34 s, IR+C 36 s, and **one `cc -O2` process 87 s** (one core, one translation unit).

**Splitting the C** (`wiz build --split N`, implemented) compiles a support unit (the
runtime with `-DWIZ_API=`, the foreign glue, the exports and `main`) plus `N` units of
generated declarations, each a `cc -c -O2` task, then links. On the same 18.8 MB
program (12934 declarations, cold cache): single **146.9 s**, `--split 2` 103.5 s,
`--split 4` 91.6 s, `--split 8` **85.8 s** (1.71×; its `cc` stage 16.2 s against 87 s
for one unit); warm cache 144.0 -> 81.1 s. The generated C each build prints is
identical. The cost is that `cc` cannot inline across unit boundaries: the program
built with `--split 8` runs 50.5 s against 38.0 s (1.33× slower). A one-unit program
against the split runtime runs 42.3 s, so ~11% is runtime calls and ~16% generated
cross-unit calls. `-fvisibility=hidden` does not help; `-flto` recovers the run time
(40.5 s) but its link costs 84.2 s, so the build is no faster than single
(`-flto=8`: 88.1 s / 43.2 s). The split is therefore **opt-in** (`--split N`,
default 1), for fast iteration rather than release builds. The partition is
deterministic (declaration order, balanced by C text), and each part keeps its object
in `<out>.split/` with a stamp of its text and flags, so a rebuild to the same output
compiles only the parts that changed (an example: 3.3 s -> 0.5 s on a second build).

What is left:

1. **Recover cross-unit inlining**: inline the hot runtime fast paths (`wiz_inc`,
   `wiz_tag`, `wiz_proj`, small-number `nat.beq`/`blt`) in `wiz_split.h`, and cut by
   module/call graph instead of text size; clang's ThinLTO (`-flto=thin`, `lld`)
   is the likely way to keep both the build and the run time.
2. **Module-effect bundles.** Have the check/build job write its modules' effects to
   one bundle per module key (derived from, and compatible with, the per-command
   cache), so a warm build or a `grail test` process replays one file per module
   instead of one per command. Targets the measured 22.6 s warm build; no key
   changes if the bundle is derived and validated by `binaryId`/module key.
3. **Batch the check-only tests of a `grail test` run** into a few worker jobs: the
   frontend already keeps isolated module states per process (`Frontend.isoKey`), so
   one process checking several test files replays the common imports once. This is
   orthogonal to the `--jobs` work in the Lean test driver.

Parallelising the 36 s IR+C stage per declaration (after the serial borrow fixpoint)
is the fallback if cross-unit inlining cannot be recovered: byte-identical output,
~16% end to end.

Raising grail's `-j` default is not one of them: the 4 -> 8 gain is 1.27×, and
memory per check job is the limit of the shared heavy slot.
### 15l: the performance dashboard

`scripts/perf-dashboard.py` turns the measurement log into one self-contained HTML page
(inline CSS, JS and SVG; it loads nothing from the network, and writes the file through a
temporary name and a rename, so it is safe to re-run):

```sh
python3 scripts/perf-dashboard.py                       # wiz-tools/perf-history.tsv
python3 scripts/perf-dashboard.py --timings RUNS --html out.html
```

`--history TSV` is the measurement log (a row per run: date, commit, label, seconds, max
RSS, exit code), `--repo DIR` the checkout whose `git log` orders commits and names them
from their merge commits, `--gap MIN` the pause between measurements that starts a new
window, and `--out`/`--html` the page to write. Labels lose their `@worktree` suffix;
failed runs are counted but leave out the medians, and A/B pairs compare each measured
commit with its nearest measured ancestor inside a window's interleaved rounds.

**CI test timings.** `--timings FILE_OR_DIR` (repeatable) ingests `test-timings.jsonl`
artifacts — the records `lake test --timings` writes and `scripts/ci.py summary` reads,
one per case (`shard`, `group`, `index`, `case`, `seconds`, `ok`, `notes`) — beside the
measurement log. A directory (a `gh run download -n test-timings` tree) is searched for
`*.jsonl`, one file is one run. A run's date and commit are not in the artifact: they
come from a `<name>.meta.json` sidecar, the records' optional `date`/`commit` fields, a
7–40 digit hex commit in the file name or a parent directory's name, else `--commit` and
`--at`. The page then has a *CI test timings* section: a table of runs, each group's
case count, total (the sum of its passed cases) with its median across runs, the change
from the previous run and a sparkline, and the slowest cases with their medians and
maximums. Since CI runs cases with `--jobs`, a group's total is test time, not wall
time; compare groups over runs, not runs on different runners.

`scripts/test-perf-dashboard.sh` checks the two input formats and the self-contained
output against the small fixtures in `scripts/fixtures/perf/` (under a second, no
toolchain). The page is published from the notes directory (`wiz-notes/`).
