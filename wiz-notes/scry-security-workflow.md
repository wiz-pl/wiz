# Scry security workflow: scan → refine → verify → PoC

Status: branch `security-workflow`, 2026-11-19. The **"before" loop** was run on a
checked-in fixture with the existing binary, and the new candidate/rank/plan logic was
validated with `#eval` in the interpreter and with the plan fed by hand to the old
reproducer. The **full post-change loop is blocked on a Slurm build slot**: the scry
package needs `grail build scry`, the batch queue is saturated by other agents' 4-hour
jobs, and the deck build is too slow (one module every ~4 minutes). The table below
labels each cell: **measured**, **eval**, **emulated**, or **not run**. A cell that was
not run is not a pass.

This note answers four questions:

1. what the loop is and what each stage produced on a real target;
2. which link was weakest, with the evidence;
3. what a candidate carries from one stage to the next, as a value in the store/report;
4. what changed, and the test that runs the loop and asserts every artifact.

## 0. What existed (verified, not assumed)

| claim in the brief | what is actually there |
|---|---|
| a findings DB with states and an authority field | `Scry.Workflow` has the checked state machine (`new → triaged → confirmed → fixed`, `false-positive`, reopen) and `Scry.WfAuthority` (L0–L5). Authority is per **evidence item** (`wfEvidenceJson`), not a record-level column. The record has `id/key/lineHash/state/history/finding/artifacts/static/dynamic/verify/firstSeen/lastSeen`. |
| `findings repro` with `--sanitize/--harness/--input` and a data-contract witness | yes: `Repro.wiz` and `WorkflowCmd.reproCmd`; `Dynamic.wiz:35-39` states the witness contract ("recorded, never applied"). The witness is a future S6a artifact; **nothing produces it today**, and when accepted it only supplies an input file and env. |
| taint rules and a findings report (SARIF/JSON) | yes: `lib/Scry/rules/default.scry`, `lib/Scry/Report.wiz` (HTML), `Scry.Sarif`, `Scry.findingJson`. |
| corpus fixtures with known-true findings (CWE-78/22/476 cases) | **partly false**: `scry/corpus/csharp/taint/` has four fixtures, all CWE-78 (`process`, `process-safe`, `startinfo`, `helper`). There are no CWE-22 or CWE-476 C# fixtures on this base. |
| a real C# solution if the project loader has landed | **not landed for C#**: `Scry.Project` reads `compile_commands.json` and runs `cc -E`; there is no `.sln`/`.csproj` loader. `scry taint FILE.cs` was hardcoded to `Scry.Native.parse "c"`, so the CLI could not analyse the C# corpus at all (the snapshot binary on the C# fixture reports 3 parse-error nodes, 0 findings). The workflow therefore uses the C# corpus, and this note includes the small change that makes the CLI reach it. |

The C# frontend itself (`Scry.CsLower`, tree-sitter-c-sharp) was already there and is
exercised by the Lean group `scry-csharp`; the gap was the **path from the CLI and the
workflow** to it.

## 1. The loop, and the stage outputs

```
scan FILE...  ──► static.json        finding + path + certificate + evidence limits
                   candidate.json    stage=scan, rank=0, verdict=unranked
      │
      ├─ refine ──► candidate.json   stage=refined, rank, verdict, reasons,
      │                             source (from the path), plan (PoC input/harness)
      │              store state: new → triaged for "pursue"
      │
      ├─ repro ───► repro.json       the plan (channel/env/input/marker/sink)
      │              dynamic.json    concrete run, derivedFrom=candidate.json,
      │                             run.markerObserved
      │
      └─ verify ──► verify/verify.json
                     static: still reported / not reported by this run
                     dynamic: the stored plan re-run
                     verdict + poc.markerObserved
```

`refine` is the semi-automated triage step. It deliberately **re-runs no analysis**: it
reads the static evidence `scan` wrote (derivation status, parse/boundary counts, the
path), reads the source line the path's first `source` step points at, and derives

* a channel (`stdin`, `env`, `argv`, `http`, `unknown`),
* the source callee as written (`getenv`, `System.Console.ReadLine`, `read`, …),
* the control's name when the line has a string literal (`getenv("SCRY_CMD")` → `SCRY_CMD`),
* a rank and the reasons for it,
* and a PoC plan (channel, env name, input text, a per-finding marker, the sink).

Only `pursue` candidates are promoted `new → triaged`; the rest keep their rank and
reasons and wait for a human. That is the difference between "listing" and triage.

### The run

Targets: `scry/corpus/csharp/taint/cwe78-process-unsafe.cs` (the C# corpus's direct
CWE-78 case) and `scry/corpus/workflow/cwe78-getenv.c` (a C fixture whose source names
its environment variable, so the derived PoC can actually reproduce it).

| stage | artifact | C: `cwe78-getenv.c` | C#: `cwe78-process-unsafe.cs` |
|---|---|---|---|
| scan | `static.json`, `candidate.json` | **measured** (old binary): 1 finding `f_edbaeb86bcfed108`, `checked`, path `source>flow>sink`, 1 boundary warning; state `new` | **measured** (old binary): 3 parse-error nodes, **0 findings** — the CLI parsed `.cs` as C. The new `analyzeCsFile` path is **not run** (blocked). |
| refine | `candidate.json` | **eval**: rank **88** (`pursue`), channel `env`, name `SCRY_CMD`, marker `scry-poc-f_edbaeb86bcfed108`; plan input `true; echo …`; duplicate → rank 0 / `reject` | **eval**: rank **93** (`pursue`), channel `stdin` (the `Console.ReadLine` line); the `refine` command itself is **not run** |
| repro | `repro.json`, `dynamic.json` | **emulated**: the plan's env (`SCRY_CMD='true; echo scry-poc-…'`) fed to the *old* reproducer; the run's stdout is exactly `scry-poc-f_edbaeb86bcfed108`, exit 0. The plan-derived harness path in `repro` is **not run**. | **not run** (needs the .NET SDK and the new binary) |
| verify | `verify/verify.json` | **measured** (old binary): `still-reported` — it has no marker/plan awareness. The new verdict `finding-present-poc-observed` is the intended result, **not run**. | **not run** |

The `before` row is the important honest comparison: the finding was real in both cases,
but the old reproducer ran the C program with a 0-byte input and no env, so it never
touched `getenv("SCRY_CMD")`; and the old CLI could not see the C# finding at all.

## 2. The weakest link, with evidence

Two links are weak; they are adjacent, and the loop failed at the second.

**(a) No candidate refinement beyond listing.** `scan` upserts every finding at
`state = new` with no rank; `list` filters only by state; `triage` takes an ID typed by a
human. Nothing deduplicates two paths to the same sink or says which of 40 alerts is
worth a day. Evidence: `WorkflowCmd.wfScanPairs` (the record is built with
`state := new` for every finding), `Scry.WfRecord` (no rank/score field), `listCmd`
(`--state` is the whole filter), `triageCmd` (`ID --state`).

**(b) The PoC is a template, not derived from the witness/path.** `Repro.wiz` has

```wiz
def Scry.wfDefaultHarnessText : String := "#!/bin/sh\nexec \"$1\"\n"
```

and `WorkflowCmd.reproCmd` generates an input only when the sink callee is literally
`gets` (a run of `A`s). The `--witness` file is accepted (schema/authority/validated
checked) and its `input.text` becomes a file, but its path condition and model are only
recorded; `Dynamic.wiz:35-39` says so explicitly. So the "PoC" for a finding is chosen by
the operator or by a fixed template: the analysis's actual path (which source, which
sink argument) does not reach the reproducer.

Measured on the C fixture before this change: `findings scan` produced
`f_edbaeb86bcfed108`, and `findings repro` ran the program under
`address+undefined` with a **0-byte** input and the fixed `exec "$1"` harness. The run
exited 0, no sanitizer fired, and `dynamic.json` had no `derivedFrom`, no `plan` and no
`markerObserved`. `verify` said `still-reported`: the finding was real, but the PoC had
not touched the source (`getenv("SCRY_CMD")`) or the sink (`system`). That is the link
this change repairs.

The C# corpus makes (b) concrete: `repro` runs `cc -std=c11` on the source, so on a
`.cs` finding it cannot produce a run at all. The finding's path says
`System.Console.ReadLine → … → System.Diagnostics.Process.Start`, and that is exactly
what a PoC needs to control (stdin) and observe (a marker in the child's output).

**What was built.** `refine` (the missing triage step) and a `repro` that consumes the
plan `refine` derived from the path. This addresses (a) by ranking/deduplicating and (b)
by replacing the hand-written harness with a channel-derived one. It is deliberately not
a symbolic-execution engine: the plan is a *concrete witness* derived from the static
path, and its authority stays L1 (observed run), not L3 (checked concolic witness).

Why not make `findings repro --witness` the fix? Because the witness contract is for a
future S6a producer. Wiring the static path to the reproducer is available today and is
the data the analysis already has; a future witness can fill the same `plan` fields with
`authority: L3` and a path condition without changing the downstream stages.

## 3. The contract between stages

The contract is one value, `Scry.WfCandidate`, stored in `WfRecord.candidate`, written to
`candidate.json`, and repeated in the root bundle under `candidate`:

```json
{
  "schema": "scry-workflow-candidate/1",
  "stage": "scan | refined | poc | poc-attempted | verified",
  "rank": 0,
  "verdict": "unranked | pursue | deprioritise | reject",
  "reasons": ["base 40", "certificate checked (+15)", "..."],
  "source": { "callee": "getenv", "channel": "env", "detail": "SCRY_CMD",
              "function": "main", "line": 7, "column": 12, "variable": 3 },
  "plan": {
    "channel": "env", "envName": "SCRY_CMD",
    "inputText": "true; echo scry-poc-f_…", "marker": "scry-poc-f_…",
    "sink": { "function": "main", "callee": "system", "argument": 0 },
    "derivedFrom": "static.json path; source getenv at main:7"
  }
}
```

Who writes what:

| stage | writes | invariants |
|---|---|---|
| `scan` | `stage=scan`, `verdict=unranked`, `rank=0`, empty plan | identity is `f_…`; the candidate is never ranked here |
| `refine` | `stage=refined`, `rank`, `verdict`, `reasons`, `source`, `plan` | no re-analysis; every input comes from `static.json`, the finding, or the source line; a duplicate of a better candidate gets `reject` (same function + sink callee + argument) |
| `repro` | `stage=poc` (marker observed) or `poc-attempted` | the plan is only *executed*; an override (`--input/--harness/--env`) is recorded as `harness.source=supplied`, and the plan is still named |
| `verify` | `stage=verified`, `verify/verify.json` | static and dynamic are separate; `finding-present-poc-observed` requires both the finding and the marker, and is not a proof of exploitability |

The store schema stays `scry-workflow-store/1`; the new fields are additive
(`candidate`, `candidateFile`) and an old store parses with `candidate = null`. The
bundle's `evidenceItems` gains a `poc` item with authority `L1` when the marker was
observed, `L0` otherwise; that is the existing authority ladder, not a new one.

## 4. The change

* `lib/Scry/Workflow.wiz`: `WfSource`, `WfPlan`, `WfCandidate`; rank and verdict;
  callee/channel/literal extraction from the source line; JSON render/parse; the record
  carries `candidate`/`candidateFile`.
* `scry/src/Scry/WorkflowCmd.wiz`:
  * `scan` writes `candidate.json` (stage `scan`).
  * `refine [--db] [--json] [--quiet]` derives and ranks, deduplicates, writes
    `candidate.json`, and promotes `pursue` = `new → triaged`.
  * `repro` builds the harness/input/env from the plan (`plan-harness.sh`,
    `plan-input.txt`), records `derivedFrom`, `harness.source`, `run.markerObserved`, and
    advances the candidate stage.
  * `verify` reports `finding-present-poc-observed`, records `poc.markerObserved`, and
    advances the candidate stage.
  * `list`/`show` display rank/verdict/stage/plan.
* `scry/src/Scry/Repro.wiz`: `ReproConfig.plan/harnessSource/derivedFrom`,
  `ReproResult.markerObserved`, and a C# mode (`dotnet run --file Program.cs`, .NET 10)
  because `cc` cannot build a C# finding. The C# run is a concrete run (L1) with no
  ASAN/UBSAN; the record says exactly that.
* `scry/src/Scry/TaintCmd.wiz`: `.cs` goes through `Scry.CsLower` (tree-sitter-c-sharp →
  spill → `Scry.Cs.programOf` → the same `Scry.analyze`), so `scry findings scan` and
  `scry taint` reach the C# fixtures. This is the "project loader" gap at the file
  level; a `.sln`/`.csproj` loader is still not there.
* `scry/corpus/workflow/cwe78-getenv.c`: a C fixture whose source names its env var, so
  the derived plan is genuinely reproducible (the existing C fixtures use `getenv(0)`,
  which a harness cannot control).
* Tests: `Tests/Groups/ScryWorkflow.lean` (pure contract/rank/plan/JSON) and
  `scry/tests/workflow-e2e.wiz` (the loop with real command functions and a real
  compiler).

## 5. The end-to-end test

`scry/tests/workflow-e2e.wiz` (`-- test: run`) does:

1. `findings scan` on the C fixture and the C# fixture, into a temp DB/artifacts dir;
2. `findings refine`; asserts `candidate.json` stage/rank/verdict/channel/env name,
   `triaged` state for the C candidate, and `stdin` for the C# candidate;
3. `findings repro` with the compiler the same probe dynamic analysis uses; asserts
   `derivedFrom = candidate.json`, `harness.source = derived`, `run.markerObserved`, and
   candidate stage `poc`;
4. `findings verify`; asserts the verdict, `poc.markerObserved`, exit 0, and candidate
   stage `verified`;
5. reads the root `finding.json` and asserts the candidate is there and the evidence has
   a `poc` item with status `observed`.

The C# repro is not in the golden test because it needs the .NET SDK (10.0.403 here;
`dotnet run --file` is the file-based app mode). A machine without the SDK still runs
the C# **scan/refine** assertions, because those need only the native grammar.

**Execution status: not run.** The test is compiled through C by `grail test`; that
needs the same `grail build scry` closure the queue is blocking (the test links the
native parser and imports `Scry.WorkflowCmd`). Static checking of the modules did pass
with the patched toolchain: `wiz check` succeeds for `lib/Scry/Workflow.wiz`,
`scry/src/Scry/Repro.wiz`, `scry/src/Scry/TaintCmd.wiz` and
`scry/src/Scry/WorkflowCmd.wiz`. Checking the test file itself exceeded the 300-second
`light` limit; that is a timeout, not a pass. The expected file is provisional: it was
written from the measured id (`f_edbaeb86bcfed108`), the eval'd rank/plan and the
emulated run, and `grail test workflow-e2e --update` should be the first thing run when
the package builds. If it differs, the diff is the finding, not a pass.

The pure contract is covered independently in CI by the `scry-workflow` group
(`Tests/Groups/ScryWorkflow.lean`), which needs no build and asserts the same
rank/verdict/plan/JSON values (rank 88/95, duplicate reject, `SCRY_CMD`).

## 6. What this does not claim

* `finding-present-poc-observed` is one concrete run of one derived input (L1). It is
  not proof that every input reaches the sink, and it is not a concolic witness (L3).
* `refine` is a heuristic ranking over static evidence, not a decision procedure. Its
  reasons are written so a reviewer can overrule it; the human `triage` command still
  exists and still owns `confirmed`/`fixed`.
* The C# frontend is the first slice (`CSHARP.md` §2): lambdas, `switch` expressions,
  nullable flow and real bounds checking are out. The four C# taint fixtures are all
  CWE-78; there are no CWE-22/476 fixtures to run, so this note does not claim them.
* The C# reproducer runs the program; it does not build a project, restore packages, or
  use a sanitizer.

## 7. How to resume the blocked run

The build slot is the only missing step. When the queue is free:

```sh
# the patched toolchain used here (a copy of the store grail with the worktree's lib)
TC=/workspace/wt/sec-workflow/.scratch/toolchain/share/wiz/.lake/build/bin/grail
/workspace/wiz-tools/heavy "$TC" -C /workspace/wt/sec-workflow/scry build scry

# then the loop test (writes the .expected on the first run; review the diff)
cd /workspace/wt/sec-workflow/scry
/workspace/wiz-tools/heavy "$TC" -C . test workflow-e2e --update
```

The toolchain copy is scratch (`.scratch/`, git-ignored): it is the store's grail and
wiz with `share/wiz/lib` replaced by the worktree's `lib`, which is what makes the
worktree's `Scry.Workflow` visible to the scry package. A normal toolchain built from
this branch (`lake build wiz grail`) does the same thing; the copy only avoided a second
Lean build.

The batch queue estimate at the time of writing was after midnight for a 6 G/3 CPU
`grail build`; the deck build ran but needed roughly one module every four minutes. No
amount of local `nice` is a substitute, so this is a report of a blocked job, not a
test that passed.
