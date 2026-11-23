# The `--target` name table: one list

**Status.** Lane `target-registry`, 2026-11-23, branch `agent/target-registry`. The F42
commit `4be566652` is merged onto `integration/train12` `f489cc876`; this note records
where the target names are parsed, what is now the single source, and what is still
owed. Base conflict resolutions: `Main.lean` (train12 had reintroduced its `targets`
literal), `selfhost/Cli.wiz` (train12's `ebpf`/probe refusal vs F42's
unknown-vs-unsupported split), `.github/repo-subsets.json` (generated; regenerated).

## 1. Inventory: who reads `--target`

| site | what it does | after this lane |
|---|---|---|
| `Wiz/Compiler/Target.lean` | the table: five entries (`c`, `llvm`, `wasm`, `bpf`, `js`), six spellings (`bpf` has the alias `ebpf`), the supported flag/reason, `choicesText`/`choices`, `resolve` | **the one name table**; `choices` is derived from it, not a literal |
| `Main.lean`: `checkTarget`, `takeTarget` | the host CLI. `--target NAME`, `--llvm`, `--wasm`; unknown vs unsupported; two-target conflicts | no name list; every flag goes through `Wiz.Target.resolve` |
| `Wiz/Selfhost.lean`: `targetsSource`, `compilerSource` | renders the table as Wiz definitions (`targetModes`, `targetImplemented`, `targetProbe`, `targetChoices`) and splices them before `selfhost/Cli.wiz`; `toolchainId` hashes the fragment | the generated artifact the driver compiles |
| `selfhost/Cli.wiz`: `parseOptsGo` | the self-hosted driver's `--target NAME`, `--llvm`, `--wasm`; `targetOk`/`targetKnown`/`targetIsProbe` | no name list: `targetModes`/`targetImplemented`/`targetProbe`/`targetChoices` come from `targetsSource` |
| `Grail/Selfhost.lean` | builds the `checker`/`compiler` roles from `Selfhost.compilerSource` | no parser of its own; it gets the generated table |
| `Grail/Cli.lean`, `Grail/Config.lean` | `grail build TARGET` names **build-graph** targets (`.exe`, `tests`, `command`), not compiler targets; `grail` never passes `--target` to `wiz` | no change; see the manifest-gap section of the `ext-registry` lane's note |
| `Main.lean` usage text, `selfhost/Cli.wiz` header/help, `docs/selfhost-compiler.md` | prose copies of the spellings | prose only, not parsed; may drift, lowest priority |
| `Tests/Groups/BpfTrace.lean` | pins the selfhost's probe refusal sentence (`ebpf`, `bpf-core/1`) | unchanged; the sentence still lives in the driver |
| `Wiz/Attest.lean` | records `backend` as `c`/`llvm` in an attestation | not a parser |

`Main.lean` used to have `targets := ["c","llvm","wasm","bpf","js","ebpf"]` and
`selfhost/Cli.wiz` had `targetModes` with the same six names. Both are gone: the host
reads `Wiz.Target.all`, and the selfhost binary is compiled with `targetsSource`
rendered from it. The selfhost's *capability* is deliberately separate:
`Wiz.Selfhost.selfhostImplemented = ["c","llvm"]` (C5), and `targetProbe` is derived
from the host row's `bpf` aliases. A name/alias added to `Wiz.Target.all` reaches both
drivers on the next build with no other edit.

The refusals still differ where they mean different things:

* `--target bogus` (host and selfhost): `unknown target bogus (choose c, llvm, wasm,
  bpf, js or ebpf)`; exit 1.
* `--target` with no value: `--target needs c, llvm, wasm, bpf, js or ebpf`; exit 1.
* `--target wasm` / `--target js` (selfhost): `unsupported target …: the self-hosted
  backend emits C and LLVM (C5)`; exit 1 — a capability, not a typo (F42).
* `--target bpf` / `--target ebpf` (selfhost): the pinned `unsupported-target: the
  backend 'ebpf' reads bpf-core/1 …` sentence; exit 1.

## 2. What this lane changed

* `Wiz/Compiler/Target.lean`: `aliases` on `Target`, `ebpf` as `bpf`'s alias (train12
  had it; the F42 table did not), `spellings`, derived `choices`, `canonicalIn`,
  `unknownIn`/`unknown`. A custom table now lists its own names in the refusal.
* `Main.lean`: `checkTarget` resolves every spelling, including `--llvm`/`--wasm`
  (previously those flags bypassed the table); the F42 unknown-vs-unsupported logic and
  messages are preserved, and `bpf`/`ebpf` dispatch is unchanged.
* `Wiz/Selfhost.lean`: `targetsSource` (the splice) and `selfhostImplemented`/
  `selfhostProbeSpellings`; `toolchainId` now includes the fragment, so a change to the
  table is a cache cold, not a stale hit.
* `selfhost/Cli.wiz`: the hand-written `targetModes` is deleted; parsing reads the
  generated names; the probe refusal and the C5 sentence are unchanged.
* `Tests/Groups/SelfhostCliDiff.lean`: the target-table case now pins six spellings, the
  `ebpf` alias, the derived choices, the exact generated `targetModes` line and that
  `selfhost/Cli.wiz` does not define `targetModes` again; the F42 case covers `js`
  (generic unsupported) and `bpf`/`ebpf` (probe refusal), each asserted **not** to be
  "unknown", plus the unknown/missing-value parity with the host.

## 3. Blocker: `Wiz/Ext` is not on `train12`

`Wiz/Ext/Basic.lean` and `Wiz/Ext/Resolve.lean` exist only as uncommitted work on
`agent/ext-registry` (read, not edited). They are the full `Entry`/`Capability`/
`Table.resolve`/`resolveBackend` model; the ext lane's `Tests/Groups/Ext.lean` covers
unknown (`unknown-target`), not-enabled (`target-not-enabled`, a package row whose set is
not selected) and undeclared capability (`target-capability`).

Because that interface is not in this tree, this lane **kept the small table** and wrote
the adapter seam in `Wiz/Compiler/Target.lean`'s module doc (a table of the `Target` →
`Wiz.Ext` mapping). It deliberately has no `set`/`caps` fields: adding them here would be
a second registry. The not-enabled and undeclared-capability tests therefore cannot be
written on this base; they must land with `Wiz/Ext` (the ext lane has them). When it
merges:

1. delete `Wiz/Compiler/Target.lean`'s table and `Main.takeTarget`'s use of it; call
   `Wiz.Ext.resolveBackend` (or `resolveBackendFor` with the build's needs) and dispatch
   on `Entry.payload`;
2. drop `Wiz.Selfhost.targetsSource`'s name rendering in favour of
   `Wiz.Ext.backendSpellings`/`backendChoices` (the splice shape stays);
3. run `=ext` together with the selfhost groups.

The manifest-declared `demo` target is still blocked for the reason in the ext lane's
note (`wiz-notes/ext-registry.md` on `agent/ext-registry`) §4: `grail` reads
`grail.wiz`, `wiz` does not, and no `--target` selection is passed from `grail` to the
compiler.

## 4. What must run later (not run here: the heavy queue was reserved)

* `lake build wiz tests` — the Lean side: `Target`, `Selfhost`, `Main`, the test group.
* `lake test -- '=selfhost-cli-diff' '=selfhost-cli'` — builds the selfhost compiler with
  the C toolchain; covers the generated table end to end (unknown/unsupported/probe,
  `=cli`-style behavior).
* `lake test -- '=selfhost'` — the host guard compiles `compilerSource`, so it is the
  first check that the spliced preamble is accepted by the host frontend; then the
  bootstrap cases.
* `lake test -- '=backend' '=wasm' '=js' '=bpf' '=bpf-trace'` — the target groups whose
  CLI paths this touches.
* `scripts/fixpoint.sh` / the selfhost chain — `self.wiz` gained the generated preamble;
  the fixpoint should still hold, but only a run proves it.
* `scripts/check-wizc-release.sh --write-pin --seed DIR` — `scripts/wizc-seed.json`
  pins `self.wiz`; it is a release-time pin (not checked by CI) and this lane changed
  that text.
* `python3 scripts/repo-subsets.py --check` — the JSON was regenerated here; the check
  is part of CI.
* After `agent/ext-registry` merges: `lake test -- '=ext'` and the follow-up in §3.
