# `=selfhost-libdiff` classification (169 diverging of 209)

Source: the four-part `=selfhost-libdiff` run on `libdiff-corpus` (`de5de5a64`,
2026-11-20 20:28–21:32) — `records-{1..4}-of-4.jsonl` and `summary-{1..4}-of-4.txt` in
that worktree's `.lake/libdiff/`. 209 files: 169 diverging, 31 bounded, 8 both-reject,
1 ok. The host is the Lean frontend; the self side is the self-hosted compiler
(`check FILE --types`). The first error is the harness's first error **in the file**,
or the first import error when the root file has none; a row whose error is in an
import says so in the location.

This is a map, not a gate. The classification is by **first cause**: the thing that
makes this file fail first, not every later error in it. For cascades the `why` column
names the failing base module; the `file` in the first-error column is where the
harness saw it.

## Counts by group

| group | files |
|---|---:|
| real selfhost bug | 131 |
| host-only syntax | 25 |
| expected divergence | 13 |
| **total** | **169** |

### Reading the groups

* **host-only syntax** — the construct is not in the selfhost frontend; implementing
  it (or declaring it out of scope) is the fix.
* **real selfhost bug** — the host accepts and the selfhost rejects or crashes; the
  frontend/kernel/runtime needs fixing.
* **expected divergence** — the module's subject is the C12 FFI/native boundary or the
  C13 63-bit `Nat`; it is deliberately outside the selfhost's current scope.
* **bounded/crash** — the appendix below; this run has 30 host timeouts and one
  self-hosted OOM, not SIGSEGV.

`lib/Sys.wiz` itself is in **real selfhost bug** (its first error, `EIO.bind`, is a
fixable elaboration bug); its clients are in **expected divergence** because their
remaining surface is the File/Sys/process/clock FFI (C12).

## Counts by root cause (top 25)

| root cause | group | files |
|---|---|---:|
| Word equations | real selfhost bug | 23 |
| Hdl/Core | real selfhost bug | 18 |
| String ++ | real selfhost bug | 13 |
| expected: C12 FFI/IO | expected divergence | 12 |
| List.foldl missing | real selfhost bug | 12 |
| Text prelude duplicate | real selfhost bug | 8 |
| Scry base | real selfhost bug | 8 |
| selfhost: no meta API | host-only syntax | 7 |
| nested inductives | real selfhost bug | 6 |
| WordArray equations | real selfhost bug | 6 |
| selfhost: no general deriver | host-only syntax | 5 |
| Logic True/Unit | real selfhost bug | 4 |
| ULift | real selfhost bug | 4 |
| selfhost: quantity terms | host-only syntax | 3 |
| pair let | real selfhost bug | 3 |
| Int order | real selfhost bug | 3 |
| selfhost: term.num | host-only syntax | 2 |
| selfhost: command.builtin | host-only syntax | 2 |
| typeclass search | real selfhost bug | 2 |
| Loom toR | real selfhost bug | 2 |
| Scry test constructors | real selfhost bug | 2 |
| Eq congrArg | real selfhost bug | 1 |
| Feral | real selfhost bug | 1 |
| FingerTree | real selfhost bug | 1 |
| HProp | real selfhost bug | 1 |

## Top five fixes by files cleared

Counts are files whose **first error** names this cause. A fix can also expose a
second error in the same file (the selfhost reports one first error per file); the
"also" column says what becomes reachable. The expected-divergence roots and the
multi-fix `Scry base` root are excluded from this ranking.

| # | fix | clears (first error) | also |
|---:|---|---:|---|
| 1 | `Word.wiz` equation compiler: `def … : (m n : Nat) → …` with equations is rejected (`equations need a function type`, Word:42). | **23** | Unblocks `Hdl/Core`'s second failure (`BitVec` at 189) and the Scry `U64`/`U64Map`/`Store`/`Datalog`/`Eval`/`PointsTo` chain. |
| 2 | Align the embedded prelude with `lib/Text`: add `List.foldl` and stop re-declaring `List.map`/`String.length`. | **20** (12 `List.foldl` + 8 `Text` duplicate) | `lib/Scry/Rules`/`Models`/`Taint`/`Workflow`/`Sarif` and the `Scry` base chain get past their first error. |
| 3 | `Hdl/Core` dotted-recursive definitions: `Hdl.indexed` cannot resolve its own `Hdl` name (Core:113). | **18** | Needs #1 for `HwTy.El`'s `BitVec` at Core:189; the two together clear the Hdl cluster. |
| 4 | `String ++`: `"…" ++ s` is inferred as `List.append` instead of `String.append` (`expected List, got String`). | **13** | The count includes the three `Json.parse` users (`Tagged`, `tests/codegen`, `tools/SchemaMain`); the same shape also appears in `Args`, `RuleTaint`, `Facts`, `Project`, `Query`, `CsLower`, `tests/cst`. |
| 5 | Host-only meta API (`Macro`/`Syntax`/`Expr`/`ParamView`): the embedded prelude omits the elaborator-time API. | **7** | Large (elaboration-time evaluation); `Data/ListLemmas`, `Deriving`, `Grail`, `OpticDerive`, `BvDecide`, `SatTactic`, `RingTactic`. |

Next by size, if #5 is too large: nested inductive occurrence (6), `WordArray.wiz:50` (6), custom `deriver` (5), `Logic` `True`/`Unit0` (4), `ULift` (4), quantity terms (3).

The `expected divergence` rows are **not** in this queue: 12 are the C12 FFI/IO
boundary (the `IO`/`Std` natives and the `EIO`/`FS`/`Clock`/`ExitStatus`/`SpawnOptions`
users) and one is the C13 63-bit numeral. They are counted separately below.

## Diverging files (169)

| file | cause | first error | group | why |
|---|---|---|---|---|
| `lib/Optic.wiz` | Data.Result quantity failure (Result.map) | `lib/Optic.wiz:58:1` unknown identifier Result.map | host-only syntax | `Result.map` is missing because Data.Result.wiz fails at its `%q` quantity field (ResultQ). |
| `lib/Sat.wiz` | absurd (term.absurd) | `lib/Sat.wiz:24:1` unsupported syntax term.absurd | host-only syntax | `absurd h.1`; `absurd` is a host prelude primitive the selfhost lacks. |
| `lib/Int.wiz` | builtin command | `lib/Int.wiz:29:1` unsupported command command.builtin | host-only syntax | `builtin int := Int`; same missing `builtin` command. |
| `lib/Prelude.wiz` | builtin command | `lib/Prelude.wiz:159:1` unsupported command command.builtin | host-only syntax | `builtin nat := Nat`; the selfhost has no `builtin` command (B18/D9). |
| `lib/Hdl/Signal.wiz` | coinductive command | `lib/Hdl/Signal.wiz:41:1` unsupported command command.coinductive | host-only syntax | `coinductive Signal …`; the selfhost has no coinductive command (A19). |
| `lib/Hdl/Axi4.wiz` | custom deriver (Bundle) | `lib/Hdl/Axi4.wiz:112:1` no deriver for Bundle (register one with `attribute [deriver Bundle] f`) | host-only syntax | `deriving Bundle` on `Axi4.Aw`; `attribute [deriver Bundle]` needs the general deriver registry (A11). |
| `lib/Hdl/AxiLite.wiz` | custom deriver (Bundle) | `lib/Hdl/AxiLite.wiz:38:1` no deriver for Bundle (register one with `attribute [deriver Bundle] f`) | host-only syntax | `deriving Bundle` on `AxiLite.Aw`; `attribute [deriver Bundle]` needs the general deriver registry (A11). |
| `lib/Hdl/AxiStream.wiz` | custom deriver (Bundle) | `lib/Hdl/AxiStream.wiz:64:1` no deriver for Bundle (register one with `attribute [deriver Bundle] f`) | host-only syntax | `deriving Bundle` on `AxiStream.Beat`; `attribute [deriver Bundle]` needs the general deriver registry (A11). |
| `lib/Hdl/Bus.wiz` | custom deriver (Bundle) | `lib/Hdl/Bus.wiz:58:1` no deriver for Bundle (register one with `attribute [deriver Bundle] f`) | host-only syntax | `deriving Bundle` on `Bus.Req`; `attribute [deriver Bundle]` needs the general deriver registry (A11). |
| `lib/Hdl/Ddr.wiz` | custom deriver (Bundle) | `lib/Hdl/Ddr.wiz:54:1` no deriver for Bundle (register one with `attribute [deriver Bundle] f`) | host-only syntax | `deriving Bundle` on `Ddr.Req`; `attribute [deriver Bundle]` needs the general deriver registry (A11). |
| `lib/Hdl/Temporal.wiz` | existential syntax (term.ex) | `lib/Hdl/Temporal.wiz:55:1` unsupported syntax term.ex | host-only syntax | `∃ k, …` in a term; the selfhost parser has no `term.ex` (A17 surface). |
| `lib/BvDecide.wiz` | macro/meta API (Expr) | `lib/BvDecide.wiz:25:1` unknown identifier Expr | host-only syntax | `Expr`; `Expr` is in lib/Prelude but not in the selfhost embedded prelude (and BvDecide imports SatTactic/Sat). |
| `lib/RingTactic.wiz` | macro/meta API (Expr) | `lib/RingTactic.wiz:39:1` unknown identifier Expr | host-only syntax | `Expr`; same missing meta API (also imports Rat/Ring). |
| `lib/SatTactic.wiz` | macro/meta API (Expr) | `lib/SatTactic.wiz:30:1` unknown identifier Expr | host-only syntax | `Expr` and term-building meta API; no elaborator-time evaluation in the selfhost. |
| `lib/Data/ListLemmas.wiz` | macro/meta API (Macro) | `lib/Data/ListLemmas.wiz:60:1` unknown identifier Macro | host-only syntax | `def List.memForallMacro : Macro := …`; the embedded prelude has no `Macro`. |
| `lib/OpticDerive.wiz` | macro/meta API (ParamView) | `lib/OpticDerive.wiz:23:1` unknown identifier ParamView | host-only syntax | `ParamView`; the embedded prelude omits the `ParamView`/`FieldView` meta types. |
| `lib/Deriving.wiz` | macro/meta API (Syntax) | `lib/Deriving.wiz:104:1` unknown identifier Syntax.mkVar | host-only syntax | `Syntax.mkVar`; no elaborator-time `Syntax` API in the embedded prelude. |
| `lib/Grail.wiz` | macro/meta API (Syntax) | `lib/Grail.wiz:335:1` unknown identifier Syntax.decimal | host-only syntax | `Syntax.decimal`; same missing `Syntax` API. |
| `scry/tests/schema.wiz` | match in #eval term (term.match) | `scry/tests/schema.wiz:9:1` unsupported syntax term.match | host-only syntax | `#eval match … with`; the selfhost parser has no `term.match` in this position. |
| `lib/SimpLemmas.wiz` | notation `^` missing | `lib/SimpLemmas.wiz:51:32` expected identifier, numeral, 'ω', string literal, 'include_str', 'Type', 'Sort', 'Prop', '_', '?', '(', '@', 'fun', 'λ', 'rfl', 'native_refl', 'Enum… | host-only syntax | `b ^ 0 = 1`; the selfhost embedded prelude has no `^` notation, so the parser stops at `^`. |
| `lib/Hdl/Apb.wiz` | numeral term (term.num) | `lib/Hdl/Apb.wiz:36:1` unsupported syntax term.num | host-only syntax | `Nat.div dw 8` (a numeral in a type term) reaches the parser as an unsupported `term.num`. |
| `lib/Hdl/Wishbone.wiz` | numeral term (term.num) | `lib/Hdl/Wishbone.wiz:33:1` unsupported syntax term.num | host-only syntax | Same `Nat.div dw 8` numeral-in-a-type `term.num` parser gap as Hdl/Apb. |
| `scry/grail.wiz` | package DSL syntax | `scry/grail.wiz:14:3` expected 'def', 'private', 'sealed', 'local', 'partial', 'mutual', 'axiom', '#check', '#print', '#reduce', '#eval', '#erase', 'import', '#run', '#ir'… | host-only syntax | `\|> Package.lib …` (grail build-file DSL); the selfhost parses commands only. |
| `lib/Data/Result.wiz` | quantity term (%t) | `lib/Data/Result.wiz:49:1` a quantity must be 0, 1 or ω (quantity terms %t are not supported by the self-hosted frontend) | host-only syntax | `(%q a : A)`; quantity terms `%t` are explicitly refused by the selfhost frontend. |
| `lib/Region.wiz` | quantity term (%t) | `lib/Region.wiz:117:1` a quantity must be 0, 1 or ω (quantity terms %t are not supported by the self-hosted frontend) | host-only syntax | `(%q h : H)`; same explicit quantity-term refusal. |
| `lib/EffHeap.wiz` | Effect missing (Eff fails) | `lib/EffHeap.wiz:34:1` unknown identifier Effect | real selfhost bug | `Effect` is unknown because Eff.wiz fails at its ULift class declaration. |
| `lib/BitBlast.wiz` | Eq.congrArg implicit mismatch | `lib/BitBlast.wiz:31:1` type mismatch: expected Eq(((((((?m0 A) B) f) a) b) e), ((((((?m2 A) B) f) a) b) e), ((((((?m3 A) B) f) a) b) e)), got Eq(A, a, b) | real selfhost bug | `Eq.congrArg f e` is checked with the wrong implicit arguments (same shape as Nat). |
| `lib/Scry/Wil.wiz` | Exception `do` desugared as IO | `lib/Scry/Wil.wiz:290:1` type mismatch: expected (x10 : World) → ((Prod ((((((((((?m42 op) a) b) dflt✝3) j✝) i✝) xs✝) ih✝) rest✝) ihs✝)) World), got ((Except String) Bool) | real selfhost bug | `Wil.Val.bin` returns `Except String …`; the `do` block is desugared with the IO/World bind, not Except.bind. |
| `lib/Feral.wiz` | Fe.inst List×Ty mismatch | `lib/Feral.wiz:288:1` type mismatch: expected (List (x11 : String) × (((((((((((?m0 x✝0) m) i✝) xs✝) ih✝) rest✝) ihs✝) _) cur✝) m) n)), got (List (x11 : String) × Fe.Ty) | real selfhost bug | `Fe.inst` sees the signature list as a dependent pair (`List (String × Fe.Ty)`) mismatch. |
| `lib/Hdl/Optic.wiz` | Hdl.zoom Lens/Store mismatch | `lib/Hdl/Optic.wiz:23:1` type mismatch: expected (x8 : ((((((((?m0 S) T) I) O) l) g) s) x)) → ((Store ((((((((?m1 S) T) I) O) l) g) s) x)) ((((((((?m0 S) T) I) O) l) g) s) x)… | real selfhost bug | `Hdl.zoom` applies `Lens.get`/`Store` with the wrong implicit telescope. |
| `lib/Hdl/Axi4Law.wiz` | Hdl/Core failure (Hw/HwTy.El/Hdl/Prim/Circuit/SimNode) | `lib/Hdl/Axi4Law.wiz:40:1` unknown identifier HwTy.El | real selfhost bug | The name is declared in Hdl/Core.wiz, which fails at Hdl.indexed (and later needs BitVec/Word). |
| `lib/Hdl/AxiStreamLaw.wiz` | Hdl/Core failure (Hw/HwTy.El/Hdl/Prim/Circuit/SimNode) | `lib/Hdl/AxiStreamLaw.wiz:31:1` unknown identifier HwTy.El | real selfhost bug | The name is declared in Hdl/Core.wiz, which fails at Hdl.indexed (and later needs BitVec/Word). |
| `lib/Hdl/BusLaw.wiz` | Hdl/Core failure (Hw/HwTy.El/Hdl/Prim/Circuit/SimNode) | `lib/Hdl/BusLaw.wiz:36:1` unknown identifier HwTy.El | real selfhost bug | The name is declared in Hdl/Core.wiz, which fails at Hdl.indexed (and later needs BitVec/Word). |
| `lib/Hdl/Cdc.wiz` | Hdl/Core failure (Hw/HwTy.El/Hdl/Prim/Circuit/SimNode) | `lib/Hdl/Cdc.wiz:38:1` unknown identifier Prim | real selfhost bug | The name is declared in Hdl/Core.wiz, which fails at Hdl.indexed (and later needs BitVec/Word). |
| `lib/Hdl/Crc.wiz` | Hdl/Core failure (Hw/HwTy.El/Hdl/Prim/Circuit/SimNode) | `lib/Hdl/Crc.wiz:34:1` unknown identifier Hw | real selfhost bug | The name is declared in Hdl/Core.wiz, which fails at Hdl.indexed (and later needs BitVec/Word). |
| `lib/Hdl/Display.wiz` | Hdl/Core failure (Hw/HwTy.El/Hdl/Prim/Circuit/SimNode) | `lib/Hdl/Display.wiz:76:1` unknown identifier Hw | real selfhost bug | The name is declared in Hdl/Core.wiz, which fails at Hdl.indexed (and later needs BitVec/Word). |
| `lib/Hdl/Mem.wiz` | Hdl/Core failure (Hw/HwTy.El/Hdl/Prim/Circuit/SimNode) | `lib/Hdl/Mem.wiz:57:1` unknown identifier HwTy.El | real selfhost bug | The name is declared in Hdl/Core.wiz, which fails at Hdl.indexed (and later needs BitVec/Word). |
| `lib/Hdl/Netlist.wiz` | Hdl/Core failure (Hw/HwTy.El/Hdl/Prim/Circuit/SimNode) | `lib/Hdl/Netlist.wiz:60:1` unknown identifier SimNode | real selfhost bug | The name is declared in Hdl/Core.wiz, which fails at Hdl.indexed (and later needs BitVec/Word). |
| `lib/Hdl/Pipe.wiz` | Hdl/Core failure (Hw/HwTy.El/Hdl/Prim/Circuit/SimNode) | `lib/Hdl/Pipe.wiz:71:1` unknown identifier Circuit | real selfhost bug | The name is declared in Hdl/Core.wiz, which fails at Hdl.indexed (and later needs BitVec/Word). |
| `lib/Hdl/Prim.wiz` | Hdl/Core failure (Hw/HwTy.El/Hdl/Prim/Circuit/SimNode) | `lib/Hdl/Prim.wiz:66:1` unknown identifier HwTy.El | real selfhost bug | The name is declared in Hdl/Core.wiz, which fails at Hdl.indexed (and later needs BitVec/Word). |
| `lib/Hdl/ProtocolLaw.wiz` | Hdl/Core failure (Hw/HwTy.El/Hdl/Prim/Circuit/SimNode) | `lib/Hdl/ProtocolLaw.wiz:43:1` unknown identifier HwTy.El | real selfhost bug | The name is declared in Hdl/Core.wiz, which fails at Hdl.indexed (and later needs BitVec/Word). |
| `lib/Hdl/Sim.wiz` | Hdl/Core failure (Hw/HwTy.El/Hdl/Prim/Circuit/SimNode) | `lib/Hdl/Sim.wiz:144:1` unknown identifier SimNode | real selfhost bug | The name is declared in Hdl/Core.wiz, which fails at Hdl.indexed (and later needs BitVec/Word). |
| `lib/Hdl/Spi.wiz` | Hdl/Core failure (Hw/HwTy.El/Hdl/Prim/Circuit/SimNode) | `lib/Hdl/Spi.wiz:69:1` unknown identifier Hw | real selfhost bug | The name is declared in Hdl/Core.wiz, which fails at Hdl.indexed (and later needs BitVec/Word). |
| `lib/Hdl/SpiLaw.wiz` | Hdl/Core failure (Hw/HwTy.El/Hdl/Prim/Circuit/SimNode) | `lib/Hdl/SpiLaw.wiz:32:1` unknown identifier HwTy.El | real selfhost bug | The name is declared in Hdl/Core.wiz, which fails at Hdl.indexed (and later needs BitVec/Word). |
| `lib/Hdl/Uart.wiz` | Hdl/Core failure (Hw/HwTy.El/Hdl/Prim/Circuit/SimNode) | `lib/Hdl/Uart.wiz:80:1` unknown identifier Hw | real selfhost bug | The name is declared in Hdl/Core.wiz, which fails at Hdl.indexed (and later needs BitVec/Word). |
| `lib/Hdl/Verified.wiz` | Hdl/Core failure (Hw/HwTy.El/Hdl/Prim/Circuit/SimNode) | `lib/Hdl/Verified.wiz:19:1` unknown identifier Hw | real selfhost bug | The name is declared in Hdl/Core.wiz, which fails at Hdl.indexed (and later needs BitVec/Word). |
| `lib/Hdl/Xdc.wiz` | Hdl/Core failure (Hw/HwTy.El/Hdl/Prim/Circuit/SimNode) | `lib/Hdl/Xdc.wiz:61:1` unknown identifier Hdl | real selfhost bug | The name is declared in Hdl/Core.wiz, which fails at Hdl.indexed (and later needs BitVec/Word). |
| `lib/Hdl/Core.wiz` | Hdl/Core.wiz:113 Hdl.indexed | `lib/Hdl/Core.wiz:113:1` unknown identifier Hdl | real selfhost bug | `def Hdl.indexed {A} : Nat → List A → List (Nat × A)` with two equation arguments: the recursive dotted name is not resolved (the product return triggers it). |
| `lib/Rat.wiz` | Int.Lt missing (IntOrder fails) | `lib/Rat.wiz:37:1` unknown identifier Int.Lt | real selfhost bug | `Int.Lt` is unavailable because IntOrder.wiz first fails with `expected Nat, got Int`. |
| `lib/IntOrder.wiz` | IntOrder.wiz:29 expected Nat, got Int | `lib/IntOrder.wiz:29:1` type mismatch: expected Nat, got Int | real selfhost bug | `Int.Le`/`Int.Lt` elaboration mismatch; downstream Rat/Plot lose Q/Int.Lt. |
| `lib/Tagged.wiz` | Json.parse missing (Json fails on String ++) | `lib/Tagged.wiz:389:1` unknown identifier Json.parse | real selfhost bug | `Json.parse` is unavailable because Json.wiz first fails on a `++` inferred as List.append. |
| `scry/tests/codegen.wiz` | Json.parse missing (Json fails on String ++) | `scry/tests/codegen.wiz:8:1` unknown identifier Json.parse | real selfhost bug | `Json.parse` is unavailable because Json.wiz first fails on a `++` inferred as List.append. |
| `scry/tools/SchemaMain.wiz` | Json.parse missing (Json fails on String ++) | `scry/tools/SchemaMain.wiz:22:1` unknown identifier Json.parse | real selfhost bug | `Json.parse` is unavailable because Json.wiz first fails on a `++` inferred as List.append. |
| `lib/Data/Order.wiz` | Logic.wiz:47 True vs Unit0 | `lib/Logic.wiz:47:1` type mismatch: expected True, got Unit0 | real selfhost bug | `def True.intro : True := ()` is rejected (`expected True, got Unit0`); Logic then loses Eq.congrArg2 and cascades. |
| `lib/Hdl/Arty.wiz` | Logic.wiz:47 True vs Unit0 | `lib/Logic.wiz:47:1` type mismatch: expected True, got Unit0 | real selfhost bug | `def True.intro : True := ()` is rejected (`expected True, got Unit0`); Logic then loses Eq.congrArg2 and cascades. |
| `lib/IntRing.wiz` | Logic.wiz:47 True vs Unit0 | `lib/IntRing.wiz:59:1` unknown identifier Eq | real selfhost bug | `def True.intro : True := ()` is rejected (`expected True, got Unit0`); Logic then loses Eq.congrArg2 and cascades. |
| `lib/Logic.wiz` | Logic.wiz:47 True vs Unit0 | `lib/Logic.wiz:47:1` type mismatch: expected True, got Unit0 | real selfhost bug | `def True.intro : True := ()` is rejected (`expected True, got Unit0`); Logic then loses Eq.congrArg2 and cascades. |
| `lib/Web/Widget.wiz` | Loom missing (Web/Loom fails) | `lib/Web/Widget.wiz:228:1` unknown identifier Loom | real selfhost bug | `Loom` is unknown because Web/Loom.wiz fails at `Loom.toR`. |
| `lib/Trace.wiz` | Mealy.outAt tuple mismatch | `lib/Trace.wiz:56:1` type mismatch: expected (x7 : (((((((?m0 S) I) O) m) s0) xs) t)) → (x8 : (((((((?m1 S) I) O) m) s0) xs) t)) → (x9 : (((((((?m0 S) I) O) m) s0) xs) t)… | real selfhost bug | `Mealy.outAt` expects a nested Prod/World shape instead of the S→I→S×O function. |
| `lib/FingerTree.wiz` | Monoid instance mismatch | `lib/FingerTree.wiz:57:1` type mismatch: expected (Monoid M), got M | real selfhost bug | `Monoid.Lawful` sees the instance argument as the carrier (`expected Monoid M, got M`). |
| `lib/Vec.wiz` | Nat.lt_self mismatch | `lib/Vec.wiz:29:1` type mismatch: expected Eq(μ0(Unit0, arg(Enum2, λx7. case(Desc0(Unit0), x7, ret(tt), ret(tt))), tt), (ind(λx7. λx8. (x9 : Nat) → Bool, λx7. λx8. λx9.… | real selfhost bug | `Nat.lt_self` fails the same Eq/induction shape as Nat/WordArray. |
| `lib/Nat.wiz` | Nat.wiz:46 congrArg2 | `lib/Nat.wiz:46:1` type mismatch: expected Eq(((((((((((?m4 A) B) C) f) a) a') b) b') e) e'), ((((((((((?m7 A) B) C) f) a) a') b) b') e) e'), ((((((((((?m8 A) B) C) f) … | real selfhost bug | `Eq.congrArg2` application is mis-unified (implicit arguments). |
| `lib/HProp.wiz` | Option.orElse_none mismatch | `lib/HProp.wiz:60:1` type mismatch: expected Eq(μmax(0, 0)(Unit0, arg(Enum2, λx8. case(Descmax(0, 0)(Unit0), x8, ret(tt), arg(x0, λx9. ret(tt)))), tt), scase(λx8. λx9. (O… | real selfhost bug | `Option.orElse o .none = o` fails a dependent equality at the `Option` eliminator. |
| `lib/HeapBorrow.wiz` | Prog missing (Hoare fails) | `lib/HeapBorrow.wiz:30:1` unknown identifier Prog | real selfhost bug | `Prog` is unknown because Hoare.wiz fails on the inductive occurrence check. |
| `lib/HoareExamples.wiz` | Prog missing (Hoare fails) | `lib/HoareExamples.wiz:22:1` unknown identifier Prog | real selfhost bug | `Prog` is unknown because Hoare.wiz fails on the inductive occurrence check. |
| `lib/Plot.wiz` | Q missing (Rat fails) | `lib/Plot.wiz:46:1` unknown identifier Q | real selfhost bug | `Q` is unavailable because Rat.wiz fails on `Int.Lt` (IntOrder). |
| `lib/Ring.wiz` | Ring.Key.cmp_eq equations need a function type | `lib/Ring.wiz:63:1` equations need a function type | real selfhost bug | Same equation-compiler failure as Word.add_succ. |
| `lib/Scope.wiz` | Scope.with Prod/Done mismatch | `lib/Scope.wiz:72:1` type mismatch: expected (x2 : World) → ((Prod ((?m0 A) body)) World), got (x2 : World) → ((Prod (x3 : A) × (Done Region.static)) World) | real selfhost bug | `Scope.with` expects `Prod A×Done` vs the `IO`/`Done` pair; likely the pair-let/IO issue. |
| `scry/src/Scry/CsCst.wiz` | Scry.CstStore missing (CstStore/Word) | `scry/src/Scry/CsCst.wiz:40:1` unknown identifier Scry | real selfhost bug | CstStore/Lower/WordArray fail first. |
| `scry/src/Scry/CstOptics.wiz` | Scry.Facts missing (Scry base) | `scry/src/Scry/CstOptics.wiz:91:1` unknown identifier Scry | real selfhost bug | Optics/Schema/Facts/CstStore fail first. |
| `scry/src/Scry/OpticsExamples.wiz` | Scry.Facts missing (Scry base) | `scry/src/Scry/OpticsExamples.wiz:22:1` unknown identifier Scry | real selfhost bug | Optics/Wil/Analysis/PointsTo/Facts/CstStore fail first. |
| `lib/Scry/Bounds.wiz` | Scry.flatten missing (Scry base) | `lib/Scry/Bounds.wiz:83:1` unknown identifier Scry | real selfhost bug | Scry.flatten is unavailable because Analysis/PointsTo/Rules/Models fail (Word/Text). |
| `lib/Scry/Nullness.wiz` | Scry.nMaxVar missing (Scry base) | `lib/Scry/Nullness.wiz:93:1` unknown identifier Scry | real selfhost bug | Wil/Analysis/AiCfg/AiDomain fail first. |
| `lib/Scry/Race.wiz` | Scry.raceStep missing (Scry base) | `lib/Scry/Race.wiz:64:1` unknown identifier Scry | real selfhost bug | Scry.Fn/nodeStmt are unavailable because Analysis/Word fails. |
| `lib/Scry/Interproc.wiz` | Scry.siteOfCall missing (Scry base) | `lib/Scry/Interproc.wiz:68:1` unknown identifier Scry | real selfhost bug | The Scry base modules (Analysis/PointsTo/Rules/Models/Lifetime) fail first. |
| `lib/Scry/Lifetime.wiz` | Scry.uCurGet missing (Scry base) | `lib/Scry/Lifetime.wiz:95:1` unknown identifier Scry | real selfhost bug | The Scry base modules (Analysis/PointsTo/Rules/Models/Engine) fail first. |
| `lib/Args.wiz` | String `++` resolved as List.append | `lib/Args.wiz:100:1` type mismatch: expected (List (((((((((?m0 x✝0) j✝) i✝) xs✝) ih✝) rest✝) ihs✝) _) f)), got String | real selfhost bug | `"…" ++ s` is inferred as `List.append` (`expected List, got String`) instead of `String.append`; one overload/coercion bug. |
| `lib/Json.wiz` | String `++` resolved as List.append | `lib/Json.wiz:359:1` type mismatch: expected (List (((((((((((((((((((((((((?m16 fuel) s0) s) c) x✝) j✝) i✝) xs✝) ih✝) rest✝) ihs✝) x✝) j✝) i✝) xs✝) ih✝) rest✝) ihs✝) x✝)… | real selfhost bug | The first `++` inside the mutual parser (`"nesting too deep (limit " ++ …`) is inferred as List.append. |
| `lib/Scry/RuleExamples.wiz` | String `++` resolved as List.append | `lib/Scry/RuleExamples.wiz:40:1` type mismatch: expected (List ?m0), got String | real selfhost bug | `"…" ++ s` is inferred as `List.append` (`expected List, got String`) instead of `String.append`; one overload/coercion bug. |
| `lib/Scry/RuleTaint.wiz` | String `++` resolved as List.append | `lib/Scry/RuleTaint.wiz:180:1` type mismatch: expected (List (?m0 m)), got String | real selfhost bug | `"…" ++ s` is inferred as `List.append` (`expected List, got String`) instead of `String.append`; one overload/coercion bug. |
| `lib/Scry/UafExamples.wiz` | String `++` resolved as List.append | `lib/Scry/UafExamples.wiz:21:1` type mismatch: expected (List ?m0), got String | real selfhost bug | `"…" ++ s` is inferred as `List.append` (`expected List, got String`) instead of `String.append`; one overload/coercion bug. |
| `scry/src/Scry/CsLower.wiz` | String `++` resolved as List.append | `scry/src/Scry/CsLower.wiz:129:1` type mismatch: expected (List (((((((((((((((((((((((((((((((((((((((((?m0 c) n) k) x✝) j✝) i✝) xs✝) ih✝) rest✝) ihs✝) x✝) j✝) i✝) xs✝) ih✝) rest✝) i… | real selfhost bug | `"…" ++ s` is inferred as `List.append` (`expected List, got String`) instead of `String.append`; one overload/coercion bug. |
| `scry/src/Scry/Facts.wiz` | String `++` resolved as List.append | `scry/src/Scry/Facts.wiz:26:1` type mismatch: expected (List (((((((((?m3 j) key) x✝) j✝) i✝) xs✝) ih✝) rest✝) ihs✝)), got String | real selfhost bug | `"…" ++ s` is inferred as `List.append` (`expected List, got String`) instead of `String.append`; one overload/coercion bug. |
| `scry/src/Scry/Project.wiz` | String `++` resolved as List.append | `scry/src/Scry/Project.wiz:252:1` type mismatch: expected (List ((?m0 file) a)), got String | real selfhost bug | `"…" ++ s` is inferred as `List.append` (`expected List, got String`) instead of `String.append`; one overload/coercion bug. |
| `scry/src/Scry/Query.wiz` | String `++` resolved as List.append | `scry/src/Scry/Query.wiz:19:1` type mismatch: expected (List (?m0 s)), got String | real selfhost bug | `"…" ++ s` is inferred as `List.append` (`expected List, got String`) instead of `String.append`; one overload/coercion bug. |
| `scry/tests/cst.wiz` | String `++` resolved as List.append | `scry/tests/cst.wiz:11:1` type mismatch: expected (List (?m0 s)), got String | real selfhost bug | `"…" ++ s` is inferred as `List.append` (`expected List, got String`) instead of `String.append`; one overload/coercion bug. |
| `lib/Sys.wiz` | Sys.wiz:71 EIO.bind | `lib/Sys.wiz:71:1` could not elaborate a constructor argument | real selfhost bug | `EIO.bind` fails to elaborate its constructor argument; every EIO/FS/Clock user then sees EIO unknown. |
| `lib/Infoview.wiz` | Text.wiz:45 duplicate List.map | `lib/Text.wiz:45:1` 'List.map' has already been declared | real selfhost bug | The embedded prelude already declares `List.map`/`String.length`; lib/Text defines them again (and lacks List.foldl). |
| `lib/Scry/Ai.wiz` | Text.wiz:45 duplicate List.map | `lib/Text.wiz:45:1` 'List.map' has already been declared | real selfhost bug | The embedded prelude already declares `List.map`/`String.length`; lib/Text defines them again (and lacks List.foldl). |
| `lib/Scry/NullExamples.wiz` | Text.wiz:45 duplicate List.map | `lib/Text.wiz:45:1` 'List.map' has already been declared | real selfhost bug | The embedded prelude already declares `List.map`/`String.length`; lib/Text defines them again (and lacks List.foldl). |
| `lib/Scry/TaintExamples.wiz` | Text.wiz:45 duplicate List.map | `lib/Text.wiz:45:1` 'List.map' has already been declared | real selfhost bug | The embedded prelude already declares `List.map`/`String.length`; lib/Text defines them again (and lacks List.foldl). |
| `lib/Scry/WilExamples.wiz` | Text.wiz:45 duplicate List.map | `lib/Text.wiz:45:1` 'List.map' has already been declared | real selfhost bug | The embedded prelude already declares `List.map`/`String.length`; lib/Text defines them again (and lacks List.foldl). |
| `lib/Text.wiz` | Text.wiz:45 duplicate List.map | `lib/Text.wiz:45:1` 'List.map' has already been declared | real selfhost bug | The embedded prelude already declares `List.map`/`String.length`; lib/Text defines them again (and lacks List.foldl). |
| `lib/Web/Editor.wiz` | Text.wiz:45 duplicate List.map | `lib/Text.wiz:45:1` 'List.map' has already been declared | real selfhost bug | The embedded prelude already declares `List.map`/`String.length`; lib/Text defines them again (and lacks List.foldl). |
| `lib/Web/Playground.wiz` | Text.wiz:45 duplicate List.map | `lib/Text.wiz:45:1` 'List.map' has already been declared | real selfhost bug | The embedded prelude already declares `List.map`/`String.length`; lib/Text defines them again (and lacks List.foldl). |
| `lib/Scry/AiExamples.wiz` | Text.wiz:55 List.foldl missing | `lib/Scry/AiExamples.wiz:73:1` unknown identifier narrowOnce | real selfhost bug | `narrowOnce` is in AiFixpoint, which fails because `List.foldl` is absent from the embedded prelude. |
| `lib/Scry/AiFixpoint.wiz` | Text.wiz:55 List.foldl missing | `lib/Scry/AiFixpoint.wiz:101:1` unknown identifier List.foldl | real selfhost bug | `List.foldl` is defined in lib/Text but absent from the embedded prelude, so it is unknown. |
| `lib/Scry/Diff.wiz` | Text.wiz:55 List.foldl missing | `lib/Scry/Diff.wiz:332:1` unknown identifier List.foldl | real selfhost bug | `List.foldl` is defined in lib/Text but absent from the embedded prelude, so it is unknown. |
| `lib/Scry/EgraphTaint.wiz` | Text.wiz:55 List.foldl missing | `lib/Scry/EgraphTaint.wiz:44:1` unknown identifier Scry | real selfhost bug | `Scry.WgeAlert` is in Taint, which fails because `List.foldl` is absent from the embedded prelude. |
| `lib/Scry/Models.wiz` | Text.wiz:55 List.foldl missing | `lib/Scry/Models.wiz:964:1` unknown identifier List.foldl | real selfhost bug | `List.foldl` is defined in lib/Text but absent from the embedded prelude, so it is unknown. |
| `lib/Scry/Report.wiz` | Text.wiz:55 List.foldl missing | `lib/Scry/Report.wiz:113:1` unknown identifier List.foldl | real selfhost bug | `List.foldl` is defined in lib/Text but absent from the embedded prelude, so it is unknown. |
| `lib/Scry/Rules.wiz` | Text.wiz:55 List.foldl missing | `lib/Scry/Rules.wiz:421:1` unknown identifier List.foldl | real selfhost bug | `List.foldl` is defined in lib/Text but absent from the embedded prelude, so it is unknown. |
| `lib/Scry/Sarif.wiz` | Text.wiz:55 List.foldl missing | `lib/Scry/Sarif.wiz:70:1` unknown identifier List.foldl | real selfhost bug | `List.foldl` is defined in lib/Text but absent from the embedded prelude, so it is unknown. |
| `lib/Scry/Taint.wiz` | Text.wiz:55 List.foldl missing | `lib/Scry/Taint.wiz:136:1` unknown identifier List.foldl | real selfhost bug | `List.foldl` is defined in lib/Text but absent from the embedded prelude, so it is unknown. |
| `lib/Scry/Workflow.wiz` | Text.wiz:55 List.foldl missing | `lib/Scry/Workflow.wiz:64:1` unknown identifier List.foldl | real selfhost bug | `List.foldl` is defined in lib/Text but absent from the embedded prelude, so it is unknown. |
| `scry/src/Scry/Preproc.wiz` | Text.wiz:55 List.foldl missing | `scry/src/Scry/Preproc.wiz:97:1` unknown identifier List.foldl | real selfhost bug | `List.foldl` is defined in lib/Text but absent from the embedded prelude, so it is unknown. |
| `scry/src/Scry/ProjectCache.wiz` | Text.wiz:55 List.foldl missing | `scry/src/Scry/ProjectCache.wiz:70:1` unknown identifier List.foldl | real selfhost bug | `List.foldl` is defined in lib/Text but absent from the embedded prelude, so it is unknown. |
| `lib/Eff.wiz` | ULift universe lift | `lib/Eff.wiz:41:1` ULift.(max(max(0, 0), 0))+1 can't lift U0, which is in Sort 2 | real selfhost bug | `class Functor (f : Type → Type)` / `structure Effect` cannot lift the class type through ULift (Sort 2). |
| `lib/Functor.wiz` | ULift universe lift | `lib/Functor.wiz:32:1` ULift.(max(max(max(0, 0), 0), 0))+1 can't lift (x2 :0 U0) → (x3 :0 U0) → (x4 : (x4 : x2) → x3) → (x5 : (x0 x2)) → (x0 x3), which is in Sort imax(2, i… | real selfhost bug | `class Functor (f : Type → Type)` / `structure Effect` cannot lift the class type through ULift (Sort 2). |
| `lib/Scry/Engine.wiz` | ULift universe lift | `lib/Scry/Engine.wiz:113:1` ULift.(max(max(max(max(0, 0), 0), 0), 0))+1 can't lift U0, which is in Sort 2 | real selfhost bug | `structure Scry.Sem (Ev : Type)` hits the same ULift/Sort-2 failure. |
| `lib/Web/Loom.wiz` | Web/Loom.wiz:228 Loom.toR | `lib/Web/Loom.wiz:228:1` type mismatch: expected (List (x20 : String) × M), got (List (x20 : String) × ((((((((((((((((((((?m14 M) x✝0) x✝1) j✝) i✝) xs✝) ih✝) rest✝) ihs✝) _)… | real selfhost bug | `Loom.toR` tuple/Prod mismatch; also needs List.foldl/List.revOnto later. |
| `lib/Scry/ConcurrencyExamples.wiz` | Wil.cstep missing (Wil fails) | `lib/Scry/ConcurrencyExamples.wiz:149:1` unknown identifier Wil | real selfhost bug | Wil.wiz fails at Wil.Val.bin; the example loses the whole Wil namespace. |
| `lib/BitVec.wiz` | Word.wiz:42 equations need a function type | `lib/BitVec.wiz:38:1` unknown identifier UIntN | real selfhost bug | Word.wiz fails at 42 (`Word.add_succ`), so `UIntN`/`U8`/`U16`/`U32`/`U64`/`BitVec` and every importer lose those names. |
| `lib/BitVecShift.wiz` | Word.wiz:42 equations need a function type | `lib/BitVecShift.wiz:14:1` unknown identifier BitVec | real selfhost bug | Word.wiz fails at 42 (`Word.add_succ`), so `UIntN`/`U8`/`U16`/`U32`/`U64`/`BitVec` and every importer lose those names. |
| `lib/Data/PMap.wiz` | Word.wiz:42 equations need a function type | `lib/Data/PMap.wiz:63:1` unknown identifier U64 | real selfhost bug | Word.wiz fails at 42 (`Word.add_succ`), so `UIntN`/`U8`/`U16`/`U32`/`U64`/`BitVec` and every importer lose those names. |
| `lib/Data/WordBytes.wiz` | Word.wiz:42 equations need a function type | `lib/Data/WordBytes.wiz:18:1` unknown identifier U8 | real selfhost bug | Word.wiz fails at 42 (`Word.add_succ`), so `UIntN`/`U8`/`U16`/`U32`/`U64`/`BitVec` and every importer lose those names. |
| `lib/Encoding.wiz` | Word.wiz:42 equations need a function type | `lib/Encoding.wiz:46:1` unknown identifier U8 | real selfhost bug | Word.wiz fails at 42 (`Word.add_succ`), so `UIntN`/`U8`/`U16`/`U32`/`U64`/`BitVec` and every importer lose those names. |
| `lib/Hdl/Bits.wiz` | Word.wiz:42 equations need a function type | `lib/Hdl/Bits.wiz:24:1` unknown identifier BitVec | real selfhost bug | Word.wiz fails at 42 (`Word.add_succ`), so `UIntN`/`U8`/`U16`/`U32`/`U64`/`BitVec` and every importer lose those names. |
| `lib/Intern.wiz` | Word.wiz:42 equations need a function type | `lib/Intern.wiz:47:1` unknown identifier U32 | real selfhost bug | Word.wiz fails at 42 (`Word.add_succ`), so `UIntN`/`U8`/`U16`/`U32`/`U64`/`BitVec` and every importer lose those names. |
| `lib/Scry/Analysis.wiz` | Word.wiz:42 equations need a function type | `lib/Scry/Analysis.wiz:119:1` unknown identifier U64Map | real selfhost bug | Word.wiz fails at 42 (`Word.add_succ`), so `UIntN`/`U8`/`U16`/`U32`/`U64`/`BitVec` and every importer lose those names. |
| `lib/Scry/Cert.wiz` | Word.wiz:42 equations need a function type | `lib/Scry/Cert.wiz:62:1` unknown identifier Scry | real selfhost bug | Word.wiz fails at 42 (`Word.add_succ`), so `UIntN`/`U8`/`U16`/`U32`/`U64`/`BitVec` and every importer lose those names. |
| `lib/Scry/Certify.wiz` | Word.wiz:42 equations need a function type | `lib/Scry/Certify.wiz:29:1` unknown identifier Scry.Derivation | real selfhost bug | Word.wiz fails at 42 (`Word.add_succ`), so `UIntN`/`U8`/`U16`/`U32`/`U64`/`BitVec` and every importer lose those names. |
| `lib/Scry/Datalog.wiz` | Word.wiz:42 equations need a function type | `lib/Scry/Datalog.wiz:33:1` unknown identifier U64 | real selfhost bug | Word.wiz fails at 42 (`Word.add_succ`), so `UIntN`/`U8`/`U16`/`U32`/`U64`/`BitVec` and every importer lose those names. |
| `lib/Scry/Eval.wiz` | Word.wiz:42 equations need a function type | `lib/Scry/Eval.wiz:35:1` unknown identifier U64 | real selfhost bug | Word.wiz fails at 42 (`Word.add_succ`), so `UIntN`/`U8`/`U16`/`U32`/`U64`/`BitVec` and every importer lose those names. |
| `lib/Scry/PointsTo.wiz` | Word.wiz:42 equations need a function type | `lib/Scry/PointsTo.wiz:185:1` unknown identifier U64 | real selfhost bug | Word.wiz fails at 42 (`Word.add_succ`), so `UIntN`/`U8`/`U16`/`U32`/`U64`/`BitVec` and every importer lose those names. |
| `lib/Scry/Prover.wiz` | Word.wiz:42 equations need a function type | `lib/Scry/Prover.wiz:176:1` unknown identifier Scry | real selfhost bug | Word.wiz fails at 42 (`Word.add_succ`), so `UIntN`/`U8`/`U16`/`U32`/`U64`/`BitVec` and every importer lose those names. |
| `lib/Scry/ProverExamples.wiz` | Word.wiz:42 equations need a function type | `lib/Scry/ProverExamples.wiz:37:1` unknown identifier Scry | real selfhost bug | Word.wiz fails at 42 (`Word.add_succ`), so `UIntN`/`U8`/`U16`/`U32`/`U64`/`BitVec` and every importer lose those names. |
| `lib/Scry/Store.wiz` | Word.wiz:42 equations need a function type | `lib/Scry/Store.wiz:50:1` unknown identifier U64 | real selfhost bug | Word.wiz fails at 42 (`Word.add_succ`), so `UIntN`/`U8`/`U16`/`U32`/`U64`/`BitVec` and every importer lose those names. |
| `lib/Sha.wiz` | Word.wiz:42 equations need a function type | `lib/Sha.wiz:36:1` unknown identifier U32 | real selfhost bug | Word.wiz fails at 42 (`Word.add_succ`), so `UIntN`/`U8`/`U16`/`U32`/`U64`/`BitVec` and every importer lose those names. |
| `lib/Word.wiz` | Word.wiz:42 equations need a function type | `lib/Word.wiz:42:1` equations need a function type | real selfhost bug | Word.wiz fails at 42 (`Word.add_succ`), so `UIntN`/`U8`/`U16`/`U32`/`U64`/`BitVec` and every importer lose those names. |
| `lib/WordMap.wiz` | Word.wiz:42 equations need a function type | `lib/WordMap.wiz:32:1` unknown identifier U64 | real selfhost bug | Word.wiz fails at 42 (`Word.add_succ`), so `UIntN`/`U8`/`U16`/`U32`/`U64`/`BitVec` and every importer lose those names. |
| `scry/gen/C/Schema.wiz` | Word.wiz:42 equations need a function type | `scry/gen/C/Schema.wiz:279:1` unknown identifier U16 | real selfhost bug | Word.wiz fails at 42 (`Word.add_succ`), so `UIntN`/`U8`/`U16`/`U32`/`U64`/`BitVec` and every importer lose those names. |
| `scry/src/Scry/CstStore.wiz` | Word.wiz:42 equations need a function type | `scry/src/Scry/CstStore.wiz:66:1` unknown identifier U64 | real selfhost bug | Word.wiz fails at 42 (`Word.add_succ`), so `UIntN`/`U8`/`U16`/`U32`/`U64`/`BitVec` and every importer lose those names. |
| `scry/tests/schema-index.wiz` | Word.wiz:42 equations need a function type | `scry/tests/schema-index.wiz:20:1` unknown identifier UIntN | real selfhost bug | Word.wiz fails at 42 (`Word.add_succ`), so `UIntN`/`U8`/`U16`/`U32`/`U64`/`BitVec` and every importer lose those names. |
| `lib/Scry/Egraph.wiz` | WordArray.wiz:50 List.length_snoc | `lib/Scry/Egraph.wiz:72:1` unknown identifier U64Array | real selfhost bug | U64Array is missing because WordArray.wiz fails at its length_snoc lemma. |
| `lib/Scry/EgraphExtract.wiz` | WordArray.wiz:50 List.length_snoc | `lib/Scry/EgraphExtract.wiz:107:1` unknown identifier Scry | real selfhost bug | Scry.EGraph is missing because WordArray.wiz fails at its length_snoc lemma. |
| `lib/Scry/EgraphNative.wiz` | WordArray.wiz:50 List.length_snoc | `lib/Scry/EgraphNative.wiz:243:1` unknown identifier U64Array | real selfhost bug | U64Array is missing because WordArray.wiz fails at its length_snoc lemma. |
| `lib/Scry/EqPlan.wiz` | WordArray.wiz:50 List.length_snoc | `lib/Scry/EqPlan.wiz:58:1` unknown identifier Scry.EGraph | real selfhost bug | Scry.EGraph is missing because WordArray.wiz fails at its length_snoc lemma. |
| `lib/WordArray.wiz` | WordArray.wiz:50 List.length_snoc | `lib/WordArray.wiz:50:1` type mismatch: expected Eq((((((((((((((?m0 A) x) l) i✝) xs✝) ih✝) rest✝) ihs✝) _) _) ih✝9) cur✝) xs), (((((((((((((?m2 A) x) l) i✝) xs✝) ih✝) rest✝)… | real selfhost bug | `List.length_snoc` type mismatch; U64Array/U32Array are then unknown to Egraph/Lower. |
| `scry/src/Scry/Lower.wiz` | WordArray.wiz:50 List.length_snoc | `scry/src/Scry/Lower.wiz:88:1` unknown identifier U32Array | real selfhost bug | U32Array is missing because WordArray.wiz fails at its length_snoc lemma. |
| `lib/Hdl/Xilinx7.wiz` | X7.spread equations need a function type | `lib/Hdl/Xilinx7.wiz:26:1` equations need a function type | real selfhost bug | Another `equations need a function type` (the same equation compiler bug as Word, on X7.spread). |
| `scry/tests/optics.wiz` | could not elaborate a constructor argument | `scry/tests/optics.wiz:19:1` could not elaborate a constructor argument | real selfhost bug | A `List`/`Scry.NodeId` constructor argument is rejected; the host accepts it. |
| `scry/tests/relations.wiz` | could not elaborate a constructor argument | `scry/tests/relations.wiz:15:1` could not elaborate a constructor argument | real selfhost bug | A `List`/`Scry.NodeId` constructor argument is rejected; the host accepts it. |
| `scry/src/Scry/Schema.wiz` | field projection a.n | `scry/src/Scry/Schema.wiz:173:1` unknown identifier a.n | real selfhost bug | `a.n` is unknown when projecting a structure field through a parameter named `a`. |
| `lib/Handle.wiz` | let (x,y) on IO/Owned pair | `lib/Handle.wiz:51:1` let (x, y) := ... expects a pair, got ((Prod ((Owned H) h)) World) | real selfhost bug | `let 1 (o, w') := …` is rejected (`expects a pair`) for the Prod/World pair produced by IO. |
| `lib/MVar.wiz` | let (x,y) on IO/Owned pair | `lib/MVar.wiz:66:1` let (x, y) := ... expects a pair, got ((Prod (x5 : (((((?m1 A) B) m) k) w)) × ((MVar.Hole (((((?m1 A) B) m) k) w)) m)) World) | real selfhost bug | `let 1 (o, w') := …` is rejected (`expects a pair`) for the Prod/World pair produced by IO. |
| `lib/Ref.wiz` | let (x,y) on IO/Owned pair | `lib/Ref.wiz:63:1` let (x, y) := ... expects a pair, got ((Prod (x5 : (Loc (((((?m1 V) B) v) k) w))) × (((Pts (((((?m1 V) B) v) k) w)) x5) v)) World) | real selfhost bug | `let 1 (o, w') := …` is rejected (`expects a pair`) for the Prod/World pair produced by IO. |
| `lib/Conc.wiz` | nested inductive occurrence | `lib/Conc.wiz:101:1` the type being defined may only occur as the type of a recursive field or the result | real selfhost bug | `the type being defined may only occur as the type of a recursive field or the result`; the host allows this nesting. |
| `lib/Hoare.wiz` | nested inductive occurrence | `lib/Hoare.wiz:53:1` the type being defined may only occur as the type of a recursive field or the result | real selfhost bug | `the type being defined may only occur as the type of a recursive field or the result`; the host allows this nesting. |
| `lib/Session.wiz` | nested inductive occurrence | `lib/Session.wiz:60:1` the type being defined may only occur as the type of a recursive field or the result | real selfhost bug | `the type being defined may only occur as the type of a recursive field or the result`; the host allows this nesting. |
| `lib/Scry/Optics.wiz` | not a function (optic composition) | `lib/Scry/Optics.wiz:118:1` not a function: its type is μmax(0, 0)(Unit0, arg(Enum1, λx6. case(Descmax(0, 0)(Unit0), x6, arg((x7 : ((((((?m0 x0) x1) x2) x3) x4) x5)) → ((((((?m2… | real selfhost bug | `Scry.Getter.comp_get` applies an optic whose type is not a function; elaboration of the composition is wrong. |
| `scry/src/Scry/Codegen.wiz` | recursive Scry.indexedFrom | `scry/src/Scry/Codegen.wiz:133:1` unknown identifier Scry | real selfhost bug | `def Scry.indexedFrom {A B} (f : …) : Nat → List A → List B` with two equation arguments: the recursive dotted name is not resolved. |
| `lib/Task.wiz` | rfl computed further | `lib/Task.wiz:94:1` rfl: the expected type is not an equation (it may have computed further): (x4 :0 Eq(((((?m0 A) B) f) g), (f tt), (f tt))) × Eq(((((?m1 A) B) f) g), c… | real selfhost bug | `Task.both_eq` rfl leaves a cast/transp redex; the host computes it away. |
| `lib/HoareTactics.wiz` | star✝3 / Hoare syntax | `lib/HoareTactics.wiz:37:1` unknown identifier star✝3 | real selfhost bug | The Hoare DSL binder is lost because Hoare.wiz fails; same inductive root. |
| `lib/Scry/AiCfg.wiz` | type class problem is stuck | `lib/Scry/AiCfg.wiz:261:1` type class problem is stuck: (((AbsDomain ((((((((?m1 C) inst✝) den) m) c) env) e) n)) ((((((((?m2 C) inst✝) den) m) c) env) e) n)) ((((((((?m3 C) in… | real selfhost bug | Instance search is stuck on `AbsDomain`/`Widen`; the host resolves them. |
| `lib/Scry/AiDomain.wiz` | type class problem is stuck | `lib/Scry/AiDomain.wiz:95:1` type class problem is stuck: ((Widen L) (((((?m8 L) inst✝) inst✝) a) b)) | real selfhost bug | Instance search is stuck on `AbsDomain`/`Widen`; the host resolves them. |
| `lib/Scry/EgraphWil.wiz` | 63-bit numeral (C13) | `lib/Scry/EgraphWil.wiz:61:1` the numeral does not fit in 63 bits (numbers are 63-bit words here) | expected divergence | 10^30/2·10^30 sentinels; the selfhost Nat is 63/64-bit (C13), the host is unbounded. |
| `scry/src/Scry/Budget.wiz` | Lean IO/Sys API (EIO/FS/Clock/ExitStatus/SpawnOptions) | `scry/src/Scry/Budget.wiz:41:1` unknown identifier Clock | expected divergence | Uses the lib/Sys process/FS/clock API; the selfhost deliberately lacks the File/Sys natives (C12) and its EIO.bind fails first. |
| `scry/src/Scry/Dynamic.wiz` | Lean IO/Sys API (EIO/FS/Clock/ExitStatus/SpawnOptions) | `scry/src/Scry/Dynamic.wiz:219:1` unknown identifier SpawnOptions | expected divergence | Uses the lib/Sys process/FS/clock API; the selfhost deliberately lacks the File/Sys natives (C12) and its EIO.bind fails first. |
| `scry/src/Scry/Repro.wiz` | Lean IO/Sys API (EIO/FS/Clock/ExitStatus/SpawnOptions) | `scry/src/Scry/Repro.wiz:94:1` unknown identifier ExitStatus | expected divergence | Uses the lib/Sys process/FS/clock API; the selfhost deliberately lacks the File/Sys natives (C12) and its EIO.bind fails first. |
| `scry/tests/cli.wiz` | Lean IO/Sys API (EIO/FS/Clock/ExitStatus/SpawnOptions) | `scry/tests/cli.wiz:13:1` unknown identifier EIO | expected divergence | Uses the lib/Sys process/FS/clock API; the selfhost deliberately lacks the File/Sys natives (C12) and its EIO.bind fails first. |
| `scry/tests/diff.wiz` | Lean IO/Sys API (EIO/FS/Clock/ExitStatus/SpawnOptions) | `scry/tests/diff.wiz:7:1` unknown identifier EIO | expected divergence | Uses the lib/Sys process/FS/clock API; the selfhost deliberately lacks the File/Sys natives (C12) and its EIO.bind fails first. |
| `scry/tests/dynamic.wiz` | Lean IO/Sys API (EIO/FS/Clock/ExitStatus/SpawnOptions) | `scry/tests/dynamic.wiz:7:1` unknown identifier EIO | expected divergence | Uses the lib/Sys process/FS/clock API; the selfhost deliberately lacks the File/Sys natives (C12) and its EIO.bind fails first. |
| `scry/tests/repl-prelude.wiz` | Lean IO/Sys API (EIO/FS/Clock/ExitStatus/SpawnOptions) | `scry/tests/repl-prelude.wiz:7:1` unknown identifier FS | expected divergence | Uses the lib/Sys process/FS/clock API; the selfhost deliberately lacks the File/Sys natives (C12) and its EIO.bind fails first. |
| `scry/tests/report-pure.wiz` | Lean IO/Sys API (EIO/FS/Clock/ExitStatus/SpawnOptions) | `scry/tests/report-pure.wiz:7:1` unknown identifier EIO | expected divergence | Uses the lib/Sys process/FS/clock API; the selfhost deliberately lacks the File/Sys natives (C12) and its EIO.bind fails first. |
| `scry/tests/sarif-id.wiz` | Lean IO/Sys API (EIO/FS/Clock/ExitStatus/SpawnOptions) | `scry/tests/sarif-id.wiz:8:1` unknown identifier EIO | expected divergence | Uses the lib/Sys process/FS/clock API; the selfhost deliberately lacks the File/Sys natives (C12) and its EIO.bind fails first. |
| `lib/Serial.wiz` | Sys/FFI API (EIO) | `lib/Serial.wiz:167:1` unknown identifier EIO | expected divergence | Uses `EIO`/`Fd` from lib/Sys; the selfhost has no File/Sys native surface (C12). |
| `lib/IO.wiz` | extern/native IO (World duplicate) | `lib/IO.wiz:34:1` 'World' has already been declared | expected divergence | `axiom World`; the selfhost embeds its own World/IO, so lib/IO collides. FFI boundary (C12). |
| `lib/Std.wiz` | extern/native Str/Array (Array duplicate) | `lib/Std.wiz:24:1` 'Array' has already been declared | expected divergence | `axiom Array`/`Str` natives; the selfhost embeds Array and implements only part of the Str surface (C12). |

## Bounded lane (31) — not part of the 169

The plan calls this the SIGSEGV lane, but this run is **not** SIGSEGV: 30 of 31 are
the **host** hitting the 60 s bound while the selfhost finishes the same file in
15–25 s; one (`lib/BitVecAdd.wiz`) is the selfhost running out of memory at ~83 s.
The host bound is too low for the large `scry/src/Scry/*` and `scry/tests/*` roots;
raising `--host-secs` (or running those roots with the selfhost only) would turn most
of this lane into real verdicts. `lib/BitVecAdd.wiz` is the one true crash.

| file | host | self | note |
|---|---|---|---|
| `lib/BitVecAdd.wiz` | ok 21s | crash 82s | self crash (wiz: out of memory) |
| `scry/App.wiz` | timeout 60s | ok 24s | host timeout |
| `scry/src/Scry/Bench.wiz` | timeout 60s | ok 16s | host timeout |
| `scry/src/Scry/BenchCmd.wiz` | timeout 60s | ok 16s | host timeout |
| `scry/src/Scry/Cli.wiz` | timeout 60s | ok 22s | host timeout |
| `scry/src/Scry/CsCmd.wiz` | timeout 60s | ok 15s | host timeout |
| `scry/src/Scry/DynamicCmd.wiz` | timeout 60s | ok 15s | host timeout |
| `scry/src/Scry/ProjectIO.wiz` | timeout 60s | ok 15s | host timeout |
| `scry/src/Scry/ProjectTaint.wiz` | timeout 60s | ok 15s | host timeout |
| `scry/src/Scry/Repl.wiz` | timeout 60s | ok 17s | host timeout |
| `scry/src/Scry/ReportCmd.wiz` | timeout 60s | ok 17s | host timeout |
| `scry/src/Scry/TaintCmd.wiz` | timeout 60s | ok 14s | host timeout |
| `scry/src/Scry/WorkflowCmd.wiz` | timeout 60s | ok 16s | host timeout |
| `scry/tests/bench.wiz` | timeout 60s | ok 16s | host timeout |
| `scry/tests/diff-cli.wiz` | timeout 60s | ok 15s | host timeout |
| `scry/tests/egraph-rewrite.wiz` | timeout 60s | ok 22s | host timeout |
| `scry/tests/egraph.wiz` | timeout 60s | ok 22s | host timeout |
| `scry/tests/oob.wiz` | timeout 60s | ok 14s | host timeout |
| `scry/tests/parse-stats.wiz` | timeout 60s | ok 22s | host timeout |
| `scry/tests/project.wiz` | timeout 60s | ok 15s | host timeout |
| `scry/tests/repl.wiz` | timeout 60s | ok 17s | host timeout |
| `scry/tests/report.wiz` | timeout 60s | ok 16s | host timeout |
| `scry/tests/scale.wiz` | timeout 60s | ok 14s | host timeout |
| `scry/tests/taint.wiz` | timeout 60s | ok 14s | host timeout |
| `scry/tests/uaf.wiz` | timeout 60s | ok 13s | host timeout |
| `scry/tests/workflow-e2e.wiz` | timeout 60s | ok 17s | host timeout |
| `scry/tests/workflow.wiz` | timeout 60s | ok 16s | host timeout |
| `scry/tools/CsCover.wiz` | timeout 60s | ok 11s | host timeout |
| `scry/tools/CsExternalsMain.wiz` | timeout 60s | ok 15s | host timeout |
| `scry/tools/CsTraceMain.wiz` | timeout 60s | ok 15s | host timeout |
| `scry/tools/ProverMain.wiz` | timeout 60s | ok 12s | host timeout |

## Both-reject and ok

Both-reject (8) and ok (1) are not gaps; the rejections are the same verdict from both
frontends (the error codes/spans/messages differ, which the harness counts separately).

| file | verdict | self first error |
|---|---|---|
| `scry/fixtures/ReplPrelude.wiz` | ok | `scry/fixtures/ReplPrelude.wiz:0:0`  |
| `scry/src/Scry/Fuzz.wiz` | rejected | `scry/src/Scry/Fuzz.wiz:69:1` unknown identifier Scry.CstStore |
| `scry/src/Scry/FuzzCmd.wiz` | rejected | `scry/src/Scry/FuzzCmd.wiz:30:1` type mismatch: expected (List ((((((((((((((((((((((((((((?m11 o) x✝0) j✝) i✝) xs✝) ih✝) rest✝) ihs✝) _) _) a) rest) x✝) x✝) j✝) i✝) xs✝) ih✝) rest✝)… |
| `scry/src/Scry/Native.wiz` | rejected | `scry/src/Scry/Native.wiz:98:1` unknown identifier U32Array |
| `scry/src/Scry/Parse.wiz` | rejected | `scry/src/Scry/Parse.wiz:34:1` type mismatch: expected (List ?m0), got String |
| `scry/tests/fuzz.wiz` | rejected | `scry/tests/fuzz.wiz:12:1` unknown identifier EIO |
| `scry/tests/native.wiz` | rejected | `scry/tests/native.wiz:14:1` type mismatch: expected (List ((((((((((?m2 label) got) want) x✝) j✝) i✝) xs✝) ih✝) rest✝) ihs✝)), got String |
| `scry/tests/preproc.wiz` | rejected | `scry/tests/preproc.wiz:24:1` type mismatch: expected (List ((((((((((?m0 label) got) want) x✝) j✝) i✝) xs✝) ih✝) rest✝) ihs✝)), got String |
| `scry/tools/CstMain.wiz` | rejected | `scry/tools/CstMain.wiz:30:1` unknown identifier EIO |

## Reproduce / regenerate

`scripts/libdiff-classify.py` reads the same `records-*.jsonl` and the cause table
`scripts/libdiff-causes.tsv`, and writes this file. It is a pure function of the run
log: a new sweep only needs the new records directory (and a line for a new file type).

```sh
# produce the report (the four-part sweeps write .lake/libdiff/records-*.jsonl)
lake test -- '=selfhost-libdiff'
# classify it
python3 scripts/libdiff-classify.py --records-dir .lake/libdiff -o /tmp/libdiff.md
```

## Caveats

* The report is the **209-file** corpus on `libdiff-corpus`; train9's corpus is **225**
  files (16 modules added by the Loom/HDL/Scry/notations merges after that run). The 16
  are not in this table; a train9 rerun flags them as `unknown` until rows are added.
* The self-hosted compiler binary used for the report is the 20:16 build; running it
  with a stale default cache can move diagnostics to `1:1 unknown identifier outParam`.
  The classification uses the report's records, not a fresh cache.
* A "first error" is often a cascade (e.g. `unknown U64` because `Word` failed). The
  `why` and `root cause` columns give the cause the file should be queued under.

