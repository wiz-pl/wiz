# An eBPF target — P0 (typed core, checker, C emitter skeleton)

**Status, 2026-11-22:** P0 implementation in progress. The typed core, checker and C
emitter skeleton are implemented, and their pure test group is green. The post-`clang`
object checks and the kernel verifier remain; they need a clang and/or privileged slot.
The design is `wiz-notes/ebpf-target.md`; this file records what the P0 cut contains and
what the remaining verifier run has to establish.

`wiz build FLOW.toml -o flow.c --target bpf` writes `flow.c` and `bpf_rt.h`. It does not
call `clang` (see "needs a queue slot"). `--target bpf` is a normal entry in the selector
list; the CLI branch in `Main.lean` is the one per-backend branch the note allows, because
the input is not the untyped IR.

## The boundary

The target is **verifier-shaped by construction**, not "Wiz on eBPF":

| file | what it is |
|---|---|
| `Wiz/Compiler/Bpf/Core.lean` | `BpfCore`: the typed, flat, first-order IR of §4.1-§4.2. Every term carries a `Ty`; a `Span`; no pointer, closure, array, `String`, `Nat` or heap object. |
| `Wiz/Compiler/Bpf/Check.lean` | the gate: type/storage/POD/map/call-graph/frame/instruction checks and the stable `bpf:` messages of §4.4. Pure, so it belongs in `wiz check`. |
| `Wiz/Compiler/Bpf/Lower.lean` | the typed-surface → `BpfCore` erasure. Widths are literals; `Nat` is compile-time only; the §2.6 edge cases are rejected here. |
| `Wiz/Compiler/Bpf/Sexp.lean` | `bpf-core/1`, the serialised typed core the P0 CLI consumes. A fixture format, not yet the public §9.4 schema. |
| `Wiz/Compiler/Bpf/C.lean` | the flat-C emitter: `SEC`, BTF map declarations, `static __always_inline` functions, `#line`, checked packet accessors, copy-out map lookups, `Map.add` as lookup + `XADD`. |
| `Wiz/Compiler/Bpf.lean` | the manifest reader (`bpf.toml`, §5.1) and `buildCmd`. |
| `Tests/fixtures/bpf/` | the IPv4 allow-list fixture (`allow.toml` + `allow.bpfcore`) and the source-level reject/accept corpus. |
| `Tests/Groups/Bpf.lean` | pure rejection/value tests. **Green, 22/22.** |

Implemented in P0:

* `UIntN 8/16/32/64`, `IntN 8/16/32/64` **without signed `/` and `%`**, `Bool`, nullary
  enums, flat structs (≤ 64 B), `Option` of those, `unit`;
* `add sub mul and or xor`, unsigned `div/mod` (the ISA and Wiz agree at zero), shifts
  with a literal amount below the width, `UIntN.resize`, `==/!=/< /<=` (signed by the
  operand type, i.e. sign-bit/`__sN` comparison);
* `let` (with a mandatory type), `proj`, struct construction, `some`/`none`,
  `if`, `match` on `Option`, exhaustive enum switch;
* `Packet.load8/16/32/64`, `be`/`le`, each with its `data`/`data_end` check in the same
  inline function; `XdpContext.packet/ingressIfindex/rxQueue`;
* `Map.lookup/update/delete/add`, declared statically (hash, array, percpu_array,
  lru_hash), scalar keys/values in the manifest (struct keys are P2/BTF);
* `Bpf.now` (helper 5) and `Bpf.random` (helper 7); helper calls are typed by the table;
* the XDP/TC context layouts that matter (`xdp_md`; `__sk_buff`'s `data`/`data_end` at
  76/80) with **no CO-RE and no `vmlinux.h`**.

Rejected with an explicit `bpf:` message (the negative corpus):

* `Nat` as a runtime value (a literal that folds is accepted as an offset);
* `String`, `Bytes`, `List`, `Array`, `Ref`, `Task`, `Float64`, `IO`, closures;
* `UIntN`/`IntN`/`BitVec` at a width outside `{8,16,32,64}`;
* signed `/` and `%` (the message names `INT_MIN / -1`);
* a shift amount that is not a literal below the width (the ISA's 63/31 mask is not
  Wiz's `k >= w = 0` rule);
* `partial`, a cyclic call graph, `Bpf.repeat` (P0 has no loops), a loop bound from data;
* a non-POD map key/value, a key > 64 B, a value > 512 B, an `array` key that is not
  `u32`, `max_entries = 0`;
* a non-action result, a non-context entry parameter, a section/type mismatch;
* a value > 64 B, an estimated frame > 256 B, an estimated program > 100k instructions;
* a literal that does not fit its width (not silently wrapped).

Not in P0 (do not mistake the skeleton for them):

* the **elaborator → `STm` adapter**. This is the load-bearing missing piece: the IR is
  untyped, and the restriction pass needs the elaborated term's types and spans. The
  surface `STm` and the erasure are written; the adapter is a roadblock, not a guess.
* `clang -target bpf`, the ELF reader/relocator, the ubpf harness, the `BPF_HOSTED` map
  implementation (the header has the shape, not the tables);
* loops (`Bpf.repeat`), enums with a default arm, TC actions beyond the enum arity,
  packet writes, `XDP_TX`/redirect, tail calls, tracing/CO-RE;
* the privileged verifier CI and a pinned-kernel matrix.

## What the first build must establish

1. **Done (2026-11-22).** `lake build wiz tests` compiles all of `Wiz/Compiler/Bpf/*`,
   `Wiz/Compiler/Bpf.lean`, `Main.lean` and `Tests/Groups/Bpf.lean` (590 jobs).
2. **Done (2026-11-22).** `lake test -- '=bpf'` passes 22/22. Every case is pure and
   unprivileged; the fixture case is the whole path manifest → reader → checker → C text.
3. `wiz build Tests/fixtures/bpf/allow.toml -o /tmp/allow.c --target bpf` exits 0 and
   writes `/tmp/allow.c` + `/tmp/allow.h` (`bpf_rt.h` beside it). **Pending**: the same
   pipeline is exercised in-process by the fixture case; the CLI path has not run yet.
4. `clang -target bpfel -mcpu=v2 -O2 -g -ffreestanding -fno-builtin
   -fno-stack-protector -fno-asynchronous-unwind-tables -nostdlibinc -Wall -Werror
   -c /tmp/allow.c -o /tmp/allow.o` succeeds. The expected object shape: `.text`, `.maps`,
   `.BTF`/`.BTF.ext`, only the two map helpers (plus `ktime`/`prandom` if used) as
   relocations, no undefined symbol, no `memcpy`/`memset`, no `__stack_chk_fail`.
5. `llvm-objdump -S /tmp/allow.o` interleaves `allow.wiz` lines (the `#line` check) and
   every packet access is preceded by the two range checks in the same block.
6. `bpftool btf dump file /tmp/allow.o` shows the key/value types and the map sizes.

## What the kernel verifier must check

The verifier is the authority; these assertions are the P0 exit (§8.4, §8.8):

* `bpftool prog load /tmp/allow.o /sys/fs/bpf/allow type xdp log_level 1
  log_buf /tmp/verifier.log` exits 0 on **each pinned LTS kernel** (6.1, 6.6, 6.12), and
  the log is kept as an artefact;
* the log's `processed N insns` is parsed and compared with a per-program budget
  (P0's static estimate is 100k; the measured number is the regression signal);
* `bpftool prog run pinned /sys/fs/bpf/allow data_in pkt.bin data_out out.bin repeat 1`
  returns the same action as the three non-kernel oracles (core interpreter, hosted C,
  ubpf) for the boundary packet corpus: `len < 34`, a non-IPv4 EtherType, an allow-list
  hit, a miss, offset 0, `len-4`, `len-3`, zero length, 64 KiB, a VLAN tag, IPv4 options;
* `bpftool map dump`/`map show` on the maps created from BTF: `allow` is a 4-byte-key,
  1-byte-value hash with 4096 entries; `hits` is a 4-byte-key, 8-byte-value per-CPU
  array with 256 entries; the hit counter's value is compared after the run, not only
  the action;
* the verifier **negative** corpus is rejected with the recorded log fragment:
  `no-bounds-check.c` (`invalid access to packet`), `unbounded-loop.c`
  (`loop is not bounded`), `lookup-no-null.c` (`map_value_or_null`),
  `pointer-in-map.c` (`leaking pointer`), `big-stack.c` (`stack limit exceeded`),
  `uninit-stack.c` (`invalid read from stack`), `recursion.c`
  (`Unsupported recursion`), `raw-user-deref.c` (`access to user memory`); the positive
  neighbours (`bounds-check.c`, `bounded-loop-masked.c`) must be accepted;
* the P0 counterexample: hand-written C that reads `*(__u16 *)(data + 12)` with no check
  is rejected. This is what proves that ubpf's acceptance is a value claim, not safety.

The negative C fixtures are not written yet: they are P0's post-emission half and belong
with the clang/loader work.

## Roadblocks that need a queue slot

1. **The elaborator adapter** (`Term R` with types and spans → `STm`). Without it the
   CLI cannot take a `.wiz` file, and the source-level `.wiz` reject fixtures in
   `Tests/fixtures/bpf/reject/` can only be checked by inspection. This is the largest
   P0 item after the emitter.
2. **The build and the test group.** Nothing here has been elaborated by Lean; the
   unrun marker in `Tests/Groups/Bpf.lean` is deliberate.
3. **`clang -target bpf` and the post-`clang` checks.** The emitter is a text printer;
   the stack/symbol/relocation/instruction checks need the object, so they cannot be
   written against the C text alone.
4. **The hosted (`BPF_HOSTED`) oracle and the ubpf harness.** The header has the
   interface shape; the map tables, packet buffer and helper callbacks are P0's next
   code, not written here.
5. **The privileged verifier runner.** The long pole (§8.5): a self-hosted VM or
   `virtme-ng` with a pinned kernel; GitHub-hosted runners must be a **probe** with the
   `skip-allowlist.json` reason, not a hard requirement.
6. **`lib/Bpf.wiz` and the ledger.** The surface library (`BpfM`, `Packet`, `Map`,
   `Bpf.repeat`) and its one-row-per-helper trust-ledger change are not in this branch:
   they need the elaborator and a review of `.github/trust-baseline.tsv`, which this lane
   did not touch.

## Known unverified assumptions

The Lean-level assumptions are now confirmed by the build: recursive `BEq`/`Inhabited`,
the `s!"…\{…\}"` escaping, the `mutual`/`partial` parsers, the `StateT` emitter, and
`Tm.ty` for `let` (the node carries the *binder* type; the term's type is the body's).

Still unverified until the `clang`/verifier slot:

* the C's `__sync_fetch_and_add` on a per-CPU map value, and whether `-Wall -Werror`
  accepts the helper-pointer idiom with `(void *)N`;
* the BTF macro forms for an anonymous map struct whose key/value are typedefs;
* the object's stack/symbol/relocation shape and the kernel verifier's acceptance.
