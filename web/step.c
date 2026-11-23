/* The browser's i32 word entry for a Loom runtime: `wiz-web/1`'s
   `wiz_step : (state : i32, payload_ptr : i32, payload_len : i32) -> i32`.
   (A lane note calls this "sota-web-wasm-gpu R1"; the ABI table is in
   docs/stages/08-backend/wasm.md, "wiz-web/1".)

   Why a second entry. The app's own export, `wiz_loom_step (state, payload) -> state`
   (`export "wiz_loom_step" loomStep` in each `web/<page>-ui.wiz`), marshals the Wiz value as the C
   ABI's 64-bit word. The JavaScript WebAssembly API has no `Number` path for an `i64`
   parameter or result: every one is a `BigInt`, so a DOM event pays a BigInt for the
   state in and another for the state out — for an opaque handle that is a 32-bit
   pointer into a < 4 GiB memory. This shim is that truncation: three `i32` words in,
   one out, no BigInt. The i64 entry stays (the Node tests drive it, and a host that
   would rather pass a Wiz value can).

   The words are the low 32 bits of the same handle, deliberately read as *unsigned*
   and written back through `uint32_t`, so a handle above `0x7FFFFFFF` survives the
   round trip (the JS side must normalise the result the same way: `>>> 0`, because a
   Wasm `i32` result arrives in JavaScript sign-extended).

   The payload. `payload` is UTF-8 at that address and `len` is its byte length. The
   host must make `payload[len]` readable: when that byte is NUL (the usual case — the
   host allocates the string with `stringToNewUTF8`) the runtime's own NUL-terminated
   conversion is used and nothing is copied; otherwise the shim makes a terminated copy
   of exactly `len` bytes, so a slice of a larger buffer is stepped at `len`, not at the
   next NUL further on. `len < 0` means "not supplied": the buffer is then read to its
   NUL, and `payload[len]` is not touched. (A `String` with an embedded U+0000 is not
   expressible through a C string; that is the C boundary's rule, unchanged by this
   entry.)

   Ownership is inherited unchanged from `wiz_loom_step`: the state is consumed, the
   returned state is owned by the caller, and the payload buffer stays the host's (the
   host frees it after the call).

   This file is linked by the page runtimes that export `wiz_loom_step`
   (`link_c "step.c"` beside `link_c "js.c"` in each `web/<page>-ui.wiz`), not by
   web/Web.wiz. */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#ifndef WIZ_VAL_DEFINED
#define WIZ_VAL_DEFINED
/* the ABI's word, as runtime/wiz_rt.h and `wiz build --lib`'s generated header spell it
   (this file is its own translation unit, so it cannot see either) */
typedef uintptr_t wiz_val;
#endif

/* The app's i64 entry (`export "wiz_loom_step" loomStep`), with the C signature
   `Wiz/Compiler/C.lean`'s export wrapper emits: kind `w` (a Wiz value) and kind `s`
   (a UTF-8 C string, borrowed for the call). */
extern wiz_val wiz_loom_step(wiz_val state, const char *payload);

int32_t wiz_step(int32_t state, int32_t payload, int32_t len) {
  const char *text = (const char *)(uintptr_t)(uint32_t)payload;
  wiz_val next;
  if (!text) {
    /* no payload at all: the empty event string, not a trap in the shim */
    next = wiz_loom_step((wiz_val)(uint32_t)state, "");
  } else if (len < 0 || text[len] == 0) {
    next = wiz_loom_step((wiz_val)(uint32_t)state, text);
  } else {
    char *copy = (char *)malloc((size_t)len + 1);
    if (!copy) return state;   /* out of memory: no step, the state is unchanged */
    memcpy(copy, text, (size_t)len);
    copy[len] = 0;
    next = wiz_loom_step((wiz_val)(uint32_t)state, copy);
    free(copy);
  }
  return (int32_t)(uint32_t)(uintptr_t)next;
}
