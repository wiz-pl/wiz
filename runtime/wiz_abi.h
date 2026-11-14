/* The Wiz value representation's compile-time parameters (stage 8b).

   A `wiz_val` is one machine word (`uintptr_t`). Its lowest bit tells a tagged
   **scalar** (a small number, a tag, or ◾) from a pointer to an **object**. The scalar
   range therefore depends on the pointer width:

   * 64-bit word: 62 value bits, `WIZ_MAX_SMALL` = 2^62 - 1 (the representation on
     every supported platform; do not change it);
   * 32-bit word: 30 value bits, `WIZ_MAX_SMALL` = 2^30 - 1.

   Both keep two bits of headroom below the word width: one for the tag, and one so that
   `WIZ_MAX_SMALL + WIZ_MAX_SMALL` and `WIZ_MAX_SMALL << 1 | 1` still fit in the word
   (the runtime's small-number fast paths rely on that).

   A target with any other pointer width is a **compile-time error**: it must not
   silently take the 64-bit (62-bit scalar) path with a narrower word.
   `scripts/test-runtime.sh` checks both selections (and the error) with
   `-DWIZ_ABI_TEST_WORD_BITS=32|64|16`, and with a real `-m32` compile when the
   toolchain has one.

   `runtime/wiz_rt.h` includes this header when the runtime is compiled as a
   translation unit; `runtime/WizRuntime.lean` embeds its text at the top of every
   generated C file (the generated program is standalone, so it cannot `#include` it).
   The split build's prelude (`Wiz/Compiler/C.lean`, `splitPrelude`) uses the same
   embedded text, so the two cannot drift. */

#ifndef WIZ_ABI_H
#define WIZ_ABI_H

/* `stdint.h` below is the first system header; define the feature-test macro before it
   (the runtime's POSIX interfaces need it, and glibc remembers the first definition). */
#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif
#include <stdint.h>
#include <stddef.h>

/* The width of a value. `WIZ_ABI_TEST_WORD_BITS` is a test seam: it lets the 32-bit
   selection be compiled on a 64-bit host, where `-m32` is not installed. */
#ifdef WIZ_ABI_TEST_WORD_BITS
#define WIZ_WORD_BITS WIZ_ABI_TEST_WORD_BITS
#elif UINTPTR_MAX == 0xFFFFFFFFu
#define WIZ_WORD_BITS 32
#elif UINTPTR_MAX == 0xFFFFFFFFFFFFFFFFu
#define WIZ_WORD_BITS 64
#else
#error "wiz: unsupported pointer width (the value representation needs a 32- or 64-bit word)"
#endif

#if WIZ_WORD_BITS == 64
#define WIZ_SMALL_BITS 62
#elif WIZ_WORD_BITS == 32
#define WIZ_SMALL_BITS 30
#else
#error "wiz: unsupported pointer width (the value representation needs a 32- or 64-bit word)"
#endif

typedef uintptr_t wiz_val;

/* the largest Nat kept in a scalar; anything above is a GMP object */
#define WIZ_MAX_SMALL ((((uintptr_t)1) << WIZ_SMALL_BITS) - 1)

#define WIZ_IS_SCALAR(v) ((v) & 1)
#define WIZ_UNBOX(v) ((v) >> 1)
#if WIZ_WORD_BITS == 64
/* The value representation is unchanged on 64-bit. */
#define WIZ_BOX(n) ((((wiz_val)(n)) << 1) | 1)
#else
/* On 32-bit a literal (or a computed value) can be above `WIZ_MAX_SMALL` while still
   below 2^62, where `C.lean` emits `WIZ_BOX`. A checked box turns that into a GMP
   number instead of a truncated scalar: `wiz_box_checked` is defined in `rt_core.inc`
   and declared in `wiz_rt.h`'s embedder section. */
#define WIZ_BOX(n) wiz_box_checked((uint64_t)(n))
#endif

_Static_assert(sizeof(uintptr_t) == sizeof(void *),
               "wiz: uintptr_t is not pointer-sized");
/* the tag is the low bit: an object pointer must have it clear */
_Static_assert(_Alignof(max_align_t) >= 2,
               "wiz: object addresses must be at least 2-byte aligned for the tag bit");
#ifndef WIZ_ABI_TEST_WORD_BITS
_Static_assert((size_t)WIZ_WORD_BITS == 8 * sizeof(uintptr_t),
               "wiz: the selected word width disagrees with uintptr_t");
#endif
_Static_assert(WIZ_SMALL_BITS == WIZ_WORD_BITS - 2,
               "wiz: small ints keep two bits of headroom (tag and the tagged shift)");
_Static_assert(WIZ_MAX_SMALL <= ((((uintptr_t)1) << (WIZ_WORD_BITS - 1)) - 1),
               "wiz: a small int does not fit in a tagged word");

#endif /* WIZ_ABI_H */
