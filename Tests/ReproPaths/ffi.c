/* The C shim for ffi.wiz (`link_c "ffi.c"`). */
#include <stdint.h>

uint64_t repro_add(uint64_t a, uint64_t b) { return a + b; }
uint64_t repro_len(const char *s) { uint64_t n = 0; while (s[n]) n++; return n; }
