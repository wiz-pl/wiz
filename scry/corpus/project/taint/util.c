#include "io.h"

/* A second file with its own direct finding. */
void util_unsafe(void) {
  char *c = getenv("UTIL");
  system(c);
}
