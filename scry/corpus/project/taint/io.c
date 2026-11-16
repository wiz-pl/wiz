#include "io.h"

/* Cross-TU sink: app.c passes getenv's result here. */
void run_cmd(char *cmd) {
  system(cmd);
}

/* Same body, but app.c sanitises before calling it: no finding. */
void safe_cmd(char *cmd) {
  system(cmd);
}

/* A TU-local helper with the same source name as app.c's helper. */
static int helper(int x) {
  return x + 1;
}

int io_helper(int x) {
  return helper(x);
}
