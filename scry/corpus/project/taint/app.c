#include "io.h"

/* Distinct from io.c's static helper; the project must not merge them. */
static int helper(int x) {
  return x + 2;
}

int main(void) {
  char *cmd = getenv("CMD");
  run_cmd(cmd);                 /* TP: sink in io.c */
  safe_cmd(escape_shell(cmd));  /* TN: sanitised */
  maybe();                      /* unresolved external */
  return helper(1) - 1;
}
