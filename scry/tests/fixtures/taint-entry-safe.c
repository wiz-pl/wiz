/* not every parameter is a source: `run` is called inside the unit with a constant, the
   unused `run_static` has internal linkage, and `callback`'s address is taken for
   `qsort`, so none is an exported entry. Only an external-linkage function with no
   caller in the unit and no address taken is. */
int system(const char *command);
void qsort(void *base, int n, int size, void (*cmp)(const char *));

void run(const char *cmd) {
  system(cmd);
  return;
}

static void run_static(const char *cmd) {
  system(cmd);
  return;
}

void callback(const char *cmd) {
  system(cmd);
  return;
}

int main(void) {
  qsort(0, 0, 0, callback);
  run("echo safe");
  return 0;
}
