/* CWE-22 with argv as the source: the shell/exec caller controls `argv[1]`. */
int open(const char *path, int flags);

int main(int argc, char **argv) {
  (void)argc;
  return open(argv[1], 0);
}
