/* CWE-78: the source is in the loop body; the only path to the sink is the
   back edge. */
char *getenv(const char *name);
int system(const char *command);

int main(int argc, char **argv) {
  char *cmd = 0;
  while (argc > 0) {
    cmd = getenv(0);
    argc = 0;
  }
  system(cmd);
  return 0;
}
