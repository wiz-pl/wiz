/* CWE-78: the two conditions are mutually exclusive, so the source cannot
   reach the sink. A path-insensitive may analysis reports a false positive
   here; this case measures that known precision cost. */
char *getenv(const char *name);
int system(const char *command);

int main(int argc, char **argv) {
  char *cmd = 0;
  if (argc > 0) {
    cmd = getenv(0);
  }
  if (argc <= 0) {
    system(cmd);
  }
  return 0;
}
