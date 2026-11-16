/* CWE-78: two sinks, both on the same tainted value. */
char *getenv(const char *name);
int system(const char *command);

int main(void) {
  char *cmd = getenv(0);
  system(cmd);
  system(cmd);
  return 0;
}
