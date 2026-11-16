/* CWE-78: escaping a copy does not clean the original value. */
char *getenv(const char *name);
char *escape_shell(char *s);
int system(const char *command);

int main(void) {
  char *cmd = getenv(0);
  char *clean = escape_shell(cmd);
  system(cmd);
  return 0;
}
