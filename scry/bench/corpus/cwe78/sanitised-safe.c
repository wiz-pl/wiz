/* CWE-78: the result sanitiser kills the flow before the sink. */
char *getenv(const char *name);
char *escape_shell(char *s);
int system(const char *command);

int main(void) {
  char *cmd = getenv(0);
  char *clean = escape_shell(cmd);
  system(clean);
  return 0;
}
