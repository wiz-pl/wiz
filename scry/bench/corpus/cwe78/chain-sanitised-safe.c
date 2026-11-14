/* CWE-78: the sanitiser result is passed through a direct call. */
char *getenv(const char *name);
char *escape_shell(char *s);
int system(const char *command);

void run(char *cmd) {
  system(cmd);
  return;
}

int main(void) {
  char *cmd = getenv(0);
  char *clean = escape_shell(cmd);
  run(clean);
  return 0;
}
