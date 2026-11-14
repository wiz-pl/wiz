/* CWE-78: argument taint crosses a direct call into run's sink. */
char *getenv(const char *name);
int system(const char *command);

void run(char *cmd) {
  system(cmd);
  return;
}

int main(void) {
  char *cmd = getenv(0);
  run(cmd);
  return 0;
}
