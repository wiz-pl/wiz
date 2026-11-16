/* CWE-78: the same call chain with a constant argument. */
int system(const char *command);

void run(char *cmd) {
  system(cmd);
  return;
}

int main(void) {
  char *cmd = 0;
  run(cmd);
  return 0;
}
