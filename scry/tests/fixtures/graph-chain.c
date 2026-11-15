/* graph fixture: a call chain and a taint path, plus a quoted C string */
char *getenv(const char *name);
int system(const char *command);

void sink(char *cmd) {
  system(cmd);
  return;
}

void pass(char *cmd) {
  sink(cmd);
  return;
}

int main(void) {
  char *cmd = getenv(0);
  pass(cmd);
  system("echo \"hi\"");
  return 0;
}
