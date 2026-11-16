/* interprocedural: main passes tainted data to run's sink */
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
