/* emit/one.c: one command-injection finding, used as the baseline fixture */
char *getenv(const char *name);
int system(const char *command);

int main(void) {
  char *cmd = getenv(0);
  system(cmd);
  return 0;
}
