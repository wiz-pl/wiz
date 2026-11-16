/* moved: the sink moves from run into main */
char *getenv(const char *name);
int system(const char *command);

void run(char *cmd) {
  (void)cmd;
}

int main(void) {
  char *cmd = getenv(0);
  system(cmd);
  return 0;
}
