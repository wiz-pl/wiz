/* command injection: getenv result reaches system */
char *getenv(const char *name);
int system(const char *command);

int main(void) {
  char *cmd = getenv(0);
  system(cmd);
  system(cmd);
  return 0;
}
