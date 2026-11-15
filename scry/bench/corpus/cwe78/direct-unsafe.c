/* CWE-78: the result of getenv reaches the command interpreter. */
char *getenv(const char *name);
int system(const char *command);

int main(void) {
  char *cmd = getenv(0);
  system(cmd);
  return 0;
}
