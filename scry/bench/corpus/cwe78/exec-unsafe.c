/* CWE-78: the exec* family is a command sink in the expanded pack. */
char *getenv(const char *name);
int execl(const char *path, const char *arg);

int main(void) {
  char *cmd = getenv(0);
  execl(cmd, cmd);
  return 0;
}
