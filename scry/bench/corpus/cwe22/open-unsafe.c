/* CWE-22: a second path sink, open(2), is in the same rule. */
char *getenv(const char *name);
int open(const char *path, int flags);

int main(void) {
  char *path = getenv(0);
  int fd = open(path, 0);
  return fd;
}
