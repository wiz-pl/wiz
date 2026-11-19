/* CWE-22 fixed: realpath's result (not the input) is what reaches the sink. */
int read(int fd, void *buf, unsigned long count);
int open(const char *path, int flags);
char *realpath(const char *path, char *resolved);

int main(void) {
  char name[256];
  read(0, name, 255);
  char *safe = realpath(name, 0);
  return open(safe, 0);
}
