/* CWE-22: a request body read into a buffer reaches a filesystem path API. */
int read(int fd, void *buf, unsigned long count);
int open(const char *path, int flags);

int main(void) {
  char name[256];
  read(0, name, 255);
  return open(name, 0);
}
