/* CWE-22 fixed: both the raw input and the output buffer are attacker-controlled, but
   realpath rewrites the output buffer with the canonical path, and open uses that. */
int read(int fd, void *buf, unsigned long count);
int open(const char *path, int flags);
char *realpath(const char *path, char *resolved);

int main(void) {
  char name[256];
  char safe[256];
  read(0, name, 255);
  read(0, safe, 255);
  realpath(name, safe);
  return open(safe, 0);
}
