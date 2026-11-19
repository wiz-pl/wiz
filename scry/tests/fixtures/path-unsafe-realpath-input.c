/* CWE-22 still vulnerable: realpath canonicalises `safe`, but the sink uses the raw
   input `name`, so the sanitiser did not launder the value that reaches open. */
int read(int fd, void *buf, unsigned long count);
int open(const char *path, int flags);
char *realpath(const char *path, char *resolved);

int main(void) {
  char name[256];
  char safe[256];
  read(0, name, 255);
  realpath(name, safe);
  return open(name, 0);
}
