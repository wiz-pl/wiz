/* CWE-787: a read length taken from attacker data fills a fixed 16-byte buffer. The
   read call writes argument 1; its count is argument 2 and is never bounded. */
long read(int fd, void *buf, unsigned long count);
char *getenv(const char *name);

int main(void) {
  char *arg = getenv("LEN");
  unsigned long n = arg[0];
  char buf[16];

  read(0, buf, n);
  return buf[0];
}
