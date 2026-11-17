/* CWE-787 control: the length is capped at the destination size by the trusted
   `clamp_len` policy model before it reaches read. The taint kill and the capacity are
   both needed; here the cap supplies both. */
long read(int fd, void *buf, unsigned long count);
char *getenv(const char *name);
unsigned long clamp_len(unsigned long n, unsigned long cap);

int main(void) {
  char *arg = getenv("LEN");
  unsigned long n = arg[0];
  char buf[16];

  n = clamp_len(n, 16);
  read(0, buf, n);
  return buf[0];
}
