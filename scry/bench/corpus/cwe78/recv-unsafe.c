/* CWE-78: the recv result is a source; it reaches system. */
char *recv(int fd, void *buf, unsigned long len, int flags);
int system(const char *command);

int main(void) {
  char *buf = recv(0, 0, 0, 0);
  system(buf);
  return 0;
}
