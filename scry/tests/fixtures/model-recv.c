/* external model: recv writes the buffer in argument 1, not its result. */
long recv(int fd, void *buf, unsigned long len, int flags);
int system(const char *command);
int main(void) {
  char buf[64];
  recv(0, buf, 63, 0);
  system(buf);
  return 0;
}
