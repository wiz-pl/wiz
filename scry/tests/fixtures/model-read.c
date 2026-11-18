/* external model: read writes the buffer in argument 1; the length is argument 2. */
long read(int fd, void *buf, unsigned long count);
int system(const char *command);
int main(void) {
  char buf[64];
  read(0, buf, 63);
  system(buf);
  return 0;
}
