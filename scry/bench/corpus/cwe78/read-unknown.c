/* CWE-78: read writes through a buffer. The register/def-use engine does not
   model the array, so this is a known coverage gap (expect: unknown). */
long read(int fd, void *buf, unsigned long count);
int system(const char *command);

int main(void) {
  char buf[64];
  read(0, buf, 63);
  system(buf);
  return 0;
}
