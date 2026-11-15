/* buffer content: a copy from a clean value into the same buffer leaves the content
   clean, so a sink on the pointer is silent. */
void *memcpy(void *dst, const void *src, unsigned long n);
int system(const char *command);
int main(void) {
  char buf[64];
  memcpy(buf, "constant", 8);
  system(buf);
  return 0;
}
