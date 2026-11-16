/* external model: a bounded strncpy is still a copy, but no source reaches it and no
   forbidden rule lists it. */
int strncpy(char *dst, const char *src, unsigned long n);
int main(void) {
  char buf[64];
  strncpy(buf, "constant", 63);
  return 0;
}
