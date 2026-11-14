/* external model: memcpy writes its source's contents into the destination object, so
   buf becomes tainted while a different array stays clean */
int *getenv(const char *name);
int system(int command);
void *memcpy(void *dst, const void *src, int n);

int main(void) {
  int buf[8];
  int other[8];
  int *t = getenv(0);
  memcpy(buf, t, 4);
  system(buf[0]);
  system(other[0]);
  return 0;
}
