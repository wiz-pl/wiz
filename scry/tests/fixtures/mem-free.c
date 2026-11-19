/* use after free: the object is freed and then read. The finding is still reported
   (conservative) and a use-after-free warning points at the offending load. */
int getenv(const char *name);
int system(int command);
int *malloc(int size);
void free(int *p);

int main(void) {
  int *p = malloc(4);
  *p = getenv(0);
  free(p);
  system(*p);
  return 0;
}
