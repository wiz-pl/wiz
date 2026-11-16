/* heap object flow: malloc's object is written through a pointer and read back, then
   freed after the last use (no use-after-free) */
int getenv(const char *name);
int system(int command);
int *malloc(int size);
void free(int *p);

int main(void) {
  int *p = malloc(4);
  *p = getenv(0);
  system(*p);
  free(p);
  return 0;
}
