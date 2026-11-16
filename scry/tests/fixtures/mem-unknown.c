/* an unmodelled external returns a pointer the analysis cannot bound: the store and the
   load through it are memory-unknown. The taint still propagates (a may analysis) and the
   two accesses are warned about. */
int getenv(const char *name);
int system(int command);
int *external_opaque(int x);

int main(void) {
  int *p = external_opaque(1);
  int t = getenv(0);
  *p = t;
  system(*p);
  return 0;
}
