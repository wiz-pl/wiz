/* store then load through a *different* stack slot: no flow, and no warning (the
   analysis knows the two slots do not alias) */
int getenv(const char *name);
int system(int command);

int main(void) {
  int a;
  int b;
  int *pa = &a;
  int *pb = &b;
  int v;
  *pa = getenv(0);
  v = *pb;
  system(v);
  return 0;
}
