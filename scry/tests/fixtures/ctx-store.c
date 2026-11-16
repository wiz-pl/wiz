/* context matters for a store through a parameter: the two callers of `store` pass
   different objects, so only `a` is tainted. A context-insensitive merge of the two call
   sites makes both store destinations tainted and reports the clean sink too. */
int getenv(const char *name);
int system(int command);

void store(int *p, int v) {
  *p = v;
  return;
}

void safe_sink(int *p) {
  int x = *p;
  system(x);
  return;
}

void tainted_sink(int *p) {
  int x = *p;
  system(x);
  return;
}

int main(void) {
  int a;
  int b;
  int *pa = &a;
  int *pb = &b;
  store(pa, getenv(0));
  store(pb, 0);
  safe_sink(pb);
  tainted_sink(pa);
  return 0;
}
