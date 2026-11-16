/* context matters for a return summary: `id` is called with the source and with a constant.
   A context-insensitive return summary taints both call results, so the clean sink is a
   false positive. A 1-call-site summary taints only the first call's result. */
int getenv(const char *name);
int system(int command);

int id(int x) {
  return x;
}

int main(void) {
  int a = getenv(0);
  int u = id(a);
  system(u);
  int b = 0;
  int c = id(b);
  system(c);
  return 0;
}
