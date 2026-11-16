/* indirect call with a known target: fp holds tainted_sink, so the argument taint reaches
   the callee's sink through the function pointer */
int getenv(const char *name);
int system(int command);

void tainted_sink(int v) {
  system(v);
  return;
}

int main(void) {
  int (*fp)(int);
  int t = getenv(0);
  fp = tainted_sink;
  fp(t);
  return 0;
}
