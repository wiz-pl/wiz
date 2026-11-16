/* indirect call with an unknown target: fp is never assigned, so the target cannot be
   resolved. Nothing is propagated; an unknown-indirect warning says so. */
int getenv(const char *name);
int system(int command);

int main(void) {
  int (*fp)(int);
  int t = getenv(0);
  fp(t);
  return 0;
}
