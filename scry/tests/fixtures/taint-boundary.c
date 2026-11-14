/* two constructs the lowering does not model: sizeof and a cast. Each is havoc plus a
   lowering-boundary warning, and each warning points at its own statement. */
struct P { int x; };

int main(void) {
  struct P p;
  int n = sizeof(struct P);
  int m = (int)n;
  return n + m;
}
