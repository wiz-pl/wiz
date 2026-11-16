/* summary boundary: a callee returns a pointer to a global and the caller writes through
   it. The return-value summary carries the points-to target across the call. */
int getenv(const char *name);
int system(int command);

int g;

int *get_ptr(void) {
  return &g;
}

int main(void) {
  int *p = get_ptr();
  *p = getenv(0);
  system(g);
  return 0;
}
