/* store then load through the same stack slot: the taint flows through memory */
int getenv(const char *name);
int system(int command);

int main(void) {
  int slot;
  int *p = &slot;
  int v;
  *p = getenv(0);
  v = *p;
  system(v);
  return 0;
}
