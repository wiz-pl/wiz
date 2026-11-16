/* array element flow: a[0] is tainted, a[1] and another array are not (constant indices
   are exact cells; a variable index would widen to the whole array) */
int getenv(const char *name);
int system(int command);

int main(void) {
  int a[4];
  int b[4];
  a[0] = getenv(0);
  a[1] = 7;
  b[0] = 3;
  system(a[0]);
  system(a[1]);
  system(b[0]);
  return 0;
}
