/* a variable array index keeps the base object but loses the element: a[i] is a finding
   because a[0] was tainted, while b[i] (another array) stays clean */
int getenv(const char *name);
int system(int command);

int main(void) {
  int a[4];
  int b[4];
  int i = 1;
  a[0] = getenv(0);
  b[0] = 7;
  system(a[i]);
  system(b[i]);
  return 0;
}
