/* pointer-to-pointer: **pp writes the variable x, and the later read of x sees it */
int getenv(const char *name);
int system(int command);

int main(void) {
  int x;
  int *p = &x;
  int **pp = &p;
  **pp = getenv(0);
  system(x);
  return 0;
}
