/* safe: free-then-null; the later store is unreachable through a non-null pointer */
int *malloc(int size);
void free(int *p);

int main(void) {
  int *p = malloc(4);
  free(p);
  p = 0;
  if (p)
    *p = 1;
  return 0;
}
