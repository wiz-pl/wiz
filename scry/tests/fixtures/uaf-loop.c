/* use-after-free inside a loop: free then use, then a fresh allocation */
int *malloc(int size);
void free(int *p);

int main(void) {
  int *p = malloc(4);
  int i = 0;
  while (i < 3) {
    free(p);
    *p = i;
    p = malloc(4);
    i = i + 1;
  }
  return 0;
}
