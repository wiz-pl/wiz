/* use-after-free: allocate, free, then store through the pointer */
int *malloc(int size);
void free(int *p);

int main(void) {
  int *p = malloc(4);
  free(p);
  *p = 1;
  return 0;
}
