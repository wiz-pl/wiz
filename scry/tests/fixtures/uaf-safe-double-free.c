/* safe: the pointer is cleared after free, so the guarded free cannot run twice */
int *malloc(int size);
void free(int *p);

int main(void) {
  int *p = malloc(4);
  free(p);
  p = 0;
  if (p)
    free(p);
  return 0;
}
