/* safe: realloc reassigns the result, so p points at the new object, not the old one */
int *malloc(int size);
int *realloc(int *p, int size);
void free(int *p);

int main(void) {
  int *p = malloc(4);
  p = realloc(p, 8);
  if (!p)
    return 1;
  *p = 1;
  free(p);
  return 0;
}
