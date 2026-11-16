/* use-after-free through an alias: q still points at the freed object */
int *malloc(int size);
void free(int *p);

int main(void) {
  int *p = malloc(4);
  int *q = p;
  free(p);
  *q = 1;
  return 0;
}
