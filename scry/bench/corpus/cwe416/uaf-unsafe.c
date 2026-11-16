/* CWE-416: the object is freed and then read. */
int *malloc(int n);
void free(int *p);

int main(void) {
  int *p = malloc(4);
  int v;
  *p = 1;
  free(p);
  v = *p;
  return v;
}
