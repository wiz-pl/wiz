/* CWE-416: the last use precedes the free. */
int *malloc(int n);
void free(int *p);

int main(void) {
  int *p = malloc(4);
  int v;
  *p = 1;
  v = *p;
  free(p);
  return v;
}
