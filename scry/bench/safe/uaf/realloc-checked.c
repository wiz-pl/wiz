/* CWE-416 safe: realloc may move the object; the result is checked and the
   old pointer is replaced. A use-after-free on the old object would need an
   unchecked alias, which this code does not keep. */
void *malloc(unsigned long n);
void *realloc(void *p, unsigned long n);
void free(void *p);

int main(void) {
  char *p = malloc(16);
  if (p == 0) {
    return 1;
  }
  char *q = realloc(p, 64);
  if (q == 0) {
    free(p);
    return 2;
  }
  p = q;
  p[0] = 'A';
  free(p);
  return 0;
}
