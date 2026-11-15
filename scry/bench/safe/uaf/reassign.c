/* CWE-416 safe: the old object is dead and the pointer is re-bound to a fresh
   allocation before the next use. A strong update at `p = malloc` clears the
   dangling value. */
void *malloc(unsigned long n);
void free(void *p);

int main(void) {
  char *p = malloc(16);
  if (p == 0) {
    return 1;
  }
  free(p);
  p = malloc(32);
  if (p == 0) {
    return 1;
  }
  p[0] = 'A';
  free(p);
  return 0;
}
