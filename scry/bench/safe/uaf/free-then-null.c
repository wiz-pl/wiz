/* CWE-416 safe: the pointer is cleared after free, so the later guard is
   false and the store cannot touch the freed object. A flow-insensitive
   freed-set reports this; a flow-sensitive lifetime does not. */
void *malloc(unsigned long n);
void free(void *p);

int main(void) {
  char *p = malloc(16);
  if (p == 0) {
    return 1;
  }
  free(p);
  p = 0;
  if (p != 0) {
    p[0] = 'A';
  }
  return 0;
}
