/* CWE-476 fixed: the NULL check guards the dereference on the path that uses p. */
int *malloc(unsigned long size);

int main(void) {
  int *p = malloc(4);
  if (!p)
    return 1;
  *p = 1;
  return *p;
}
