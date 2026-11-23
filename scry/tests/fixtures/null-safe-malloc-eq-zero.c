/* CWE-476 fixed: the `p == 0` early return is the C spelling of a null test. */
int *malloc(unsigned long size);

int main(void) {
  int *p = malloc(4);
  if (p == 0)
    return 1;
  *p = 1;
  return *p;
}
