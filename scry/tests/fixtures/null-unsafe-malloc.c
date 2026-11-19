/* CWE-476: malloc can fail; the store dereferences the result without a check. */
int *malloc(unsigned long size);

int main(void) {
  int *p = malloc(4);
  *p = 1;
  return *p;
}
