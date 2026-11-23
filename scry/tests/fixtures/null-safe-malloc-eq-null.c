/* CWE-476 fixed: `p == nullptr` is the same null test as `p == NULL`; the direct
   parser sees the C23 null literal rather than a macro expansion. */
int *malloc(unsigned long size);

int main(void) {
  int *p = malloc(4);
  if (p == nullptr)
    return 1;
  *p = 1;
  return *p;
}
