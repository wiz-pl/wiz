/* CWE-190: a constant stack-allocation size is not attacker-controlled. */
void *alloca(int n);

int main(void) {
  int n = 16;
  void *p = alloca(n);
  return 0;
}
