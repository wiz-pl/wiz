/* CWE-190: the stack-allocation size is attacker-controlled. alloca stays a call in the
   lowering, so the allocation-size sink can see it. */
int getenv(const char *name);
void *alloca(int n);

int main(void) {
  int n = getenv(0);
  void *p = alloca(n);
  return 0;
}
