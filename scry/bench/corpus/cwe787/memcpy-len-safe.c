/* CWE-787: a constant copy length is not attacker-controlled. */
void *memcpy(void *dst, const void *src, int n);

int main(void) {
  char *dst = 0;
  char *src = 0;
  memcpy(dst, src, 4);
  return 0;
}
