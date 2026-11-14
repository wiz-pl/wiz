/* CWE-787: the copy length is attacker-controlled. The rule reports reachability to
   the length argument; it does not claim a proven overflow. */
int getenv(const char *name);
void *memcpy(void *dst, const void *src, int n);

int main(void) {
  int n = getenv(0);
  char *dst = 0;
  char *src = 0;
  memcpy(dst, src, n);
  return 0;
}
