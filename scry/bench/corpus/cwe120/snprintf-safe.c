/* CWE-120: snprintf takes a bound, so it is not in the forbidden set. */
int snprintf(char *dst, int n, const char *fmt);

int main(void) {
  char *dst = 0;
  char *fmt = "%s";
  snprintf(dst, 16, fmt);
  return 0;
}
