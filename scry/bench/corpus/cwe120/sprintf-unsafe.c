/* CWE-120: sprintf does not bound its destination, even with a literal format. */
int sprintf(char *dst, const char *fmt);

int main(void) {
  char *dst = 0;
  sprintf(dst, "%s");
  return 0;
}
