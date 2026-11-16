/* CWE-242: the forbidden call is reported, but the array argument is a
   lowering boundary, so the case is detected and marked unknown. */
char *gets(char *s);

int main(void) {
  char buf[16];
  gets(buf);
  return 0;
}
