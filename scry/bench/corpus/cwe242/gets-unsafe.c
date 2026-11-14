/* CWE-242: gets cannot bound its write. */
char *gets(char *s);

int main(void) {
  char *buf = 0;
  gets(buf);
  return 0;
}
