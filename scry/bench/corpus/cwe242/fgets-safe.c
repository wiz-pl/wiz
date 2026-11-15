/* CWE-242: the bounded alternative is not in the forbidden set. */
typedef void FILE;
char *fgets(char *s, int size, FILE *stream);

int main(void) {
  char *buf = 0;
  FILE *in = 0;
  fgets(buf, 0, in);
  return 0;
}
