/* The fixed sibling of workflow-gets.c: the static `gets-overflow` finding is gone
   and the same repro input is accepted without a sanitizer report. */
char *fgets(char *s, int n, void *stream);
int puts(const char *s);
void *stdin;

int main(void) {
  char buf[16];
  if (fgets(buf, 16, stdin) == 0) return 0;
  puts(buf);
  return 0;
}
