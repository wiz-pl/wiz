/* Workflow loop fixture: a forbidden `gets` whose overflow is also a dynamic
   crash. The static finding is `gets-overflow`; the repro feeds 64 `A`s on stdin
   and ASAN reports a stack-buffer-overflow. */
char *gets(char *s);
int puts(const char *s);

int main(void) {
  char buf[16];
  gets(buf);
  puts(buf);
  return 0;
}
