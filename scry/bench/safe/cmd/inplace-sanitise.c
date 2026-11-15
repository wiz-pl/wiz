/* CWE-78 safe: the buffer is read from the socket, then cleaned in place by a
   sanitiser before the shell runs it. The in-place form is the sanitise arg 0
   model, not a result sanitiser. */
int read(int fd, void *buf, unsigned long count);
void sanitize(char *s);
int system(const char *command);

int main(void) {
  char buf[64];
  read(0, buf, 63);
  buf[63] = 0;
  sanitize(buf);
  system(buf);
  return 0;
}
