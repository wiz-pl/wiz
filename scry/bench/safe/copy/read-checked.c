/* CWE-787 safe in intent: the received length is checked against the
   destination before the bounded read. The check is a branch condition, not a
   sanitiser result, so a flow-insensitive length rule reports a finding. */
int read(int fd, void *buf, unsigned long count);

int main(void) {
  char lenbuf[16];
  char dst[64];
  read(0, lenbuf, 15);
  int n = lenbuf[0];
  if (n < 64) {
    read(0, dst, n);
  }
  return 0;
}
