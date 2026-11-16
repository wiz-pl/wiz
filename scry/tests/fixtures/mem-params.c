/* aliased parameters: main passes the same object as both p and q, so the store through
   p is the value sink_q reads */
int getenv(const char *name);
int system(int command);

void sink_q(int *q) {
  system(*q);
  return;
}

void set_p(int *p, int v) {
  *p = v;
  return;
}

int main(void) {
  int x;
  int *a = &x;
  int *b = &x;
  set_p(a, getenv(0));
  sink_q(b);
  return 0;
}
