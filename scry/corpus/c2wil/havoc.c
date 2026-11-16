struct P { int x; int y; };

int main(void) {
  struct P p;
  p.x = 7;
  int y = p.x + 1;
  return y;
}
