static int twice(int x) {
  return x + x;
}

int add3(int a, int b, int c) {
  return a + b + c;
}

int main(void) {
  int x = twice(3);
  int y = add3(x, 1, 2);
  return y;
}
