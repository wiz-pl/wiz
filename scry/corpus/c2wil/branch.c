int main(void) {
  int n = 10;
  int acc = 0;
  int i = 0;
  while (i <= n) {
    if (i - (i / 2) * 2 == 0) {
      acc = acc + i;
    }
    i = i + 1;
  }
  return acc;
}
