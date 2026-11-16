int main(void) {
  int acc = 0;
  int i;
  for (i = 0; i < 5; i = i + 1) {
    acc = acc + i * i;
  }
  return acc;
}
