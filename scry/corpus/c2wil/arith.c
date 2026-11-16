int main(void) {
  unsigned int u = 4294967289u;
  int s = -7;
  int q = s / 2;
  int r = s % 2;
  int wrapped = (u + 10u == 3u);
  int sh = (3 << 4) + (64 >> 3);
  return q + r + wrapped + sh;
}
