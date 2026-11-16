static int classify(int x) {
  int r = 0;
  switch (x) {
    case 1:
      r = 10;
      break;
    case 2:
      r = 20;
      break;
    case 3:
      r = 30;
      /* fallthrough */
    case 4:
      r = r + 1;
      break;
    default:
      r = 99;
  }
  return r;
}

int main(void) {
  return classify(1) + classify(2) + classify(3) + classify(4) + classify(7);
}
