#include "math.h"

int add(int a, int b) {
  return a + b;
}

int scaled(int x) {
  return SCALE(x);
}

static int helper(int x) {
  return x + 1;
}

int use_helper(int x) {
  return helper(x);
}
