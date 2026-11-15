#include "math.h"

int main(void) {
  int pad = SCALE(1);
  return add(2, 3) + scaled(4) + pad - pad;
}
