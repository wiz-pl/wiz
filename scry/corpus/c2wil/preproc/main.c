#include "inc.h"

#define TWICE(x) ((x) * 2)

int main(void) {
  int a = TWICE(3);
#if WITH_OFFSET
  int b = a + OFFSET;
#else
  int b = a;
#endif
  return bump(b);
}
