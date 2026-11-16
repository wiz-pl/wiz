#include <stdlib.h>
int main(void) {
  char *p = malloc(4);
  p[5] = 1;
  free(p);
  return 0;
}
