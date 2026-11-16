#include <stdio.h>
#include <stdlib.h>
int main(void) {
  char *fmt = getenv("SCRY_DYNAMIC_FMT");
  if (fmt != 0) {
    printf(fmt);
  }
  return 0;
}
