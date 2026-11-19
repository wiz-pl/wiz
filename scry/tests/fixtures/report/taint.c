#include <stdlib.h>

int main(void) {
  char *cmd = getenv("CMD");
  system(cmd);
  return 0;
}
