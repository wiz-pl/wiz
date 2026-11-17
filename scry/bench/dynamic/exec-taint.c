#include <stdlib.h>
int main(void) {
  char *cmd = getenv("SCRY_DYNAMIC_CMD");
  system(cmd);
  return 0;
}
