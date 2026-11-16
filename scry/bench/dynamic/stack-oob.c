#include <string.h>
int main(void) {
  char buf[8];
  strcpy(buf, "AAAAAAAAAAAAAAAA");
  return buf[0];
}
