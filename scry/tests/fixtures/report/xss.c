#include <stdlib.h>

int main(void) {
  char *cmd = getenv("CMD");
  const char *html = "<script>alert('x&y')</script></style>";
  system(cmd); /* <script>alert(1)</script> & "quoted" */
  return html ? 0 : 0;
}
