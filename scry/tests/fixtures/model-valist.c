/* A tainted format string crosses two calls and a va_list before vsnprintf. */
#include <stdarg.h>

long read(int fd, void *buf, unsigned long count);
int vsnprintf(char *str, unsigned long size, const char *format, va_list ap);

static void v(const char *f, va_list ap) {
  char b[64];
  vsnprintf(b, 64, f, ap);
}

static void h(const char *f, ...) {
  va_list ap;
  va_start(ap, f);
  v(f, ap);
  va_end(ap);
}

int main(void) {
  char b[64];
  read(0, b, 63);
  h(b);
  return 0;
}
