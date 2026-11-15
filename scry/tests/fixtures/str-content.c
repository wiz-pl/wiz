/* buffer content: the sink argument is a stack array whose bytes were copied from the
   source. The pointer value of `buf` is never tainted; its content is. */
char *getenv(const char *name);
char *strcpy(char *dst, const char *src);
int system(const char *command);
int main(void) {
  char buf[64];
  char *t = getenv(0);
  strcpy(buf, t);
  system(buf);
  return 0;
}
