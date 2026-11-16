/* external model: malloc and realloc allocate an object the points-to layer can name;
   the copy into it and the sink stay precise. */
char *getenv(const char *name);
int system(int command);
void *malloc(unsigned long n);
void *realloc(void *p, unsigned long n);
char *strcpy(char *dst, const char *src);
int main(void) {
  char *p = malloc(8);
  p = realloc(p, 16);
  strcpy(p, getenv(0));
  system(p[0]);
  return 0;
}
