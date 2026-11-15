/* external model: calloc allocates a fresh zeroed object; the copy into it and the sink
   stay precise (the sibling of the malloc/realloc case). */
char *getenv(const char *name);
int system(int command);
void *calloc(unsigned long n, unsigned long size);
char *strcpy(char *dst, const char *src);
int main(void) {
  char *p = calloc(8, 1);
  strcpy(p, getenv(0));
  system(p[0]);
  return 0;
}
