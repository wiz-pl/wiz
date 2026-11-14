/* external model: strcpy writes its source's contents into the destination object, so
   buf becomes tainted while a different array stays clean */
int getenv(const char *name);
int system(int command);
char *strcpy(char *dst, const char *src);

int main(void) {
  int buf[8];
  int other[8];
  int *t = getenv(0);
  strcpy(buf, t);
  system(buf[0]);
  system(other[0]);
  return 0;
}
