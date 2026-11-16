/* external model: strcpy copies argument 1 into argument 0's object; the forbidden
   rule reports the unbounded call and the copy carries the taint to the sink. */
char *getenv(const char *name);
int system(int command);
char *strcpy(char *dst, const char *src);
int main(void) {
  char buf[64];
  char *t = getenv(0);
  strcpy(buf, t);
  system(buf[0]);
  return 0;
}
