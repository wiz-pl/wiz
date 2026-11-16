/* CWE-120: strcat is the second forbidden copy in the default pack. */
char *strcat(char *dst, const char *src);

int main(void) {
  char *dst = 0;
  char *src = 0;
  strcat(dst, src);
  return 0;
}
