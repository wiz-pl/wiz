/* strdup is a fresh heap allocation: freeing it and then writing through the result
   is a use-after-free (the points-to model gives the call a heap site). */
char *strdup(const char *s);
void free(void *p);

int main(void) {
  char *p = strdup("hello");
  free(p);
  p[0] = 65;
  return 0;
}
