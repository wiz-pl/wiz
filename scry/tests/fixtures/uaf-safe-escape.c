/* safe: the object escapes through a global and a parameter, is freed in another
   function, and is never used afterwards */
int *g;
int *malloc(int size);
void free(int *p);

void stash(int *p) {
  g = p;
  return;
}

void release(void) {
  free(g);
  return;
}

int main(void) {
  int *p = malloc(4);
  stash(p);
  release();
  return 0;
}
