/* use-after-free across a call: release() frees the caller's object */
int *malloc(int size);
void free(int *p);

void release(int *p) {
  free(p);
  return;
}

int main(void) {
  int *p = malloc(4);
  release(p);
  *p = 1;
  return 0;
}
