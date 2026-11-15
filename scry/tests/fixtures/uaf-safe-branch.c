/* safe: the freeing branch returns, so the later use is only on the path where the
   object was not freed */
int *malloc(int size);
void free(int *p);

int main(int argc) {
  int *p = malloc(4);
  if (argc > 0) {
    free(p);
    return 0;
  }
  *p = 1;
  return 0;
}
