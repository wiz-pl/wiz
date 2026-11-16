/* use-after-free on one branch: the free is conditional, the use is after the merge */
int *malloc(int size);
void free(int *p);

int main(int argc) {
  int *p = malloc(4);
  if (argc > 0)
    free(p);
  *p = 1;
  return 0;
}
