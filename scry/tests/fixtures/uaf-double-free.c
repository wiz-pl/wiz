/* double free: the second free is a use of the already-freed object */
int *malloc(int size);
void free(int *p);

int main(void) {
  int *p = malloc(4);
  free(p);
  free(p);
  return 0;
}
