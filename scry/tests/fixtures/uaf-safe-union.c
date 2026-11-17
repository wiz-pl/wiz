/* safe: type punning writes the union's integer view after the heap object is freed;
   no pointer into the freed object is dereferenced */
union U {
  int *p;
  int v;
};

int *malloc(int size);
void free(int *p);

int main(void) {
  union U u;
  u.p = malloc(4);
  free(u.p);
  u.v = 0;
  return 0;
}
