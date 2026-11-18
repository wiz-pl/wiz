/* CWE-125: the same heap array, now on the load side. The index is attacker data and
   no bound check dominates the read. */
int *malloc(unsigned long size);
char *getenv(const char *name);

int main(void) {
  char *arg = getenv("IDX");
  int i = arg[0];
  int *a = malloc(32);

  return a[i];
}
