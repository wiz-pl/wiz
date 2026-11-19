/* The parameter assumption: a pointer parameter is a valid object at entry, so a
   dereference inside the function is not a null-dereference warning. The caller may
   pass NULL (CVE-2020-1971's shape); that is a documented false negative. */
int deref(int *p) {
  return *p;
}

int main(void) {
  int x = 1;
  return deref(&x);
}
