/* A clean project: no source, no sink, no boundary warning. `scry project --taint`
   reports zero findings and exits 0. */
int helper(int x) {
  return x + 1;
}

int main(void) {
  return helper(1) - 1;
}
