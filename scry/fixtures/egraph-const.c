/* The `scry egraph` fixture: straight-line arithmetic that the e-graph rewrites.
   `2 + 3` folds to 5, `a * 1` and `a + 0` simplify to `a`, and with those classes
   `b + c` folds to 10. The function is never executed by the test; the report is
   deterministic. */
int egraph_const(void) {
  int a = 2 + 3;
  int b = a * 1;
  int c = a + 0;
  return b + c;
}
