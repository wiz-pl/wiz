/* Macro-heavy on purpose: cc -E handles the macros, but tree-sitter-c rejects the
   C++ linkage block, so the tree is a recovery tree (use --allow-errors). */
#define A(x) ((x) + 1)
#define B(x) A(A(x))
#define C(x) B(B(x))

extern "C" {
int declared_only(void);
}

int main(void) {
  return C(1);
}
