/* an unterminated macro plus broken C: tree-sitter recovers with ERROR/MISSING */
#define BAD(x) ((x) +
int broken(int x {
  return x +
}
