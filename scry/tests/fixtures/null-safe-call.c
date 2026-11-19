/* CWE-476 fixed: the call result is checked before the field access. */
struct item {
  int value;
};

struct item *lookup(void);

int main(void) {
  struct item *p = lookup();
  if (!p)
    return 1;
  return p->value;
}
