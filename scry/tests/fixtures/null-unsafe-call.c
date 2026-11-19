/* CWE-476: a function result is dereferenced without a NULL check. */
struct item {
  int value;
};

struct item *lookup(void);

int main(void) {
  struct item *p = lookup();
  return p->value;
}
