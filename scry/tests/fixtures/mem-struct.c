/* struct field flow: s.x is tainted, s.y is not, a different struct's field is not, and a
   module global's field flows too (field-sensitive points-to keeps the cells apart) */
struct S { int x; int y; };

int getenv(const char *name);
int system(int command);

struct S g;

int main(void) {
  struct S s;
  struct S t;
  s.x = getenv(0);
  s.y = 1;
  t.x = 2;
  system(s.x);
  system(s.y);
  system(t.x);
  g.x = getenv(0);
  system(g.x);
  system(g.y);
  return 0;
}
