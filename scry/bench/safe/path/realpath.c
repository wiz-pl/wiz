/* CWE-22 safe: the path is canonicalised with realpath, which fails for a
   non-existent or unresolvable path; only the resolved path is opened. A
   path-traversal rule that treats realpath's result as still attacker
   controlled would be a false positive. */
char *getenv(const char *name);
char *realpath(const char *path, char *resolved);
void *fopen(const char *path, const char *mode);

int main(void) {
  char *name = getenv("FILE");
  char *p = realpath(name, 0);
  if (p != 0) {
    fopen(p, "r");
  }
  return 0;
}
