/* CWE-22: an attacker-controlled path reaches fopen. */
typedef void FILE;
char *getenv(const char *name);
FILE *fopen(const char *path, const char *mode);

int main(void) {
  char *path = getenv(0);
  FILE *f = fopen(path, "r");
  return 0;
}
