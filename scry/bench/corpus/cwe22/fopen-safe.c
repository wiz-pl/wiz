/* CWE-22: a constant path is not attacker-controlled. */
typedef void FILE;
FILE *fopen(const char *path, const char *mode);

int main(void) {
  char *path = "/etc/hostname";
  FILE *f = fopen(path, "r");
  return 0;
}
