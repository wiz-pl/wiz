/* CWE-78: the other command sink in the default pack. */
typedef void FILE;
char *getenv(const char *name);
FILE *popen(const char *command, const char *mode);

int main(void) {
  char *cmd = getenv(0);
  FILE *p = popen(cmd, 0);
  return 0;
}
