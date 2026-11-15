/* CWE-78 safe: the attacker value selects from a fixed command, it is never
   spliced into the command line. This is the allow-list counterpart of a
   command built with snprintf/strcat. */
char *getenv(const char *name);
int strcmp(const char *a, const char *b);
int system(const char *command);

int main(void) {
  char *mode = getenv("MODE");
  if (strcmp(mode, "status") == 0) {
    system("/usr/bin/uptime");
  } else {
    system("/usr/bin/true");
  }
  return 0;
}
