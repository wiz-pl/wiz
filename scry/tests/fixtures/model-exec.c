/* external model: the exec* family is a command sink across its variadic argv; the
   command string is argument 3 of execl, not only the path in argument 0. */
char *getenv(const char *name);
int execl(const char *path, const char *arg, ...);
int main(void) {
  char *cmd = getenv(0);
  execl("/bin/sh", "sh", "-c", cmd, 0);
  return 0;
}
