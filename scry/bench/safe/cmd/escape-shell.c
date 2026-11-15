/* CWE-78 safe: the environment value is shell-escaped before the shell sees it.
   Same source and sink as cwe78/direct-unsafe.c, with the policy sanitiser. */
char *getenv(const char *name);
char *escape_shell(const char *s);
int system(const char *command);

int main(void) {
  char *cmd = getenv("QUERY_STRING");
  char *safe = escape_shell(cmd);
  system(safe);
  return 0;
}
