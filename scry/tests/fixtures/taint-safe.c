/* the sanitiser cleans the result, so system is safe */
char *getenv(const char *name);
char *escape_shell(char *s);
int system(const char *command);

int main(void) {
  char *raw = getenv(0);
  char *safe = escape_shell(raw);
  system(safe);
  return 0;
}
