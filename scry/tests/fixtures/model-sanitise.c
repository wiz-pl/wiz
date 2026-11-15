/* external model: a policy sanitiser's result is clean, including a name the default
   pack does not spell out (shellescape). */
char *getenv(const char *name);
char *shellescape(char *s);
int system(const char *command);
int main(void) {
  system(shellescape(getenv(0)));
  return 0;
}
