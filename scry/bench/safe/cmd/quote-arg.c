/* CWE-78 safe: quote_arg is the policy model for one shell argument. It is in
   Models.policyModels but a pack has to trust it; this case measures whether
   the default pack does. */
char *getenv(const char *name);
char *quote_arg(const char *s);
int system(const char *command);

int main(void) {
  char *arg = getenv("FILENAME");
  char *quoted = quote_arg(arg);
  system(quoted);
  return 0;
}
