/* CWE-134: a literal format string is safe. */
void syslog(int priority, const char *fmt);

int main(void) {
  char *fmt = "%s";
  syslog(3, fmt);
  return 0;
}
