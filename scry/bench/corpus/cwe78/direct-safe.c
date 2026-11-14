/* CWE-78: a constant command, with the same sink, is safe. */
int system(const char *command);

int main(void) {
  char *cmd = 0;
  system(cmd);
  return 0;
}
