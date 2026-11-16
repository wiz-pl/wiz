/* CWE-78: the same loop shape with a constant value. */
int system(const char *command);

int main(int argc, char **argv) {
  char *cmd = 0;
  while (argc > 0) {
    cmd = 0;
    argc = 0;
  }
  system(cmd);
  return 0;
}
