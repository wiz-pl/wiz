/* CWE-78: both arms are constants, but the frontend skips the else branch;
   the case is therefore a coverage probe, not a verified safe verdict. */
int system(const char *command);

int main(int argc, char **argv) {
  char *cmd = 0;
  if (argc > 1) {
    cmd = 0;
  } else {
    cmd = 0;
  }
  system(cmd);
  return 0;
}
