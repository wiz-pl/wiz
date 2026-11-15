/* CWE-78: one branch taints the merge; the other arm is a constant. */
char *getenv(const char *name);
int system(const char *command);

int main(int argc, char **argv) {
  char *cmd = 0;
  if (argc > 1) {
    cmd = getenv(0);
  } else {
    cmd = 0;
  }
  system(cmd);
  return 0;
}
