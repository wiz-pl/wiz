/* CWE-78: an environment variable reaches the command interpreter. The variable name
   is a literal, so the candidate's derived plan can reproduce the finding: set
   SCRY_CMD to a shell command. Declarations are local on purpose: the single-file
   analyser parses, it does not run the system preprocessor. */
char *getenv(const char *name);
int system(const char *command);

int main(void) {
  char *cmd = getenv("SCRY_CMD");
  if (cmd) {
    system(cmd);
  }
  return 0;
}
