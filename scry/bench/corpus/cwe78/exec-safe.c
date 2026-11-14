/* CWE-78: a constant program path is not attacker-controlled. */
int execl(const char *path, const char *arg);

int main(void) {
  char *cmd = "/bin/true";
  execl(cmd, cmd);
  return 0;
}
