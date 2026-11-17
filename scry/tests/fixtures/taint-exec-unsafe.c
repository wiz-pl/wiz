/* command injection through the exec family and system: every callee is a command sink,
   including the variadic execl/execlp where the tainted word is argument 3, and
   posix_spawn whose program path is argument 1 */
char *getenv(const char *name);
int system(const char *command);
int execl(const char *path, const char *a0, const char *a1, const char *a2, const char *a3);
int execlp(const char *file, const char *a0, const char *a1, const char *a2, const char *a3);
int execv(const char *path, const char *argv);
int execvp(const char *file, const char *argv);
int execve(const char *path, const char *argv, const char *envp);
int posix_spawn(int pid, const char *path, const char *file_actions, const char *attrp,
                const char *argv, const char *envp);
int posix_spawnp(int pid, const char *file, const char *file_actions, const char *attrp,
                 const char *argv, const char *envp);

int main(void) {
  char *cmd = getenv(0);
  execl("/bin/sh", "sh", "-c", cmd, 0);
  execlp("sh", "sh", "-c", cmd, 0);
  execv(cmd, 0);
  execvp(cmd, 0);
  execve(cmd, 0, 0);
  posix_spawn(0, cmd, 0, 0, 0, 0);
  posix_spawnp(0, cmd, 0, 0, 0, 0);
  system(cmd);
  return 0;
}
