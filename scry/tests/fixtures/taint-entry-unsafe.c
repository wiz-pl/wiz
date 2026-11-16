/* an exported C-ABI entry (external linkage, no caller in this unit): its `cmd`
   parameter is attacker-controlled and reaches the shell through execl */
int execl(const char *path, const char *a0, const char *a1, const char *a2, const char *a3);

int iv_spawn(const char *cmd) {
  execl("/bin/sh", "sh", "-c", cmd, 0);
  return 0;
}
