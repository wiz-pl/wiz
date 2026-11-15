/* external model: an exec call with a constant command has no tainted argument. */
int execl(const char *path, const char *arg, ...);
int main(void) {
  execl("/bin/true", "true", 0);
  return 0;
}
