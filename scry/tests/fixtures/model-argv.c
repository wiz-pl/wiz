/* main's argv is an environment-dependent input: the program name reaches a
   format sink even though no getenv/read call is involved. */
int vfprintf(void *stream, const char *format, ...);

int main(int argc, char **argv) {
  (void)argc;
  vfprintf(0, argv[0], 0);
  return 0;
}
