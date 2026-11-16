/* unknown is explicit: an unmodelled external with a pointer argument gets an
   unmodelled-external warning, not a silent "pure" assumption. */
void mystery_write(char *p);
int system(const char *command);
int main(void) {
  char buf[8];
  mystery_write(buf);
  system(buf);
  return 0;
}
