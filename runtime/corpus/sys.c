/* The runtime's POSIX interfaces (Sys): the environment, directories and files (the
   string and byte APIs, and a FILE handle), links and removal. Everything it creates
   is removed before the program returns. */
#include "corpus.h"
#include <string.h>

static wiz_val entry(void) {
  /* environment */
  check(wiz_sys_setenv("WIZ_CORPUS_ENV", "42") == 0, "Sys.setenv");
  const char *v = wiz_sys_getenv("WIZ_CORPUS_ENV");
  check(strcmp(v, "42") == 0 && wiz_sys_errno() == 0, "Sys.getenv");
  check(wiz_sys_unsetenv("WIZ_CORPUS_ENV") == 0, "Sys.unsetenv");
  v = wiz_sys_getenv("WIZ_CORPUS_ENV");
  check(v[0] == 0 && wiz_sys_errno() != 0, "Sys.getenv of an unset variable");
  check(wiz_sys_getpid() != 0, "Sys.getpid");
  check(wiz_sys_clock_ns(0) != 0, "Sys.clockNs");
  wiz_sys_sleep_ns(1000000); /* one millisecond */
  check(wiz_sys_app_path()[0] != 0, "Sys.appPath");

  /* a temporary directory, and the current directory */
  const char *made = wiz_sys_mkdtemp("/tmp/wiz-corpus-");
  check(made[0] != 0 && wiz_sys_errno() == 0, "Sys.mkdtemp");
  char *dir = strdup(made);
  if (!dir) return WIZ_BOX(0);
  const char *cwd = wiz_sys_getcwd();
  char *saved = strdup(cwd);
  check(saved != NULL && saved[0] != 0, "Sys.getcwd");
  char *path = NULL, *path2 = NULL, *sub = NULL, *subfile = NULL, *subfile2 = NULL, *link = NULL;
  if (asprintf(&path, "%s/a.txt", dir) < 0 || asprintf(&path2, "%s/b.txt", dir) < 0 ||
      asprintf(&sub, "%s/sub", dir) < 0 ||
      asprintf(&subfile, "%s/first", sub) < 0 || asprintf(&subfile2, "%s/second", sub) < 0 ||
      asprintf(&link, "%s/link", sub) < 0) {
    free(dir); free(saved);
    return WIZ_BOX(0);
  }

  /* text files */
  check(wiz_sys_write_file(path, "hello\nworld\n", 0) == 0, "Sys.writeFile");
  check(strcmp(wiz_sys_read_file(path), "hello\nworld\n") == 0, "Sys.readFile");
  check(wiz_sys_write_file(path, "again\n", 1) == 0, "Sys.writeFile append");
  check(strcmp(wiz_sys_read_file(path), "hello\nworld\nagain\n") == 0, "Sys.readFile after append");
  wiz_val st = wiz_sys_stat(path, 1);
  check(wiz_tag(st) == 1 && list_nat(st, 0) == 0, "Sys.stat: a regular file");
  check(list_nat(st, 1) == 18, "Sys.stat: its size");
  wiz_dec(st);
  check(wiz_sys_chmod(path, 0600) == 0, "Sys.chmod");
  st = wiz_sys_stat(path, 1);
  check((list_nat(st, 4) & 0777) == 0600, "Sys.stat: the mode");
  wiz_dec(st);

  /* a FILE handle: line by line, then the rest */
  void *h = wiz_sys_file_open(path, "r");
  check(h != NULL, "Sys.fileOpen");
  if (h) {
    wiz_val fv = wiz_out_ptr(h, wiz_sys_file_free);
    check(strcmp(wiz_sys_file_read_line(h), "hello") == 0, "File.readLine");
    check(strcmp(wiz_sys_file_read_all(h), "world\nagain\n") == 0, "File.readAll");
    check(wiz_sys_file_close(h) == 0, "File.close");
    check(wiz_sys_file_close(h) != 0, "File.close twice");
    wiz_dec(fv); /* the finalizer frees the handle */
  }

  /* bytes */
  wiz_val rb = wiz_sys_read_bytes(path);
  check(wiz_bytes_size(share(rb)) == 18, "Sys.readBytes");
  wiz_dec(rb);
  wiz_val wb = wiz_bytes_of_string("abc");
  check(wiz_sys_write_bytes(path2, wb, 0) == 0, "Sys.writeBytes");
  wiz_val rb2 = wiz_sys_read_bytes(path2);
  check(wiz_bytes_eq(rb2, wiz_bytes_of_string("abc")), "Sys.readBytes of what was written");

  /* the library's simpler file helpers */
  wiz_io_write_file(path2, "io\n");
  check(strcmp(wiz_io_read_file(path2), "io\n") == 0, "IO.readFile/writeFile");

  /* directories: mkdir, list, rename, link, readlink, unlink, recursive remove */
  check(wiz_sys_mkdir(sub, 0755) == 0, "Sys.mkdir");
  check(wiz_sys_write_file(subfile, "x", 0) == 0, "write into a new directory");
  wiz_val listing = wiz_sys_list_dir(sub);
  check(list_len_is(listing, 1), "Sys.listDir");
  wiz_dec(listing);
  check(wiz_sys_chdir(sub) == 0, "Sys.chdir");
  const char *inside = wiz_sys_getcwd();
  check(strstr(inside, "sub") != NULL, "Sys.getcwd after chdir");
  check(wiz_sys_chdir(saved) == 0, "Sys.chdir back");
  check(wiz_sys_rename(subfile, subfile2) == 0, "Sys.rename");
  check(wiz_sys_symlink(subfile2, link) == 0, "Sys.symlink");
  check(strcmp(wiz_sys_readlink(link), subfile2) == 0, "Sys.readlink");
  st = wiz_sys_stat(link, 0);
  check(wiz_tag(st) == 1 && list_nat(st, 0) == 2, "Sys.stat of a link (not followed)");
  wiz_dec(st);
  check(wiz_sys_unlink(link) == 0, "Sys.unlink");
  check(wiz_sys_rmdir(sub) != 0, "Sys.rmdir of a non-empty directory fails");
  check(wiz_sys_remove_all(sub) == 0, "Sys.removeAll");
  check(wiz_sys_stat(sub, 0) == WIZ_BOX(0), "the directory is gone");

  /* the environment as a flat list of name, value, … */
  wiz_val env = wiz_sys_environ();
  check(wiz_tag(env) == 1, "Sys.environ");
  wiz_dec(env);

  /* clean up */
  check(wiz_sys_unlink(path) == 0, "unlink a file");
  check(wiz_sys_unlink(path2) == 0, "unlink another file");
  check(wiz_sys_remove_all(dir) == 0, "remove the temporary directory");
  free(path); free(path2); free(sub); free(subfile); free(subfile2); free(link);
  free(dir);
  free(saved);

  printf("sys: ok\n");
  return WIZ_BOX(0);
}

int main(void) {
  int rc = wiz_run_main(entry, 0);
  if (wiz_corpus_failures) fprintf(stderr, "corpus: %d check(s) failed\n", wiz_corpus_failures);
  return wiz_corpus_failures ? 1 : rc;
}
