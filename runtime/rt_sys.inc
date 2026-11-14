
/* ---- system interfaces (stage 9h, lib/Sys.wiz): processes, environment, files ----

   POSIX calls, with errors as errno numbers. A call that returns a status gives 0 or
   the errno; a call that returns a value records its error per thread, read back with
   `wiz_sys_errno` (the IO token orders the two calls). Lists come back as Wiz lists
   (`List String`, `List Nat`), built like `wiz_out_string`. */

#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <spawn.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

extern char **environ;

#define WIZ_SYS_EOF 100000 /* not an errno: the end of a file (`File.readLine`) */
static _Thread_local int wiz_sys_err = 0;
static _Thread_local char *wiz_sys_scratch = NULL;

/* a result string, kept until the next one (the wrapper copies it) */
static const char *wiz_sys_keep(char *s) {
  free(wiz_sys_scratch);
  wiz_sys_scratch = s ? s : (char *)calloc(1, 1);
  return wiz_sys_scratch;
}
static uint64_t wiz_sys_status(int r) { return r < 0 ? (uint64_t)errno : 0; }

WIZ_API uint64_t wiz_sys_errno(void) { return (uint64_t)wiz_sys_err; }
WIZ_API const char *wiz_sys_strerror(uint64_t e) {
  if (e == WIZ_SYS_EOF) return "end of file";
  if (e == 100001) return "timed out"; /* WIZ_SYS_TIMEOUT */
  return strerror((int)e);
}

/* Wiz lists, from C */
static wiz_val wiz_sys_cons(wiz_val h, wiz_val t) { wiz_val fs[2] = {h, t}; return wiz_con(1, 2, fs); }
/* a `List String` as a NULL-terminated array of C strings (consumes the list) */
static char **wiz_sys_strings(wiz_val l, const char *first) {
  size_t n = 0, cap = 8;
  char **v = (char **)malloc(cap * sizeof(char *));
  if (first) v[n++] = strdup(first);
  for (wiz_val c = l; wiz_tag(c) == 1; c = wiz_field_ref(c, 1)) {
    if (n + 2 > cap) { cap *= 2; v = (char **)realloc(v, cap * sizeof(char *)); }
    wiz_val s = wiz_field_ref(c, 0);
    wiz_inc(s);
    v[n++] = wiz_in_string(s);
  }
  v[n] = NULL;
  wiz_dec(l);
  return v;
}
static void wiz_sys_free_strings(char **v) { for (char **p = v; *p; p++) free(*p); free(v); }
static int wiz_sys_cmp(const void *a, const void *b) { return strcmp(*(char *const *)a, *(char *const *)b); }

/* ---- environment ---- */

/* the value of a variable; error ENOENT when it is unset */
WIZ_API const char *wiz_sys_getenv(const char *k) {
  const char *v = getenv(k);
  wiz_sys_err = v ? 0 : ENOENT;
  return wiz_sys_keep(strdup(v ? v : ""));
}
WIZ_API uint64_t wiz_sys_setenv(const char *k, const char *v) { return wiz_sys_status(setenv(k, v, 1)); }
WIZ_API uint64_t wiz_sys_unsetenv(const char *k) { return wiz_sys_status(unsetenv(k)); }
/* every variable, sorted by name, as a flat list name₁, value₁, name₂, … */
WIZ_API wiz_val wiz_sys_environ(void) {
  size_t n = 0;
  for (char **e = environ; e && *e; e++) n++;
  char **v = (char **)malloc((n + 1) * sizeof(char *));
  for (size_t i = 0; i < n; i++) v[i] = environ[i];
  qsort(v, n, sizeof(char *), wiz_sys_cmp);
  wiz_val l = WIZ_BOX(0);
  for (size_t i = n; i > 0; i--) {
    char *kv = strdup(v[i - 1]), *eq = strchr(kv, '=');
    const char *val = "";
    if (eq) { *eq = 0; val = eq + 1; }
    l = wiz_sys_cons(wiz_out_string(kv), wiz_sys_cons(wiz_out_string(val), l));
    free(kv);
  }
  free(v);
  return l;
}

/* ---- files and directories ---- */

WIZ_API const char *wiz_sys_getcwd(void) {
  char *b = getcwd(NULL, 0);
  wiz_sys_err = b ? 0 : errno;
  return wiz_sys_keep(b);
}
WIZ_API uint64_t wiz_sys_chdir(const char *p) { return wiz_sys_status(chdir(p)); }
WIZ_API uint64_t wiz_sys_mkdir(const char *p, uint64_t mode) { return wiz_sys_status(mkdir(p, (mode_t)mode)); }
WIZ_API uint64_t wiz_sys_rmdir(const char *p) { return wiz_sys_status(rmdir(p)); }
WIZ_API uint64_t wiz_sys_unlink(const char *p) { return wiz_sys_status(unlink(p)); }
WIZ_API uint64_t wiz_sys_rename(const char *a, const char *b) { return wiz_sys_status(rename(a, b)); }
WIZ_API uint64_t wiz_sys_symlink(const char *target, const char *link) { return wiz_sys_status(symlink(target, link)); }
WIZ_API uint64_t wiz_sys_chmod(const char *p, uint64_t mode) { return wiz_sys_status(chmod(p, (mode_t)mode)); }
WIZ_API const char *wiz_sys_readlink(const char *p) {
  size_t cap = 256;
  for (;;) {
    char *b = (char *)malloc(cap);
    ssize_t n = readlink(p, b, cap);
    if (n < 0) { wiz_sys_err = errno; free(b); return wiz_sys_keep(NULL); }
    if ((size_t)n < cap) { b[n] = 0; wiz_sys_err = 0; return wiz_sys_keep(b); }
    free(b);
    cap *= 2;
  }
}
/* a new directory `<prefix>XXXXXX` */
WIZ_API const char *wiz_sys_mkdtemp(const char *prefix) {
  size_t n = strlen(prefix);
  char *t = (char *)malloc(n + 7);
  memcpy(t, prefix, n);
  memcpy(t + n, "XXXXXX", 7);
  if (!mkdtemp(t)) { wiz_sys_err = errno; free(t); return wiz_sys_keep(NULL); }
  wiz_sys_err = 0;
  return wiz_sys_keep(t);
}
/* [kind, size, mtime seconds, mtime nanoseconds, mode] (kind: 0 file, 1 directory,
   2 symbolic link, 3 other), or [] with the error; `follow` follows a final link */
WIZ_API wiz_val wiz_sys_stat(const char *p, int follow) {
  struct stat st;
  if ((follow ? stat(p, &st) : lstat(p, &st)) < 0) { wiz_sys_err = errno; return WIZ_BOX(0); }
  wiz_sys_err = 0;
  uint64_t kind = S_ISREG(st.st_mode) ? 0 : S_ISDIR(st.st_mode) ? 1 : S_ISLNK(st.st_mode) ? 2 : 3;
  uint64_t fs[5] = {kind, (uint64_t)st.st_size, (uint64_t)st.st_mtim.tv_sec, (uint64_t)st.st_mtim.tv_nsec,
                    (uint64_t)(st.st_mode & 07777)};
  wiz_val l = WIZ_BOX(0);
  for (int i = 4; i >= 0; i--) l = wiz_sys_cons(wiz_out_nat(fs[i]), l);
  return l;
}
/* the names in a directory (without . and ..), sorted */
WIZ_API wiz_val wiz_sys_list_dir(const char *p) {
  DIR *d = opendir(p);
  if (!d) { wiz_sys_err = errno; return WIZ_BOX(0); }
  size_t n = 0, cap = 16;
  char **v = (char **)malloc(cap * sizeof(char *));
  struct dirent *e;
  while ((e = readdir(d))) {
    if (!strcmp(e->d_name, ".") || !strcmp(e->d_name, "..")) continue;
    if (n == cap) { cap *= 2; v = (char **)realloc(v, cap * sizeof(char *)); }
    v[n++] = strdup(e->d_name);
  }
  closedir(d);
  qsort(v, n, sizeof(char *), wiz_sys_cmp);
  wiz_val l = WIZ_BOX(0);
  for (size_t i = n; i > 0; i--) { l = wiz_sys_cons(wiz_out_string(v[i - 1]), l); free(v[i - 1]); }
  free(v);
  wiz_sys_err = 0;
  return l;
}
/* remove a file, or a directory and everything in it (links are not followed) */
static int wiz_sys_rm_rf(const char *p) {
  struct stat st;
  if (lstat(p, &st) < 0) return -1;
  if (!S_ISDIR(st.st_mode)) return unlink(p);
  DIR *d = opendir(p);
  if (!d) return -1;
  struct dirent *e;
  int r = 0;
  size_t n = strlen(p);
  while (r == 0 && (e = readdir(d))) {
    if (!strcmp(e->d_name, ".") || !strcmp(e->d_name, "..")) continue;
    char *q = (char *)malloc(n + strlen(e->d_name) + 2);
    sprintf(q, "%s/%s", p, e->d_name);
    r = wiz_sys_rm_rf(q);
    free(q);
  }
  int saved = errno;
  closedir(d);
  if (r < 0) { errno = saved; return -1; }
  return rmdir(p);
}
WIZ_API uint64_t wiz_sys_remove_all(const char *p) { return wiz_sys_status(wiz_sys_rm_rf(p)); }

static int wiz_sys_write_all(int fd, const char *s, size_t n) {
  while (n > 0) {
    ssize_t k = write(fd, s, n);
    if (k < 0) { if (errno == EINTR) continue; return -1; }
    s += k; n -= (size_t)k;
  }
  return 0;
}
static int wiz_sys_write_path(const char *p, const char *s, size_t n, int append) {
  int fd = open(p, O_WRONLY | O_CREAT | O_CLOEXEC | (append ? O_APPEND : O_TRUNC), 0666);
  if (fd < 0) return -1;
  int r = wiz_sys_write_all(fd, s, n);
  int saved = errno;
  if (close(fd) < 0 && r == 0) return -1;
  errno = saved;
  return r;
}
/* read everything from a descriptor into a NUL-terminated buffer */
static char *wiz_sys_read_fd(int fd, size_t *len) {
  size_t cap = 4096, n = 0;
  char *b = (char *)malloc(cap);
  for (;;) {
    if (n + 1 >= cap) {
      char *nb = (char *)realloc(b, cap * 2);
      if (!nb) { free(b); errno = ENOMEM; return NULL; }
      cap *= 2; b = nb;
    }
    ssize_t k = read(fd, b + n, cap - n - 1);
    if (k < 0) { if (errno == EINTR) continue; free(b); return NULL; }
    if (k == 0) break;
    n += (size_t)k;
  }
  b[n] = 0;
  if (len) *len = n;
  return b;
}
WIZ_API const char *wiz_sys_read_file(const char *p) {
  int fd = open(p, O_RDONLY | O_CLOEXEC);
  if (fd < 0) { wiz_sys_err = errno; return wiz_sys_keep(NULL); }
  char *b = wiz_sys_read_fd(fd, NULL);
  wiz_sys_err = b ? 0 : errno;
  close(fd);
  return wiz_sys_keep(b);
}
WIZ_API uint64_t wiz_sys_write_file(const char *p, const char *s, int append) {
  return wiz_sys_status(wiz_sys_write_path(p, s, strlen(s), append));
}
WIZ_API wiz_val wiz_sys_read_bytes(const char *p) {
  wiz_val v = wiz_bytes_empty();
  int fd = open(p, O_RDONLY | O_CLOEXEC);
  if (fd < 0) { wiz_sys_err = errno; return v; }
  size_t n = 0;
  char *b = wiz_sys_read_fd(fd, &n);
  wiz_sys_err = b ? 0 : errno;
  close(fd);
  if (b) { wiz_bytes *y = (wiz_bytes *)v; y->data = (unsigned char *)b; y->len = n; y->cap = n + 1; }
  return v;
}
WIZ_API uint64_t wiz_sys_write_bytes(const char *p, wiz_val v, int append) {
  wiz_bytes *b = (wiz_bytes *)v;
  uint64_t r = wiz_sys_status(wiz_sys_write_path(p, (const char *)b->data, b->len, append));
  wiz_dec(v);
  return r;
}

/* ---- file handles: `foreign_type File (finalizer := "wiz_sys_file_free")` ---- */

typedef struct { FILE *f; int owned; } wiz_sys_file;
WIZ_API void wiz_sys_file_free(void *p) {
  wiz_sys_file *h = (wiz_sys_file *)p;
  if (h->f && h->owned) fclose(h->f);
  free(h);
}
/* fopen modes ("r", "w", "a", "r+", …); NULL with the error */
WIZ_API void *wiz_sys_file_open(const char *p, const char *mode) {
  FILE *f = fopen(p, mode);
  if (!f) { wiz_sys_err = errno; return NULL; }
  wiz_sys_err = 0;
  wiz_sys_file *h = (wiz_sys_file *)malloc(sizeof *h);
  h->f = f; h->owned = 1;
  return h;
}
/* 0 stdin, 1 stdout, 2 stderr (never closed) */
WIZ_API void *wiz_sys_file_std(uint64_t i) {
  wiz_sys_file *h = (wiz_sys_file *)malloc(sizeof *h);
  h->f = i == 0 ? stdin : i == 1 ? stdout : stderr;
  h->owned = 0;
  return h;
}
/* a line without its newline; error WIZ_SYS_EOF at the end */
WIZ_API const char *wiz_sys_file_read_line(void *p) {
  wiz_sys_file *h = (wiz_sys_file *)p;
  if (!h->f) { wiz_sys_err = EBADF; return wiz_sys_keep(NULL); }
  char *line = NULL;
  size_t cap = 0;
  errno = 0;
  ssize_t n = getline(&line, &cap, h->f);
  if (n < 0) { wiz_sys_err = errno ? errno : WIZ_SYS_EOF; free(line); return wiz_sys_keep(NULL); }
  if (n > 0 && line[n - 1] == '\n') line[n - 1] = 0;
  wiz_sys_err = 0;
  return wiz_sys_keep(line);
}
WIZ_API const char *wiz_sys_file_read_all(void *p) {
  wiz_sys_file *h = (wiz_sys_file *)p;
  if (!h->f) { wiz_sys_err = EBADF; return wiz_sys_keep(NULL); }
  size_t cap = 4096, n = 0, k;
  char *b = (char *)malloc(cap);
  while ((k = fread(b + n, 1, cap - n - 1, h->f)) > 0) {
    n += k;
    if (n + 1 >= cap) { cap *= 2; b = (char *)realloc(b, cap); }
  }
  b[n] = 0;
  wiz_sys_err = ferror(h->f) ? EIO : 0;
  return wiz_sys_keep(b);
}
WIZ_API uint64_t wiz_sys_file_write(void *p, const char *s) {
  wiz_sys_file *h = (wiz_sys_file *)p;
  if (!h->f) return EBADF;
  size_t n = strlen(s);
  return fwrite(s, 1, n, h->f) == n ? 0 : (errno ? (uint64_t)errno : EIO);
}
WIZ_API uint64_t wiz_sys_file_flush(void *p) {
  wiz_sys_file *h = (wiz_sys_file *)p;
  if (!h->f) return EBADF;
  return wiz_sys_status(fflush(h->f) == 0 ? 0 : -1);
}
WIZ_API uint64_t wiz_sys_file_close(void *p) {
  wiz_sys_file *h = (wiz_sys_file *)p;
  /* take the stream atomically: two threads closing one handle close it once */
  FILE *f = __atomic_exchange_n(&h->f, (FILE *)NULL, __ATOMIC_ACQ_REL);
  if (!f) return EBADF;
  int r = h->owned ? fclose(f) : fflush(f);
  return wiz_sys_status(r == 0 ? 0 : -1);
}

/* ---- processes: `foreign_type Child (finalizer := "wiz_sys_child_free")` ---- */

typedef struct {
  pid_t pid;
  int fd[3];      /* our ends of the pipes to stdin, stdout, stderr, or -1 */
  int waited;     /* the status is known */
  int status;     /* exit code, or 256 + signal */
  char *buf[2];   /* stdout and stderr, once collected by `communicate` */
} wiz_sys_child;

WIZ_API void wiz_sys_child_free(void *p) {
  wiz_sys_child *c = (wiz_sys_child *)p;
  for (int i = 0; i < 3; i++) if (c->fd[i] >= 0) close(c->fd[i]);
  /* reap it if it has finished (otherwise it is left to init when we exit) */
  if (!c->waited) waitpid(c->pid, NULL, WNOHANG);
  free(c->buf[0]); free(c->buf[1]);
  free(c);
}
static void wiz_sys_close_fd(int *fd) { if (*fd >= 0) { close(*fd); *fd = -1; } }

/* spawn `cmd` (searched in PATH) with arguments; each stream is 0 inherited,
   1 a pipe, 2 /dev/null. NULL with the error. */
/* the environment for a child: this program's with `changes` applied ("+K=V" sets K,
   "-K" removes it), or only the "+" entries if `clear` (consumes the list) */
static char **wiz_sys_child_env(wiz_val changes, int clear) {
  char **ch = wiz_sys_strings(changes, NULL);
  size_t n = 0, m = 0;
  if (!clear) for (char **e = environ; *e; e++) n++;
  for (char **c = ch; *c; c++) m++;
  char **env = (char **)malloc((n + m + 1) * sizeof(char *));
  size_t k = 0;
  if (!clear) for (char **e = environ; *e; e++) env[k++] = strdup(*e);
  for (char **c = ch; *c; c++) {
    const char *kv = *c + 1;
    size_t klen = strcspn(kv, "=");
    /* drop an earlier binding of the same name */
    for (size_t i = 0; i < k; i++)
      if (strncmp(env[i], kv, klen) == 0 && env[i][klen] == '=') { free(env[i]); env[i] = env[--k]; break; }
    if (**c == '+') env[k++] = strdup(kv);
  }
  env[k] = NULL;
  wiz_sys_free_strings(ch);
  return env;
}
static void *wiz_sys_spawn_in(const char *cmd, wiz_val args, uint64_t in, uint64_t out, uint64_t err,
                              const char *cwd, char **envp, uint64_t group);
WIZ_API void *wiz_sys_spawn(const char *cmd, wiz_val args, uint64_t in, uint64_t out, uint64_t err) {
  return wiz_sys_spawn_in(cmd, args, in, out, err, "", NULL, 0);
}
/* (sys-bytes) the same in directory `cwd` (unless ""), with the environment changed
   (`wiz_sys_child_env`), and `group` 0 this program's process group, 1 a new process
   group (the child leads it), 2 a new session (setsid) */
WIZ_API void *wiz_sys_spawn_with(const char *cmd, wiz_val args, uint64_t in, uint64_t out, uint64_t err,
                                 const char *cwd, wiz_val env, int clear, uint64_t group) {
  char **envp = wiz_sys_child_env(env, clear);
  void *c = wiz_sys_spawn_in(cmd, args, in, out, err, cwd, envp, group);
  wiz_sys_free_strings(envp);
  return c;
}
/* posix_spawn_file_actions_addchdir_np is glibc 2.29 (the release toolchain's sysroot,
   26f, is glibc 2.27): without it, a spawn with a directory forks, and the child sets
   itself up with async-signal-safe calls only. -DWIZ_NO_SPAWN_CHDIR forces that path
   (the tests run it both ways). */
#if defined(__GLIBC__) && defined(__GLIBC_PREREQ) && !defined(WIZ_NO_SPAWN_CHDIR)
#if __GLIBC_PREREQ(2, 29)
#define WIZ_SPAWN_ADDCHDIR 1
#endif
#endif
#ifndef WIZ_SPAWN_ADDCHDIR
/* fork, set up the child as posix_spawn would (signals, group, streams, directory), and
   exec `cmd`, searched in this program's PATH as posix_spawnp does. 0 or the errno of
   the step that failed (the child reports it through a close-on-exec pipe). */
static int wiz_sys_fork_spawn(pid_t *pid, const char *cmd, char **argv, char **envp, const uint64_t *modes,
                              int pipes[3][2], const char *cwd, uint64_t group) {
  /* everything the child needs is computed here: it must not allocate */
  const char *path = getenv("PATH");
  if (!path) path = "/bin:/usr/bin";
  size_t clen = strlen(cmd);
  int slash = strchr(cmd, '/') != NULL;
  int rep[2];
  if (pipe(rep) < 0) return errno;
  fcntl(rep[0], F_SETFD, FD_CLOEXEC); fcntl(rep[1], F_SETFD, FD_CLOEXEC);
  sigset_t all, old;
  sigfillset(&all);
  pthread_sigmask(SIG_SETMASK, &all, &old);
  pid_t p = fork();
  if (p == 0) {
    int e = 0;
    signal(SIGPIPE, SIG_DFL);
    sigset_t none;
    sigemptyset(&none);
    if (group == 1 && setpgid(0, 0) < 0) e = errno;
    if (!e && group == 2 && setsid() < 0) e = errno;
    for (int i = 0; i < 3 && !e; i++) {
      if (modes[i] == 1) {
        int child_end = i == 0 ? pipes[i][0] : pipes[i][1];
        if (dup2(child_end, i) < 0) e = errno;
      } else if (modes[i] == 2) {
        int fd = open("/dev/null", i == 0 ? O_RDONLY : O_WRONLY);
        if (fd < 0) e = errno;
        else if (fd != i) { if (dup2(fd, i) < 0) e = errno; close(fd); }
      }
    }
    if (!e && chdir(cwd) < 0) e = errno;
    if (!e) {
      sigprocmask(SIG_SETMASK, &none, NULL);
      if (slash) { execve(cmd, argv, envp); e = errno; }
      else {
        char buf[4096];
        e = ENOENT;
        for (const char *d = path; ; ) {
          const char *colon = strchr(d, ':');
          size_t dlen = colon ? (size_t)(colon - d) : strlen(d);
          if (dlen + 1 + clen + 1 <= sizeof buf) {
            size_t k = 0;
            if (dlen == 0) buf[k++] = '.'; else { memcpy(buf, d, dlen); k = dlen; }
            buf[k++] = '/';
            memcpy(buf + k, cmd, clen + 1);
            execve(buf, argv, envp);
            /* as posix_spawnp: keep looking after these, remember a permission error */
            if (errno == EACCES) e = EACCES;
            else if (errno != ENOENT && errno != ENOTDIR) { e = errno; break; }
          }
          if (!colon) break;
          d = colon + 1;
        }
      }
    }
    ssize_t w = write(rep[1], &e, sizeof e);
    (void)w;
    _exit(127);
  }
  int r = 0;
  if (p < 0) r = errno;
  pthread_sigmask(SIG_SETMASK, &old, NULL);
  close(rep[1]);
  if (p > 0) {
    int e = 0;
    ssize_t n;
    do n = read(rep[0], &e, sizeof e); while (n < 0 && errno == EINTR);
    if (n == (ssize_t)sizeof e) { r = e; waitpid(p, NULL, 0); }
    else *pid = p;
  }
  close(rep[0]);
  return r;
}
#endif
static void *wiz_sys_spawn_in(const char *cmd, wiz_val args, uint64_t in, uint64_t out, uint64_t err,
                              const char *cwd, char **envp, uint64_t group) {
  static int sigpipe_ignored = 0;
  if (!sigpipe_ignored) { signal(SIGPIPE, SIG_IGN); sigpipe_ignored = 1; }
  char **argv = wiz_sys_strings(args, cmd);
  uint64_t modes[3] = {in, out, err};
  int pipes[3][2] = {{-1, -1}, {-1, -1}, {-1, -1}};
  posix_spawn_file_actions_t fa;
  posix_spawn_file_actions_init(&fa);
  int r = 0;
  for (int i = 0; i < 3 && r == 0; i++) {
    if (modes[i] == 1) {
      if (pipe(pipes[i]) < 0) { r = errno; break; }
      fcntl(pipes[i][0], F_SETFD, FD_CLOEXEC); fcntl(pipes[i][1], F_SETFD, FD_CLOEXEC);
      int child_end = i == 0 ? pipes[i][0] : pipes[i][1];
      posix_spawn_file_actions_adddup2(&fa, child_end, i);
    } else if (modes[i] == 2) {
      posix_spawn_file_actions_addopen(&fa, i, "/dev/null", i == 0 ? O_RDONLY : O_WRONLY, 0);
    }
  }
  pid_t pid = 0;
#ifdef WIZ_SPAWN_ADDCHDIR
  if (r == 0 && cwd[0]) r = posix_spawn_file_actions_addchdir_np(&fa, cwd);
#else
  if (r == 0 && cwd[0]) {
    fflush(stdout); fflush(stderr);
    r = wiz_sys_fork_spawn(&pid, cmd, argv, envp ? envp : environ, modes, pipes, cwd, group);
  } else
#endif
  if (r == 0) {
    fflush(stdout); fflush(stderr);
    /* the child gets SIGPIPE back (we ignore it), and an empty signal mask */
    posix_spawnattr_t at;
    posix_spawnattr_init(&at);
    sigset_t def, none;
    sigemptyset(&def); sigaddset(&def, SIGPIPE);
    sigemptyset(&none);
    posix_spawnattr_setsigdefault(&at, &def);
    posix_spawnattr_setsigmask(&at, &none);
    short fl = POSIX_SPAWN_SETSIGDEF | POSIX_SPAWN_SETSIGMASK;
    if (group == 1) { fl |= POSIX_SPAWN_SETPGROUP; posix_spawnattr_setpgroup(&at, 0); }
#ifdef POSIX_SPAWN_SETSID
    if (group == 2) fl |= POSIX_SPAWN_SETSID;
#else
    if (group == 2) r = ENOSYS;
#endif
    posix_spawnattr_setflags(&at, fl);
    /* with a new environment, PATH is still this program's (posix_spawnp looks in ours) */
    if (r == 0) r = posix_spawnp(&pid, cmd, &fa, &at, argv, envp ? envp : environ);
    posix_spawnattr_destroy(&at);
  }
  posix_spawn_file_actions_destroy(&fa);
  wiz_sys_free_strings(argv);
  wiz_sys_child *c = NULL;
  if (r == 0) {
    c = (wiz_sys_child *)calloc(1, sizeof *c);
    c->pid = pid;
  }
  for (int i = 0; i < 3; i++) {
    if (pipes[i][0] < 0) { if (c) c->fd[i] = -1; continue; }
    int ours = i == 0 ? pipes[i][1] : pipes[i][0], theirs = i == 0 ? pipes[i][0] : pipes[i][1];
    close(theirs);
    if (c) c->fd[i] = ours; else close(ours);
  }
  wiz_sys_err = r;
  return c;
}
WIZ_API uint64_t wiz_sys_child_pid(void *p) { return (uint64_t)((wiz_sys_child *)p)->pid; }
WIZ_API uint64_t wiz_sys_child_write(void *p, const char *s) {
  wiz_sys_child *c = (wiz_sys_child *)p;
  if (c->fd[0] < 0) return EBADF;
  return wiz_sys_status(wiz_sys_write_all(c->fd[0], s, strlen(s)));
}
WIZ_API uint64_t wiz_sys_child_close_stdin(void *p) {
  wiz_sys_child *c = (wiz_sys_child *)p;
  if (c->fd[0] < 0) return EBADF;
  int r = close(c->fd[0]);
  c->fd[0] = -1;
  return wiz_sys_status(r);
}
/* the rest of stdout (1) or stderr (2): what `communicate` collected, or read to the end */
WIZ_API const char *wiz_sys_child_read(void *p, uint64_t i) {
  wiz_sys_child *c = (wiz_sys_child *)p;
  if (i != 1 && i != 2) { wiz_sys_err = EINVAL; return wiz_sys_keep(NULL); }
  if (c->buf[i - 1]) { char *b = c->buf[i - 1]; c->buf[i - 1] = NULL; wiz_sys_err = 0; return wiz_sys_keep(b); }
  if (c->fd[i] < 0) { wiz_sys_err = EBADF; return wiz_sys_keep(NULL); }
  char *b = wiz_sys_read_fd(c->fd[i], NULL);
  wiz_sys_err = b ? 0 : errno;
  wiz_sys_close_fd(&c->fd[i]);
  return wiz_sys_keep(b);
}
/* write `input` to stdin and close it, while collecting stdout and stderr (whichever are
   pipes) to their ends, without deadlocking on full pipes */
WIZ_API uint64_t wiz_sys_child_communicate(void *p, const char *input) {
  wiz_sys_child *c = (wiz_sys_child *)p;
  size_t inlen = strlen(input), inpos = 0;
  size_t cap[2] = {0, 0}, len[2] = {0, 0};
  char *buf[2] = {NULL, NULL};
  int r = 0;
  /* the streams that are pipes get a buffer, even if nothing comes */
  for (int i = 1; i < 3; i++) if (c->fd[i] >= 0) { cap[i - 1] = 8192; buf[i - 1] = (char *)malloc(cap[i - 1]); }
  if (c->fd[0] >= 0 && inlen == 0) wiz_sys_close_fd(&c->fd[0]);
  while (c->fd[0] >= 0 || c->fd[1] >= 0 || c->fd[2] >= 0) {
    struct pollfd pf[3];
    for (int i = 0; i < 3; i++) { pf[i].fd = c->fd[i]; pf[i].events = i == 0 ? POLLOUT : POLLIN; pf[i].revents = 0; }
    if (poll(pf, 3, -1) < 0) { if (errno == EINTR) continue; r = errno; break; }
    if (pf[0].revents & (POLLOUT | POLLERR | POLLHUP)) {
      ssize_t k = write(c->fd[0], input + inpos, inlen - inpos);
      if (k < 0 && errno != EINTR && errno != EAGAIN) wiz_sys_close_fd(&c->fd[0]); /* EPIPE: it stopped reading */
      else if (k > 0 && (inpos += (size_t)k) == inlen) wiz_sys_close_fd(&c->fd[0]);
    }
    for (int i = 1; i < 3; i++) {
      if (!(pf[i].revents & (POLLIN | POLLERR | POLLHUP))) continue;
      if (cap[i - 1] - len[i - 1] < 4097) {
        char *nb = (char *)realloc(buf[i - 1], cap[i - 1] * 2);
        if (!nb) { r = ENOMEM; break; }
        cap[i - 1] *= 2; buf[i - 1] = nb;
      }
      ssize_t k = read(c->fd[i], buf[i - 1] + len[i - 1], cap[i - 1] - len[i - 1] - 1);
      if (k > 0) len[i - 1] += (size_t)k;
      else if (k == 0 || (errno != EINTR && errno != EAGAIN)) wiz_sys_close_fd(&c->fd[i]);
    }
    if (r) break;
  }
  for (int i = 0; i < 2; i++) {
    if (!buf[i]) continue;
    if (r) { free(buf[i]); continue; }
    buf[i][len[i]] = 0;
    free(c->buf[i]);
    c->buf[i] = buf[i];
  }
  return (uint64_t)r;
}
/* wait for it to finish: its exit code, or 256 + the signal that stopped it */
WIZ_API uint64_t wiz_sys_child_wait(void *p) {
  wiz_sys_child *c = (wiz_sys_child *)p;
  if (!c->waited) {
    int st;
    pid_t r;
    while ((r = waitpid(c->pid, &st, 0)) < 0 && errno == EINTR) {}
    if (r < 0) { wiz_sys_err = errno; return 0; }
    c->waited = 1;
    c->status = WIFEXITED(st) ? WEXITSTATUS(st) : WIFSIGNALED(st) ? 256 + WTERMSIG(st) : 512;
  }
  wiz_sys_err = 0;
  return (uint64_t)c->status;
}
WIZ_API uint64_t wiz_sys_child_kill(void *p, uint64_t sig) {
  wiz_sys_child *c = (wiz_sys_child *)p;
  if (c->waited) return ESRCH;
  return wiz_sys_status(kill(c->pid, (int)sig));
}
/* (sys-bytes) without blocking: as `wiz_sys_child_wait`, or 2^32 while it runs */
WIZ_API uint64_t wiz_sys_child_try_wait(void *p) {
  wiz_sys_child *c = (wiz_sys_child *)p;
  if (!c->waited) {
    int st;
    pid_t r;
    while ((r = waitpid(c->pid, &st, WNOHANG)) < 0 && errno == EINTR) {}
    if (r < 0) { wiz_sys_err = errno; return 0; }
    wiz_sys_err = 0;
    if (r == 0) return (uint64_t)1 << 32;
    c->waited = 1;
    c->status = WIFEXITED(st) ? WEXITSTATUS(st) : WIFSIGNALED(st) ? 256 + WTERMSIG(st) : 512;
  }
  wiz_sys_err = 0;
  return (uint64_t)c->status;
}
/* a signal to the process group the child leads (spawned with a new group or session) */
WIZ_API uint64_t wiz_sys_child_kill_group(void *p, uint64_t sig) {
  wiz_sys_child *c = (wiz_sys_child *)p;
  return wiz_sys_status(kill(-c->pid, (int)sig));
}
/* take our end of pipe i (0 stdin, 1 stdout, 2 stderr) out of the child, as a
   descriptor number for `wiz_sys_fd_adopt` (the child no longer closes it) */
WIZ_API uint64_t wiz_sys_child_take(void *p, uint64_t i) {
  wiz_sys_child *c = (wiz_sys_child *)p;
  if (i > 2 || c->fd[i] < 0 || (i > 0 && c->buf[i - 1])) { wiz_sys_err = EBADF; return 0; }
  int fd = c->fd[i];
  c->fd[i] = -1;
  wiz_sys_err = 0;
  return (uint64_t)fd;
}
/* replace this program (returns only with an error) */
WIZ_API uint64_t wiz_sys_exec(const char *cmd, wiz_val args) {
  char **argv = wiz_sys_strings(args, cmd);
  fflush(stdout); fflush(stderr);
  signal(SIGPIPE, SIG_DFL);
  execvp(cmd, argv);
  int e = errno;
  wiz_sys_free_strings(argv);
  return (uint64_t)e;
}
WIZ_API void wiz_sys_exit(uint64_t code) { exit((int)code); }
WIZ_API uint64_t wiz_sys_getpid(void) { return (uint64_t)getpid(); }

/* ---- (sys-bytes) paths, the program's own path, clocks ---- */

#include <limits.h>
#include <time.h>
#ifdef __APPLE__
#include <mach-o/dyld.h>
#endif

WIZ_API const char *wiz_sys_realpath(const char *p) {
  char *r = realpath(p, NULL);
  wiz_sys_err = r ? 0 : errno;
  return wiz_sys_keep(r);
}
/* the running executable: /proc/self/exe on Linux, _NSGetExecutablePath on macOS
   (other systems: ENOSYS) */
WIZ_API const char *wiz_sys_app_path(void) {
#if defined(__linux__)
  return wiz_sys_readlink("/proc/self/exe");
#elif defined(__APPLE__)
  uint32_t n = 0;
  _NSGetExecutablePath(NULL, &n);
  char *b = (char *)malloc(n + 1);
  if (_NSGetExecutablePath(b, &n) != 0) { free(b); wiz_sys_err = ENAMETOOLONG; return wiz_sys_keep(NULL); }
  char *r = realpath(b, NULL);
  free(b);
  wiz_sys_err = r ? 0 : errno;
  return wiz_sys_keep(r);
#else
  wiz_sys_err = ENOSYS;
  return wiz_sys_keep(NULL);
#endif
}
/* nanoseconds: 0 the monotonic clock (since an unspecified point, never goes back),
   1 the wall clock (since the epoch) */
WIZ_API uint64_t wiz_sys_clock_ns(uint64_t which) {
  struct timespec t;
  clock_gettime(which == 0 ? CLOCK_MONOTONIC : CLOCK_REALTIME, &t);
  return (uint64_t)t.tv_sec * 1000000000u + (uint64_t)t.tv_nsec;
}
WIZ_API void wiz_sys_sleep_ns(uint64_t ns) {
  struct timespec t = {(time_t)(ns / 1000000000u), (long)(ns % 1000000000u)};
  while (nanosleep(&t, &t) < 0 && errno == EINTR) {}
}

/* ---- (sys-bytes) byte buffers: slices, joins, comparison ---- */

/* a buffer that owns `data` (malloc'd, `cap` bytes, `len` used) */
static wiz_val wiz_bytes_adopt(unsigned char *data, size_t len, size_t cap) {
  wiz_bytes *b = (wiz_bytes *)wiz_bytes_empty();
  if (data && len == 0) { free(data); data = NULL; cap = 0; }
  b->data = data; b->len = len; b->cap = cap;
  return (wiz_val)b;
}
/* bytes [start, start + len), cut at the end */
WIZ_API wiz_val wiz_bytes_slice(wiz_val v, uint64_t start, uint64_t len) {
  wiz_bytes *b = (wiz_bytes *)v;
  size_t s = start < b->len ? start : b->len;
  size_t n = len < b->len - s ? len : b->len - s;
  unsigned char *d = n ? (unsigned char *)malloc(n) : NULL;
  if (n) memcpy(d, b->data + s, n);
  wiz_dec(v);
  return wiz_bytes_adopt(d, n, n);
}
/* `a` then `b`: in place when `a` is unique */
WIZ_API wiz_val wiz_bytes_append(wiz_val a, wiz_val b) {
  wiz_bytes *y = (wiz_bytes *)b;
  if (y->len == 0) { wiz_dec(b); return a; }
  a = wiz_bytes_unique(a);
  wiz_bytes *x = (wiz_bytes *)a;
  if (x->len + y->len > x->cap) {
    size_t cap = x->cap ? x->cap : 8;
    while (cap < x->len + y->len) cap *= 2;
    x->data = (unsigned char *)realloc(x->data, cap); x->cap = cap;
  }
  memcpy(x->data + x->len, y->data, y->len);
  x->len += y->len;
  wiz_dec(b);
  return a;
}
WIZ_API int wiz_bytes_eq(wiz_val a, wiz_val b) {
  wiz_bytes *x = (wiz_bytes *)a, *y = (wiz_bytes *)b;
  int r = x->len == y->len && (x->len == 0 || memcmp(x->data, y->data, x->len) == 0);
  wiz_dec(a); wiz_dec(b);
  return r;
}

/* ---- (sys-bytes) byte I/O on `File` (stdio: buffered, shares the buffer with
   readLine/write) ---- */

#define WIZ_SYS_TIMEOUT 100001 /* not an errno: the time ran out (a timed read) */

/* up to n bytes; fewer only at the end of the file (error WIZ_SYS_EOF with nothing) */
WIZ_API wiz_val wiz_sys_file_read_bytes(void *p, uint64_t n) {
  wiz_sys_file *h = (wiz_sys_file *)p;
  if (!h->f) { wiz_sys_err = EBADF; return wiz_bytes_empty(); }
  if (n == 0) { wiz_sys_err = 0; return wiz_bytes_empty(); }
  unsigned char *d = (unsigned char *)malloc(n);
  if (!d) { wiz_sys_err = ENOMEM; return wiz_bytes_empty(); }
  size_t k = fread(d, 1, n, h->f);
  if (k == 0) {
    free(d);
    wiz_sys_err = ferror(h->f) ? (errno ? errno : EIO) : WIZ_SYS_EOF;
    clearerr(h->f);
    return wiz_bytes_empty();
  }
  wiz_sys_err = 0;
  return wiz_bytes_adopt(d, k, n);
}
WIZ_API uint64_t wiz_sys_file_write_bytes(void *p, wiz_val v) {
  wiz_sys_file *h = (wiz_sys_file *)p;
  wiz_bytes *b = (wiz_bytes *)v;
  uint64_t r = !h->f ? EBADF : (b->len == 0 || fwrite(b->data, 1, b->len, h->f) == b->len) ? 0 : (errno ? (uint64_t)errno : EIO);
  wiz_dec(v);
  return r;
}
/* whence 0 from the start, 1 from here, 2 from the end; `back`: the offset is negative.
   The new offset from the start. */
static int wiz_sys_whence(uint64_t w) { return w == 0 ? SEEK_SET : w == 1 ? SEEK_CUR : SEEK_END; }
WIZ_API uint64_t wiz_sys_file_seek(void *p, uint64_t whence, uint64_t off, int back) {
  wiz_sys_file *h = (wiz_sys_file *)p;
  if (!h->f) { wiz_sys_err = EBADF; return 0; }
  off_t o = back ? -(off_t)off : (off_t)off;
  if (fseeko(h->f, o, wiz_sys_whence(whence)) < 0) { wiz_sys_err = errno; return 0; }
  off_t at = ftello(h->f);
  wiz_sys_err = at < 0 ? errno : 0;
  return at < 0 ? 0 : (uint64_t)at;
}

/* ---- (sys-bytes) descriptors: `foreign_type Fd (finalizer := "wiz_sys_fd_free")` ----

   Unbuffered: each read is one read(2) (or a loop of them), so poll(2) sees what is
   really waiting. For terminals, pipes and devices; for regular files `File` is
   faster. Closing twice is an error (EBADF), never a second close(2) of a number
   that may have been reused. */

typedef struct { int fd; int owned; int eio_eof; } wiz_sys_fdh;
WIZ_API void wiz_sys_fd_free(void *p) {
  wiz_sys_fdh *h = (wiz_sys_fdh *)p;
  if (h->fd >= 0 && h->owned) close(h->fd);
  free(h);
}
static void *wiz_sys_fd_wrap(int fd, int owned) {
  wiz_sys_fdh *h = (wiz_sys_fdh *)malloc(sizeof *h);
  h->fd = fd; h->owned = owned; h->eio_eof = 0;
  return h;
}
/* access 0 read, 1 write, 2 both; flags: 1 create, 2 truncate, 4 append, 8 exclusive,
   16 no controlling terminal, 32 non-blocking open (cleared afterwards). Close-on-exec. */
WIZ_API void *wiz_sys_fd_open(const char *path, uint64_t access, uint64_t flags, uint64_t mode) {
  int f = (access == 0 ? O_RDONLY : access == 1 ? O_WRONLY : O_RDWR) | O_CLOEXEC;
  if (flags & 1) f |= O_CREAT;
  if (flags & 2) f |= O_TRUNC;
  if (flags & 4) f |= O_APPEND;
  if (flags & 8) f |= O_EXCL;
  if (flags & 16) f |= O_NOCTTY;
  if (flags & 32) f |= O_NONBLOCK;
  int fd = open(path, f, (mode_t)mode);
  if (fd < 0) { wiz_sys_err = errno; return NULL; }
  if (flags & 32) fcntl(fd, F_SETFL, fcntl(fd, F_GETFL) & ~O_NONBLOCK);
  wiz_sys_err = 0;
  return wiz_sys_fd_wrap(fd, 1);
}
/* 0 stdin, 1 stdout, 2 stderr (never closed) */
WIZ_API void *wiz_sys_fd_std(uint64_t i) { return wiz_sys_fd_wrap((int)(i < 3 ? i : 2), 0); }
/* take over a descriptor number made elsewhere (a C shim, `pipe`): closed with it */
WIZ_API void *wiz_sys_fd_adopt(uint64_t fd) { return wiz_sys_fd_wrap((int)fd, 1); }
/* the descriptor number, for C shims (-1 once closed: a huge Nat) */
WIZ_API uint64_t wiz_sys_fd_raw(void *p) { return (uint64_t)(int64_t)((wiz_sys_fdh *)p)->fd; }
/* a pseudo-terminal's controller: EIO from a read is the end of the file (Linux says
   EIO once no one has the terminal side open) */
WIZ_API void wiz_sys_fd_set_pty(void *p) { ((wiz_sys_fdh *)p)->eio_eof = 1; }
/* nothing: a use of the handle, so it stays open until here (`Fd.withRaw`) */
WIZ_API void wiz_sys_fd_keep(void *p) { (void)p; }
WIZ_API uint64_t wiz_sys_fd_close(void *p) {
  wiz_sys_fdh *h = (wiz_sys_fdh *)p;
  /* take the number atomically: two threads closing one handle close it once (never a
     second close(2) of a number another thread may have reused) */
  int fd = __atomic_exchange_n(&h->fd, -1, __ATOMIC_ACQ_REL);
  if (fd < 0) return EBADF;
  int r = h->owned ? close(fd) : 0;
  return wiz_sys_status(r);
}
/* a pipe: (read end) + 2^32 * (write end), both close-on-exec */
WIZ_API uint64_t wiz_sys_pipe(void) {
  int p[2];
  if (pipe2(p, O_CLOEXEC) < 0) { wiz_sys_err = errno; return 0; }
  wiz_sys_err = 0;
  return (uint64_t)(unsigned)p[0] | ((uint64_t)(unsigned)p[1] << 32);
}

/* wait until fd is ready for `events` or the deadline (monotonic ns; 0: none) passes:
   1 ready, 0 timed out, -1 error (errno) */
static int wiz_sys_wait_fd(int fd, short events, uint64_t deadline) {
  for (;;) {
    int ms = -1;
    if (deadline) {
      uint64_t now = wiz_sys_clock_ns(0);
      if (now >= deadline) ms = 0;
      else { uint64_t d = (deadline - now + 999999u) / 1000000u; ms = d > INT_MAX ? INT_MAX : (int)d; }
    }
    struct pollfd pf = {fd, events, 0};
    int r = poll(&pf, 1, ms);
    if (r < 0) { if (errno == EINTR) continue; return -1; }
    if (r > 0) {
      if (pf.revents & POLLNVAL) { errno = EBADF; return -1; }
      return 1; /* POLLHUP/POLLERR: the read or write that follows reports it */
    }
    if (ms == 0) return 0;
    if (deadline && wiz_sys_clock_ns(0) >= deadline) return 0;
  }
}
static uint64_t wiz_sys_deadline(int timed, uint64_t ns) {
  if (!timed) return 0;
  uint64_t d = wiz_sys_clock_ns(0) + ns;
  return d ? d : 1;
}
/* one read: up to n bytes (at least one), or error WIZ_SYS_EOF (nothing: the end) or
   WIZ_SYS_TIMEOUT (nothing came within `ns`, if `timed`) */
WIZ_API wiz_val wiz_sys_fd_read(void *p, uint64_t n, int timed, uint64_t ns) {
  wiz_sys_fdh *h = (wiz_sys_fdh *)p;
  if (h->fd < 0) { wiz_sys_err = EBADF; return wiz_bytes_empty(); }
  if (n == 0) { wiz_sys_err = 0; return wiz_bytes_empty(); }
  uint64_t deadline = wiz_sys_deadline(timed, ns);
  unsigned char *d = (unsigned char *)malloc(n);
  if (!d) { wiz_sys_err = ENOMEM; return wiz_bytes_empty(); }
  for (;;) {
    if (timed) {
      int w = wiz_sys_wait_fd(h->fd, POLLIN, deadline);
      if (w <= 0) { wiz_sys_err = w == 0 ? WIZ_SYS_TIMEOUT : errno; free(d); return wiz_bytes_empty(); }
    }
    ssize_t k = read(h->fd, d, n);
    if (k > 0) { wiz_sys_err = 0; return wiz_bytes_adopt(d, (size_t)k, n); }
    if (k == 0) { wiz_sys_err = WIZ_SYS_EOF; free(d); return wiz_bytes_empty(); }
    if (errno == EINTR) continue;
    if (errno == EAGAIN && timed) continue; /* spurious readiness on a non-blocking fd */
    wiz_sys_err = errno == EIO && h->eio_eof ? WIZ_SYS_EOF : errno; free(d); return wiz_bytes_empty();
  }
}
/* exactly n bytes, unless the end (WIZ_SYS_EOF) or the deadline (WIZ_SYS_TIMEOUT)
   comes first: then what came before it */
WIZ_API wiz_val wiz_sys_fd_read_exact(void *p, uint64_t n, int timed, uint64_t ns) {
  wiz_sys_fdh *h = (wiz_sys_fdh *)p;
  if (h->fd < 0) { wiz_sys_err = EBADF; return wiz_bytes_empty(); }
  uint64_t deadline = wiz_sys_deadline(timed, ns);
  unsigned char *d = n ? (unsigned char *)malloc(n) : NULL;
  if (n && !d) { wiz_sys_err = ENOMEM; return wiz_bytes_empty(); }
  size_t got = 0;
  int e = 0;
  while (got < n) {
    if (timed) {
      int w = wiz_sys_wait_fd(h->fd, POLLIN, deadline);
      if (w <= 0) { e = w == 0 ? WIZ_SYS_TIMEOUT : errno; break; }
    }
    ssize_t k = read(h->fd, d + got, n - got);
    if (k > 0) { got += (size_t)k; continue; }
    if (k == 0) { e = WIZ_SYS_EOF; break; }
    if (errno == EINTR || (errno == EAGAIN && timed)) continue;
    e = errno == EIO && h->eio_eof ? WIZ_SYS_EOF : errno; break;
  }
  wiz_sys_err = e;
  return wiz_bytes_adopt(d, got, n);
}
/* all of the buffer (waiting while a non-blocking descriptor is full) */
WIZ_API uint64_t wiz_sys_fd_write(void *p, wiz_val v) {
  wiz_sys_fdh *h = (wiz_sys_fdh *)p;
  wiz_bytes *b = (wiz_bytes *)v;
  uint64_t r = 0;
  if (h->fd < 0) r = EBADF;
  else {
    size_t off = 0;
    while (off < b->len) {
      ssize_t k = write(h->fd, b->data + off, b->len - off);
      if (k > 0) { off += (size_t)k; continue; }
      if (k < 0 && errno == EINTR) continue;
      if (k < 0 && errno == EAGAIN) { if (wiz_sys_wait_fd(h->fd, POLLOUT, 0) < 0) { r = errno; break; } continue; }
      r = k < 0 ? (uint64_t)errno : EIO; break;
    }
  }
  wiz_dec(v);
  return r;
}
/* readable (events 1) or writable (2) within `ns` (if timed; forever otherwise):
   1 ready, 0 not */
WIZ_API uint64_t wiz_sys_fd_wait(void *p, uint64_t events, int timed, uint64_t ns) {
  wiz_sys_fdh *h = (wiz_sys_fdh *)p;
  if (h->fd < 0) { wiz_sys_err = EBADF; return 0; }
  int w = wiz_sys_wait_fd(h->fd, events == 2 ? POLLOUT : POLLIN, wiz_sys_deadline(timed, ns));
  wiz_sys_err = w < 0 ? errno : 0;
  return w > 0;
}
WIZ_API uint64_t wiz_sys_fd_seek(void *p, uint64_t whence, uint64_t off, int back) {
  wiz_sys_fdh *h = (wiz_sys_fdh *)p;
  if (h->fd < 0) { wiz_sys_err = EBADF; return 0; }
  off_t at = lseek(h->fd, back ? -(off_t)off : (off_t)off, wiz_sys_whence(whence));
  wiz_sys_err = at < 0 ? errno : 0;
  return at < 0 ? 0 : (uint64_t)at;
}
/* poll several: `fds` a `List Fd`, `events` a `List Nat` (1 read, 2 write, 3 both) of
   the same length; within `ns` if timed. The list of ready positions (each with what
   it is ready for: 8 * position + (1 readable | 2 writable | 4 hung up or error)),
   empty when the time ran out. Both lists are consumed. */
WIZ_API wiz_val wiz_sys_fd_poll(wiz_val fds, wiz_val events, int timed, uint64_t ns) {
  size_t n = 0;
  for (wiz_val c = fds; wiz_tag(c) == 1; c = wiz_field_ref(c, 1)) n++;
  struct pollfd *pf = (struct pollfd *)calloc(n ? n : 1, sizeof *pf);
  size_t i = 0;
  wiz_val e = events;
  for (wiz_val c = fds; wiz_tag(c) == 1; c = wiz_field_ref(c, 1), i++) {
    wiz_sys_fdh *h = (wiz_sys_fdh *)wiz_in_ptr(wiz_field_ref(c, 0));
    uint64_t ev = 1;
    if (wiz_tag(e) == 1) { wiz_val x = wiz_field_ref(e, 0); ev = WIZ_IS_SCALAR(x) ? WIZ_UNBOX(x) : 1; e = wiz_field_ref(e, 1); }
    pf[i].fd = h->fd; /* a closed one (-1) is ignored by poll */
    pf[i].events = (short)(((ev & 1) ? POLLIN : 0) | ((ev & 2) ? POLLOUT : 0));
  }
  uint64_t deadline = wiz_sys_deadline(timed, ns);
  int r;
  for (;;) {
    int ms = -1;
    if (deadline) {
      uint64_t now = wiz_sys_clock_ns(0);
      if (now >= deadline) ms = 0;
      else { uint64_t d = (deadline - now + 999999u) / 1000000u; ms = d > INT_MAX ? INT_MAX : (int)d; }
    }
    r = poll(pf, (nfds_t)n, ms);
    if (r < 0 && errno == EINTR) continue;
    if (r == 0 && ms != 0 && deadline && wiz_sys_clock_ns(0) < deadline) continue;
    break;
  }
  wiz_sys_err = r < 0 ? errno : 0;
  wiz_val out = wiz_con(0, 0, NULL);
  for (size_t k = n; r > 0 && k > 0; k--) {
    short re = pf[k - 1].revents;
    if (!re) continue;
    uint64_t what = ((re & POLLIN) ? 1 : 0) | ((re & POLLOUT) ? 2 : 0) | ((re & (POLLHUP | POLLERR | POLLNVAL)) ? 4 : 0);
    out = wiz_sys_cons(wiz_out_nat(8 * (uint64_t)(k - 1) + what), out);
  }
  free(pf);
  wiz_dec(fds); wiz_dec(events);
  return out;
}

/* ---- output: a generic tree, read back by the compiler using the type ---- */

static void wiz_print(wiz_val v) {
  if (WIZ_IS_SCALAR(v)) { printf("%lu", (unsigned long)WIZ_UNBOX(v)); return; }
  wiz_hdr *h = (wiz_hdr *)v;
  if (h->tag == WIZ_TAG_BIG) { mpz_out_str(stdout, 10, ((wiz_big *)v)->z); return; }
  if (h->tag == WIZ_TAG_CLO || h->tag == WIZ_TAG_THUNK) { printf("<fn>"); return; }
  if (h->tag == WIZ_TAG_RAW) { printf("#%llu", (unsigned long long)wiz_raw_bits(v)); return; }
  printf("(%u", h->tag);
  for (uint32_t i = 0; i < h->size; i++) { putchar(' '); wiz_print(((wiz_ctor *)v)->fields[i]); }
  putchar(')');
}

/* WIZ_SET as a function, for the LLVM backend */
WIZ_API void wiz_set(wiz_val o, uint32_t i, wiz_val v) { WIZ_SET(o, i, v); }
