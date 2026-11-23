/* Terminal and socket glue for the infoview TUI (infoview/Tui.wiz).
   Wiz's FFI marshals Nat <-> uint64_t and String <-> UTF-8 char*, and has no
   callbacks or structs, so the parts that need them live here: raw mode (termios),
   the alternate screen, the window size, SIGWINCH (through a self-pipe), poll, and
   Unix sockets. Everything else, from decoding keys to drawing, is Wiz.
   Tui.wiz names it with `link_c "term.c"`, so `wiz build` compiles and links it. */
#define _DEFAULT_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <termios.h>
#include <unistd.h>

static struct termios iv_saved;
static int iv_raw = 0;
static int iv_pipe[2] = {-1, -1};
/* end of file per stream: [0] the keys (stdin), [1] the socket. A key stream at end of
   file is readable for ever, so `iv_wait` drops it; a socket's end is what `iv_closed`
   reports. (`--dump` reads no keys at all and uses `iv_wait_fd`.) */
static int iv_eof[2];

static void iv_write_all(int fd, const char *s, size_t n) {
  while (n > 0) {
    ssize_t k = write(fd, s, n);
    if (k < 0) { if (errno == EINTR) continue; return; }
    s += k; n -= (size_t)k;
  }
}

void iv_term_close(void) {
  if (!iv_raw) return;
  /* leave the alternate screen, show the cursor, no mouse */
  const char *bye = "\x1b[?1000l\x1b[?1006l\x1b[0m\x1b[?25h\x1b[?1049l";
  iv_write_all(1, bye, strlen(bye));
  tcsetattr(0, TCSAFLUSH, &iv_saved);
  iv_raw = 0;
}

static void iv_on_winch(int sig) {
  (void)sig;
  int e = errno;
  if (iv_pipe[1] >= 0) { char c = 'w'; (void)!write(iv_pipe[1], &c, 1); }
  errno = e;
}
static void iv_on_term(int sig) { iv_term_close(); signal(sig, SIG_DFL); raise(sig); }

/* Raw mode, the alternate screen, a hidden cursor, SGR mouse reports. 1 on success. */
uint64_t iv_term_open(void) {
  if (!isatty(0) || tcgetattr(0, &iv_saved) != 0) return 0;
  struct termios t = iv_saved;
  t.c_iflag &= ~(BRKINT | ICRNL | INPCK | ISTRIP | IXON);
  t.c_cflag |= CS8;
  t.c_lflag &= ~(ECHO | ICANON | IEXTEN | ISIG);
  t.c_cc[VMIN] = 0; t.c_cc[VTIME] = 0;
  if (tcsetattr(0, TCSAFLUSH, &t) != 0) return 0;
  iv_raw = 1;
  atexit(iv_term_close);
  if (pipe(iv_pipe) == 0) {
    fcntl(iv_pipe[0], F_SETFL, O_NONBLOCK);
    fcntl(iv_pipe[1], F_SETFL, O_NONBLOCK);
  }
  struct sigaction sa;
  memset(&sa, 0, sizeof sa);
  sa.sa_handler = iv_on_winch;
  sigaction(SIGWINCH, &sa, NULL);
  signal(SIGTERM, iv_on_term);
  signal(SIGHUP, iv_on_term);
  signal(SIGPIPE, SIG_IGN);
  const char *hi = "\x1b[?1049h\x1b[?25l\x1b[?1000h\x1b[?1006h";
  iv_write_all(1, hi, strlen(hi));
  return 1;
}

uint64_t iv_term_cols(void) {
  struct winsize w;
  if (ioctl(1, TIOCGWINSZ, &w) == 0 && w.ws_col > 0) return w.ws_col;
  const char *c = getenv("COLUMNS");
  return c ? (uint64_t)atoi(c) : 80;
}
uint64_t iv_term_rows(void) {
  struct winsize w;
  if (ioctl(1, TIOCGWINSZ, &w) == 0 && w.ws_row > 0) return w.ws_row;
  const char *r = getenv("LINES");
  return r ? (uint64_t)atoi(r) : 24;
}

/* Output to the terminal, all of it. */
void iv_out(const char *s) { iv_write_all(1, s, strlen(s)); }

/* ---- sockets: fds are passed to Wiz as fd + 1, so 0 means "none" ---- */

static int iv_addr(const char *path, struct sockaddr_un *a) {
  memset(a, 0, sizeof *a);
  a->sun_family = AF_UNIX;
  if (strlen(path) >= sizeof a->sun_path) return -1;
  strcpy(a->sun_path, path);
  return 0;
}
uint64_t iv_connect(const char *path) {
  struct sockaddr_un a;
  if (iv_addr(path, &a) != 0) return 0;
  int fd = socket(AF_UNIX, SOCK_STREAM, 0);
  if (fd < 0) return 0;
  if (connect(fd, (struct sockaddr *)&a, sizeof a) != 0) { close(fd); return 0; }
  return (uint64_t)fd + 1;
}
/* Listen at `path` (replacing a stale socket file). */
uint64_t iv_listen(const char *path) {
  struct sockaddr_un a;
  if (iv_addr(path, &a) != 0) return 0;
  int fd = socket(AF_UNIX, SOCK_STREAM, 0);
  if (fd < 0) return 0;
  unlink(path);
  if (bind(fd, (struct sockaddr *)&a, sizeof a) != 0 || listen(fd, 1) != 0) { close(fd); return 0; }
  return (uint64_t)fd + 1;
}
uint64_t iv_accept(uint64_t lfd) {
  if (lfd == 0) return 0;
  int fd = accept((int)lfd - 1, NULL, NULL);
  return fd < 0 ? 0 : (uint64_t)fd + 1;
}
void iv_close(uint64_t fd) { if (fd) close((int)fd - 1); }

/* Wait up to `ms` milliseconds (0: forever) for input. The result is a bit set:
   1 a key, 2 data on `fd` (or it closed), 4 the window changed size. Once stdin has
   reached end of file it stays "readable" for ever, so it is dropped from the poll: a
   loop that treated that as a key would spin (and run out of stack). */
uint64_t iv_wait(uint64_t fd, uint64_t ms) {
  struct pollfd p[3];
  int n = 0, kp = -1, ip = -1, sp = -1;
  if (!iv_eof[0]) { kp = n; p[n].fd = 0; p[n].events = POLLIN; p[n].revents = 0; n++; }
  if (iv_pipe[0] >= 0) { ip = n; p[n].fd = iv_pipe[0]; p[n].events = POLLIN; p[n].revents = 0; n++; }
  if (fd) { sp = n; p[n].fd = (int)fd - 1; p[n].events = POLLIN; p[n].revents = 0; n++; }
  int r = poll(p, n, ms ? (int)ms : -1);
  if (r < 0 && errno == EINTR) {
    r = poll(p, n, 0);   /* the signal interrupted us: look again, without waiting */
  }
  if (r <= 0) return 0;
  uint64_t bits = 0;
  if (kp >= 0 && p[kp].revents) bits |= 1;
  if (ip >= 0 && p[ip].revents) {
    char buf[64];
    while (read(iv_pipe[0], buf, sizeof buf) > 0) {}
    bits |= 4;
  }
  if (sp >= 0 && p[sp].revents) bits |= 2;
  return bits;
}

/* Wait for the socket only (bit 2). `--dump` never reads keys, so it must not be woken
   by stdin: an inherited stdin at end of file is readable for ever, and a wait that
   reported it as input made the dump loop spin until its stack ran out. A window resize
   is not reported either: --dump has no terminal. */
uint64_t iv_wait_fd(uint64_t fd, uint64_t ms) {
  if (!fd) return 0;
  struct pollfd p;
  p.fd = (int)fd - 1; p.events = POLLIN; p.revents = 0;
  int r = poll(&p, 1, ms ? (int)ms : -1);
  if (r < 0 && errno == EINTR) r = poll(&p, 1, 0);
  return (r > 0 && p.revents) ? 2 : 0;
}

/* Reading. Bytes are handed to Wiz as UTF-8 text; a multi-byte character cut in two
   by a read is kept back until the rest arrives. NUL bytes are dropped (they would end
   the C string). An empty result and `iv_closed` mean end of file. */
static char iv_carry[2][4];
static int iv_ncarry[2];
static char *iv_buf = NULL;

static const char *iv_read_into(int fd, int slot) {
  enum { CAP = 65536 };
  if (!iv_buf) iv_buf = (char *)malloc(CAP + 8);
  int n = iv_ncarry[slot];
  memcpy(iv_buf, iv_carry[slot], (size_t)n);
  ssize_t k;
  do { k = read(fd, iv_buf + n, CAP - n); } while (k < 0 && errno == EINTR);
  int *eof = &iv_eof[slot];
  *eof = (k == 0) || (k < 0 && errno != EAGAIN && errno != EWOULDBLOCK);
  if (k < 0) k = 0;
  size_t len = (size_t)n + (size_t)k;
  /* drop NULs */
  size_t w = 0;
  for (size_t i = 0; i < len; i++) if (iv_buf[i]) iv_buf[w++] = iv_buf[i];
  len = w;
  /* keep back an incomplete UTF-8 sequence at the end */
  size_t cut = len, back = 0;
  while (back < 3 && back < len && ((unsigned char)iv_buf[len - 1 - back] & 0xC0) == 0x80) back++;
  if (back < len) {
    unsigned char lead = (unsigned char)iv_buf[len - 1 - back];
    int need = lead >= 0xF0 ? 4 : lead >= 0xE0 ? 3 : lead >= 0xC0 ? 2 : 1;
    if ((size_t)need > back + 1 && !*eof) cut = len - 1 - back;
  }
  iv_ncarry[slot] = (int)(len - cut);
  memcpy(iv_carry[slot], iv_buf + cut, len - cut);
  iv_buf[cut] = 0;
  return iv_buf;
}
const char *iv_read_keys(void) { return iv_read_into(0, 0); }
const char *iv_read_fd(uint64_t fd) {
  if (!fd) { iv_eof[1] = 1; iv_buf = iv_buf ? iv_buf : (char *)calloc(1, 65544); iv_buf[0] = 0; return iv_buf; }
  return iv_read_into((int)fd - 1, 1);
}
uint64_t iv_closed(void) { return (uint64_t)iv_eof[1]; }

/* Send text on a socket, all of it; 0 if the peer is gone. */
uint64_t iv_send(uint64_t fd, const char *s) {
  if (!fd) return 0;
  size_t n = strlen(s);
  while (n > 0) {
    ssize_t k = write((int)fd - 1, s, n);
    if (k < 0) { if (errno == EINTR) continue; return 0; }
    s += k; n -= (size_t)k;
  }
  return 1;
}

/* Milliseconds since some fixed point (for key-sequence timeouts). */
#include <time.h>
uint64_t iv_now_ms(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (uint64_t)ts.tv_sec * 1000 + (uint64_t)ts.tv_nsec / 1000000;
}

/* ---- arguments and processes ---- */

/* The program's arguments (Wiz has no `IO.args` yet: wishful io-args), read from
   /proc/self/cmdline. `iv_arg 0` is the first argument after the program name; past the
   end, "". */
static char *iv_cmdline = NULL;
static size_t iv_cmdlen = 0;
static void iv_load_args(void) {
  if (iv_cmdline) return;
  FILE *f = fopen("/proc/self/cmdline", "rb");
  size_t cap = 4096;
  iv_cmdline = (char *)malloc(cap);
  if (!f) return;
  size_t k;
  while ((k = fread(iv_cmdline + iv_cmdlen, 1, cap - iv_cmdlen, f)) > 0) {
    iv_cmdlen += k;
    if (iv_cmdlen == cap) { cap *= 2; iv_cmdline = (char *)realloc(iv_cmdline, cap); }
  }
  fclose(f);
}
uint64_t iv_argc(void) {
  iv_load_args();
  uint64_t n = 0;
  for (size_t i = 0; i < iv_cmdlen; i++) if (iv_cmdline[i] == 0) n++;
  return n ? n - 1 : 0;
}
const char *iv_arg(uint64_t i) {
  iv_load_args();
  size_t p = 0;
  for (uint64_t k = 0; k <= i && p < iv_cmdlen; k++) p += strlen(iv_cmdline + p) + 1;
  return p < iv_cmdlen ? iv_cmdline + p : "";
}

/* Run `sh -c cmd` with its stdin and stdout on one end of a socket pair (stderr to
   /dev/null); the other end, as fd + 1 (0 on failure). */
uint64_t iv_spawn(const char *cmd) {
  int sv[2];
  if (socketpair(AF_UNIX, SOCK_STREAM, 0, sv) != 0) return 0;
  pid_t pid = fork();
  if (pid < 0) { close(sv[0]); close(sv[1]); return 0; }
  if (pid == 0) {
    close(sv[0]);
    dup2(sv[1], 0); dup2(sv[1], 1);
    int devnull = open("/dev/null", O_WRONLY);
    if (devnull >= 0) dup2(devnull, 2);
    execl("/bin/sh", "sh", "-c", cmd, (char *)NULL);
    _exit(127);
  }
  close(sv[1]);
  return (uint64_t)sv[0] + 1;
}

/* An absolute path ("" if it doesn't exist). */
const char *iv_realpath(const char *p) {
  static char buf[4096];
  return realpath(p, buf) ? buf : "";
}

void iv_exit(uint64_t code) { iv_term_close(); exit((int)code); }
