/* Sockets for `wiz lsp --infoview SOCK` (Unix-domain) and `wiz lsp --ws PORT` (TCP,
   for WebSockets): Wiz/Socket.lean.

   Lean's standard library has no Unix-domain sockets, and its TCP sockets are
   asynchronous (libuv) rather than handles, so the server listens, accepts and connects
   here, and turns each connection into two ordinary Lean handles (one for reading, one
   for writing), which it then reads and writes like stdin/stdout.

   The linker compiles this file into each executable (`moreLinkObjs` in the lakefile),
   without Lean's include directory, so it does not include <lean/lean.h>: Lean values
   are opaque pointers, and results are built by functions Wiz/Socket.lean exports. */
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/un.h>
#include <unistd.h>

typedef struct lean_object lean_object;

/* from Lean's runtime */
extern lean_object *lean_decode_io_error(int errnum, lean_object *fname);
/* lean::io_wrap_handle(FILE *), the constructor of `IO.FS.Handle` (C++: the name is its
   Itanium mangling) */
extern lean_object *_ZN4lean14io_wrap_handleEP8_IO_FILE(FILE *);
#define wrap_handle _ZN4lean14io_wrap_handleEP8_IO_FILE

/* from Wiz/Socket.lean (`@[export]`): IO results */
extern lean_object *wiz_sock_ok_unit(lean_object *w);
extern lean_object *wiz_sock_ok_fd(uint32_t fd, lean_object *w);
extern lean_object *wiz_sock_ok_conn(uint32_t fd, lean_object *r, lean_object *wr, lean_object *w);
extern lean_object *wiz_sock_ok_handles(lean_object *r, lean_object *wr, lean_object *w);
extern lean_object *wiz_sock_ok_pair(lean_object *r0, lean_object *w0, lean_object *r1, lean_object *w1, lean_object *w);
extern lean_object *wiz_sock_error(lean_object *err, lean_object *w);

static lean_object *io_errno(lean_object *w) {
  return wiz_sock_error(lean_decode_io_error(errno, NULL), w);
}

/* The socket path, sent a byte at a time (Lean strings are opaque here). Only the
   thread that starts the server (or a test) uses it. */
static struct sockaddr_un path_addr;
static size_t path_len;

lean_object *wiz_sock_path_clear(lean_object *w) {
  memset(&path_addr, 0, sizeof path_addr);
  path_addr.sun_family = AF_UNIX;
  path_len = 0;
  return wiz_sock_ok_unit(w);
}

lean_object *wiz_sock_path_push(uint8_t b, lean_object *w) {
  if (path_len + 1 >= sizeof path_addr.sun_path) { errno = ENAMETOOLONG; return io_errno(w); }
  path_addr.sun_path[path_len++] = (char)b;
  return wiz_sock_ok_unit(w);
}

/* The pair (read handle, write handle) of a connected socket `c`, which it takes over.
   Returns 0, or -1 with errno set (and `c` closed). */
static int conn_handles(int c, lean_object **r_out, lean_object **w_out) {
  int c2 = fcntl(c, F_DUPFD_CLOEXEC, 0);
  if (c2 < 0) { int e = errno; close(c); errno = e; return -1; }
  FILE *r = fdopen(c, "r");
  FILE *wr = fdopen(c2, "w");
  if (!r || !wr) {
    int e = errno;
    if (r) fclose(r); else close(c);
    if (wr) fclose(wr); else close(c2);
    errno = e;
    return -1;
  }
  *r_out = wrap_handle(r);
  *w_out = wrap_handle(wr);
  return 0;
}

/* Listen on the path, replacing a stale socket file (never another kind of file).
   Returns the listening descriptor. */
lean_object *wiz_unix_listen(lean_object *w) {
  /* a client that goes away must not kill the server: writes then fail with EPIPE */
  signal(SIGPIPE, SIG_IGN);
  struct stat st;
  if (lstat(path_addr.sun_path, &st) == 0 && S_ISSOCK(st.st_mode)) unlink(path_addr.sun_path);
  int fd = socket(AF_UNIX, SOCK_STREAM | SOCK_CLOEXEC, 0);
  if (fd < 0) return io_errno(w);
  if (bind(fd, (struct sockaddr *)&path_addr, sizeof path_addr) != 0 || listen(fd, 8) != 0) {
    int e = errno; close(fd); errno = e; return io_errno(w);
  }
  return wiz_sock_ok_fd((uint32_t)fd, w);
}

/* Listen on TCP address `addr` (IPv4, host byte order: 0x7f000001 is 127.0.0.1) and
   `port` (0: any free port, see `wiz_tcp_port`). Returns the listening descriptor. */
lean_object *wiz_tcp_listen(uint32_t addr, uint16_t port, lean_object *w) {
  signal(SIGPIPE, SIG_IGN);
  int fd = socket(AF_INET, SOCK_STREAM | SOCK_CLOEXEC, 0);
  if (fd < 0) return io_errno(w);
  int one = 1;
  setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
  struct sockaddr_in a;
  memset(&a, 0, sizeof a);
  a.sin_family = AF_INET;
  a.sin_addr.s_addr = htonl(addr);
  a.sin_port = htons(port);
  if (bind(fd, (struct sockaddr *)&a, sizeof a) != 0 || listen(fd, 8) != 0) {
    int e = errno; close(fd); errno = e; return io_errno(w);
  }
  return wiz_sock_ok_fd((uint32_t)fd, w);
}

/* The port a TCP socket is bound to. */
lean_object *wiz_tcp_port(uint32_t fd, lean_object *w) {
  struct sockaddr_in a;
  socklen_t len = sizeof a;
  if (getsockname((int)fd, (struct sockaddr *)&a, &len) != 0) return io_errno(w);
  return wiz_sock_ok_fd((uint32_t)ntohs(a.sin_port), w);
}

/* Connect to TCP `addr`:`port` (for tests): read handle and write handle. */
lean_object *wiz_tcp_connect(uint32_t addr, uint16_t port, lean_object *w) {
  signal(SIGPIPE, SIG_IGN);
  int c = socket(AF_INET, SOCK_STREAM | SOCK_CLOEXEC, 0);
  if (c < 0) return io_errno(w);
  struct sockaddr_in a;
  memset(&a, 0, sizeof a);
  a.sin_family = AF_INET;
  a.sin_addr.s_addr = htonl(addr);
  a.sin_port = htons(port);
  if (connect(c, (struct sockaddr *)&a, sizeof a) != 0) {
    int e = errno; close(c); errno = e; return io_errno(w);
  }
  lean_object *r, *wr;
  if (conn_handles(c, &r, &wr) != 0) return io_errno(w);
  return wiz_sock_ok_handles(r, wr, w);
}

/* Stop listening on a TCP socket (a thread blocked in accept returns). */
lean_object *wiz_fd_close(uint32_t fd, lean_object *w) {
  shutdown((int)fd, SHUT_RDWR);
  close((int)fd);
  return wiz_sock_ok_unit(w);
}

/* Accept a connection on a listening socket, Unix or TCP (blocking): its descriptor (for `wiz_fd_shutdown`), read handle
   and write handle. */
lean_object *wiz_unix_accept(uint32_t fd, lean_object *w) {
  int c;
  do c = accept4((int)fd, NULL, NULL, SOCK_CLOEXEC); while (c < 0 && errno == EINTR);
  if (c < 0) return io_errno(w);
  lean_object *r, *wr;
  if (conn_handles(c, &r, &wr) != 0) return io_errno(w);
  return wiz_sock_ok_conn((uint32_t)c, r, wr, w);
}

/* Connect to the path (for clients and tests): read handle and write handle. */
lean_object *wiz_unix_connect(lean_object *w) {
  signal(SIGPIPE, SIG_IGN);
  int c = socket(AF_UNIX, SOCK_STREAM | SOCK_CLOEXEC, 0);
  if (c < 0) return io_errno(w);
  if (connect(c, (struct sockaddr *)&path_addr, sizeof path_addr) != 0) {
    int e = errno; close(c); errno = e; return io_errno(w);
  }
  lean_object *r, *wr;
  if (conn_handles(c, &r, &wr) != 0) return io_errno(w);
  return wiz_sock_ok_handles(r, wr, w);
}

/* A connected pair of sockets: each end's read and write handles. An in-process pipe,
   for tests. */
lean_object *wiz_socket_pair(lean_object *w) {
  int sv[2];
  signal(SIGPIPE, SIG_IGN);
  if (socketpair(AF_UNIX, SOCK_STREAM | SOCK_CLOEXEC, 0, sv) != 0) return io_errno(w);
  lean_object *r0, *w0, *r1, *w1;
  if (conn_handles(sv[0], &r0, &w0) != 0) { int e = errno; close(sv[1]); errno = e; return io_errno(w); }
  if (conn_handles(sv[1], &r1, &w1) != 0) return io_errno(w);
  return wiz_sock_ok_pair(r0, w0, r1, w1, w);
}

/* Shut a connection down: a thread blocked reading it sees the end of the stream. */
lean_object *wiz_fd_shutdown(uint32_t fd, lean_object *w) {
  shutdown((int)fd, SHUT_RDWR);
  return wiz_sock_ok_unit(w);
}

/* Stop listening (a thread blocked in accept returns) and remove the socket file. */
lean_object *wiz_unix_close(uint32_t fd, lean_object *w) {
  shutdown((int)fd, SHUT_RDWR);
  close((int)fd);
  unlink(path_addr.sun_path);
  return wiz_sock_ok_unit(w);
}

/* Kernel hygiene: a Lean `panic!` (an ill-typed value in the
   evaluator, `xs[i]!` out of range) prints a message and goes on with the type's default
   value. A checker must not go on: with the flag set, the process exits with status 1
   after the message. */
extern void lean_set_exit_on_panic(_Bool flag);

lean_object *wiz_exit_on_panic(uint8_t flag, lean_object *w) {
  lean_set_exit_on_panic(flag != 0);
  return wiz_sock_ok_unit(w);
}
