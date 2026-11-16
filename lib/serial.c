/* termios and pseudo-terminals for lib/Serial.wiz (`link_c "serial.c"`).

   Wiz's FFI passes Nat as uint64_t and String as UTF-8 char *; descriptors come as
   numbers (`Fd.raw`) and go back with `Fd.adopt`. A result that can fail is a number
   with bit 63 set for an error: errno in the low bits. */
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <termios.h>
#include <unistd.h>

#define WIZSER_ERR(e) (((uint64_t)1 << 63) | (uint64_t)(e))

/* the baud rates, in the order of `Baud` in Serial.wiz */
static const speed_t wizser_speeds[] = {
  B1200, B2400, B4800, B9600, B19200, B38400, B57600, B115200, B230400,
#ifdef B460800
  B460800,
#else
  0,
#endif
#ifdef B921600
  B921600,
#else
  0,
#endif
#ifdef B1000000
  B1000000,
#else
  0,
#endif
#ifdef B2000000
  B2000000,
#else
  0,
#endif
#ifdef B3000000
  B3000000,
#else
  0,
#endif
};
#define WIZSER_NSPEEDS (sizeof wizser_speeds / sizeof wizser_speeds[0])

static int wizser_speed_index(speed_t s) {
  for (size_t i = 0; i < WIZSER_NSPEEDS; i++) if (wizser_speeds[i] == s && s) return (int)i;
  return -1;
}

/* raw mode: no line editing, echo, signals or translation; `bits` 5…8, `parity` 0 none
   1 even 2 odd, `stop` 1 or 2, `flow` 0 none 1 RTS/CTS 2 XON/XOFF; reads wait for one
   byte (VMIN 1, VTIME 0: time limits are Fd.readWithin's). Read back and compared:
   100002 (not an errno) if the driver did not keep the data bits, parity, stop bits or
   rate (a Linux pseudo-terminal is always CS8 without parity). */
uint64_t wizser_configure(uint64_t fd, uint64_t baud, uint64_t bits, uint64_t parity, uint64_t stop, uint64_t flow) {
  if (baud >= WIZSER_NSPEEDS || !wizser_speeds[baud]) return EINVAL;
  struct termios t;
  if (tcgetattr((int)fd, &t) < 0) return errno;
  cfmakeraw(&t);
  t.c_iflag &= ~(IXON | IXOFF | IXANY | INPCK | ISTRIP);
  t.c_cflag &= ~(CSIZE | PARENB | PARODD | CSTOPB | CRTSCTS);
  t.c_cflag |= CLOCAL | CREAD;
  t.c_cflag |= bits == 5 ? CS5 : bits == 6 ? CS6 : bits == 7 ? CS7 : CS8;
  if (parity == 1) t.c_cflag |= PARENB;
  if (parity == 2) t.c_cflag |= PARENB | PARODD;
  if (parity) t.c_iflag |= INPCK;
  if (stop == 2) t.c_cflag |= CSTOPB;
  if (flow == 1) t.c_cflag |= CRTSCTS;
  if (flow == 2) t.c_iflag |= IXON | IXOFF;
  t.c_cc[VMIN] = 1;
  t.c_cc[VTIME] = 0;
  if (cfsetispeed(&t, wizser_speeds[baud]) < 0 || cfsetospeed(&t, wizser_speeds[baud]) < 0) return errno;
  if (tcsetattr((int)fd, TCSANOW, &t) < 0) return errno;
  struct termios u;
  if (tcgetattr((int)fd, &u) < 0) return errno;
  if ((u.c_cflag & (CSIZE | PARENB | PARODD | CSTOPB)) != (t.c_cflag & (CSIZE | PARENB | PARODD | CSTOPB)) ||
      cfgetospeed(&u) != cfgetospeed(&t)) return 100002;
  return 0;
}

/* the settings, packed: baud index (255 unknown) | bits << 8 | parity << 12 |
   stop << 16 | flow << 20 (3: both) | raw << 24 (no ICANON, ECHO, ISIG, OPOST, ICRNL) |
   VMIN << 32 | VTIME << 40 */
uint64_t wizser_get(uint64_t fd) {
  struct termios t;
  if (tcgetattr((int)fd, &t) < 0) return WIZSER_ERR(errno);
  int sp = wizser_speed_index(cfgetospeed(&t));
  uint64_t cs = t.c_cflag & CSIZE;
  uint64_t bits = cs == CS5 ? 5 : cs == CS6 ? 6 : cs == CS7 ? 7 : 8;
  uint64_t parity = !(t.c_cflag & PARENB) ? 0 : (t.c_cflag & PARODD) ? 2 : 1;
  uint64_t stop = (t.c_cflag & CSTOPB) ? 2 : 1;
  uint64_t flow = ((t.c_cflag & CRTSCTS) ? 1 : 0) | ((t.c_iflag & (IXON | IXOFF)) ? 2 : 0);
  uint64_t raw = !(t.c_lflag & (ICANON | ECHO | ISIG | IEXTEN)) && !(t.c_oflag & OPOST) && !(t.c_iflag & (ICRNL | INLCR | IGNCR));
  return (uint64_t)(sp < 0 ? 255 : sp) | bits << 8 | parity << 12 | stop << 16 | flow << 20 | raw << 24 |
         (uint64_t)t.c_cc[VMIN] << 32 | (uint64_t)t.c_cc[VTIME] << 40;
}

/* 0 the input queue (received, not read), 1 output (written, not sent), 2 both */
uint64_t wizser_flush(uint64_t fd, uint64_t q) {
  return tcflush((int)fd, q == 0 ? TCIFLUSH : q == 1 ? TCOFLUSH : TCIOFLUSH) < 0 ? (uint64_t)errno : 0;
}
/* wait until everything written has been sent */
uint64_t wizser_drain(uint64_t fd) {
  int r;
  while ((r = tcdrain((int)fd)) < 0 && errno == EINTR) {}
  return r < 0 ? (uint64_t)errno : 0;
}
uint64_t wizser_isatty(uint64_t fd) { return isatty((int)fd) ? 1 : 0; }

/* a new pseudo-terminal: the controller's descriptor (close-on-exec) */
uint64_t wizser_pty_open(void) {
  int m = posix_openpt(O_RDWR | O_NOCTTY | O_CLOEXEC);
  if (m < 0) return WIZSER_ERR(errno);
  if (grantpt(m) < 0 || unlockpt(m) < 0) { int e = errno; close(m); return WIZSER_ERR(e); }
  return (uint64_t)m;
}
/* the path of its terminal side ("" with an error) */
static _Thread_local char wizser_name[256];
const char *wizser_pty_name(uint64_t m) {
  if (ptsname_r((int)m, wizser_name, sizeof wizser_name) != 0) wizser_name[0] = 0;
  return wizser_name;
}
