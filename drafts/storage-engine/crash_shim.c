/* Quire crash matrix: an LD_PRELOAD shim that kills the process at a named
   checkpoint of the commit or compaction protocol.

   The point of the shim is that the engine is not modified for the test: the
   same `Durable.wiz`/`Compact.wiz` code writes the file, and the shim decides,
   from `QUIRE_CRASH`, when the process gets `SIGKILL`.  A checkpoint is one of:

     commit:    before-pages, during-page, after-pages, after-fdatasync,
                torn-meta, after-meta-write, after-fsync, torn-page-published
     compaction: compact-during-temp, compact-torn-temp,
                compact-before-temp-fsync, compact-after-temp-fsync,
                compact-before-rename, compact-after-rename,
                compact-after-dir-fsync

   The file under test is `QUIRE_DB` (absolute); the compaction temp file is
   `QUIRE_DB.compact`.  A write is classified by its descriptor's path and the
   file offset: the meta slots are 96 bytes at offset 0 or 4096, a data or
   registry page is 4096 bytes at an offset of at least 8192.

   "Torn" checkpoints write half the bytes and either die immediately or (for
   torn-page-published) lie to the caller about the write length so the commit
   runs to its fsync, leaving a checksum-invalid page under a valid meta.  All
   death is `kill(getpid(), SIGKILL)`: the parent sees signal 9, exactly as for
   a `kill -9` from outside.  (SIGKILL cannot be caught; no finalizer runs.)

   Build: cc -shared -fPIC -O2 -o crash_shim.so crash_shim.c -ldl        */

#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

static const char *crash;
static const char *db;
static ssize_t (*real_write)(int, const void *, size_t);
static int (*real_fsync)(int);
static int (*real_fdatasync)(int);
static int (*real_rename)(const char *, const char *);
static int saw_data_write;
static int saw_meta_write;
static int saw_temp_write;
static int renamed;

static void init(void) __attribute__((constructor));
static void init(void) {
  crash = getenv("QUIRE_CRASH");
  db = getenv("QUIRE_DB");
  real_write = (ssize_t (*)(int, const void *, size_t))dlsym(RTLD_NEXT, "write");
  real_fsync = (int (*)(int))dlsym(RTLD_NEXT, "fsync");
  real_fdatasync = (int (*)(int))dlsym(RTLD_NEXT, "fdatasync");
  real_rename = (int (*)(const char *, const char *))dlsym(RTLD_NEXT, "rename");
}

static int at(const char *name) {
  return crash && *crash && strcmp(crash, name) == 0;
}

/* The path a descriptor names, or 0.  The suffix " (deleted)" is dropped: it is
   not part of the name the engine opened. */
static int path_of(int fd, char *buf, size_t n) {
  char link[64];
  int m = snprintf(link, sizeof link, "/proc/self/fd/%d", fd);
  if (m < 0 || (size_t)m >= sizeof link) return 0;
  ssize_t k = readlink(link, buf, n - 1);
  if (k < 0) return 0;
  buf[k] = 0;
  char *d = strstr(buf, " (deleted)");
  if (d) *d = 0;
  return 1;
}

static int is_db(const char *p) { return db && strcmp(p, db) == 0; }

static int is_tmp(const char *p) {
  if (!db) return 0;
  size_t n = strlen(db);
  return strncmp(p, db, n) == 0 && strcmp(p + n, ".compact") == 0;
}

static int is_dir_fd(int fd) {
  struct stat st;
  return fstat(fd, &st) == 0 && S_ISDIR(st.st_mode);
}

/* SIGKILL, then an exit the compiler can see.  No atexit, no finalizer, no
   flush: the same state a `kill -9` from the parent leaves. */
static void die(void) {
  kill(getpid(), SIGKILL);
  _exit(137);
}

ssize_t write(int fd, const void *buf, size_t count) {
  if (!crash || !*crash) return real_write(fd, buf, count);
  char p[4096];
  if (!path_of(fd, p, sizeof p)) return real_write(fd, buf, count);
  off_t off = lseek(fd, 0, SEEK_CUR);

  if (is_db(p)) {
    /* The first data/registry page of the commit. */
    if (count == 4096 && off >= 8192 && !saw_data_write) {
      saw_data_write = 1;
      if (at("before-pages")) die();
      if (at("during-page")) {
        real_write(fd, buf, count / 2);
        die();
      }
      if (at("torn-page-published")) {
        /* Half a page plus one stale byte in the second half, but tell the
           caller all of it is written.  The commit continues; its meta is
           written and fsynced; the page checksum fails on the next open.  (A
           plain half write of this page would still verify: the record area is
           in the first 96 bytes and the rest of a freshly built page is zero,
           so the skipped half is exactly the zeros the checksum covered.) */
        char junk = (char)0xAA;
        real_write(fd, buf, count / 2);
        lseek(fd, off + (off_t)(count / 2), SEEK_SET);
        real_write(fd, &junk, 1);
        return (ssize_t)count;
      }
    }
    /* The 96-byte meta slot. */
    if (count == 96 && (off == 0 || off == 4096) && !saw_meta_write) {
      saw_meta_write = 1;
      if (at("torn-meta")) {
        real_write(fd, buf, 48);
        die();
      }
      if (at("after-meta-write")) {
        real_write(fd, buf, count);
        die();
      }
    }
  }

  /* The first live page of the compacted image. */
  if (is_tmp(p) && count == 4096 && !saw_temp_write) {
    saw_temp_write = 1;
    if (at("compact-during-temp")) {
      real_write(fd, buf, count / 2);
      die();
    }
    if (at("compact-torn-temp")) {
      real_write(fd, buf, count / 2);
      return (ssize_t)count;
    }
  }

  return real_write(fd, buf, count);
}

int fdatasync(int fd) {
  if (!crash || !*crash) return real_fdatasync(fd);
  char p[4096];
  if (path_of(fd, p, sizeof p) && is_db(p)) {
    if (at("after-pages")) die();
    if (at("after-fdatasync")) {
      int r = real_fdatasync(fd);
      (void)r;
      die();
    }
  }
  return real_fdatasync(fd);
}

int fsync(int fd) {
  if (!crash || !*crash) return real_fsync(fd);
  char p[4096];
  if (path_of(fd, p, sizeof p)) {
    if (is_db(p)) {
      if (at("after-fsync") || at("torn-page-published")) {
        real_fsync(fd);
        die();
      }
    } else if (is_tmp(p)) {
      if (at("compact-before-temp-fsync") || at("compact-torn-temp")) die();
      if (at("compact-after-temp-fsync")) {
        real_fsync(fd);
        die();
      }
    } else if (renamed && at("compact-after-dir-fsync") && is_dir_fd(fd)) {
      real_fsync(fd);
      die();
    }
  }
  return real_fsync(fd);
}

int rename(const char *from, const char *to) {
  if (at("compact-before-rename")) die();
  int r = real_rename(from, to);
  if (r == 0) {
    renamed = 1;
    if (at("compact-after-rename")) {
      /* The new name is in the directory entry; the directory fsync has not
         run.  This is the documented hole of the two-file swap. */
      die();
    }
  }
  return r;
}
