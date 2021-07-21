/* An extremely minimalist syscalls.c for newlib
 * Based on riscv newlib libgloss/riscv/sys_*.c
 *
 * Copyright 2019 Claire Wolf
 * Copyright 2019 ETH Zürich and University of Bologna
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH
 * REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY
 * AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT,
 * INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM
 * LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR
 * OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR
 * PERFORMANCE OF THIS SOFTWARE.
 */

#include <sys/stat.h>
#include <sys/timeb.h>
#include <sys/times.h>
#include <sys/utime.h>
#include <newlib.h>
#include <unistd.h>
#include <errno.h>
#include <machine/syscall.h>
#include <assert.h>
#undef errno
extern int errno;

/* write to this reg for outputting strings */
#define STDOUT_REG 0x10000000
/* write test result of program to this reg */
#define RESULT_REG 0x20000000
/* write exit value of program to this reg */
#define EXIT_REG 0x20000004

#define STDOUT_FILENO 1

/* It turns out that older newlib versions use different symbol names which goes
 * against newlib recommendations. Anyway this is fixed in later version.
 */
#if __NEWLIB__ <= 2 && __NEWLIB_MINOR__ <= 5
#define _sbrk sbrk
#define _write write
#define _close close
#define _lseek lseek
#define _read read
#define _fstat fstat
#define _isatty isatty
#endif
/* Upstream newlib now defines this in libgloss/riscv/internal_syscall.h.  */
long
__syscall_error(long a0)
{
  errno = -a0;
  return -1;
}

void unimplemented_syscall()
{
  const char *p = "BSP: Unimplemented system call called!\n";
  while (*p)
    *(volatile int *)STDOUT_REG = *(p++);
}

int nanosleep(const struct timespec *rqtp, struct timespec *rmtp)
{
  errno = ENOSYS;
  return -1;
}

int _access(const char *file, int mode)
{
  errno = ENOSYS;
  return -1;
}

int _chdir(const char *path)
{
  errno = ENOSYS;
  return -1;
}

int _chmod(const char *path, mode_t mode)
{
  errno = ENOSYS;
  return -1;
}

int _chown(const char *path, uid_t owner, gid_t group)
{
  errno = ENOSYS;
  return -1;
}

int _close(int file)
{
  return -1;
}

int _execve(const char *name, char *const argv[], char *const env[])
{
  errno = ENOMEM;
  return -1;
}

void _exit(int exit_status)
{
  *(volatile int *)EXIT_REG = exit_status;
  asm volatile("wfi");
  /* _exit should not return */
  while (1) {};
}

int _faccessat(int dirfd, const char *file, int mode, int flags)
{
  errno = ENOSYS;
  return -1;
}

int _fork(void)
{
  errno = EAGAIN;
  return -1;
}

int _fstat(int file, struct stat *st)
{
  st->st_mode = S_IFCHR;
  return 0;
  // errno = -ENOSYS;
  // return -1;
}

int _fstatat(int dirfd, const char *file, struct stat *st, int flags)
{
  errno = ENOSYS;
  return -1;
}

int _ftime(struct timeb *tp)
{
  errno = ENOSYS;
  return -1;
}

char *_getcwd(char *buf, size_t size)
{
  errno = -ENOSYS;
  return NULL;
}

int _getpid()
{
  return 1;
}

int _gettimeofday(struct timeval *tp, void *tzp)
{
  errno = -ENOSYS;
  return -1;
}

int _isatty(int file)
{
  return (file == STDOUT_FILENO);
}

int _kill(int pid, int sig)
{
  errno = EINVAL;
  return -1;
}

int _link(const char *old_name, const char *new_name)
{
  errno = EMLINK;
  return -1;
}

off_t _lseek(int file, off_t ptr, int dir)
{
  return 0;
}

int _lstat(const char *file, struct stat *st)
{
  errno = ENOSYS;
  return -1;
}

int _open(const char *name, int flags, int mode)
{
  return -1;
}

int _openat(int dirfd, const char *name, int flags, int mode)
{
  errno = ENOSYS;
  return -1;
}

ssize_t _read(int file, void *ptr, size_t len)
{
  return 0;
}

int _stat(const char *file, struct stat *st)
{
  st->st_mode = S_IFCHR;
  return 0;
  // errno = ENOSYS;
  // return -1;
}

long _sysconf(int name)
{

  return -1;
}

clock_t _times(struct tms *buf)
{
  return -1;
}

int _unlink(const char *name)
{
  errno = ENOENT;
  return -1;
}

int _utime(const char *path, const struct utimbuf *times)
{
  errno = ENOSYS;
  return -1;
}

int _wait(int *status)
{
  errno = ECHILD;
  return -1;
}

ssize_t _write(int file, const void *ptr, size_t len)
{
  const char *cptr = (char *)ptr;
  if (file != STDOUT_FILENO)
    {
      errno = ENOSYS;
      return -1;
    }

  const void *eptr = cptr + len;
  while (cptr != eptr)
    *(volatile int *)STDOUT_REG = *cptr++;
  return len;
}

extern char __heap_start[];
extern char __heap_end[];
static char *brk = __heap_start;

int _brk(void *addr)
{
  brk = addr;
  return 0;
}

void *_sbrk(ptrdiff_t incr)
{
  char *old_brk = brk;
  register long sp asm("sp");

  char *new_brk = brk += incr;
  if (new_brk < (char *) sp && new_brk < __heap_end)
    {
      brk = new_brk;

      return old_brk;
    }
  else
    {
      errno = ENOMEM;
      return (void *) -1;
    }
}

void handle_syscall (long a0,
		     long a1,
		     long a2,
		     long a3,
		     __attribute__((unused)) long a4,
		     __attribute__((unused)) long a5,
		     __attribute__((unused)) long a6,
		     long a7) {
  #ifdef __riscv_32e
    register long syscall_id asm("t0");
  #else
    long syscall_id = a7;
  #endif

  switch (syscall_id) {
    case SYS_exit:
      _exit (a0);
      break;
    case SYS_read:
      _read (a0, (void *) a1, a2);
      break;
    case SYS_write:
      _write (a0, (const void *) a1, a2);
      break;
    case SYS_getpid:
      _getpid ();
      break;
    case SYS_kill:
      _kill (a0, a1);
      break;
    case SYS_open:
      _open ((const char *) a0, a1, a2);
      break;
    case SYS_openat:
      _openat (a0, (const char *) a1, a2, a3);
      break;
    case SYS_close:
      _close (a0);
      break;
    case SYS_lseek:
      _lseek (a0, a1, a2);
      break;
    case SYS_brk:
      _brk ((void *) a0);
      break;
    case SYS_link:
      _link ((const char *) a0, (const char *) a1);
      break;
    case SYS_unlink:
      _unlink ((const char *) a0);
      break;
    case SYS_chdir:
      _chdir ((const char *) a0);
      break;
    case SYS_getcwd:
      _getcwd ((char *) a0, a1);
      break;
    case SYS_stat:
      _stat ((const char *) a0, (struct stat *) a1);
      break;
    case SYS_fstat:
      _fstat (a0, (struct stat *) a1);
      break;
    case SYS_lstat:
      _lstat ((const char *) a0, (struct stat *) a1);
      break;
    case SYS_fstatat:
      _fstatat (a0, (const char *) a1, (struct stat *) a2, a3);
      break;
    case SYS_access:
      _access ((const char *) a0, a1);
      break;
    case SYS_faccessat:
      _faccessat (a0, (const char *) a1, a2, a3);
      break;
    case SYS_gettimeofday:
      _gettimeofday ((struct timeval *) a0, (void *) a1);
      break;
    case SYS_times:
      _times ((struct tms *) a0);
      break;
    default:
      unimplemented_syscall ();
      break;
  }
}
