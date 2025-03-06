/* Copyright (c) 2017  SiFive Inc. All rights reserved.

   This copyrighted material is made available to anyone wishing to use,
   modify, copy, or redistribute it subject to the terms and conditions
   of the FreeBSD License.   This program is distributed in the hope that
   it will be useful, but WITHOUT ANY WARRANTY expressed or implied,
   including the implied warranties of MERCHANTABILITY or FITNESS FOR
   A PARTICULAR PURPOSE.  A copy of this license is available at
   http://www.opensource.org/licenses.
*/

#ifndef _MACHINE_SYSCALL_H
#define _MACHINE_SYSCALL_H

#define SYS_getcwd 17
#define SYS_dup 23
#define SYS_fcntl 25
#define SYS_faccessat 48
#define SYS_chdir 49
#define SYS_openat 56
#define SYS_close 57
#define SYS_getdents 61
#define SYS_lseek 62
#define SYS_read 63
#define SYS_write 64
#define SYS_writev 66
#define SYS_pread 67
#define SYS_pwrite 68
#define SYS_fstatat 79
#define SYS_fstat 80
#define SYS_exit 93
#define SYS_exit_group 94
#define SYS_kill 129
#define SYS_rt_sigaction 134
#define SYS_times 153
#define SYS_uname 160
#define SYS_gettimeofday 169
#define SYS_getpid 172
#define SYS_getuid 174
#define SYS_geteuid 175
#define SYS_getgid 176
#define SYS_getegid 177
#define SYS_brk 214
#define SYS_munmap 215
#define SYS_mremap 216
#define SYS_mmap 222
#define SYS_clock_gettime64 403
#define SYS_open 1024
#define SYS_link 1025
#define SYS_unlink 1026
#define SYS_mkdir 1030
#define SYS_access 1033
#define SYS_stat 1038
#define SYS_lstat 1039
#define SYS_time 1062
#define SYS_getmainvars 2011

/* Semihosting operations.  */
#define SEMIHOST_clock 0x10
#define SEMIHOST_close 0x02
#define SEMIHOST_elapsed 0x30
#define SEMIHOST_errno 0x13
#define SEMIHOST_exit 0x18
#define SEMIHOST_exit_extended 0x20
#define SEMIHOST_flen 0x0C
#define SEMIHOST_get_cmdline 0x15
#define SEMIHOST_heapinfo 0x16
#define SEMIHOST_iserror 0x08
#define SEMIHOST_istty 0x09
#define SEMIHOST_open 0x01
#define SEMIHOST_read 0x06
#define SEMIHOST_readc 0x07
#define SEMIHOST_remove 0x0E
#define SEMIHOST_rename 0x0F
#define SEMIHOST_seek 0x0A
#define SEMIHOST_system 0x12
#define SEMIHOST_tickfreq 0x31
#define SEMIHOST_time 0x11
#define SEMIHOST_tmpnam 0x0D
#define SEMIHOST_write 0x05
#define SEMIHOST_writec 0x03
#define SEMIHOST_write0 0x04
#endif
