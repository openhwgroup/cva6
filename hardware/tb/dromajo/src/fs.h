/*
 * Filesystem abstraction
 *
 * Copyright (c) 2016 Fabrice Bellard
 * Copyright (C) 2018,2019, Esperanto Technologies Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License")
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * THIS FILE IS BASED ON THE RISCVEMU SOURCE CODE WHICH IS DISTRIBUTED
 * UNDER THE FOLLOWING LICENSE:
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */

/* FSQID.type */
#define P9_QTDIR 0x80
#define P9_QTAPPEND 0x40
#define P9_QTEXCL 0x20
#define P9_QTMOUNT 0x10
#define P9_QTAUTH 0x08
#define P9_QTTMP 0x04
#define P9_QTSYMLINK 0x02
#define P9_QTLINK 0x01
#define P9_QTFILE 0x00

/* mode bits */
#define P9_S_IRWXUGO 0x01FF
#define P9_S_ISVTX   0x0200
#define P9_S_ISGID   0x0400
#define P9_S_ISUID   0x0800

#define P9_S_IFMT   0xF000
#define P9_S_IFIFO  0x1000
#define P9_S_IFCHR  0x2000
#define P9_S_IFDIR  0x4000
#define P9_S_IFBLK  0x6000
#define P9_S_IFREG  0x8000
#define P9_S_IFLNK  0xA000
#define P9_S_IFSOCK 0xC000

/* flags for lopen()/lcreate() */
#define P9_O_RDONLY        0x00000000
#define P9_O_WRONLY        0x00000001
#define P9_O_RDWR          0x00000002
#define P9_O_NOACCESS      0x00000003
#define P9_O_CREAT         0x00000040
#define P9_O_EXCL          0x00000080
#define P9_O_NOCTTY        0x00000100
#define P9_O_TRUNC         0x00000200
#define P9_O_APPEND        0x00000400
#define P9_O_NONBLOCK      0x00000800
#define P9_O_DSYNC         0x00001000
#define P9_O_FASYNC        0x00002000
#define P9_O_DIRECT        0x00004000
#define P9_O_LARGEFILE     0x00008000
#define P9_O_DIRECTORY     0x00010000
#define P9_O_NOFOLLOW      0x00020000
#define P9_O_NOATIME       0x00040000
#define P9_O_CLOEXEC       0x00080000
#define P9_O_SYNC          0x00100000

/* for fs_setattr() */
#define P9_SETATTR_MODE      0x00000001
#define P9_SETATTR_UID       0x00000002
#define P9_SETATTR_GID       0x00000004
#define P9_SETATTR_SIZE      0x00000008
#define P9_SETATTR_ATIME     0x00000010
#define P9_SETATTR_MTIME     0x00000020
#define P9_SETATTR_CTIME     0x00000040
#define P9_SETATTR_ATIME_SET 0x00000080
#define P9_SETATTR_MTIME_SET 0x00000100

#define P9_EPERM     1
#define P9_ENOENT    2
#define P9_EIO       5
#define	P9_EEXIST    17
#define	P9_ENOTDIR   20
#define P9_EINVAL    22
#define	P9_ENOSPC    28
#define P9_ENOTEMPTY 39
#define P9_EPROTO    71
#define P9_ENOTSUP   524

typedef struct FSDevice FSDevice;
typedef struct FSFile FSFile;

typedef struct {
    uint32_t f_bsize;
    uint64_t f_blocks;
    uint64_t f_bfree;
    uint64_t f_bavail;
    uint64_t f_files;
    uint64_t f_ffree;
} FSStatFS;

typedef struct {
    uint8_t type; /* P9_IFx */
    uint32_t version;
    uint64_t path;
} FSQID;

typedef struct {
    FSQID qid;
    uint32_t st_mode;
    uint32_t st_uid;
    uint32_t st_gid;
    uint64_t st_nlink;
    uint64_t st_rdev;
    uint64_t st_size;
    uint64_t st_blksize;
    uint64_t st_blocks;
    uint64_t st_atime_sec;
    uint32_t st_atime_nsec;
    uint64_t st_mtime_sec;
    uint32_t st_mtime_nsec;
    uint64_t st_ctime_sec;
    uint32_t st_ctime_nsec;
} FSStat;

#define P9_LOCK_TYPE_RDLCK 0
#define P9_LOCK_TYPE_WRLCK 1
#define P9_LOCK_TYPE_UNLCK 2

#define P9_LOCK_FLAGS_BLOCK 1
#define P9_LOCK_FLAGS_RECLAIM 2

#define P9_LOCK_SUCCESS 0
#define P9_LOCK_BLOCKED 1
#define P9_LOCK_ERROR   2
#define P9_LOCK_GRACE   3

#define FSCMD_NAME ".fscmd"

typedef struct {
    uint8_t type;
    uint32_t flags;
    uint64_t start;
    uint64_t length;
    uint32_t proc_id;
    char *client_id;
} FSLock;

typedef void FSOpenCompletionFunc(FSDevice *fs, FSQID *qid, int err,
                                  void *opaque);

struct FSDevice {
    void (*fs_end)(FSDevice *s);
    void (*fs_delete)(FSDevice *s, FSFile *f);
    void (*fs_statfs)(FSDevice *fs, FSStatFS *st);
    int (*fs_attach)(FSDevice *fs, FSFile **pf, FSQID *qid, uint32_t uid,
                     const char *uname, const char *aname);
    int (*fs_walk)(FSDevice *fs, FSFile **pf, FSQID *qids,
                   FSFile *f, int n, char **names);
    int (*fs_mkdir)(FSDevice *fs, FSQID *qid, FSFile *f,
                    const char *name, uint32_t mode, uint32_t gid);
    int (*fs_open)(FSDevice *fs, FSQID *qid, FSFile *f, uint32_t flags,
                   FSOpenCompletionFunc *cb, void *opaque);
    int (*fs_create)(FSDevice *fs, FSQID *qid, FSFile *f, const char *name, 
                     uint32_t flags, uint32_t mode, uint32_t gid);
    int (*fs_stat)(FSDevice *fs, FSFile *f, FSStat *st);
    int (*fs_setattr)(FSDevice *fs, FSFile *f, uint32_t mask,
                      uint32_t mode, uint32_t uid, uint32_t gid,
                      uint64_t size, uint64_t atime_sec, uint64_t atime_nsec,
                      uint64_t mtime_sec, uint64_t mtime_nsec);
    void (*fs_close)(FSDevice *fs, FSFile *f);
    int (*fs_readdir)(FSDevice *fs, FSFile *f, uint64_t offset,
                      uint8_t *buf, int count);
    int (*fs_read)(FSDevice *fs, FSFile *f, uint64_t offset,
            uint8_t *buf, int count);
    int (*fs_write)(FSDevice *fs, FSFile *f, uint64_t offset,
             const uint8_t *buf, int count);
    int (*fs_link)(FSDevice *fs, FSFile *df, FSFile *f, const char *name);
    int (*fs_symlink)(FSDevice *fs, FSQID *qid,
                      FSFile *f, const char *name, const char *symgt, uint32_t gid);
    int (*fs_mknod)(FSDevice *fs, FSQID *qid,
                    FSFile *f, const char *name, uint32_t mode, uint32_t major,
                    uint32_t minor, uint32_t gid);
    int (*fs_readlink)(FSDevice *fs, char *buf, int buf_size, FSFile *f);
    int (*fs_renameat)(FSDevice *fs, FSFile *f, const char *name, 
                       FSFile *new_f, const char *new_name);
    int (*fs_unlinkat)(FSDevice *fs, FSFile *f, const char *name);
    int (*fs_lock)(FSDevice *fs, FSFile *f, const FSLock *lock);
    int (*fs_getlock)(FSDevice *fs, FSFile *f, FSLock *lock);
};

FSDevice *fs_disk_init(const char *root_path);
FSDevice *fs_mem_init(void);
FSDevice *fs_net_init(const char *url, void (*start)(void *opaque), void *opaque);
void fs_net_set_pwd(FSDevice *fs, const char *pwd);
void fs_export_file(const char *filename,
                    const uint8_t *buf, int buf_len);
void fs_end(FSDevice *fs);

FSFile *fs_dup(FSDevice *fs, FSFile *f);
FSFile *fs_walk_path1(FSDevice *fs, FSFile *f, const char *path,
                      char **pname);
FSFile *fs_walk_path(FSDevice *fs, FSFile *f, const char *path);
