/*
 * Filesystem on disk
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
#if !defined(__APPLE__)
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <inttypes.h>
#include <assert.h>
#include <stdarg.h>
#include <sys/statfs.h>
#include <sys/stat.h>
#include <sys/sysmacros.h>
#include <unistd.h>
#include <fcntl.h>
#include <dirent.h>
#include <errno.h>

#include "cutils.h"
#include "list.h"
#include "fs.h"

typedef struct {
    FSDevice common;
    char *root_path;
} FSDeviceDisk;

static void fs_close(FSDevice *fs, FSFile *f);

struct FSFile {
    uint32_t uid;
    char *path; /* complete path */
    BOOL is_opened;
    BOOL is_dir;
    union {
        int fd;
        DIR *dirp;
    } u;
};

static void fs_delete(FSDevice *fs, FSFile *f)
{
    if (f->is_opened)
        fs_close(fs, f);
    free(f->path);
    free(f);
}

/* warning: path belong to fid_create() */
static FSFile *fid_create(FSDevice *s1, char *path, uint32_t uid)
{
    FSFile *f = (FSFile *)mallocz(sizeof *f);
    f->path = path;
    f->uid = uid;
    return f;
}


static int errno_table[][2] = {
    { P9_EPERM, EPERM },
    { P9_ENOENT, ENOENT },
    { P9_EIO, EIO },
    { P9_EEXIST, EEXIST },
    { P9_EINVAL, EINVAL },
    { P9_ENOSPC, ENOSPC },
    { P9_ENOTEMPTY, ENOTEMPTY },
    { P9_EPROTO, EPROTO },
    { P9_ENOTSUP, ENOTSUP },
};

static int errno_to_p9(int err)
{
    if (err == 0)
        return 0;
    for (unsigned int i = 0; i < countof(errno_table); i++) {
        if (err == errno_table[i][1])
            return errno_table[i][0];
    }
    return P9_EINVAL;
}

static int open_flags[][2] = {
    { P9_O_CREAT, O_CREAT },
    { P9_O_EXCL, O_EXCL },
    //    { P9_O_NOCTTY, O_NOCTTY },
    { P9_O_TRUNC, O_TRUNC },
    { P9_O_APPEND, O_APPEND },
    { P9_O_NONBLOCK, O_NONBLOCK },
    { P9_O_DSYNC, O_DSYNC },
    //    { P9_O_FASYNC, O_FASYNC },
    //    { P9_O_DIRECT, O_DIRECT },
    //    { P9_O_LARGEFILE, O_LARGEFILE },
    //    { P9_O_DIRECTORY, O_DIRECTORY },
    { P9_O_NOFOLLOW, O_NOFOLLOW },
    //    { P9_O_NOATIME, O_NOATIME },
    //    { P9_O_CLOEXEC, O_CLOEXEC },
    { P9_O_SYNC, O_SYNC },
};

static int p9_flags_to_host(int flags)
{
    int ret = (flags & P9_O_NOACCESS);
    for (unsigned int i = 0; i < countof(open_flags); i++) {
        if (flags & open_flags[i][0])
            ret |= open_flags[i][1];
    }
    return ret;
}

static void stat_to_qid(FSQID *qid, const struct stat *st)
{
    if (S_ISDIR(st->st_mode))
        qid->type = P9_QTDIR;
    else if (S_ISLNK(st->st_mode))
        qid->type = P9_QTSYMLINK;
    else
        qid->type = P9_QTFILE;
    qid->version = 0; /* no caching on client */
    qid->path = st->st_ino;
}

static void fs_statfs(FSDevice *fs1, FSStatFS *st)
{
    FSDeviceDisk *fs = (FSDeviceDisk *)fs1;
    struct statfs st1;
    statfs(fs->root_path, &st1);
    st->f_bsize = st1.f_bsize;
    st->f_blocks = st1.f_blocks;
    st->f_bfree = st1.f_bfree;
    st->f_bavail = st1.f_bavail;
    st->f_files = st1.f_files;
    st->f_ffree = st1.f_ffree;
}

static char *compose_path(const char *path, const char *name)
{
    int path_len = strlen(path);
    int name_len = strlen(name);
    char *d = (char *)malloc(path_len + 1 + name_len + 1);

    memcpy(d, path, path_len);
    d[path_len] = '/';
    memcpy(d + path_len + 1, name, name_len + 1);
    return d;
}

static int fs_attach(FSDevice *fs1, FSFile **pf,
                     FSQID *qid, uint32_t uid,
                     const char *uname, const char *aname)
{
    FSDeviceDisk *fs = (FSDeviceDisk *)fs1;
    struct stat st;
    FSFile *f;

    if (lstat(fs->root_path, &st) != 0) {
        *pf = NULL;
        return -errno_to_p9(errno);
    }
    f = fid_create(fs1, strdup(fs->root_path), uid);
    stat_to_qid(qid, &st);
    *pf = f;
    return 0;
}

static int fs_walk(FSDevice *fs, FSFile **pf, FSQID *qids,
                   FSFile *f, int n, char **names)
{
    char *path, *path1;
    struct stat st;
    int i;

    path = strdup(f->path);
    for (i = 0; i < n; i++) {
        path1 = compose_path(path, names[i]);
        if (lstat(path1, &st) != 0) {
            free(path1);
            break;
        }
        free(path);
        path = path1;
        stat_to_qid(&qids[i], &st);
    }
    *pf = fid_create(fs, path, f->uid);
    return i;
}


static int fs_mkdir(FSDevice *fs, FSQID *qid, FSFile *f,
                    const char *name, uint32_t mode, uint32_t gid)
{
    char *path;
    struct stat st;

    path = compose_path(f->path, name);
    if (mkdir(path, mode) < 0) {
        free(path);
        return -errno_to_p9(errno);
    }
    if (lstat(path, &st) != 0) {
        free(path);
        return -errno_to_p9(errno);
    }
    free(path);
    stat_to_qid(qid, &st);
    return 0;
}

static int fs_open(FSDevice *fs, FSQID *qid, FSFile *f, uint32_t flags,
                   FSOpenCompletionFunc *cb, void *opaque)
{
    struct stat st;
    fs_close(fs, f);

    if (stat(f->path, &st) != 0)
        return -errno_to_p9(errno);
    stat_to_qid(qid, &st);

    if (flags & P9_O_DIRECTORY) {
        DIR *dirp;
        dirp = opendir(f->path);
        if (!dirp)
            return -errno_to_p9(errno);
        f->is_opened = TRUE;
        f->is_dir = TRUE;
        f->u.dirp = dirp;
    } else {
        int fd;
        fd = open(f->path, p9_flags_to_host(flags) & ~O_CREAT);
        if (fd < 0)
            return -errno_to_p9(errno);
        f->is_opened = TRUE;
        f->is_dir = FALSE;
        f->u.fd = fd;
    }
    return 0;
}

static int fs_create(FSDevice *fs, FSQID *qid, FSFile *f, const char *name,
                     uint32_t flags, uint32_t mode, uint32_t gid)
{
    struct stat st;
    char *path;
    int ret, fd;

    fs_close(fs, f);

    path = compose_path(f->path, name);
    fd = open(path, p9_flags_to_host(flags) | O_CREAT, mode);
    if (fd < 0) {
        free(path);
        return -errno_to_p9(errno);
    }
    ret = lstat(path, &st);
    if (ret != 0) {
        free(path);
        close(fd);
        return -errno_to_p9(errno);
    }
    free(f->path);
    f->path = path;
    f->is_opened = TRUE;
    f->is_dir = FALSE;
    f->u.fd = fd;
    stat_to_qid(qid, &st);
    return 0;
}

static int fs_readdir(FSDevice *fs, FSFile *f, uint64_t offset,
                      uint8_t *buf, int count)
{
    struct dirent *de;
    int len, pos, name_len, type, d_type;

    if (!f->is_opened || !f->is_dir)
        return -P9_EPROTO;
    if (offset == 0)
        rewinddir(f->u.dirp);
    else
        seekdir(f->u.dirp, offset);
    pos = 0;
    for (;;) {
        de = readdir(f->u.dirp);
        if (de == NULL)
            break;
        name_len = strlen(de->d_name);
        len = 13 + 8 + 1 + 2 + name_len;
        if ((pos + len) > count)
            break;
        offset = telldir(f->u.dirp);
        d_type = de->d_type;
        if (d_type == DT_UNKNOWN) {
            char *path;
            struct stat st;
            path = compose_path(f->path, de->d_name);
            if (lstat(path, &st) == 0) {
                d_type = st.st_mode >> 12;
            } else {
                d_type = DT_REG; /* default */
            }
            free(path);
        }
        if (d_type == DT_DIR)
            type = P9_QTDIR;
        else if (d_type == DT_LNK)
            type = P9_QTSYMLINK;
        else
            type = P9_QTFILE;
        buf[pos++] = type;
        put_le32(buf + pos, 0); /* version */
        pos += 4;
        put_le64(buf + pos, de->d_ino);
        pos += 8;
        put_le64(buf + pos, offset);
        pos += 8;
        buf[pos++] = d_type;
        put_le16(buf + pos, name_len);
        pos += 2;
        memcpy(buf + pos, de->d_name, name_len);
        pos += name_len;
    }
    return pos;
}

static int fs_read(FSDevice *fs, FSFile *f, uint64_t offset,
                   uint8_t *buf, int count)
{
    int ret;

    if (!f->is_opened || f->is_dir)
        return -P9_EPROTO;
    ret = pread(f->u.fd, buf, count, offset);
    if (ret < 0)
        return -errno_to_p9(errno);
    else
        return ret;
}

static int fs_write(FSDevice *fs, FSFile *f, uint64_t offset,
                    const uint8_t *buf, int count)
{
    int ret;

    if (!f->is_opened || f->is_dir)
        return -P9_EPROTO;
    ret = pwrite(f->u.fd, buf, count, offset);
    if (ret < 0)
        return -errno_to_p9(errno);
    else
        return ret;
}

static void fs_close(FSDevice *fs, FSFile *f)
{
    if (!f->is_opened)
        return;
    if (f->is_dir)
        closedir(f->u.dirp);
    else
        close(f->u.fd);
    f->is_opened = FALSE;
}

static int fs_stat(FSDevice *fs, FSFile *f, FSStat *st)
{
    struct stat st1;

    if (lstat(f->path, &st1) != 0)
        return -P9_ENOENT;
    stat_to_qid(&st->qid, &st1);
    st->st_mode = st1.st_mode;
    st->st_uid = st1.st_uid;
    st->st_gid = st1.st_gid;
    st->st_nlink = st1.st_nlink;
    st->st_rdev = st1.st_rdev;
    st->st_size = st1.st_size;
    st->st_blksize = st1.st_blksize;
    st->st_blocks = st1.st_blocks;
    st->st_atime_sec = st1.st_atim.tv_sec;
    st->st_atime_nsec = st1.st_atim.tv_nsec;
    st->st_mtime_sec = st1.st_mtim.tv_sec;
    st->st_mtime_nsec = st1.st_mtim.tv_nsec;
    st->st_ctime_sec = st1.st_ctim.tv_sec;
    st->st_ctime_nsec = st1.st_ctim.tv_nsec;
    return 0;
}

static int fs_setattr(FSDevice *fs, FSFile *f, uint32_t mask,
                      uint32_t mode, uint32_t uid, uint32_t gid,
                      uint64_t size, uint64_t atime_sec, uint64_t atime_nsec,
                      uint64_t mtime_sec, uint64_t mtime_nsec)
{
    BOOL ctime_updated = FALSE;

    if (mask & (P9_SETATTR_UID | P9_SETATTR_GID)) {
        if (lchown(f->path, (mask & P9_SETATTR_UID) ? uid : -1,
                   (mask & P9_SETATTR_GID) ? gid : -1) < 0)
            return -errno_to_p9(errno);
        ctime_updated = TRUE;
    }
    /* must be done after uid change for suid */
    if (mask & P9_SETATTR_MODE) {
        if (chmod(f->path, mode) < 0)
            return -errno_to_p9(errno);
        ctime_updated = TRUE;
    }
    if (mask & P9_SETATTR_SIZE) {
        if (truncate(f->path, size) < 0)
            return -errno_to_p9(errno);
        ctime_updated = TRUE;
    }
    if (mask & (P9_SETATTR_ATIME | P9_SETATTR_MTIME)) {
        struct timespec ts[2];
        if (mask & P9_SETATTR_ATIME) {
            if (mask & P9_SETATTR_ATIME_SET) {
                ts[0].tv_sec = atime_sec;
                ts[0].tv_nsec = atime_nsec;
            } else {
                ts[0].tv_sec = 0;
                ts[0].tv_nsec = UTIME_NOW;
            }
        } else {
            ts[0].tv_sec = 0;
            ts[0].tv_nsec = UTIME_OMIT;
        }
        if (mask & P9_SETATTR_MTIME) {
            if (mask & P9_SETATTR_MTIME_SET) {
                ts[1].tv_sec = mtime_sec;
                ts[1].tv_nsec = mtime_nsec;
            } else {
                ts[1].tv_sec = 0;
                ts[1].tv_nsec = UTIME_NOW;
            }
        } else {
            ts[1].tv_sec = 0;
            ts[1].tv_nsec = UTIME_OMIT;
        }
        if (utimensat(AT_FDCWD, f->path, ts, AT_SYMLINK_NOFOLLOW) < 0)
            return -errno_to_p9(errno);
        ctime_updated = TRUE;
    }
    if ((mask & P9_SETATTR_CTIME) && !ctime_updated) {
        if (lchown(f->path, -1, -1) < 0)
            return -errno_to_p9(errno);
    }
    return 0;
}

static int fs_link(FSDevice *fs, FSFile *df, FSFile *f, const char *name)
{
    char *path;

    path = compose_path(df->path, name);
    if (link(f->path, path) < 0) {
        free(path);
        return -errno_to_p9(errno);
    }
    free(path);
    return 0;
}

static int fs_symlink(FSDevice *fs, FSQID *qid,
                      FSFile *f, const char *name, const char *symgt, uint32_t gid)
{
    char *path;
    struct stat st;

    path = compose_path(f->path, name);
    if (symlink(symgt, path) < 0) {
        free(path);
        return -errno_to_p9(errno);
    }
    if (lstat(path, &st) != 0) {
        free(path);
        return -errno_to_p9(errno);
    }
    free(path);
    stat_to_qid(qid, &st);
    return 0;
}

static int fs_mknod(FSDevice *fs, FSQID *qid,
             FSFile *f, const char *name, uint32_t mode, uint32_t major,
             uint32_t minor, uint32_t gid)
{
    char *path;
    struct stat st;

    path = compose_path(f->path, name);
    if (mknod(path, mode, makedev(major, minor)) < 0) {
        free(path);
        return -errno_to_p9(errno);
    }
    if (lstat(path, &st) != 0) {
        free(path);
        return -errno_to_p9(errno);
    }
    free(path);
    stat_to_qid(qid, &st);
    return 0;
}

static int fs_readlink(FSDevice *fs, char *buf, int buf_size, FSFile *f)
{
    int ret;
    ret = readlink(f->path, buf, buf_size - 1);
    if (ret < 0)
        return -errno_to_p9(errno);
    buf[ret] = '\0';
    return 0;
}

static int fs_renameat(FSDevice *fs, FSFile *f, const char *name,
                FSFile *new_f, const char *new_name)
{
    char *path, *new_path;
    int ret;

    path = compose_path(f->path, name);
    new_path = compose_path(new_f->path, new_name);
    ret = rename(path, new_path);
    free(path);
    free(new_path);
    if (ret < 0)
        return -errno_to_p9(errno);
    return 0;
}

static int fs_unlinkat(FSDevice *fs, FSFile *f, const char *name)
{
    char *path;
    int ret;

    path = compose_path(f->path, name);
    ret = remove(path);
    free(path);
    if (ret < 0)
        return -errno_to_p9(errno);
    return 0;

}

static int fs_lock(FSDevice *fs, FSFile *f, const FSLock *lock)
{
    int ret;
    struct flock fl;

    if (!f->is_opened || f->is_dir)
        return -P9_EPROTO;

    fl.l_type = lock->type;
    fl.l_whence = SEEK_SET;
    fl.l_start = lock->start;
    fl.l_len = lock->length;

    ret = fcntl(f->u.fd, F_SETLK, &fl);
    if (ret == 0) {
        ret = P9_LOCK_SUCCESS;
    } else if (errno == EAGAIN || errno == EACCES) {
        ret = P9_LOCK_BLOCKED;
    } else {
        ret = -errno_to_p9(errno);
    }
    return ret;
}

static int fs_getlock(FSDevice *fs, FSFile *f, FSLock *lock)
{
    int ret;
    struct flock fl;

    if (!f->is_opened || f->is_dir)
        return -P9_EPROTO;

    fl.l_type = lock->type;
    fl.l_whence = SEEK_SET;
    fl.l_start = lock->start;
    fl.l_len = lock->length;

    ret = fcntl(f->u.fd, F_GETLK, &fl);
    if (ret < 0) {
        ret = -errno_to_p9(errno);
    } else {
        lock->type = fl.l_type;
        lock->start = fl.l_start;
        lock->length = fl.l_len;
    }
    return ret;
}

static void fs_disk_end(FSDevice *fs1)
{
    FSDeviceDisk *fs = (FSDeviceDisk *)fs1;
    free(fs->root_path);
}

FSDevice *fs_disk_init(const char *root_path)
{
    struct stat st;

    lstat(root_path, &st);
    if (!S_ISDIR(st.st_mode))
        return NULL;

    FSDeviceDisk *fs = (FSDeviceDisk *)mallocz(sizeof *fs);

    fs->common.fs_end = fs_disk_end;
    fs->common.fs_delete = fs_delete;
    fs->common.fs_statfs = fs_statfs;
    fs->common.fs_attach = fs_attach;
    fs->common.fs_walk = fs_walk;
    fs->common.fs_mkdir = fs_mkdir;
    fs->common.fs_open = fs_open;
    fs->common.fs_create = fs_create;
    fs->common.fs_stat = fs_stat;
    fs->common.fs_setattr = fs_setattr;
    fs->common.fs_close = fs_close;
    fs->common.fs_readdir = fs_readdir;
    fs->common.fs_read = fs_read;
    fs->common.fs_write = fs_write;
    fs->common.fs_link = fs_link;
    fs->common.fs_symlink = fs_symlink;
    fs->common.fs_mknod = fs_mknod;
    fs->common.fs_readlink = fs_readlink;
    fs->common.fs_renameat = fs_renameat;
    fs->common.fs_unlinkat = fs_unlinkat;
    fs->common.fs_lock = fs_lock;
    fs->common.fs_getlock = fs_getlock;

    fs->root_path = strdup(root_path);
    return (FSDevice *)fs;
}
#endif
