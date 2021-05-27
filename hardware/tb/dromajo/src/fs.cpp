/*
 * Filesystem utilities
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
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <inttypes.h>
#include <assert.h>
#include <stdarg.h>

#include "cutils.h"
#include "fs.h"

FSFile *fs_dup(FSDevice *fs, FSFile *f)
{
    FSQID qid;
    fs->fs_walk(fs, &f, &qid, f, 0, NULL);
    return f;
}

FSFile *fs_walk_path1(FSDevice *fs, FSFile *f, const char *path,
                      char **pname)
{
    const char *p;
    char *name;
    FSFile *f1;
    FSQID qid;
    int len, ret;
    BOOL is_last, is_first;

    if (path[0] == '/')
        path++;

    is_first = TRUE;
    for (;;) {
        p = strchr(path, '/');
        if (!p) {
            name = (char *)path;
            if (pname) {
                *pname = name;
                if (is_first) {
                    ret = fs->fs_walk(fs, &f, &qid, f, 0, NULL);
                    if (ret < 0)
                        f = NULL;
                }
                return f;
            }
            is_last = TRUE;
        } else {
            len = p - path;
            name = (char *)malloc(len + 1);
            memcpy(name, path, len);
            name[len] = '\0';
            is_last = FALSE;
        }
        ret = fs->fs_walk(fs, &f1, &qid, f, 1, &name);
        if (!is_last)
            free(name);
        if (!is_first)
            fs->fs_delete(fs, f);
        f = f1;
        is_first = FALSE;
        if (ret <= 0) {
            fs->fs_delete(fs, f);
            f = NULL;
            break;
        } else if (is_last) {
            break;
        }
        path = p + 1;
    }
    return f;
}

FSFile *fs_walk_path(FSDevice *fs, FSFile *f, const char *path)
{
    return fs_walk_path1(fs, f, path, NULL);
}

void fs_end(FSDevice *fs)
{
    fs->fs_end(fs);
    free(fs);
}
