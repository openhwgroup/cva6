/*
 * Misc FS utilities
 *
 * Copyright (c) 2016-2017 Fabrice Bellard
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
#define HEAD_FILENAME "head"
#define ROOT_FILENAME "files"

#define FILEID_SIZE_MAX 32

#define FS_KEY_LEN 16

/* default block size to determine the total filesytem size */
#define FS_BLOCK_SIZE_LOG2 12
#define FS_BLOCK_SIZE (1 << FS_BLOCK_SIZE_LOG2)

typedef enum {
    FS_ERR_OK = 0,
    FS_ERR_GENERIC = -1,
    FS_ERR_SYNTAX = -2,
    FS_ERR_REVISION = -3,
    FS_ERR_FILE_ID = -4,
    FS_ERR_IO = -5,
    FS_ERR_NOENT = -6,
    FS_ERR_COUNTERS = -7,
    FS_ERR_QUOTA = -8,
    FS_ERR_PROTOCOL_VERSION = -9,
    FS_ERR_HEAD = -10,
} FSCommitErrorCode;

typedef uint64_t FSFileID;

static inline BOOL isspace_nolf(int c)
{
    return (c == ' ' || c == '\t');
}

static inline int from_hex(int c)
{
    if (c >= '0' && c <= '9')
        return c - '0';
    else if (c >= 'A' && c <= 'F')
        return c - 'A' + 10;
    else if (c >= 'a' && c <= 'f')
        return c - 'a' + 10;
    else
        return -1;
}

static inline uint64_t block_align(uint64_t val, uint64_t align)
{
    return (val + align - 1) & ~(align - 1);
}

void pstrcpy(char *buf, int buf_size, const char *str);
char *pstrcat(char *buf, int buf_size, const char *s);
char *compose_path(const char *path, const char *name);
char *compose_url(const char *base_url, const char *name);
void skip_line(const char **pp);
char *quoted_str(const char *str);
int parse_fname(char *buf, int buf_size, const char **pp);
int parse_uint32_base(uint32_t *pval, const char **pp, int base);
int parse_uint64_base(uint64_t *pval, const char **pp, int base);
int parse_uint64(uint64_t *pval, const char **pp);
int parse_uint32(uint32_t *pval, const char **pp);
int parse_time(uint32_t *psec, uint32_t *pnsec, const char **pp);
int parse_file_id(FSFileID *pval, const char **pp);
char *file_id_to_filename(char *buf, FSFileID file_id);
void encode_hex(char *str, const uint8_t *buf, int len);
int decode_hex(uint8_t *buf, const char *str, int len);
BOOL is_url(const char *path);

const char *skip_header(const char *p);
int parse_tag(char *buf, int buf_size, const char *str, const char *tag);
int parse_tag_uint64(uint64_t *pval, const char *str, const char *tag);
int parse_tag_file_id(FSFileID *pval, const char *str, const char *tag);
int parse_tag_version(const char *str);
