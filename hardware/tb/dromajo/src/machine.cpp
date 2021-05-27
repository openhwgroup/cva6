/*
 * VM utilities
 *
 * Copyright (c) 2017 Fabrice Bellard
 * Copyright (C) 2017,2018,2019, Esperanto Technologies Inc.
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

#include "dromajo.h"
#include <stdlib.h>
#include <stdint.h>
#include <stdarg.h>
#include <string.h>
#include <inttypes.h>
#include <assert.h>
#include <fcntl.h>
#include <errno.h>
#include <unistd.h>
#include <time.h>

#include "cutils.h"
#include "iomem.h"
#include "virtio.h"
#include "fs_utils.h"
#ifdef CONFIG_FS_NET
#include "fs_wget.h"
#endif
#include "riscv_machine.h"
#include "elf64.h"

void __attribute__((format(printf, 1, 2))) vm_error(const char *fmt, ...)
{
    va_list ap;
    va_start(ap, fmt);
    vfprintf(dromajo_stderr, fmt, ap);
    va_end(ap);
}

int vm_get_int(JSONValue obj, const char *name, int64_t *pval)
{
    JSONValue val = json_object_get(obj, name);

    if (json_is_undefined(val)) {
        vm_error("expecting '%s' property\n", name);
        return -1;
    }

    if (val.type != JSON_INT) {
        vm_error("%s: integer expected\n", name);
        return -1;
    }

    *pval = val.u.int64;

    return 0;
}

int vm_get_mmio_addrset_opt(JSONValue obj, VirtMachineParams *p)
{
    JSONValue val = json_object_get(obj, "mmio_addrset");

    if (json_is_undefined(val))
        return 0;

    if (val.type != JSON_ARRAY) {
        vm_error("%s: array expected\n", "mmio_addrset");
        return -1;
    }

    uint64_t mmio_addrset_size = val.u.array->len;
    AddressSet *mmio_addrset = (AddressSet *)mallocz(sizeof(AddressSet)*mmio_addrset_size);

    for (int i = 0; i < val.u.array->len; ++i) {
        JSONValue obj = json_array_get(val, i);
        vm_get_int(obj, "start", (int64_t*)&mmio_addrset[i].start);
        vm_get_int(obj, "size",(int64_t*)&mmio_addrset[i].size);
    }

    p->mmio_addrset = mmio_addrset;
    p->mmio_addrset_size = mmio_addrset_size;

    return 0;
}

int vm_get_missing_csrs_opt(JSONValue obj, VirtMachineParams *p)
{
    JSONValue val = json_object_get(obj, "missing_csrs");
    if (json_is_undefined(val))
        return 0;

    if (val.type != JSON_ARRAY) {
        vm_error("%s: array expected\n", "missing_csrs");
        return -1;
    }

    uint64_t array_size = val.u.array->len;
    uint64_t* array_ptr = (uint64_t*)mallocz(sizeof(uint64_t)*array_size);

    for (uint64_t i = 0; i < array_size; i++) {
      JSONValue obj = json_array_get(val, i);
      array_ptr[i] = obj.u.int64;
    }

    p->missing_csrs = array_ptr;
    p->missing_csrs_size = array_size;

    return 0;
}

int vm_get_skip_commit_opt(JSONValue obj, VirtMachineParams *p)
{
    JSONValue val = json_object_get(obj, "skip_commit");
    if (json_is_undefined(val))
        return 0;

    if (val.type != JSON_ARRAY) {
        vm_error("%s: array expected\n", "skip_commit");
        return -1;
    }

    uint64_t array_size = val.u.array->len;
    uint64_t* array_ptr = (uint64_t*)mallocz(sizeof(uint64_t)*array_size);

    for (uint64_t i = 0; i < array_size; i++) {
      JSONValue obj = json_array_get(val, i);
      array_ptr[i] = obj.u.int64;
    }

    p->skip_commit = array_ptr;
    p->skip_commit_size = array_size;

    return 0;
}

static void vm_get_uint64_opt(JSONValue obj, const char *name, uint64_t *pval)
{
    JSONValue val = json_object_get(obj, name);

    if (json_is_undefined(val))
        return;

    if (val.type != JSON_INT) {
        vm_error("%s: integer expected\n", name);
        return;
    }

    *pval = (uint64_t)val.u.int64;
}

static int vm_get_str2(JSONValue obj, const char *name, const char **pstr,
                      BOOL is_opt)
{
    JSONValue val;
    val = json_object_get(obj, name);
    if (json_is_undefined(val)) {
        if (is_opt) {
            *pstr = NULL;
            return 0;
        } else {
            vm_error("expecting '%s' property\n", name);
            return -1;
        }
    }
    if (val.type != JSON_STR) {
        vm_error("%s: string expected\n", name);
        return -1;
    }
    *pstr = val.u.str->data;
    return 0;
}

static int vm_get_str(JSONValue obj, const char *name, const char **pstr)
{
    return vm_get_str2(obj, name, pstr, FALSE);
}

static int vm_get_str_opt(JSONValue obj, const char *name, const char **pstr)
{
    return vm_get_str2(obj, name, pstr, TRUE);
}

static char *strdup_null(const char *str)
{
    if (!str)
        return NULL;
    else
        return strdup(str);
}

/* currently only for "TZ" */
static char *cmdline_subst(const char *cmdline)
{
    DynBuf dbuf;
    const char *p;
    char var_name[32], *q, buf[32];

    dbuf_init(&dbuf);
    p = cmdline;
    while (*p != '\0') {
        if (p[0] == '$' && p[1] == '{') {
            p += 2;
            q = var_name;
            while (*p != '\0' && *p != '}') {
                if ((q - var_name) < (int)sizeof(var_name) - 1)
                    *q++ = *p;
                p++;
            }
            *q = '\0';
            if (*p == '}')
                p++;
            if (!strcmp(var_name, "TZ")) {
                time_t ti;
                struct tm tm;
                int n, sg;
                /* get the offset to UTC */
                time(&ti);
                localtime_r(&ti, &tm);
                n = tm.tm_gmtoff / 60;
                sg = '-';
                if (n < 0) {
                    sg = '+';
                    n = -n;
                }
                snprintf(buf, sizeof(buf), "UTC%c%02d:%02d",
                         sg, n / 60, n % 60);
                dbuf_putstr(&dbuf, buf);
            }
        } else {
            dbuf_putc(&dbuf, *p++);
        }
    }
    dbuf_putc(&dbuf, 0);
    return (char *)dbuf.buf;
}

static int virt_machine_parse_config(VirtMachineParams *p,
                                     char *config_file_str, int len)
{
    int64_t version, val;
    const char *tag_name, *machine_name, *str;
    char buf1[256];
    JSONValue cfg, obj, el;
    p->maxinsns = 0;
    p->dump_memories = false;

    cfg = json_parse_value_len(config_file_str, len);
    if (json_is_error(cfg)) {
        vm_error("error: %s\n", json_get_error(cfg));
        json_free(cfg);
        return -1;
    }

    if (vm_get_int(cfg, "version", &version) < 0)
        goto tag_fail;
    if (version != VM_CONFIG_VERSION) {
        if (version > VM_CONFIG_VERSION) {
            vm_error("The emulator is too old to run this VM: please upgrade\n");
            return -1;
        } else {
            vm_error("The VM configuration file is too old for this emulator version: please upgrade the VM configuration file\n");
            return -1;
        }
    }

    if (vm_get_str(cfg, "machine", &str) < 0)
        goto tag_fail;
    machine_name = virt_machine_get_name();
    if (strcmp(machine_name, str) != 0) {
        vm_error("Unsupported machine: '%s' (running machine is '%s')\n",
                 str, machine_name);
        return -1;
    }

    vm_get_uint64_opt(cfg, "memory_base_addr", &p->ram_base_addr);

    tag_name = "memory_size";
    if (vm_get_int(cfg, tag_name, &val) < 0)
        goto tag_fail;
    p->ram_size = (size_t)val << 20;

    tag_name = "bios";
    if (vm_get_str_opt(cfg, tag_name, &str) < 0)
        goto tag_fail;
    if (str) {
        p->files[VM_FILE_BIOS].filename = strdup(str);
    }

    tag_name = "kernel";
    if (vm_get_str_opt(cfg, tag_name, &str) < 0)
        goto tag_fail;
    if (str) {
        p->files[VM_FILE_KERNEL].filename = strdup(str);
    }

    tag_name = "initrd";
    if (vm_get_str_opt(cfg, tag_name, &str) < 0)
        goto tag_fail;
    if (str) {
        p->files[VM_FILE_INITRD].filename = strdup(str);
    }

    if (vm_get_str_opt(cfg, "cmdline", &str) < 0)
        goto tag_fail;
    if (str) {
        p->cmdline = cmdline_subst(str);
    }

    if (vm_get_missing_csrs_opt(cfg, p) < 0)
        goto tag_fail;

    if (vm_get_skip_commit_opt(cfg, p) < 0)
        goto tag_fail;

    vm_get_uint64_opt(cfg, "htif_base_addr", &p->htif_base_addr);
    vm_get_uint64_opt(cfg, "maxinsns", &p->maxinsns);

    // checkpoint file path
    p->snapshot_load_name = NULL;
    tag_name = "load";
    str = NULL;
    if (vm_get_str_opt(cfg, tag_name, &str) == 0 && str != NULL) {
        p->snapshot_load_name = strdup(str);
    }

    for (;;) {
        snprintf(buf1, sizeof(buf1), "drive%d", p->drive_count);
        obj = json_object_get(cfg, buf1);
        if (json_is_undefined(obj))
            break;
        if (p->drive_count >= MAX_DRIVE_DEVICE) {
            vm_error("Too many drives\n");
            return -1;
        }
        if (vm_get_str(obj, "file", &str) < 0)
            goto tag_fail;
        p->tab_drive[p->drive_count].filename = strdup(str);
        if (vm_get_str_opt(obj, "device", &str) < 0)
            goto tag_fail;
        p->tab_drive[p->drive_count].device = strdup_null(str);
        p->drive_count++;
    }

    for (;;) {
        snprintf(buf1, sizeof(buf1), "fs%d", p->fs_count);
        obj = json_object_get(cfg, buf1);
        if (json_is_undefined(obj))
            break;
        if (p->fs_count >= MAX_DRIVE_DEVICE) {
            vm_error("Too many filesystems\n");
            return -1;
        }
        if (vm_get_str(obj, "file", &str) < 0)
            goto tag_fail;
        p->tab_fs[p->fs_count].filename = strdup(str);
        if (vm_get_str_opt(obj, "tag", &str) < 0)
            goto tag_fail;
        if (!str) {
            if (p->fs_count == 0)
                strcpy(buf1, "/dev/root");
            else
                snprintf(buf1, sizeof(buf1), "/dev/root%d", p->fs_count);
            str = buf1;
        }
        p->tab_fs[p->fs_count].tag = strdup(str);
        p->fs_count++;
    }

    for (;;) {
        snprintf(buf1, sizeof(buf1), "eth%d", p->eth_count);
        obj = json_object_get(cfg, buf1);
        if (json_is_undefined(obj))
            break;
        if (p->eth_count >= MAX_ETH_DEVICE) {
            vm_error("Too many ethernet interfaces\n");
            return -1;
        }
        if (vm_get_str(obj, "driver", &str) < 0)
            goto tag_fail;
        p->tab_eth[p->eth_count].driver = strdup(str);
        if (!strcmp(str, "tap")) {
            if (vm_get_str(obj, "ifname", &str) < 0)
                goto tag_fail;
            p->tab_eth[p->eth_count].ifname = strdup(str);
        }
        p->eth_count++;
    }

    p->display_device = NULL;
    obj = json_object_get(cfg, "display0");
    if (!json_is_undefined(obj)) {
        if (vm_get_str(obj, "device", &str) < 0)
            goto tag_fail;
        p->display_device = strdup(str);
        if (vm_get_int(obj, "width", &p->width) < 0)
            goto tag_fail;
        if (vm_get_int(obj, "height", &p->height) < 0)
            goto tag_fail;
        if (vm_get_str_opt(obj, "vga_bios", &str) < 0)
            goto tag_fail;
        if (str) {
            p->files[VM_FILE_VGA_BIOS].filename = strdup(str);
        }
    }

    if (vm_get_str_opt(cfg, "input_device", &str) < 0)
        goto tag_fail;
    p->input_device = strdup_null(str);

    if (vm_get_str_opt(cfg, "accel", &str) < 0)
        goto tag_fail;
    if (str) {
        if (!strcmp(str, "none")) {
            p->accel_enable = FALSE;
        } else if (!strcmp(str, "auto")) {
            p->accel_enable = TRUE;
        } else {
            vm_error("unsupported 'accel' config: %s\n", str);
            return -1;
        }
    }

    tag_name = "rtc_local_time";
    el = json_object_get(cfg, tag_name);
    if (!json_is_undefined(el)) {
        if (el.type != JSON_BOOL) {
            vm_error("%s: boolean expected\n", tag_name);
            goto tag_fail;
        }
        p->rtc_local_time = el.u.b;
    }

    vm_get_uint64_opt(cfg, "ncpus", &p->ncpus);

    vm_get_uint64_opt(cfg, "mmio_start", &p->mmio_start);
    vm_get_uint64_opt(cfg, "mmio_end",   &p->mmio_end);
    if (vm_get_mmio_addrset_opt(cfg, p) < 0)
        goto tag_fail;

    vm_get_uint64_opt(cfg, "physical_addr_len", &p->physical_addr_len);

    if (vm_get_str_opt(cfg, "logfile", &str) < 0)
        goto tag_fail;
    if (str)
        p->logfile = strdup(str);

    json_free(cfg);
    return 0;
 tag_fail:
    json_free(cfg);
    return -1;
}

typedef void FSLoadFileCB(void *opaque, uint8_t *buf, int buf_len);

typedef struct {
    VirtMachineParams *vm_params;
    void (*start_cb)(void *opaque);
    void *opaque;

    FSLoadFileCB *file_load_cb;
    void *file_load_opaque;
    int file_index;
} VMConfigLoadState;

static void config_file_loaded(void *opaque, uint8_t *buf, int buf_len);
static void config_additional_file_load(VMConfigLoadState *s);
static void config_additional_file_load_cb(void *opaque,
                                           uint8_t *buf, int buf_len);

char *get_file_path(const char *base_filename, const char *filename)
{
    if (!base_filename)
        return strdup(filename);
    if (strchr(filename, ':'))
        return strdup(filename);
    if (filename[0] == '/')
        return strdup(filename);

    const char *p = strrchr(base_filename, '/');
    if (!p)
        return strdup(filename);

    int len = p + 1 - base_filename;
    int len1 = strlen(filename);
    char *fname = (char *)malloc(len + len1 + 1);
    memcpy(fname, base_filename, len);
    memcpy(fname + len, filename, len1 + 1);
    return fname;
}


/* return -1 if error. */
int load_file(uint8_t **pbuf, const char *filename)
{
    FILE *f = fopen(filename, "rb");
    if (!f) {
        perror(filename);
        exit(1);
    }
    fseek(f, 0, SEEK_END);
    size_t size = ftell(f);
    fseek(f, 0, SEEK_SET);
    uint8_t *buf = (uint8_t *)malloc(size);
    if (fread(buf, 1, size, f) != size) {
        fprintf(dromajo_stderr, "%s: read error\n", filename);
        exit(1);
    }
    fclose(f);
    *pbuf = buf;
    return size;
}

#ifdef CONFIG_FS_NET
static void config_load_file_cb(void *opaque, int err, void *data, size_t size)
{
    VMConfigLoadState *s = opaque;

    //    fprintf(dromajo_stdout, "err=%d data=%p size=%ld\n", err, data, size);
    if (err < 0) {
        vm_error("Error %d while loading file\n", -err);
        exit(1);
    }
    s->file_load_cb(s->file_load_opaque, data, size);
}
#endif

static void config_load_file(VMConfigLoadState *s, const char *filename,
                             FSLoadFileCB *cb, void *opaque)
{
    //    printf("loading %s\n", filename);
#ifdef CONFIG_FS_NET
    if (is_url(filename)) {
        s->file_load_cb = cb;
        s->file_load_opaque = opaque;
        fs_wget(filename, NULL, NULL, s, config_load_file_cb, TRUE);
    } else
#endif
    {
        uint8_t *buf;
        int size = load_file(&buf, filename);
        cb(opaque, buf, size);
        free(buf);
    }
}

void virt_machine_load_config_file(VirtMachineParams *p,
                                   const char *filename,
                                   void (*start_cb)(void *opaque),
                                   void *opaque)
{
    VMConfigLoadState *s = (VMConfigLoadState *)mallocz(sizeof(*s));
    s->vm_params = p;
    s->start_cb = start_cb;
    s->opaque = opaque;
    p->cfg_filename = strdup(filename);

    config_load_file(s, filename, config_file_loaded, s);
}

static void config_file_loaded(void *opaque, uint8_t *buf, int buf_len)
{
    VMConfigLoadState *s = (VMConfigLoadState *)opaque;
    VirtMachineParams *p = s->vm_params;

    if (virt_machine_parse_config(p, (char *)buf, buf_len) < 0)
        exit(1);

    /* load the additional files */
    s->file_index = 0;
    config_additional_file_load(s);
}

static void config_additional_file_load(VMConfigLoadState *s)
{
    VirtMachineParams *p = s->vm_params;
    while (s->file_index < VM_FILE_COUNT &&
           p->files[s->file_index].filename == NULL) {
        s->file_index++;
    }
    if (s->file_index == VM_FILE_COUNT) {
        if (s->start_cb)
            s->start_cb(s->opaque);
        free(s);
    } else {
        char *fname;

        fname = get_file_path(p->cfg_filename,
                              p->files[s->file_index].filename);
        config_load_file(s, fname,
                         config_additional_file_load_cb, s);
        free(fname);
    }
}

static void config_additional_file_load_cb(void *opaque,
                                           uint8_t *buf, int buf_len)
{
    VMConfigLoadState *s = (VMConfigLoadState *)opaque;
    VirtMachineParams *p = s->vm_params;

    p->files[s->file_index].buf = (uint8_t *)malloc(buf_len);
    memcpy(p->files[s->file_index].buf, buf, buf_len);
    p->files[s->file_index].len = buf_len;

    /* load the next files */
    s->file_index++;
    config_additional_file_load(s);
}

void vm_add_cmdline(VirtMachineParams *p, const char *cmdline)
{
    char *new_cmdline;
    if (cmdline[0] == '!') {
        new_cmdline = strdup(cmdline + 1);
    } else {
        const char *old_cmdline = p->cmdline;
        if (!old_cmdline)
            old_cmdline = "";
        new_cmdline = (char *)malloc(strlen(old_cmdline) + 1 + strlen(cmdline) + 1);
        strcpy(new_cmdline, old_cmdline);
        strcat(new_cmdline, " ");
        strcat(new_cmdline, cmdline);
    }
    free(p->cmdline);
    p->cmdline = new_cmdline;
}

void virt_machine_free_config(VirtMachineParams *p)
{
    int i;

    free(p->cmdline);
    for (i = 0; i < VM_FILE_COUNT; i++) {
        free(p->files[i].filename);
        free(p->files[i].buf);
    }
    for (i = 0; i < p->drive_count; i++) {
        free(p->tab_drive[i].filename);
        free(p->tab_drive[i].device);
    }
    for (i = 0; i < p->fs_count; i++) {
        free(p->tab_fs[i].filename);
        free(p->tab_fs[i].tag);
    }
    for (i = 0; i < p->eth_count; i++) {
        free(p->tab_eth[i].driver);
        free(p->tab_eth[i].ifname);
    }
    free(p->input_device);
    free(p->display_device);
    free(p->cfg_filename);
}
