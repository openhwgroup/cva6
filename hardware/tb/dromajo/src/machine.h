/*
 * VM definitions
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

#include <stdint.h>
#include "json.h"

typedef struct RISCVMachine RISCVMachine;

typedef struct FBDevice FBDevice;

typedef void SimpleFBDrawFunc(FBDevice *fb_dev, void *opaque,
                              int x, int y, int w, int h);

struct FBDevice {
    /* the following is set by the device */
    int width;
    int height;
    int stride; /* current stride in bytes */
    uint8_t *fb_data; /* current pointer to the pixel data */
    int fb_size; /* frame buffer memory size (info only) */
    void *device_opaque;
    void (*refresh)(struct FBDevice *fb_dev,
                    SimpleFBDrawFunc *redraw_func, void *opaque);
};

#ifndef MACHINE_H
#define MACHINE_H

#include <stdint.h>

#include "virtio.h"


#define MAX_DRIVE_DEVICE 4
#define MAX_FS_DEVICE 4
#define MAX_ETH_DEVICE 1

#define VM_CONFIG_VERSION 1

typedef enum {
    VM_FILE_BIOS,
    VM_FILE_VGA_BIOS,
    VM_FILE_KERNEL,
    VM_FILE_INITRD,

    VM_FILE_COUNT,
} VMFileTypeEnum;

typedef struct {
    char *filename;
    uint8_t *buf;
    int len;
} VMFileEntry;

typedef struct {
    char *device;
    char *filename;
    BlockDevice *block_dev;
} VMDriveEntry;

typedef struct {
    char *device;
    char *tag; /* 9p mount tag */
    char *filename;
    FSDevice *fs_dev;
} VMFSEntry;

typedef struct {
    char *driver;
    char *ifname;
    EthernetDevice *net;
} VMEthEntry;

typedef struct AddressSet{
    uint64_t start;
    uint64_t size;
} AddressSet;

typedef struct {
    char *cfg_filename;
    uint64_t ram_base_addr;
    uint64_t ram_size;
    BOOL rtc_local_time;
    char *display_device; /* NULL means no display */
    int64_t width, height; /* graphic width & height */
    CharacterDevice *console;
    VMDriveEntry tab_drive[MAX_DRIVE_DEVICE];
    int drive_count;
    VMFSEntry tab_fs[MAX_FS_DEVICE];
    int fs_count;
    VMEthEntry tab_eth[MAX_ETH_DEVICE];
    int eth_count;
    uint64_t htif_base_addr;

    /* some csrs may not be implemented in some implementations,
     * this arrya contains list of these csrs to make sure bootcode
     * is not generated for them
     */
    uint64_t* missing_csrs;
    uint64_t missing_csrs_size;

    /* commit of some instruction in the RTL is not visible,
     * this array contains the list of these instructions
     * to hide them in dromajo as well
     */
    uint64_t* skip_commit;
    uint64_t skip_commit_size;

    char *cmdline; /* bios or kernel command line */
    BOOL accel_enable; /* enable acceleration (KVM) */
    char *input_device; /* NULL means no input */

    /* kernel, bios and other auxiliary files */
    VMFileEntry files[VM_FILE_COUNT];

    /* maximum increment of instructions to execute */
    uint64_t maxinsns;

    /* snapshot load file */
    const char *snapshot_load_name;

    /* bootrom params */
    const char *bootrom_name;
    const char *dtb_name;
    bool compact_bootrom;

    /* reset vector used at startup */
    uint64_t reset_vector;

    /* number of cpus */
    uint64_t ncpus;

    /* MMIO range (for co-simulation only) */
    uint64_t mmio_start;
    uint64_t mmio_end;
    AddressSet *mmio_addrset;
    uint64_t mmio_addrset_size;

    /* PLIC/CLINT Params */
    uint64_t plic_base_addr;
    uint64_t plic_size;
    uint64_t clint_base_addr;
    uint64_t clint_size;

    /* Add to misa custom extensions */
    bool custom_extension;

    uint64_t physical_addr_len;

    char    *logfile; // If non-zero, all output goes here, stderr and stdout

    bool dump_memories;
} VirtMachineParams;

typedef struct VirtMachine {
    /* network */
    EthernetDevice *net;
    /* console */
    VIRTIODevice *console_dev;
    CharacterDevice *console;
    /* graphics */
    FBDevice *fb_dev;

    const char *snapshot_load_name;
    const char *snapshot_save_name;
    const char *terminate_event;
    uint32_t    save_format;
    uint64_t    maxinsns;
    uint64_t    trace;

    /* For co-simulation only, they are -1 if nothing is pending. */
    bool        cosim;
    int         pending_interrupt;
    int         pending_exception;
} VirtMachine;

int load_file(uint8_t **pbuf, const char *filename);
void __attribute__((format(printf, 1, 2))) vm_error(const char *fmt, ...);
int vm_get_int(JSONValue obj, const char *name, int64_t *pval);

const char *virt_machine_get_name(void);
void virt_machine_set_defaults(VirtMachineParams *p);
void virt_machine_load_config_file(VirtMachineParams *p,
                                   const char *filename,
                                   void (*start_cb)(void *opaque),
                                   void *opaque);
void vm_add_cmdline(VirtMachineParams *p, const char *cmdline);
char *get_file_path(const char *base_filename, const char *filename);
void virt_machine_free_config(VirtMachineParams *p);
RISCVMachine *virt_machine_init(const VirtMachineParams *p);
int virt_machine_get_sleep_duration(RISCVMachine *s, int hartid, int delay);
BOOL vm_mouse_is_absolute(RISCVMachine *s);
void vm_send_mouse_event(RISCVMachine *s1, int dx, int dy, int dz,
                         unsigned int buttons);
void vm_send_key_event(RISCVMachine *s1, BOOL is_down, uint16_t key_code);

/* gui */
void sdl_refresh(RISCVMachine *m);
void sdl_init(int width, int height);

/* simplefb.c */
typedef struct SimpleFBState SimpleFBState;
SimpleFBState *simplefb_init(PhysMemoryMap *map, uint64_t phys_addr,
                             FBDevice *fb_dev, int width, int height);
void simplefb_refresh(FBDevice *fb_dev,
                      SimpleFBDrawFunc *redraw_func, void *opaque,
                      PhysMemoryRange *mem_range,
                      int fb_page_count);

/* vga.c */
typedef struct VGAState VGAState;
VGAState *pci_vga_init(PCIBus *bus, FBDevice *fb_dev,
                       int width, int height,
                       const uint8_t *vga_rom_buf, int vga_rom_size);

/* block_net.c */
BlockDevice *block_device_init_http(const char *url,
                                    int max_cache_size_kb,
                                    void (*start_cb)(void *opaque),
                                    void *start_opaque);
#ifdef __cplusplus
extern "C" {
#endif
RISCVMachine*virt_machine_main       (int argc, char **argv);
void         virt_machine_end        (RISCVMachine *s);
void         virt_machine_serialize  (RISCVMachine *m, const char *dump_name);
void         virt_machine_deserialize(RISCVMachine *m, const char *dump_name);
BOOL         virt_machine_run        (RISCVMachine *m, int hartid);
uint64_t     virt_machine_get_pc     (RISCVMachine *m, int hartid);
uint64_t     virt_machine_get_reg    (RISCVMachine *m, int hartid, int rn);
uint64_t     virt_machine_get_fpreg  (RISCVMachine *m, int hartid, int rn);
#ifdef __cplusplus
} // extern C
#endif

#endif
