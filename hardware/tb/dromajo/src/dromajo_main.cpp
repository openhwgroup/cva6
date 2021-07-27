/*
 * RISCV emulator
 *
 * Copyright (c) 2016-2017 Fabrice Bellard
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
#include <stdio.h>
#include <stdbool.h>
#include <stdarg.h>
#include <string.h>
#include <inttypes.h>
#include <assert.h>
#include <fcntl.h>
#include <errno.h>
#include <unistd.h>
#include <time.h>
#include <getopt.h>
#include <termios.h>
#include <sys/ioctl.h>
#include <net/if.h>
#ifndef __APPLE__
#include <linux/if_tun.h>
#endif
#include <sys/stat.h>
#include <signal.h>
#include <err.h>

#include "cutils.h"
#include "iomem.h"
#include "virtio.h"
#ifdef CONFIG_FS_NET
#include "fs_utils.h"
#include "fs_wget.h"
#endif
#include "riscv_machine.h"
#ifdef CONFIG_SLIRP
#include "slirp/libslirp.h"
#endif
#include "elf64.h"

FILE *dromajo_stdout;
FILE *dromajo_stderr;

typedef struct {
    FILE *stdin, *out;
    int  console_esc_state;
    BOOL resize_pending;
} STDIODevice;

static struct termios oldtty;
static int old_fd0_flags;
static STDIODevice *global_stdio_device;

static void term_exit(void)
{
    tcsetattr (0, TCSANOW, &oldtty);
    fcntl(0, F_SETFL, old_fd0_flags);
}

static void term_init(BOOL allow_ctrlc)
{
    struct termios tty;

    memset(&tty, 0, sizeof(tty));
    tcgetattr (0, &tty);
    oldtty = tty;
    old_fd0_flags = fcntl(0, F_GETFL);

    tty.c_iflag &= ~(IGNBRK|BRKINT|PARMRK|ISTRIP
                          |INLCR|IGNCR|ICRNL|IXON);
    tty.c_oflag |= OPOST;
    tty.c_lflag &= ~(ECHO|ECHONL|ICANON|IEXTEN);
    if (!allow_ctrlc)
        tty.c_lflag &= ~ISIG;
    tty.c_cflag &= ~(CSIZE|PARENB);
    tty.c_cflag |= CS8;
    tty.c_cc[VMIN] = 1;
    tty.c_cc[VTIME] = 0;

    tcsetattr (0, TCSANOW, &tty);

    atexit(term_exit);
}

static void console_write(void *opaque, const uint8_t *buf, int len)
{
    STDIODevice *s = (STDIODevice *)opaque;
    fwrite(buf, 1, len, s->out);
    fflush(s->out);
}

static int console_read(void *opaque, uint8_t *buf, int len)
{
    STDIODevice *s = (STDIODevice *)opaque;

    if (len <= 0)
        return 0;

    int ret = fread(buf, len, 1, s->stdin);
    if (ret <= 0)
        return 0;

    int j = 0;
    for (int i = 0; i < ret; i++) {
        uint8_t ch = buf[i];
        if (s->console_esc_state) {
            s->console_esc_state = 0;
            switch (ch) {
            case 'x':
                fprintf(dromajo_stderr, "Terminated\n");
                exit(0);
            case 'h':
                fprintf(dromajo_stderr, "\n"
                        "C-b h   print this help\n"
                        "C-b x   exit emulator\n"
                        "C-b C-b send C-b\n");
                break;
            case 1:
                goto output_char;
            default:
                break;
            }
        } else {
            if (ch == 2) { // Change to work with tmux
                s->console_esc_state = 1;
            } else {
            output_char:
                buf[j++] = ch;
            }
        }
    }

    return j;
}

static void term_resize_handler(int sig)
{
    if (global_stdio_device)
        global_stdio_device->resize_pending = TRUE;
}

CharacterDevice *console_init(BOOL allow_ctrlc, FILE *stdin, FILE *out)
{
    term_init(allow_ctrlc);

    CharacterDevice *dev = (CharacterDevice *)mallocz(sizeof *dev);
    STDIODevice *s = (STDIODevice *)mallocz(sizeof *s);
    s->stdin = stdin;
    s->out = out;
    /* Note: the glibc does not properly tests the return value of
       write() in printf, so some messages on out may be lost */
    fcntl(fileno(s->stdin), F_SETFL, O_NONBLOCK);

    s->resize_pending = TRUE;
    global_stdio_device = s;

    /* use a signal to get the host terminal resize events */
    struct sigaction sig;
    sig.sa_handler = term_resize_handler;
    sigemptyset(&sig.sa_mask);
    sig.sa_flags = 0;
    sigaction(SIGWINCH, &sig, NULL);

    dev->opaque = s;
    dev->write_data = console_write;
    dev->read_data = console_read;
    return dev;
}

typedef enum {
    BF_MODE_RO,
    BF_MODE_RW,
    BF_MODE_SNAPSHOT,
} BlockDeviceModeEnum;

#define SECTOR_SIZE 512UL

typedef struct BlockDeviceFile {
    FILE *f;
    int64_t nb_sectors;
    BlockDeviceModeEnum mode;
    uint8_t **sector_table;
} BlockDeviceFile;

static int64_t bf_get_sector_count(BlockDevice *bs)
{
    BlockDeviceFile *bf = (BlockDeviceFile *)bs->opaque;
    return bf->nb_sectors;
}

//#define DUMP_BLOCK_READ

static int bf_read_async(BlockDevice *bs,
                         uint64_t sector_num, uint8_t *buf, int n,
                         BlockDeviceCompletionFunc *cb, void *opaque)
{
    BlockDeviceFile *bf = (BlockDeviceFile *)bs->opaque;
#ifdef DUMP_BLOCK_READ
    {
        static FILE *f;
        if (!f)
            f = fopen("/tmp/read_sect.txt", "wb");
        fprintf(f, "%" PRId64 " %d\n", sector_num, n);
    }
#endif
    if (!bf->f)
        return -1;
    if (bf->mode == BF_MODE_SNAPSHOT) {
        int i;
        for (i = 0; i < n; i++) {
            if (!bf->sector_table[sector_num]) {
                fseek(bf->f, sector_num * SECTOR_SIZE, SEEK_SET);
                size_t got = fread(buf, 1, SECTOR_SIZE, bf->f);
                assert(got == SECTOR_SIZE);
            } else {
                memcpy(buf, bf->sector_table[sector_num], SECTOR_SIZE);
            }
            sector_num++;
            buf += SECTOR_SIZE;
        }
    } else {
        fseek(bf->f, sector_num * SECTOR_SIZE, SEEK_SET);
        size_t got = fread(buf, 1, n * SECTOR_SIZE, bf->f);
        assert(got == n * SECTOR_SIZE);
    }
    /* synchronous read */
    return 0;
}

static int bf_write_async(BlockDevice *bs,
                          uint64_t sector_num, const uint8_t *buf, int n,
                          BlockDeviceCompletionFunc *cb, void *opaque)
{
    BlockDeviceFile *bf = (BlockDeviceFile *)bs->opaque;
    int ret;

    switch (bf->mode) {
    case BF_MODE_RO:
        ret = -1; /* error */
        break;
    case BF_MODE_RW:
        fseek(bf->f, sector_num * SECTOR_SIZE, SEEK_SET);
        fwrite(buf, 1, n * SECTOR_SIZE, bf->f);
        ret = 0;
        break;
    case BF_MODE_SNAPSHOT:
        {
            if ((unsigned int)(sector_num + n) > bf->nb_sectors)
                return -1;
            for (int i = 0; i < n; i++) {
                if (!bf->sector_table[sector_num]) {
                    bf->sector_table[sector_num] = (uint8_t *)malloc(SECTOR_SIZE);
                }
                memcpy(bf->sector_table[sector_num], buf, SECTOR_SIZE);
                sector_num++;
                buf += SECTOR_SIZE;
            }
            ret = 0;
        }
        break;
    default:
        abort();
    }

    return ret;
}

static BlockDevice *block_device_init(const char *filename,
                                      BlockDeviceModeEnum mode)
{
    const char *mode_str;

    if (mode == BF_MODE_RW) {
        mode_str = "r+b";
    } else {
        mode_str = "rb";
    }

    FILE *f = fopen(filename, mode_str);
    if (!f) {
        perror(filename);
        exit(1);
    }
    fseek(f, 0, SEEK_END);
    int64_t file_size = ftello(f);

    BlockDevice *bs = (BlockDevice *)mallocz(sizeof *bs);
    BlockDeviceFile *bf = (BlockDeviceFile *)mallocz(sizeof *bf);

    bf->mode = mode;
    bf->nb_sectors = file_size / 512;
    bf->f = f;

    if (mode == BF_MODE_SNAPSHOT) {
        bf->sector_table = (uint8_t **)mallocz(sizeof(bf->sector_table[0]) *
                                   bf->nb_sectors);
    }

    bs->opaque = bf;
    bs->get_sector_count = bf_get_sector_count;
    bs->read_async = bf_read_async;
    bs->write_async = bf_write_async;
    return bs;
}

#define MAX_EXEC_CYCLE 1
#define MAX_SLEEP_TIME 10 /* in ms */

#if !defined(__APPLE__)
typedef struct {
    int fd;
    BOOL select_filled;
} TunState;

static void tun_write_packet(EthernetDevice *net,
                             const uint8_t *buf, int len)
{
    TunState *s = (TunState *)net->opaque;
    ssize_t got = write(s->fd, buf, len);
    assert(got == len);
}

static void tun_select_fill(EthernetDevice *net, int *pfd_max,
                            fd_set *rfds, fd_set *wfds, fd_set *efds,
                            int *pdelay)
{
    TunState *s = (TunState *)net->opaque;
    int net_fd = s->fd;

    s->select_filled = net->device_can_write_packet(net);
    if (s->select_filled) {
        FD_SET(net_fd, rfds);
        *pfd_max = max_int(*pfd_max, net_fd);
    }
}

static void tun_select_poll(EthernetDevice *net,
                            fd_set *rfds, fd_set *wfds, fd_set *efds,
                            int select_ret)
{
    TunState *s = (TunState *)net->opaque;
    int net_fd = s->fd;
    uint8_t buf[2048];
    int ret;

    if (select_ret <= 0)
        return;
    if (s->select_filled && FD_ISSET(net_fd, rfds)) {
        ret = read(net_fd, buf, sizeof(buf));
        if (ret > 0)
            net->device_write_packet(net, buf, ret);
    }

}

/* configure with:
# bridge configuration (connect tap0 to bridge interface br0)
   ip link add br0 type bridge
   ip tuntap add dev tap0 mode tap [user x] [group x]
   ip link set tap0 master br0
   ip link set dev br0 up
   ip link set dev tap0 up

# NAT configuration (eth1 is the interface connected to internet)
   ifconfig br0 192.168.3.1
   echo 1 > /proc/sys/net/ipv4/ip_forward
   iptables -D FORWARD 1
   iptables -t nat -A POSTROUTING -o eth1 -j MASQUERADE

   In the VM:
   ifconfig eth0 192.168.3.2
   route add -net 0.0.0.0 netmask 0.0.0.0 gw 192.168.3.1
*/
static EthernetDevice *tun_open(const char *ifname)
{
    struct ifreq ifr;
    int fd, ret;

    fd = open("/dev/net/tun", O_RDWR);
    if (fd < 0) {
        fprintf(dromajo_stderr, "Error: could not open /dev/net/tun\n");
        return NULL;
    }
    memset(&ifr, 0, sizeof(ifr));
    ifr.ifr_flags = IFF_TAP | IFF_NO_PI;
    pstrcpy(ifr.ifr_name, sizeof(ifr.ifr_name), ifname);
    ret = ioctl(fd, TUNSETIFF, (void *) &ifr);
    if (ret != 0) {
        fprintf(dromajo_stderr, "Error: could not configure /dev/net/tun\n");
        close(fd);
        return NULL;
    }
    fcntl(fd, F_SETFL, O_NONBLOCK);

    EthernetDevice *net = (EthernetDevice *)mallocz(sizeof *net);
    net->mac_addr[0] = 0x02;
    net->mac_addr[1] = 0x00;
    net->mac_addr[2] = 0x00;
    net->mac_addr[3] = 0x00;
    net->mac_addr[4] = 0x00;
    net->mac_addr[5] = 0x01;

    TunState *s = (TunState *)mallocz(sizeof *s);
    s->fd = fd;
    net->opaque = s;
    net->write_packet = tun_write_packet;
    net->select_fill = tun_select_fill;
    net->select_poll = tun_select_poll;
    return net;
}

#endif /* !__APPLE__*/

#ifdef CONFIG_SLIRP

/*******************************************************/
/* slirp */

static Slirp *slirp_state;

static void slirp_write_packet(EthernetDevice *net,
                               const uint8_t *buf, int len)
{
    Slirp *slirp_state = net->opaque;
    slirp_input(slirp_state, buf, len);
}

int slirp_can_output(void *opaque)
{
    EthernetDevice *net = opaque;
    return net->device_can_write_packet(net);
}

void slirp_output(void *opaque, const uint8_t *pkt, int pkt_len)
{
    EthernetDevice *net = opaque;
    return net->device_write_packet(net, pkt, pkt_len);
}

static void slirp_select_fill1(EthernetDevice *net, int *pfd_max,
                               fd_set *rfds, fd_set *wfds, fd_set *efds,
                               int *pdelay)
{
    Slirp *slirp_state = net->opaque;
    slirp_select_fill(slirp_state, pfd_max, rfds, wfds, efds);
}

static void slirp_select_poll1(EthernetDevice *net,
                               fd_set *rfds, fd_set *wfds, fd_set *efds,
                               int select_ret)
{
    Slirp *slirp_state = net->opaque;
    slirp_select_poll(slirp_state, rfds, wfds, efds, (select_ret <= 0));
}

static EthernetDevice *slirp_open(void)
{
    EthernetDevice *net;
    struct in_addr net_addr  = { .s_addr = htonl(0x0a000200) }; /* 10.0.2.0 */
    struct in_addr mask = { .s_addr = htonl(0xffffff00) }; /* 255.255.255.0 */
    struct in_addr host = { .s_addr = htonl(0x0a000202) }; /* 10.0.2.2 */
    struct in_addr dhcp = { .s_addr = htonl(0x0a00020f) }; /* 10.0.2.15 */
    struct in_addr dns  = { .s_addr = htonl(0x0a000203) }; /* 10.0.2.3 */
    const char *bootfile = NULL;
    const char *vhostname = NULL;
    int restricted = 0;

    if (slirp_state) {
        fprintf(dromajo_stderr, "Only a single slirp instance is allowed\n");
        return NULL;
    }
    net = mallocz(sizeof(*net));

    slirp_state = slirp_init(restricted, net_addr, mask, host, vhostname,
                             "", bootfile, dhcp, dns, net);

    net->mac_addr[0] = 0x02;
    net->mac_addr[1] = 0x00;
    net->mac_addr[2] = 0x00;
    net->mac_addr[3] = 0x00;
    net->mac_addr[4] = 0x00;
    net->mac_addr[5] = 0x01;
    net->opaque = slirp_state;
    net->write_packet = slirp_write_packet;
    net->select_fill = slirp_select_fill1;
    net->select_poll = slirp_select_poll1;

    return net;
}

#endif /* CONFIG_SLIRP */

BOOL virt_machine_run(RISCVMachine *s, int hartid)
{
    (void) virt_machine_get_sleep_duration(s, hartid, MAX_SLEEP_TIME);

    riscv_cpu_interp64(s->cpu_state[hartid], 1);

    if (s->htif_tohost_addr) {
        uint32_t tohost;
        bool fail = true;
        tohost = riscv_phys_read_u32(s->cpu_state[hartid], s->htif_tohost_addr, &fail);
        if (!fail && tohost & 1)
            return false;
    }

    return !riscv_terminated(s->cpu_state[hartid]) && s->common.maxinsns > 0;
}

void launch_alternate_executable(char **argv)
{
    char filename[1024];
    char new_exename[64];
    const char *p, *exename;
    int len;

    snprintf(new_exename, sizeof(new_exename), "dromajo64");
    exename = argv[0];
    p = strrchr(exename, '/');
    if (p) {
        len = p - exename + 1;
    } else {
        len = 0;
    }
    if (len + strlen(new_exename) > sizeof(filename) - 1) {
        fprintf(dromajo_stderr, "%s: filename too long\n", exename);
        exit(1);
    }
    memcpy(filename, exename, len);
    filename[len] = '\0';
    strcat(filename, new_exename);
    argv[0] = filename;

    if (execvp(argv[0], argv) < 0) {
        perror(argv[0]);
        exit(1);
    }
}

#ifdef CONFIG_FS_NET
static BOOL net_completed;

static void net_start_cb(void *arg)
{
    net_completed = TRUE;
}

static BOOL net_poll_cb(void *arg)
{
    return net_completed;
}

#endif

static void usage(const char *prog, const char *msg)
{
    fprintf(dromajo_stderr,
            "error: %s\n"
            CONFIG_VERSION ", Copyright (c) 2016-2017 Fabrice Bellard,"
            " Copyright (c) 2018,2019 Esperanto Technologies\n"
            "usage: %s {options} [config|elf-file]\n"
            "       --cmdline Kernel command line arguments to append\n"
            "       --ncpus number of cpus to simulate (default 1)\n"
            "       --load resumes a previously saved snapshot\n"
            "       --save saves a snapshot upon exit\n"
            "       --save_format [0(default)=bin, 1=hex]\n"
            "       --maxinsns terminates execution after a number of instructions\n"
            "       --terminate-event name of the validate event to terminate execution\n"
            "       --trace start trace dump after a number of instructions. Trace disabled by default\n"
            "       --ignore_sbi_shutdown continue simulation even upon seeing the SBI_SHUTDOWN call\n"
            "       --dump_memories dump memories that could be used to load a cosimulation\n"
            "       --memory_size sets the memory size in MiB (default 256 MiB)\n"
            "       --memory_addr sets the memory start address (default 0x%lx)\n"
            "       --bootrom load in a bootrom img file (default is dromajo bootrom)\n"
            "       --dtb load in a dtb file (default is dromajo dtb)\n"
            "       --compact_bootrom have dtb be directly after bootrom (default 256B after boot base)\n"
            "       --reset_vector set reset vector (default 0x%lx)\n"
            "       --mmio_range START:END [START,END) mmio range for cosim (overridden by config file)\n"
            "       --plic START:SIZE set PLIC start address and size (defaults to 0x%lx:0x%lx)\n"
            "       --clint START:SIZE set CLINT start address and size (defaults to 0x%lx:0x%lx)\n"
            "       --custom_extension add X extension to isa\n",
            msg,
            prog,
            (long)BOOT_BASE_ADDR, (long)RAM_BASE_ADDR,
            (long)PLIC_BASE_ADDR, (long)PLIC_SIZE,
            (long)CLINT_BASE_ADDR, (long)CLINT_SIZE);

    exit(EXIT_FAILURE);
}

static bool load_elf_and_fake_the_config(VirtMachineParams *p, const char *path)
{
    uint8_t    *buf;
    int         buf_len = load_file(&buf, path);

    if (elf64_is_riscv64(buf, buf_len)) {

        /* Fake the corresponding config file */
        p->files[VM_FILE_BIOS].filename = strdup(path);
        p->files[VM_FILE_BIOS].buf      = buf;
        p->files[VM_FILE_BIOS].len      = buf_len;
        p->ram_size                     = (size_t)256 << 20; // Default to 256 MiB
        p->ram_base_addr                = elf64_get_entrypoint(buf);
        elf64_find_global(buf, buf_len, "tohost", &p->htif_base_addr);

        return true;
    }

    free(buf);

    return false;
}

RISCVMachine *virt_machine_main(int argc, char **argv)
{
    const char *prog                     = argv[0];
    const char *snapshot_load_name       = 0;
    const char *snapshot_save_name       = 0;
    const char *path                     = NULL;
    const char *cmdline                  = NULL;
    uint32_t    save_format              = 0;
    long        ncpus                    = 0;
    uint64_t    maxinsns                 = 0;
    uint64_t    trace                    = UINT64_MAX;
    long        memory_size_override     = 0;
    uint64_t    memory_addr_override     = 0;
    bool        ignore_sbi_shutdown      = false;
    bool        dump_memories            = false;
    const char *bootrom_name             = 0;
    const char *dtb_name                 = 0;
    bool        compact_bootrom          = false;
    uint64_t    reset_vector_override    = 0;
    uint64_t    mmio_start_override      = 0;
    uint64_t    mmio_end_override        = 0;
    uint64_t    plic_base_addr_override  = 0;
    uint64_t    plic_size_override       = 0;
    uint64_t    clint_base_addr_override = 0;
    uint64_t    clint_size_override      = 0;
    bool        custom_extension         = false;

    dromajo_stdout = stdout;
    dromajo_stderr = stderr;

    optind = 0;

    for (;;) {
        int option_index = 0;
        static struct option long_options[] = {
            {"cmdline",                 required_argument, 0,  'c' }, // CFG
            {"ncpus",                   required_argument, 0,  'n' }, // CFG
            {"load",                    required_argument, 0,  'l' },
            {"save",                    required_argument, 0,  's' },
            {"save_format",             required_argument, 0,  'f' },
            {"maxinsns",                required_argument, 0,  'm' }, // CFG
            {"trace   ",                required_argument, 0,  't' },
            {"ignore_sbi_shutdown",     required_argument, 0,  'P' }, // CFG
            {"dump_memories",           required_argument, 0,  'D' }, // CFG
            {"memory_size",             required_argument, 0,  'M' }, // CFG
            {"memory_addr",             required_argument, 0,  'A' }, // CFG
            {"bootrom",                 required_argument, 0,  'b' }, // CFG
            {"compact_bootrom",               no_argument, 0,  'o' },
            {"reset_vector",            required_argument, 0,  'r' }, // CFG
            {"dtb",                     required_argument, 0,  'd' }, // CFG
            {"mmio_range",              required_argument, 0,  'R' }, // CFG
            {"plic",                    required_argument, 0,  'p' }, // CFG
            {"clint",                   required_argument, 0,  'C' }, // CFG
            {"custom_extension",              no_argument, 0,  'u' }, // CFG
            {0,                         0,                 0,  0 }
        };

        int c = getopt_long(argc, argv, "", long_options, &option_index);
        if (c == -1)
            break;

        switch (c) {
        case 'c':
            if (cmdline)
                usage(prog, "already had a kernel command line");
            cmdline = strdup(optarg);
            break;

        case 'n':
            if (ncpus != 0)
                usage(prog, "already had a ncpus set");
            ncpus = atoll(optarg);
            break;

        case 'l':
            if (snapshot_load_name)
                usage(prog, "already had a snapshot to load");
            snapshot_load_name = strdup(optarg);
            break;

        case 's':
            if (snapshot_save_name)
                usage(prog, "already had a snapshot to save");
            snapshot_save_name = strdup(optarg);
            break;

        case 'f':
            if (save_format)
                usage(prog, "already had a save format set");
            save_format = (uint32_t) atoll(optarg);
            break;

        case 'm':
            if (maxinsns)
                usage(prog, "already had a max instructions");
            maxinsns = (uint64_t) atoll(optarg);
            break;

        case 't':
            if (trace != UINT64_MAX)
                usage(prog, "already had a trace set");
            trace = (uint64_t) atoll(optarg);
            break;

        case 'P':
            ignore_sbi_shutdown = true;
            break;

        case 'D':
            dump_memories = true;
            break;

        case 'M':
            memory_size_override = atoi(optarg);
            break;

        case 'A':
            if (optarg[0] != '0' || optarg[1] != 'x')
                usage(prog, "--memory_addr expects argument to start with 0x... ");
            memory_addr_override = strtoll(optarg + 2, NULL, 16);
            break;

        case 'b':
            if (bootrom_name)
                usage(prog, "already had a bootrom to load");
            bootrom_name = strdup(optarg);
            break;

        case 'd':
            if (dtb_name)
                usage(prog, "already had a dtb to load");
            dtb_name = strdup(optarg);
            break;

        case 'o':
            compact_bootrom = true;
            break;

        case 'r':
            if (optarg[0] != '0' || optarg[1] != 'x')
                usage(prog, "--reset_vector expects argument to start with 0x... ");
            reset_vector_override = strtoll(optarg+2, NULL, 16);
            break;

        case 'R': {
                if (!strchr(optarg, ':'))
                    usage(prog, "--mmio_range expects an argument like START:END");

                char *mmio_start = strtok(optarg, ":");
                char *mmio_end   = strtok(NULL, ":");

                if (mmio_start[0] != '0' || mmio_start[1] != 'x')
                    usage(prog, "--mmio_range START address must begin with 0x...");
                mmio_start_override = strtoll(mmio_start+2, NULL, 16);

                if (mmio_end[0] != '0' || mmio_end[1] != 'x')
                    usage(prog, "--mmio_range END address must begin with 0x...");
                mmio_end_override = strtoll(mmio_end+2, NULL, 16);
            }
            break;

        case 'p': {
                if (!strchr(optarg, ':'))
                    usage(prog, "--plic expects an argument like START:SIZE");

                char *plic_base_addr = strtok(optarg, ":");
                char *plic_size      = strtok(NULL, ":");

                if (plic_base_addr[0] != '0' || plic_base_addr[1] != 'x')
                    usage(prog, "--plic START address must begin with 0x...");
                plic_base_addr_override = strtoll(plic_base_addr+2, NULL, 16);

                if (plic_size[0] != '0' || plic_size[1] != 'x')
                    usage(prog, "--plic SIZE must begin with 0x...");
                plic_size_override = strtoll(plic_size+2, NULL, 16);
            }
            break;

        case 'C': {
                if (!strchr(optarg, ':'))
                    usage(prog, "--clint expects an argument like START:SIZE");

                char *clint_base_addr = strtok(optarg, ":");
                char *clint_size      = strtok(NULL, ":");

                if (clint_base_addr[0] != '0' || clint_base_addr[1] != 'x')
                    usage(prog, "--clint START address must begin with 0x...");
                clint_base_addr_override = strtoll(clint_base_addr+2, NULL, 16);

                if (clint_size[0] != '0' || clint_size[1] != 'x')
                    usage(prog, "--clint SIZE must begin with 0x...");
                clint_size_override = strtoll(clint_size+2, NULL, 16);
            }
            break;

        case 'u':
            custom_extension = true;
            break;

        default:
            usage(prog, "I'm not having this argument");
        }
    }

    if (optind >= argc)
        usage(prog, "missing config file");
    else
        path = argv[optind++];

    if (optind < argc)
        usage(prog, "too many arguments");

    assert(path);
    BlockDeviceModeEnum drive_mode = BF_MODE_SNAPSHOT;
    VirtMachineParams p_s, *p = &p_s;

    virt_machine_set_defaults(p);
#ifdef CONFIG_FS_NET
    fs_wget_init();
#endif

    if (!load_elf_and_fake_the_config(p, path))
        virt_machine_load_config_file(p, path, NULL, NULL);

    if (p->logfile) {
        FILE *log_out = fopen(p->logfile, "w");
        if (!log_out) {
            perror(p->logfile);
            exit(1);
        }

        dromajo_stdout = log_out;
        dromajo_stderr = log_out;
    }


#ifdef CONFIG_FS_NET
    fs_net_event_loop(NULL, NULL);
#endif

    /* override some config parameters */
    if (memory_addr_override)
        p->ram_base_addr = memory_addr_override;
    if (memory_size_override)
        p->ram_size = memory_size_override << 20;

    if (ncpus)
        p->ncpus = ncpus;
    if (p->ncpus>=MAX_CPUS)
        usage(prog, "ncpus limit reached (MAX_CPUS).  Increase MAX_CPUS");

    if (p->ncpus == 0)
        p->ncpus = 1;

    if (cmdline)
        vm_add_cmdline(p, cmdline);

    /* open the files & devices */
    for (int i = 0; i < p->drive_count; i++) {
        BlockDevice *drive;
        char *fname;
        fname = get_file_path(p->cfg_filename, p->tab_drive[i].filename);
#ifdef CONFIG_FS_NET
        if (is_url(fname)) {
            net_completed = FALSE;
            drive = block_device_init_http(fname, 128 * 1024,
                                           net_start_cb, NULL);
            /* wait until the drive is initialized */
            fs_net_event_loop(net_poll_cb, NULL);
        } else
#endif
        {
            drive = block_device_init(fname, drive_mode);
        }
        free(fname);
        p->tab_drive[i].block_dev = drive;
    }

    for (int i = 0; i < p->fs_count; i++) {
        FSDevice *fs;
        const char *path;
        path = p->tab_fs[i].filename;
#ifdef CONFIG_FS_NET
        if (is_url(path)) {
            fs = fs_net_init(path, NULL, NULL);
            if (!fs)
                exit(1);
            fs_net_event_loop(NULL, NULL);
        } else
#endif
        {
#if defined(__APPLE__)
            fprintf(dromajo_stderr, "Filesystem access not supported yet\n");
            exit(1);
#else
            char *fname;
            fname = get_file_path(p->cfg_filename, path);
            fs = fs_disk_init(fname);
            if (!fs) {
                fprintf(dromajo_stderr, "%s: must be a directory\n", fname);
                exit(1);
            }
            free(fname);
#endif
        }
        p->tab_fs[i].fs_dev = fs;
    }

    for (int i = 0; i < p->eth_count; i++) {
#ifdef CONFIG_SLIRP
        if (!strcmp(p->tab_eth[i].driver, "user")) {
            p->tab_eth[i].net = slirp_open();
            if (!p->tab_eth[i].net)
                exit(1);
        } else
#endif
#if !defined(__APPLE__)
        if (!strcmp(p->tab_eth[i].driver, "tap")) {
            p->tab_eth[i].net = tun_open(p->tab_eth[i].ifname);
            if (!p->tab_eth[i].net)
                exit(1);
        } else
#endif
        {
            fprintf(dromajo_stderr, "Unsupported network driver '%s'\n",
                    p->tab_eth[i].driver);
            exit(1);
        }
    }

    p->console = console_init(TRUE, stdin, dromajo_stdout);
    p->dump_memories = dump_memories;

    // Setup bootrom params
    if (bootrom_name)
        p->bootrom_name = bootrom_name;
    if (dtb_name)
        p->dtb_name = dtb_name;
    p->compact_bootrom = compact_bootrom;

    // Setup particular reset vector
    if (reset_vector_override)
        p->reset_vector = reset_vector_override;

    // MMIO ranges
    if (mmio_start_override)
        p->mmio_start = mmio_start_override;
    if (mmio_end_override)
        p->mmio_end = mmio_end_override;

    // PLIC params
    if (plic_base_addr_override)
        p->plic_base_addr = plic_base_addr_override;
    if (plic_size_override)
        p->plic_size = plic_size_override;

    // CLINT params
    if (clint_base_addr_override)
        p->clint_base_addr = clint_base_addr_override;
    if (clint_size_override)
        p->clint_size = clint_size_override;

    // ISA modifications
    p->custom_extension = custom_extension;

    RISCVMachine *s = virt_machine_init(p);
    if (!s)
        return NULL;

    // Overwrite the value specified in the configuration file
    if (snapshot_load_name) {
        s->common.snapshot_load_name = snapshot_load_name;
    }

    s->common.snapshot_save_name = snapshot_save_name;
    s->common.save_format        = save_format;
    s->common.trace              = trace;

    // Allow the command option argument to overwrite the value
    // specified in the configuration file
    if (maxinsns > 0) {
        s->common.maxinsns = maxinsns;
    }

    // If not value is specified in the configuration or the command line
    // then run indefinitely
    if (s->common.maxinsns == 0)
        s->common.maxinsns = UINT64_MAX;

    for (int i = 0; i < s->ncpus; ++i)
        s->cpu_state[i]->ignore_sbi_shutdown = ignore_sbi_shutdown;

    virt_machine_free_config(p);

    if (s->common.net)
        s->common.net->device_set_carrier(s->common.net, TRUE);

    if (s->common.snapshot_load_name)
        virt_machine_deserialize(s, s->common.snapshot_load_name);

    return s;
}
