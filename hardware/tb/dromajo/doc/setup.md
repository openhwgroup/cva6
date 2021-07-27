# Example things on run on Dromajo

## Bare-metal riscv-tests (~ 2 min)

Assumption: you have the `riscv64-unknown-elf-` (Newlib) toolchain.

```
git clone --recursive https://github.com/riscv/riscv-tests
cd riscv-tests
autoconf
./configure --prefix=${PWD}/../riscv-tests-root/
make
make install
cd ..
```

To run one of the benchmarks with trace enabled

```
../src/dromajo --trace 0 riscv-tests-root/share/riscv-tests/isa/rv64ua-p-amoadd_d
```

## Linux with buildroot

### Get a trivial buildroot (~ 23 min)

```
wget -nc https://github.com/buildroot/buildroot/archive/2019.08.1.tar.gz
tar xzf 2019.08.1.tar.gz
cp config-buildroot-2019.08.1 buildroot-2019.08.1/.config
make -j16 -C buildroot-2019.08.1
```

### Get the Linux kernel up and running (~ 3 min)

Assumption: you have the `riscv64-linux-gnu-` (GlibC) toolchain.

```
export CROSS_COMPILE=riscv64-linux-gnu-
wget -nc https://github.com/torvalds/linux/archive/v5.7-rc4.tar.gz
tar -xvf v5.7-rc4.tar.gz
make -C linux-5.7-rc4 ARCH=riscv defconfig
make -C linux-5.7-rc4 ARCH=riscv -j16
```

### OpenSBI (~ 1 min)

```
export CROSS_COMPILE=riscv64-linux-gnu-
git clone https://github.com/riscv/opensbi.git
cd opensbi
git checkout 7be75f519f7705367030258c4410d9ff9ea24a6f -b temp
make PLATFORM=generic
cd ..
```

### To boot Linux (login:root password:root)

```
cp buildroot-2019.08.1/output/images/rootfs.* .
cp linux-5.7-rc4/arch/riscv/boot/Image .
cp opensbi/build/platform/generic/firmware/fw_jump.bin .
../src/dromajo boot.cfg
```

### To boot a quad-core RISC-V CPU

```
../src/dromajo --ncpus 4 boot.cfg
```

### Create and run checkpoints

Dromajo creates checkpoints by dumping the memory state, and creating a bootram
that includes a sequence of valid RISC-V instructions to recover the CPU to the
same state as before the checkpoint was created. This information includes not
only the architectural state, but CSRs, and PLIC/CLINT programmed registers. It
does not include any state in a hardware devices.

It allows to create Linux boot checkpoints. E.g:

Run 1M instructions and create a checkpoint from a Linux+openSBI boot:

```
../src/dromajo --save ck1 --maxinsn 2000000 ./boot.cfg

OpenSBI v0.7-39-g7be75f5
   ____                    _____ ____ _____
  / __ \                  / ____|  _ \_   _|
 | |  | |_ __   ___ _ __ | (___ | |_) || |
 | |  | | '_ \ / _ \ '_ \ \___ \|  _ < | |
 | |__| | |_) |  __/ | | |____) | |_) || |_
  \____/| .__/ \___|_| |_|_____/|____/_____|
        | |
        |_|

Platform Name          : ucbbar,dromajo-bare
Platform HART Count    : 1
Boot HART ID           : 0
Boot HART ISA          : rv64imafdcsu
Firmware Base          : 0x80000000
Firmware Size          : 76 KB
Runtime SBI Version    : 0.2

MIDELEG : 0x0000000000000222
MEDELEG : 0x000000000000b109
PMP0    : 0x0000000080000000-0x000000008001ffff (A)
PMP1    : 0x0000000000000000-0x000001ffffffffff (A,R,W,X)

Power off.
plic: 0 0 timecmp=ffffffffffffffff
NOTE: creating a new boot rom
clint hartid=0 timecmp=-1 cycles (124999)
```

The previous example creates 3 files. ck1.re_regs is an ascii dump for
debugging. The ck1.mainram is a memory dump of the main memory after 1M cycles.
The ck1.bootram is the new bootram needed to recover the state.

To continue booting Linux:

```
../src/dromajo --load ck1 ./boot.cfg
[    0.000000] OF: fdt: Ignoring memory range 0x80000000 - 0x80200000
[    0.000000] Linux version 5.7.0-rc4 (anup@anup-ubuntu64) (gcc version 9.2.0 (GCC), GNU ld (GNU Binutils) 2.32) #1 SMP Fri May 8 10:04:14 IST 2020
[    0.000000] earlycon: sbi0 at I/O port 0x0 (options '')
[    0.000000] printk: bootconsole [sbi0] enabled
[    0.000000] Initial ramdisk at: 0x(____ptrval____) (4997120 bytes)
[    0.000000] Zone ranges:
[    0.000000]   DMA32    [mem 0x0000000080200000-0x00000000bfffffff]
[    0.000000]   Normal   empty
[    0.000000] Movable zone start for each node
[    0.000000] Early memory node ranges
[    0.000000]   node   0: [mem 0x0000000080200000-0x00000000bfffffff]
[    0.000000] Initmem setup node 0 [mem 0x0000000080200000-0x00000000bfffffff]
[    0.000000] software IO TLB: mapped [mem 0xbad39000-0xbed39000] (64MB)
[    0.000000] SBI specification v0.2 detected
[    0.000000] SBI implementation ID=0x1 Version=0x7
[    0.000000] SBI v0.2 TIME extension detected
[    0.000000] SBI v0.2 IPI extension detected
[    0.000000] SBI v0.2 RFENCE extension detected
[    0.000000] SBI v0.2 HSM extension detected
[    0.000000] elf_hwcap is 0x112d
[    0.000000] percpu: Embedded 17 pages/cpu s31976 r8192 d29464 u69632
[    0.000000] Built 1 zonelists, mobility grouping on.  Total pages: 258055
[    0.000000] Kernel command line: root=/dev/ram rw earlycon=sbi console=hvc0
[    0.000000] Dentry cache hash table entries: 131072 (order: 8, 1048576 bytes, linear)
[    0.000000] Inode-cache hash table entries: 65536 (order: 7, 524288 bytes, linear)
[    0.000000] Sorting __ex_table...
[    0.000000] mem auto-init: stack:off, heap alloc:off, heap free:off
[    0.000000] Memory: 942628K/1046528K available (6386K kernel code, 4285K rwdata, 4096K rodata, 235K init, 317K bss, 103900K reserved, 0K cma-reserved)
[    0.000000] Virtual kernel memory layout:
[    0.000000]       fixmap : 0xffffffcefee00000 - 0xffffffceff000000   (2048 kB)
[    0.000000]       pci io : 0xffffffceff000000 - 0xffffffcf00000000   (  16 MB)
[    0.000000]      vmemmap : 0xffffffcf00000000 - 0xffffffcfffffffff   (4095 MB)
[    0.000000]      vmalloc : 0xffffffd000000000 - 0xffffffdfffffffff   (65535 MB)
[    0.000000]       lowmem : 0xffffffe000000000 - 0xffffffe03fe00000   (1022 MB)
[    0.000000] SLUB: HWalign=64, Order=0-3, MinObjects=0, CPUs=1, Nodes=1
[    0.000000] rcu: Hierarchical RCU implementation.
[    0.000000] rcu: 	RCU restricting CPUs from NR_CPUS=8 to nr_cpu_ids=1.
[    0.000000] rcu: 	RCU debug extended QS entry/exit.
[    0.000000] rcu: RCU calculated value of scheduler-enlistment delay is 25 jiffies.
[    0.000000] rcu: Adjusting geometry for rcu_fanout_leaf=16, nr_cpu_ids=1
[    0.000000] NR_IRQS: 0, nr_irqs: 0, preallocated irqs: 0
[    0.000000] plic: mapped 31 interrupts with 1 handlers for 2 contexts.
[    0.000000] riscv_timer_init_dt: Registering clocksource cpuid [0] hartid [0]
[    0.000000] clocksource: riscv_clocksource: mask: 0xffffffffffffffff max_cycles: 0x24e6a1710, max_idle_ns: 440795202120 ns
[    0.000024] sched_clock: 64 bits at 10MHz, resolution 100ns, wraps every 4398046511100ns
[    0.000752] Console: colour dummy device 80x25
[    0.000995] printk: console [hvc0] enabled
[    0.000995] printk: console [hvc0] enabled
[    0.001400] printk: bootconsole [sbi0] disabled
[    0.001400] printk: bootconsole [sbi0] disabled
[    0.001878] Calibrating delay loop (skipped), value calculated using timer frequency.. 20.00 BogoMIPS (lpj=40000)
[    0.002403] pid_max: default: 32768 minimum: 301
[    0.003226] Mount-cache hash table entries: 2048 (order: 2, 16384 bytes, linear)
[    0.003630] Mountpoint-cache hash table entries: 2048 (order: 2, 16384 bytes, linear)
[    0.008021] rcu: Hierarchical SRCU implementation.
[    0.009313] smp: Bringing up secondary CPUs ...
[    0.009557] smp: Brought up 1 node, 1 CPU
[    0.010551] devtmpfs: initialized
[    0.013004] random: get_random_u32 called from bucket_table_alloc.isra.0+0x4e/0x154 with crng_init=0
[    0.013985] clocksource: jiffies: mask: 0xffffffff max_cycles: 0xffffffff, max_idle_ns: 7645041785100000 ns
[    0.014915] futex hash table entries: 256 (order: 2, 16384 bytes, linear)
[    0.016379] NET: Registered protocol family 16
[    0.066786] vgaarb: loaded
[    0.067978] SCSI subsystem initialized
[    0.069291] usbcore: registered new interface driver usbfs
[    0.069711] usbcore: registered new interface driver hub
[    0.070082] usbcore: registered new device driver usb
[    0.073131] clocksource: Switched to clocksource riscv_clocksource
[    0.093678] NET: Registered protocol family 2
[    0.095795] tcp_listen_portaddr_hash hash table entries: 512 (order: 2, 20480 bytes, linear)
[    0.096347] TCP established hash table entries: 8192 (order: 4, 65536 bytes, linear)
[    0.097372] TCP bind hash table entries: 8192 (order: 6, 262144 bytes, linear)
[    0.099225] TCP: Hash tables configured (established 8192 bind 8192)
[    0.099781] UDP hash table entries: 512 (order: 3, 49152 bytes, linear)
[    0.100359] UDP-Lite hash table entries: 512 (order: 3, 49152 bytes, linear)
[    0.101320] NET: Registered protocol family 1
[    0.102643] RPC: Registered named UNIX socket transport module.
[    0.102946] RPC: Registered udp transport module.
[    0.103193] RPC: Registered tcp transport module.
[    0.103442] RPC: Registered tcp NFSv4.1 backchannel transport module.
[    0.103772] PCI: CLS 0 bytes, default 64
[    0.104442] Unpacking initramfs...
[    0.234261] Freeing initrd memory: 4880K
[    0.236114] workingset: timestamp_bits=62 max_order=18 bucket_order=0
[    0.271749] NFS: Registering the id_resolver key type
[    0.272075] Key type id_resolver registered
[    0.272298] Key type id_legacy registered
[    0.272536] nfs4filelayout_init: NFSv4 File Layout Driver Registering...
[    0.273319] 9p: Installing v9fs 9p2000 file system support
[    0.274667] NET: Registered protocol family 38
[    0.274973] Block layer SCSI generic (bsg) driver version 0.4 loaded (major 252)
[    0.275344] io scheduler mq-deadline registered
[    0.275584] io scheduler kyber registered
update_mip: hartid=0 mask=0 value=0
[    0.441363] Serial: 8250/16550 driver, 4 ports, IRQ sharing disabled
[    0.444490] sifive-serial 54000000.uart: IRQ index 0 not found
[    0.446348] [drm] radeon kernel modesetting enabled.
[    0.469590] loop: module loaded
[    0.472629] libphy: Fixed MDIO Bus: probed
[    0.475395] e1000e: Intel(R) PRO/1000 Network Driver - 3.2.6-k
[    0.475693] e1000e: Copyright(c) 1999 - 2015 Intel Corporation.
[    0.476289] ehci_hcd: USB 2.0 'Enhanced' Host Controller (EHCI) Driver
[    0.476620] ehci-pci: EHCI PCI platform driver
[    0.476958] ehci-platform: EHCI generic platform driver
[    0.477417] ohci_hcd: USB 1.1 'Open' Host Controller (OHCI) Driver
[    0.477752] ohci-pci: OHCI PCI platform driver
[    0.478089] ohci-platform: OHCI generic platform driver
[    0.479174] usbcore: registered new interface driver uas
[    0.479599] usbcore: registered new interface driver usb-storage
[    0.480257] mousedev: PS/2 mouse device common for all mice
[    0.482197] usbcore: registered new interface driver usbhid
[    0.482480] usbhid: USB HID core driver
[    0.485418] NET: Registered protocol family 10
[    0.487962] Segment Routing with IPv6
[    0.488378] sit: IPv6, IPv4 and MPLS over IPv4 tunneling driver
[    0.490490] NET: Registered protocol family 17
[    0.491411] 9pnet: Installing 9P2000 support
[    0.491785] Key type dns_resolver registered
[    0.493290] sifive-serial 54000000.uart: IRQ index 0 not found
[    0.494004] sifive-serial 54000000.uart: IRQ index 0 not found
[    0.496251] Freeing unused kernel memory: 232K
[    0.501340] Run /init as init process
Starting syslogd: OK
Starting klogd: OK
Running sysctl: OK
Initializing random number generator... [    0.743667] random: dd: uninitialized urandom read (512 bytes read)
done.
Starting network: OK

Welcome to Dromajo Buildroot
buildroot login:
```
