# CVA6 RISC-V CPU [![Build Status](https://github.com/openhwgroup/cva6/actions/workflows/ci.yml/badge.svg?branch=master)](https://github.com/openhwgroup/cva6/actions/workflows/ci.yml) [![CVA6 dashboard](https://riscv-ci.pages.thales-invia.fr/dashboard/badge_master.svg)](https://riscv-ci.pages.thales-invia.fr/dashboard/dashboard_cva6.html) [![Documentation Status](https://readthedocs.com/projects/openhw-group-cva6-user-manual/badge/?version=latest)](https://docs.openhwgroup.org/projects/cva6-user-manual/?badge=latest) [![GitHub release](https://img.shields.io/github/release/openhwgroup/cva6?include_prereleases=&sort=semver&color=blue)](https://github.com/openhwgroup/cva6/releases/)

CVA6 is a 6-stage, single-issue, in-order CPU which implements the 64-bit RISC-V instruction set. It fully implements I, M, A and C extensions as specified in Volume I: User-Level ISA V 2.3 as well as the draft privilege extension 1.10. It implements three privilege levels M, S, U to fully support a Unix-like operating system. Furthermore, it is compliant to the draft external debug spec 0.13.

It has a configurable size, separate TLBs, a hardware PTW and branch-prediction (branch target buffer and branch history table). The primary design goal was on reducing critical path length.

The CVA6 core is part of a vivid ecosystem. In [this document](RESOURCES.md), we gather pointers to this ecosystem (building blocks, designs, partners...).

A performance model of CVA6 is available in the `perf-model/` folder of this repository.
It can be used to investigate performance-related micro-architecture changes.

<img src="docs/03_cva6_design/_static/ariane_overview.drawio.png"/>


# Quick setup

The following instructions will allow you to compile and run a Verilator model of the CVA6 APU (which instantiates the CVA6 core) within the CVA6 APU testbench (corev_apu/tb).

Throughout all build and simulations scripts executions, you can use the environment variable `NUM_JOBS` to set the number of concurrent jobs launched by `make`:
- if left undefined, `NUM_JOBS` will default to 1, resulting in a sequential execution
of `make` jobs;
- when setting `NUM_JOBS` to an explicit value, it is recommended not to exceed 2/3 of
the total number of virtual cores available on your system.    

1. Checkout the repository and initialize all submodules.
```sh
git clone https://github.com/openhwgroup/cva6.git
cd cva6
git submodule update --init --recursive
```

2. Install the GCC Toolchain [build prerequisites](util/toolchain-builder/README.md#Prerequisites) then [the toolchain itself](util/toolchain-builder/README.md#Getting-started).

:warning: It is **strongly recommended** to use the toolchain built with the provided scripts.

3. Install `cmake`, version 3.14 or higher.

4. Set the RISCV environment variable.
```sh
export RISCV=/path/to/toolchain/installation/directory
```

5. Install `help2man` and `device-tree-compiler` packages.

For Debian-based Linux distributions, run :

```sh
sudo apt-get install help2man device-tree-compiler
```

6. Install the riscv-dv requirements:

```sh
pip3 install -r verif/sim/dv/requirements.txt
```

7. Run these commands to install a custom Spike and Verilator (i.e. these versions must be used to simulate the CVA6) and [these](#running-regression-tests-simulations) tests suites.
```sh
# DV_SIMULATORS is detailed in the next section
export DV_SIMULATORS=veri-testharness,spike
bash verif/regress/smoke-tests.sh
```


# Tutorials

* **[Running Simulations](tutorials/running_sim.md)**
* **[ASIC Implementation](tutorials/asic.md)**
* **[FPGA Implementation and running an OS](tutorials/fpga.md)**


- **Agilex 7**
  
   Tested on Quartus Prime Version 24.1.0 Pro Edition. The FPGA currently contains the following peripherals:
  
   - DDR4 memory controller
   - JTAG port (see debugging section below)
   - Bootrom containing zero stage bootloader
   - UART
   - GPIOs connected to LEDs

> The ethernet controller and the corresponding network connection, as well as the SD Card connection and the capability to boot linux are still work in progress and not functional at the moment. Expect some updates soon-ish. 


## Programming the Memory Configuration File or bitstream

- **Genesys 2**

   - Open Vivado
   - Open the hardware manager and open the target board (Genesys II - `xc7k325t`)
   - Tools - Add Configuration Memory Device
   - Select the following Spansion SPI flash `s25fl256xxxxxx0`
   - Add `ariane_xilinx.mcs`
   - Press Ok. Flashing will take a couple of minutes.
   - Right click on the FPGA device - Boot from Configuration Memory Device (or press the program button on the FPGA)

- **Agilex 7**

   - Open Quartus programmer
   - Configure HW Setup by selecting the AGF FPGA Development Kit
   - Click Auto-Detect to scan the JTAG chain
   - In the device list, right click over device AGFB014R24B and add file (.sof)
   - Click on Start button to program the FPGA
   - Right now only baremetal is supported, so right after programming you can connect to the UART and see your CVA6 alive on Agilex!
   - For this you need to use the JTAG UART provided with Quartus installation

```
.$quartus_installation_path/qprogrammer/quartus/bin/juart-terminal 
juart-terminal: connected to hardware target using JTAG UART on cable
juart-terminal: "AGF FPGA Development Kit [1-3]", device 1, instance 0
juart-terminal: (Use the IDE stop button or Ctrl-C to terminate)

Hello World!
```

## Preparing the SD Card

The first stage bootloader will boot from SD Card by default. Get yourself a suitable SD Card (we use [this](https://www.amazon.com/Kingston-Digital-Mobility-MBLY10G2-32GB/dp/B00519BEQO) one). Either grab a pre-built Linux image from [here](https://github.com/pulp-platform/ariane-sdk/releases) or generate the Linux image yourself following the README in the [ariane-sdk repository](https://github.com/pulp-platform/ariane-sdk). Prepare the SD Card by following the "Booting from SD card" section in the ariane-sdk repository.

Connect a terminal to the USB serial device opened by the FTDI chip e.g.:
```
screen /dev/ttyUSB0 115200
```

Default baudrate set by the bootlaoder and Linux is `115200`.

After you've inserted the SD Card and programmed the FPGA you can connect to the serial port of the FPGA and should see the bootloader and afterwards Linux booting. Default username is `root`, no password required.


## Generating a Bitstream

- **Genesys 2**

To generate the FPGA bitstream (and memory configuration) yourself for the Genesys II board run:

```
make fpga
```

This will produce a bitstream file and memory configuration file (in `fpga/work-fpga`) which you can permanently flash by running the above commands.

- **Agilex 7**

To generate the FPGA bitstream yourself for the Agilex 7 board run:

```
make altera
```

We recommend to set the parameter FpgaAlteraEn (and also FpgaEn) to benefit from the FPGA optimizations.

This will produce a bitstream file (in `altera/output_files`) which you can program following the previous instructions. **Note: Bear in mind that you need a Quartus Pro Licence to be able to generate this bitstream**

To clean the project after generating the bitstream, use 

```
make clean-altera
```

## Debugging

- **Genesys 2**
You can debug (and program) the FPGA using [OpenOCD](http://openocd.org/doc/html/Architecture-and-Core-Commands.html). We provide two example scripts for OpenOCD below.

To get started, connect the micro USB port that is labeled with JTAG to your machine. This port is attached to the FTDI 2232 USB-to-serial chip on the Genesys 2 board, and is usually used to access the native JTAG interface of the Kintex-7 FPGA (e.g. to program the device using Vivado). However, the FTDI chip also exposes a second serial link that is routed to GPIO pins on the FPGA, and we leverage this to wire up the JTAG from the RISC-V debug module.

>If you are on an Ubuntu based system you need to add the following udev rule to `/etc/udev/rules.d/99-ftdi.rules`
>```
> SUBSYSTEM=="usb", ACTION=="add", ATTRS{idProduct}=="6010", ATTRS{idVendor}=="0403", MODE="664", GROUP="plugdev"
>```

Once attached to your system, the FTDI chip should be listed when you type `lsusb`:

```
Bus 005 Device 019: ID 0403:6010 Future Technology Devices International, Ltd FT2232C/D/H Dual UART/FIFO IC
```

If this is the case, you can go on and start openocd with the `fpga/ariane.cfg` configuration file:

```
openocd -f fpga/ariane.cfg

Open On-Chip Debugger 0.10.0+dev-00195-g933cb87 (2018-09-14-19:32)
Licensed under GNU GPL v2
For bug reports, read
    http://openocd.org/doc/doxygen/bugs.html
adapter speed: 1000 kHz
Info : auto-selecting first available session transport "jtag". To override use 'transport select <transport>'.
Info : clock speed 1000 kHz
Info : TAP riscv.cpu does not have IDCODE
Info : datacount=2 progbufsize=8
Info : Examined RISC-V core; found 1 harts
Info :  hart 0: XLEN=64, misa=0x8000000000141105
Info : Listening on port 3333 for gdb connections
Ready for Remote Connections
Info : Listening on port 6666 for tcl connections
Info : Listening on port 4444 for telnet connections
Info : accepting 'gdb' connection on tcp/3333
```
- **Agilex 7**

You can debug (and program) the FPGA using a modified version of OpenOCD included with Quartus installation ($quartus_installation_path/qprogrammer/quartus/bin/openocd). 

To get started, connect the micro USB port that is labeled with J13 to your machine. It is the same port that is used for the UART. Both use the JTAG interface and connect to the System Level Debugging (SLD) Hub instantiated inside the FPGA. Then the debugger connection goes to the virtual JTAG IP (vJTAG) which can be accessed with the modified version of OpenOCD.

You can start openocd with the `altera/cva6.cfg` configuration file:

```
./$quartus_installation_path/qprogrammer/quartus/bin/openocd -f altera/cva6.cfg 
Open On-Chip Debugger 0.11.0-R22.4
Licensed under GNU GPL v2
For bug reports, read
        http://openocd.org/doc/doxygen/bugs.html
Info : only one transport option; autoselect 'jtag'
Info : Application name is OpenOCD.20241016093010
Info : No cable specified, so will be searching for cables

Info : At present, The first hardware cable will be used [1 cable(s) detected]
Info : Cable 1: device_name=(null), hw_name=AGF FPGA Development Kit, server=(null), port=1-3, chain_id=0x559319c8cde0, persistent_id=1, chain_type=1, features=34816, server_version_info=Version 24.1.0 Build 115 03/21/2024 SC Pro Edition
Info : TAP position 0 (C341A0DD) has 3 SLD nodes
Info :     node  0 idcode=00406E00 position_n=0
Info :     node  1 idcode=30006E00 position_n=0
Info :     node  2 idcode=0C006E00 position_n=0
Info : TAP position 1 (20D10DD) has 1 SLD nodes
Info :     node  0 idcode=0C206E00 position_n=0
Info : Discovered 2 TAP devices
Info : Detected device (tap_position=0) device_id=c341a0dd, instruction_length=10, features=12, device_name=AGFB014R24A(.|R1|R2)/..
Info : Found an Intel device at tap_position 0.Currently assuming it is SLD Hub
Info : Detected device (tap_position=1) device_id=020d10dd, instruction_length=10, features=4, device_name=VTAP10
Info : Found an Intel device at tap_position 1.Currently assuming it is SLD Hub
Info : This adapter doesn't support configurable speed
Info : JTAG tap: agilex7.fpga.tap tap/device found: 0xc341a0dd (mfg: 0x06e (Altera), part: 0x341a, ver: 0xc)
Info : JTAG tap: auto0.tap tap/device found: 0x020d10dd (mfg: 0x06e (Altera), part: 0x20d1, ver: 0x0)
Info : JTAG tap: agilex7.fpga.tap Parent Tap found: 0xc341a0dd (mfg: 0x06e (Altera), part: 0x341a, ver: 0xc)
Info : Virtual Tap/SLD node 0x00406E00 found at tap position 0 vtap position 0
Warn : AUTO auto0.tap - use "jtag newtap auto0 tap -irlen 10 -expected-id 0x020d10dd"
Info : datacount=2 progbufsize=8
Info : Examined RISC-V core; found 1 harts
Info :  hart 0: XLEN=32, misa=0x40141107
Info : starting gdb server for agilex7.cva6.0 on 3333
Info : Listening on port 3333 for gdb connections
Ready for Remote Connections
Info : Listening on port 6666 for tcl connections
Info : Listening on port 4444 for telnet connections
```

- **Common for both boards**

Then you will be able to either connect through `telnet` or with `gdb`:

```
risc-none-elf-gdb /path/to/elf

(gdb) target remote localhost:3333
(gdb) load
Loading section .text, size 0x6508 lma 0x80000000
Loading section .rodata, size 0x900 lma 0x80006508
(gdb) b putchar
(gdb) c
Continuing.

Program received signal SIGTRAP, Trace/breakpoint trap.
0x0000000080009126 in putchar (s=72) at lib/qprintf.c:69
69    uart_sendchar(s);
(gdb) si
0x000000008000912a  69    uart_sendchar(s);
(gdb) p/x $mepc
$1 = 0xfffffffffffdb5ee
```

You can read or write device memory by using:
```
(gdb) x/i 0x1000
    0x1000: lui t0,0x4
(gdb) set {int} 0x1000 = 22
(gdb) set $pc = 0x1000
```


## Preliminary Support for OpenPiton Cache System

CVA6 has preliminary support for the OpenPiton distributed cache system from Princeton University. To this end, a different L1 cache subsystem (`src/cache_subsystem/wt_cache_subsystem.sv`) has been developed that follows a write-through protocol and that has support for cache invalidations and atomics.

The corresponding integration patches will be released on [OpenPiton GitHub repository](https://github.com/PrincetonUniversity/openpiton). Check the `README` in that repository to see how to use CVA6 in the OpenPiton setting.

To activate the different cache system, compile your code with the macro `DCACHE_TYPE`.

## Hybrid Cache Implementation

The CVA6 now supports a hybrid cache implementation that dynamically switches between set associative and fully associative cache organizations based on the processor's privilege level:

- **Machine Mode (M-mode)**: Uses set associative organization for better performance
- **Supervisor/User Mode (S/U-mode)**: Uses fully associative organization for better isolation

This provides better security isolation while maintaining performance for trusted code. Four configurations are available:

1. **WT**: Standard Write-Through cache (baseline)
2. **WT_HYB**: Hybrid cache with dynamic privilege-based mode switching
3. **WT_HYB_FORCE_SET_ASS**: Hybrid cache forced to set associative mode
4. **WT_HYB_FORCE_FULL_ASS**: Hybrid cache forced to fully associative mode

The fully associative mode uses a hash function seeded by the `HASH_SEED` parameter to randomize lookup table indices and reduce deterministic collisions.

To compare these configurations, use the provided `compare_hybrid_cache_configs.sh` script. For detailed analysis, use the `analyze_hybrid_cache.py` script which generates visualizations and reports. Pass `-j` to adjust the number of worker threads and `--verbose` to print progress while parsing logs.

For more details, see the [hybrid_cache_validation.md](hybrid_cache_validation.md) document.
See `docs/hybrid_cache/advanced_visualization.md` for instructions on generating timeline views and interactive charts.


## Re-generating the Bootcode (ZSBL)

The zero stage bootloader (ZSBL) for RTL simulation lives in `bootrom/` while the bootcode for the FPGA is in `fpga/src/bootrom`. The RTL bootcode simply jumps to the base of the DRAM where the FSBL takes over. For the FPGA the ZSBL performs additional housekeeping. Both bootloader pass the hartid as well as address to the device tree in argumen register `a0` and `a1` respectively.

To re-generate the bootcode you can use the existing makefile within those directories. To generate the SystemVerilog files you will need the `bitstring` python package installed on your system.


# Directory Structure:

The directory structure separates the [CVA6 RISC-V CPU](#cva6-risc-v-cpu) core from the [CORE-V-APU FPGA Emulation Platform](#corev-apu-fpga-emulation).
Files, directories and submodules under `cva6` are for the core _only_ and should not have any dependencies on the APU.
Files, directories and submodules under `corev_apu` are for the FPGA Emulation platform.
The CVA6 core can be compiled stand-alone, and obviously the APU is dependent on the core.

The top-level directories of this repo:
* **ci**: Scriptware for CI.
* **common**: Source code used by both the CVA6 Core and the COREV APU. Subdirectories from here are `local` for common files that are hosted in this repo and `submodules` that are hosted in other repos.
* **core**: Source code for the CVA6 Core only. There should be no sources in this directory used to build anything other than the CVA6 core.
* **corev_apu**: Source code for the CVA6 APU, exclusive of the CVA6 core. There should be no sources in this directory used to build the CVA6 core.
* **docs**: Documentation.
* **pd**: Example and CI scripts to synthesis CVA6.
* **util**: General utility scriptware.
* **vendor**: Third-party IP maintained outside the repository.
* **verif**: Verification environment for the CVA6. The verification files shared with other cores are in the [core-v-verif](https://github.com/openhwgroup/core-v-verif) repository on GitHub. core-v-verif is defined as a cva6 submodule.


## verif Directories

- **bsp**:     board support package for test-programs compiled/assembled/linked for the CVA6.
This BSP is used by both `core` testbench and `uvmt_cva6` UVM verification environment.
- **regress**: scripts to install tools, test suites, CVA6 code and to execute tests
- **sim**:     simulation environment (e.g. riscv-dv)
- **tb**:      testbench module instancing the core
- **tests**:   source of test cases and test lists


# Contributing

We highly appreciate community contributions.
To ease the work of reviewing contributions, please review [CONTRIBUTING](CONTRIBUTING.md).

Contributions to the documentation (`docs/` and `tutorials/` directories) are very welcome as well.

If you find any problems or issues with CVA6 or the documentation, please check out the [issue tracker](https://github.com/openhwgroup/cva6/issues)
and create a new issue if your problem is not yet tracked. \
[The CVA6 Kanban Board](https://github.com/orgs/openhwgroup/project/3/view/7) loosely tracks planned improvements.


# Publication

If you use CVA6 in your academic work you can cite us:

<details>
<summary>CVA6 Publication</summary>

```
@article{zaruba2019cost,
   author={F. {Zaruba} and L. {Benini}},
   journal={IEEE Transactions on Very Large Scale Integration (VLSI) Systems},
   title={The Cost of Application-Class Processing: Energy and Performance Analysis of a Linux-Ready 1.7-GHz 64-Bit RISC-V Core in 22-nm FDSOI Technology},
   year={2019},
   volume={27},
   number={11},
   pages={2629-2640},
   doi={10.1109/TVLSI.2019.2926114},
   ISSN={1557-9999},
   month={Nov},
}
```

</details>

# Acknowledgements

Check out the [acknowledgements](ACKNOWLEDGEMENTS.md).


