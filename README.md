![Build Status](https://github.com/openhwgroup/cva6/actions/workflows/ci.yml/badge.svg?branch=master)

> **Warning**
> We inform you that big RTL modifications are in process to better parametrize CVA6. For deeper information, please refer to the https://github.com/openhwgroup/cva6/issues/1233 github issue :warning:

These changes will impact CVA6 interfaces (and top-level parameters). They will be performed progressively with several pull requests over a few weeks.
To avoid integrating a moving target in their design, CVA6 users can therefore consider pointing to a specific GitHub hash during the changes
(or investigate [vendorization](https://opentitan.org/book/util/doc/vendor.html)).

# CVA6 RISC-V CPU

CVA6 is a 6-stage, single-issue, in-order CPU which implements the 64-bit RISC-V instruction set. It fully implements I, M, A and C extensions as specified in Volume I: User-Level ISA V 2.3 as well as the draft privilege extension 1.10. It implements three privilege levels M, S, U to fully support a Unix-like operating system. Furthermore, it is compliant to the draft external debug spec 0.13.

It has a configurable size, separate TLBs, a hardware PTW and branch-prediction (branch target buffer and branch history table). The primary design goal was on reducing critical path length.

![](docs/01_cva6_user/_static/ariane_overview.png)

## Directory Structure:
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

## Contributing
We highly appreciate community contributions.
<br><br>To ease the work of reviewing contributions, please review [CONTRIBUTING](https://github.com/openhwgroup/cva6/blob/master/CONTRIBUTING.md).

## Issues and Troubleshooting
If you find any problems or issues with CVA6 or the documentation, please check out the [issue tracker](https://github.com/openhwgroup/cva6/issues)
and create a new issue if your problem is not yet tracked.

## Publication

If you use CVA6 in your academic work you can cite us:

<details>
<summary>CVA6 Publication</summary>
<p>

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

</p>
</details>

CVA6 User Documentation
=======================

- [CVA6 RISC-V CPU](#cva6-risc-v-cpu)
  - [Directory Structure:](#directory-structure)
  - [Verification](#verification)
  - [Contributing](#contributing)
  - [Issues and Troubleshooting](#issues-and-troubleshooting)
  - [Publication](#publication)
- [CVA6 User Documentation](#cva6-user-documentation)
  - [Getting Started](#getting-started)
    - [Checkout Repo](#checkout-repo)
    - [Build Model and Run Simulations with verif directory](#build-model-and-run-simulations-with-verif-directory)
      - [Directories](#directories)
      - [Prerequisites](#prerequisites)
      - [Environent setup](#environent-setup)
      - [Test execution](#test-execution)
    - [Running User-Space Applications](#running-user-space-applications)
  - [Physical Implementation](#physical-implementation)
    - [ASIC Synthesis](#asic-synthesis)
    - [ASIC Gate Simulation with `core-v-verif` repository](#asic-gate-simulation-with-core-v-verif-repository)
  - [COREV-APU FPGA Emulation](#corev-apu-fpga-emulation)
    - [Programming the Memory Configuration File](#programming-the-memory-configuration-file)
    - [Preparing the SD Card](#preparing-the-sd-card)
    - [Generating a Bitstream](#generating-a-bitstream)
    - [Debugging](#debugging)
    - [Preliminary Support for OpenPiton Cache System](#preliminary-support-for-openpiton-cache-system)
  - [Planned Improvements](#planned-improvements)
  - [Going Beyond](#going-beyond)
    - [CI Testsuites and Randomized Constrained Testing with Torture](#ci-testsuites-and-randomized-constrained-testing-with-torture)
    - [Memory Preloading](#memory-preloading)
    - [Re-generating the Bootcode (ZSBL)](#re-generating-the-bootcode-zsbl)
- [Contributing](#contributing-1)
- [Acknowledgements](#acknowledgements)

Created by [gh-md-toc](https://github.com/ekalinin/github-markdown-toc)

## Getting Started

The following instructions will allow you to compile and run a Verilator model of the CVA6 APU (which instantiates the CVA6 core) within the CVA6 APU testbench (corev_apu/tb).

### Checkout Repo

Checkout the repository and initialize all submodules
```sh
git clone https://github.com/openhwgroup/cva6.git
cd cva6
git submodule update --init --recursive
```

### Build Model and Run Simulations with verif directory

#### verif Directories
- **bsp**:     board support package for test-programs compiled/assembled/linked for the CVA6.
This BSP is used by both `core` testbench and `uvmt_cva6` UVM verification environment.
- **regress**: scripts to install tools, test suites, CVA6 code and to execute tests
- **sim**:     simulation environment (e.g. riscv-dv)
- **tb**:      testbench module instancing the core
- **tests**:   source of test cases and test lists

There are README files in each directory with additional information.

#### Prerequisites

In brief, you will need:
- a native C/C++ development environment to build simulation tools and models;
- a RISC-V toolchain to build the CVA6 test programs;
- optionally, an EDA tool that supports building and running simulation models of designs expressed in SystemVerilog.

To build the open-source tools used by CVA6 and to run CVA6 simulations, you will need
a native compilation toolchain for C and C++.  Such toolchains are available on virtually
all Linux distributions as pre-installed or optional packages.   If unsure, ask your system
administrator to install one on your system.

To build test programs for the CVA6 core, you need a RISC-V toolchain.
For GCC-based toolchains, only GCC versions above 11.1.0 are supported;
it is recommended to use GCC 13.1.0 or above.

You can use a pre-built toolchain (available for most common Linux/macOS
distributions from a variety of providers) or build one from scratch using
publicly available source code repositiores.  The second approach may prove
necessary on older or unsupported Linux installations.

To use a pre-built RISC-V toolchain, download and install the package(s) for your
Linux distribution as per instructions from the toolchain provider, and set the
`RISCV` environment variable to the installation location of the toolchain:

```sh
# Set environment variable RISCV to the location of the installed toolchain.
export RISCV=/path/to/toolchain/installation/directory
```

To build and install RISC-V GCC toolchain locally, you can use the toolchain generation scripts
located under `util/gcc-toolchain-builder`.  Please make sure beforehand that you have
installed all the required *toolchain build* dependencies (see
[the toolchain README file](file:util/gcc-toolchain-builder/README.md).)

```sh
# Set environment variable RISCV to the desired installation location.
# The toolchain can be installed in any user-writable directory.
export RISCV=/path/to/toolchain/installation/directory

# Get the source code of toolchain components from public repositiories.
cd util/gcc-toolchain-builder
bash ./get-toolchain.sh

# For the build prerequisites, see the local README.md.

# Build and install the GCC toolchain.
bash ./build-toolchain.sh $RISCV

# Return to the toplevel CVA6 directory.
cd -
```

You will now be able to run the CVA6 test scripts.

#### Environent setup

To run simulation, several tools and repositories are needed:
- Gcc as compiler,
- Spike as instruction set simulator,
- Verilator as simulator (if used as simulator to simulate),
- [riscv-dv](https://github.com/google/riscv-dv) as simulation environment.

If you would like to use a precompiled Verilator, please setup the path to the installation directory
```sh
export VERILATOR_INSTALL_DIR=/path/to/installation/directory
```

The smoke_tests execution will end up the installation by installing Verilator, Spike, tests from regression suites as arch-test, riscv-dv. Then it runs the smoke_tests test.

Three simulation types are supported:
- **veri-testharness**: verilator with corev_apu/testharness testbench,
- **vcs-testharness**: vcs with corev_apu/testharness testbench,
- **vcs-uvm**: vcs with UVM testbench.
To check the RTL cva6 behaviour, the RTL simulation trace is compared to spike trace. `DV_SIMULATORS` need to be setup to define which simulators are used.

```sh
export DV_SIMULATORS=veri-testharness,spike
bash verif/regress/smoke-tests.sh
```

#### Test execution

Run one of the shell scripts:

```sh
# riscv-compliance (https://github.com/riscv/riscv-compliance) test suite:
bash verif/regress/dv-riscv-compliance.sh
# riscv-tests (https://github.com/riscv/riscv-tests) test suite:
bash verif/regress/dv-riscv-tests.sh
```


### Running User-Space Applications

> :warning: **Warning**: this chapter needs to be updated. See Github issue https://github.com/openhwgroup/cva6/issues/1358.

It is possible to run user-space binaries on CVA6 with ([RISC-V Proxy Kernel and Boot Loader](https://github.com/riscv/riscv-pk)).
RISC-V PK can be installed by running: `./ci/install-riscvpk.sh`

```
mkdir build
cd build
../configure --prefix=$RISCV --host=riscv64-unknown-elf
make
make install
```

Then to run a RISC-V ELF using the Verilator model do:

```
echo '
#include <stdio.h>

int main(int argc, char const *argv[]) {
    printf("Hello CVA6!\\n");
    return 0;
}' > hello.c
riscv64-unknown-elf-gcc hello.c -o hello.elf
```

```
make verilate
work-ver/Variane_testharness $RISCV/riscv64-unknown-elf/bin/pk hello.elf
```

If you want to use QuestaSim to run it you can use the following command:
```
make sim elf-bin=$RISCV/riscv64-unknown-elf/bin/pk target-options=hello.elf  batch-mode=1
```

> Be patient! RTL simulation is way slower than Spike. If you think that you ran into problems you can inspect the trace files.

## Physical Implementation

### ASIC Synthesis

How to make cva6 synthesis ?
```
make -C pd/synth cva6_synth FOUNDRY_PATH=/your/techno/basepath/ TECH_NAME=yourTechnoName TARGET_LIBRARY_FILES="yourLib1.db\ yourLib2.db" PERIOD=10 NAND2_AREA=650 TARGET=cv64a6_imafdc_sv39 ADDITIONAL_SEARCH_PATH="others/libs/paths/one\ others/libs/paths/two"
```
Don't forget to escape spaces in lists.
Reports are under: pd/synth/ariane/reports

### ASIC Gate Simulation with `core-v-verif` repository

> :warning: **Warning**: this chapter needs to be updated. See Github issue https://github.com/openhwgroup/cva6/issues/1358.

```sh
export DV_SIMULATORS=veri-testharness,spike
cva6/regress/smoke-tests.sh
make -C pd/synth cva6_synth FOUNDRY_PATH=/your/techno/basepath/ TECH_NAME=yourTechnoName TARGET_LIBRARY_FILES="yourLib1.db\ yourLib2.db" PERIOD=10 NAND2_AREA=650 TARGET=cv64a6_imafdc_sv39 ADDITIONAL_SEARCH_PATH="others/libs/paths/one\ others/libs/paths/two"
sed 's/module SyncSpRamBeNx64_1/module SyncSpRamBeNx64_2/' pd/synth/ariane_synth.v > pd/synth/ariane_synth_modified.v
cd cva6/sim
make vcs_clean
python3 cva6.py --testlist=../tests/testlist_riscv-tests-cv64a6_imafdc_sv39-p.yaml --test rv64ui-p-ld --iss_yaml cva6.yaml --target cv64a6_imafdc_sv39 --iss=spike,vcs-core-gate $DV_OPTS
```

## COREV-APU FPGA Emulation

We currently only provide support for the [Genesys 2 board](https://reference.digilentinc.com/reference/programmable-logic/genesys-2/reference-manual). We provide pre-build bitstream and memory configuration files for the Genesys 2 [here](https://github.com/openhwgroup/cva6/releases).

Tested on Vivado 2018.2. The FPGA currently contains the following peripherals:

- DDR3 memory controller
- SPI controller to conncet to an SDCard
- Ethernet controller
- JTAG port (see debugging section below)
- Bootrom containing zero stage bootloader and device tree.

![](docs/01_cva6_user/_static/fpga_bd.png)

> The ethernet controller and the corresponding network connection is still work in progress and not functional at the moment. Expect some updates soon-ish.

### Programming the Memory Configuration File

- Open Vivado
- Open the hardware manager and open the target board (Genesys II - `xc7k325t`)
- Tools - Add Configuration Memory Device
- Select the following Spansion SPI flash `s25fl256xxxxxx0`
- Add `ariane_xilinx.mcs`
- Press Ok. Flashing will take a couple of minutes.
- Right click on the FPGA device - Boot from Configuration Memory Device (or press the program button on the FPGA)

### Preparing the SD Card

The first stage bootloader will boot from SD Card by default. Get yourself a suitable SD Card (we use [this](https://www.amazon.com/Kingston-Digital-Mobility-MBLY10G2-32GB/dp/B00519BEQO) one). Either grab a pre-built Linux image from [here](https://github.com/pulp-platform/ariane-sdk/releases) or generate the Linux image yourself following the README in the [ariane-sdk repository](https://github.com/pulp-platform/ariane-sdk). Prepare the SD Card by following the "Booting from SD card" section in the ariane-sdk repository.

Connect a terminal to the USB serial device opened by the FTDI chip e.g.:
```
screen /dev/ttyUSB0 115200
```

Default baudrate set by the bootlaoder and Linux is `115200`.

After you've inserted the SD Card and programmed the FPGA you can connect to the serial port of the FPGA and should see the bootloader and afterwards Linux booting. Default username is `root`, no password required.

### Generating a Bitstream

To generate the FPGA bitstream (and memory configuration) yourself for the Genesys II board run:

```
make fpga
```

This will produce a bitstream file and memory configuration file (in `fpga/work-fpga`) which you can permanently flash by running the above commands.

### Debugging

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

Then you will be able to either connect through `telnet` or with `gdb`:

```
riscv64-unknown-elf-gdb /path/to/elf

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

### Preliminary Support for OpenPiton Cache System

CVA6 has preliminary support for the OpenPiton distributed cache system from Princeton University. To this end, a different L1 cache subsystem (`src/cache_subsystem/wt_cache_subsystem.sv`) has been developed that follows a write-through protocol and that has support for cache invalidations and atomics.

The corresponding integration patches will be released on [OpenPiton GitHub repository](https://github.com/PrincetonUniversity/openpiton). Check the `README` in that repository to see how to use CVA6 in the OpenPiton setting.

To activate the different cache system, compile your code with the macro `DCACHE_TYPE`.

## Planned Improvements

Check-out the issue tab which also loosely tracks planned improvements.


## Going Beyond

The core has been developed with a full licensed version of QuestaSim. If you happen to have this simulator available yourself here is how you could run the core with it.

To specify the test to run use (e.g.: you want to run `rv64ui-p-sraw` inside the `tmp/risc-tests/build/isa` folder:
```
make sim elf-bin=path/to/rv64ui-p-sraw
```

If you call `sim` with `batch-mode=1` it will run without the GUI. QuestaSim uses `riscv-fesvr` for communication as well.

### CI Testsuites and Randomized Constrained Testing with Torture

We provide two CI configuration files for Travis CI and GitLab CI that run the RISCV assembly tests, the RISCV benchmarks and a randomized RISCV Torture test. The difference between the two is that Travis CI runs these tests only on Verilator, whereas GitLab CI runs the same tests on QuestaSim and Verilator.

If you would like to run the CI test suites locally on your machine, follow any of the two scripts `ci/travis-ci-emul.sh` and `ci/travis-ci-emul.sh` (depending on whether you have QuestaSim or not). In particular, you have to get the required packages for your system, the paths in `ci/path-setup.sh` to match your setup, and run the installation and build scripts prior to running any of the tests suites.

Once everything is set up and installed, you can run the tests suites as follows (using Verilator):

```
make verilate
make run-asm-tests-verilator
make run-benchmarks-verilator
```

In order to run randomized Torture tests, you first have to generate the randomized program prior to running the simulation:

```
./ci/get-torture.sh
make torture-gen
make torture-rtest-verilator
```
This runs the randomized program on Spike and on the RTL target, and checks whether the two signatures match. The random instruction mix can be configured in the `./tmp/riscv-torture/config/default.config` file.

CVA6 can dump a trace-log in Questa which can be easily diffed against Spike with commit log enabled. In `include/ariane_pkg.sv` set:

```verilog
localparam bit ENABLE_SPIKE_COMMIT_LOG = 1'b1;
```
This runs the randomized program on Spike and on the RTL target, and checks whether the two signatures match. The random instruction mix can be configured in the `./tmp/riscv-torture/config/default.config` file.
This will dump a file called `trace_hart_*_*_commit.log`.

This can be helpful for debugging long traces (e.g.: torture traces). To compile Spike with the commit log feature do:

```
apt-get install device-tree-compiler
mkdir build
cd build
../configure --prefix=$RISCV --with-fesvr=$RISCV --enable-commitlog
make
make install
```

### Memory Preloading

In standard configuration the debug module will take care of loading the memory content. It will also handle communication with `riscv-fesvr`.
Depending on the scenario this might not be diserable (e.g.: preloading of a large elf or linux boot in simulation). You can use the preload elf flag to specify the path
to a binary which will be preloaded.

> You will loose all `riscv-fesvr` communcation like sytemcalls and eoc capabilities.

```
make sim preload=elf
```

<!-- ### Tandem Verification with Spike

```
$ make sim preload=/home/zarubaf/Downloads/riscv-tests/build/benchmarks/dhrystone.riscv tandem=1
```
There are a couple of caveats:

- Memories should be initialized to zero. Random or `x` are not supported.
- UART needs to be replaced by a mock UART which exhibits always ready behavior.
- There is no end of test signaling at the moment. You are supposed to kill the simulation when sufficiently long run.
- You need to use the modified Spike version in the `tb` subdirectory.
- The RTC clock needs to be sufficiently slow (e.g.: 32 kHz seems to work). This is needed as otherwise there will be a difference when reading the `mtime` register as the RTL simulation takes more time to propagate the information through the system.
- All traps except memory traps need to zero the `tval` register. There is a switch you can set in `ariane_pkg`.
- `mcycle` needs to be incremented with `instret` to be similar to the performance counters found in Spike (IPC = 1)
 -->

### Re-generating the Bootcode (ZSBL)

The zero stage bootloader (ZSBL) for RTL simulation lives in `bootrom/` while the bootcode for the FPGA is in `fpga/src/bootrom`. The RTL bootcode simply jumps to the base of the DRAM where the FSBL takes over. For the FPGA the ZSBL performs additional housekeeping. Both bootloader pass the hartid as well as address to the device tree in argumen register `a0` and `a1` respectively.

To re-generate the bootcode you can use the existing makefile within those directories. To generate the SystemVerilog files you will need the `bitstring` python package installed on your system.

# Contributing

Check out the [contribution guide](CONTRIBUTING.md)

# Acknowledgements

Thanks to Gian Marti, Thomas Kramer and Thomas E. Benz for implementing the PLIC.
