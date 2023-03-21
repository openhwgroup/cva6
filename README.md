![Build Status](https://github.com/openhwgroup/cva6/actions/workflows/ci.yml/badge.svg?branch=master)

# CVA6 RISC-V CPU

CVA6 is a 6-stage, single issue, in-order CPU which implements the 64-bit RISC-V instruction set. It fully implements I, M, A and C extensions as specified in Volume I: User-Level ISA V 2.3 as well as the draft privilege extension 1.10. It implements three privilege levels M, S, U to fully support a Unix-like operating system. Furthermore it is compliant to the draft external debug spec 0.13.

It has configurable size, separate TLBs, a hardware PTW and branch-prediction (branch target buffer and branch history table). The primary design goal was on reducing critical path length.

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
* **scripts**: General scriptware.

## Verification
The verification environment for the CVA6 is _not_ in this Repository.

The verification environment for this core as well as other cores in the OpenHW Group CORE-V family is at the
[core-v-verif](https://github.com/openhwgroup/core-v-verif) repository on GitHub.

The Makefiles supported in the **core-v-verif** project automatically clone the appropriate version of the **CVA6**  RTL sources.

## Contributing
We highly appreciate community contributions.
<br><br>To ease the work of reviewing contributions, please review [CONTRIBUTING](https://github.com/openhwgroup/cva6/blob/master/CONTRIBUTING.md).

## Issues and Troubleshooting
If you find any problems or issues with CVA6 or the documentation, please check out the [issue tracker](https://github.com/openhwgroup/cva6/issues)
and create a new issue if your problem is not yet tracked.

## Publication

If you use CVA6 in your academic work you can cite us:

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

CVA6 User Documentation
=======================

   * [CVA6 RISC-V CPU](#cva6-risc-v-cpu)
   * [Table of Contents](#table-of-contents)
      * [Getting Started](#getting-started)
        * [Checkout Repo](#checkout-repo)
        * [Install Verilator Simulation Flow](#install-verilator-simulation-flow)
        * [Build Model and Run Simulations](#build-model-and-run-simulations)
        * [Running User-Space Applications](#running-user-space-applications)
      * [Physical Implementation](#physical-implementation)
         * [ASIC Synthesis](#asic-synthesis)
         * [ASIC Gate Simulation with core-v-verif repository](#asic-gate-simulation-with-core-v-verif-repository)
      * [FPGA Emulation](#fpga-emulation)
         * [Programming the Memory Configuration File](#programming-the-memory-configuration-file)
         * [Preparing the SD Card](#preparing-the-sd-card)
         * [Generating a Bitstream](#generating-a-bitstream)
         * [Debugging](#debugging)
         * [Preliminary Support for OpenPiton Cache System](#preliminary-support-for-openpiton-cache-system)
      * [Planned Improvements](#planned-improvements)
      * [Going Beyond](#going-beyond)
         * [CI Testsuites and Randomized Constrained Testing with Torture](#ci-testsuites-and-randomized-constrained-testing-with-torture)
         * [Re-generating the Bootcode (ZSBL)](#re-generating-the-bootcode-zsbl)
         * [Co-simulation with Dromajo](#co-simulation-with-dromajo)
   * [Contributing](#contributing)
   * [Acknowledgements](#acknowledgements)

Created by [gh-md-toc](https://github.com/ekalinin/github-markdown-toc)

## Getting Started

The following instructions will allow you to compile and run a Verilator model of the CVA6 APU (which instantiates the CVA6 core) within the CVA6 APU testbench (corev_apu/tb).

### Checkout Repo

Checkout the repository and initialize all submodules
```
git clone https://github.com/openhwgroup/cva6.git
git submodule update --init --recursive
```

### Install Verilator Simulation Flow

1. Setup install directory `RISCV` environment variable i.e. `export RISCV=/YOUR/TOOLCHAIN/INSTALLATION/DIRECTORY`
2. Run `./ci/setup.sh` to install all required tools (i.e. verilator, device-tree-compiler, riscv64-unknown-elf-*, ..)

You can install verilator from source using `./ci/install-verilator.sh` or by manually installing `verilator >= 4.002`
Note: There is currently a known issue with version 4.106 and 4.108. 4.106 does not compile and 4.108 hangs after a 
couple of cycles simulation time.)


### Build Model and Run Simulations

Build the Verilator model of CVA6 by using the Makefile:
```
make verilate
```

To build the verilator model with support for vcd files run
```
make verilate DEBUG=1
```

This will create a C++ model of the core including a SystemVerilog wrapper and link it against a C++ testbench (in the `tb` subfolder). The binary can be found in the `work-ver` and accepts a RISC-V ELF binary as an argument, e.g.:

```
work-ver/Variane_testharness rv64um-v-divuw
```

The Verilator testbench makes use of the `riscv-fesvr`. This means that you can use the `riscv-tests` repository as well as `riscv-pk` out-of-the-box. As a general rule of thumb the Verilator model will behave like Spike (exception for being orders of magnitudes slower).

Both, the Verilator model as well as the Questa simulation will produce trace logs. The Verilator trace is more basic but you can feed the log to `spike-dasm` to resolve instructions to mnemonics. Unfortunately value inspection is currently not possible for the Verilator trace file.

```
spike-dasm < trace_hart_00.dasm > logfile.txt
```

To build, compile and run the CVA6 core-only in its example testbench using Verilator (known to work with V4.108):
```
$ cd core/example_tb
$ make veri_run
```
`make help` will print all supported targets.


### Running User-Space Applications

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

```
export DV_SIMULATORS=veri-testharness,spike
cva6/regress/smoke-tests.sh
make -C core-v-cores/cva6/pd/synth cva6_synth FOUNDRY_PATH=/your/techno/basepath/ TECH_NAME=yourTechnoName TARGET_LIBRARY_FILES="yourLib1.db\ yourLib2.db" PERIOD=10 NAND2_AREA=650 TARGET=cv64a6_imafdc_sv39 ADDITIONAL_SEARCH_PATH="others/libs/paths/one\ others/libs/paths/two"
sed 's/module SyncSpRamBeNx64_1/module SyncSpRamBeNx64_2/' core-v-cores/cva6/pd/synth/ariane_synth.v > core-v-cores/cva6/pd/synth/ariane_synth_modified.v
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

### Co-simulation with Dromajo
CVA6 can be co-simulated with [Dromajo](https://github.com/chipsalliance/dromajo) (currently in the verilator model).

```
make verilate DROMAJO=1
make run-dromajo-verilator BIN=/path/to/elf
```

The co-simulation flow is depicted in the figure below.
![image](https://user-images.githubusercontent.com/8511359/84510824-7ceb3b80-ac7a-11ea-9530-24c428ee87d9.png)
1. Load the binary of interest into Dromajo.
2. Run Dromajo stand alone and let a couple of instructions to complete.
3. Dump the checkpoint. This is the whole architectural state of the reference model. Dromajo dumps the main and boot memories. In addition, it generates a boot code. If you were to run that code it will restore the whole architectural state. This means that you can bring any two or more cores into complete synced architectural state by running this piece of code.
4. Load the checkpoint into the RTL memory and the instance of Dromajo in RTL. Dromajo gets linked to a simulator as a shared library. RTL communicates to Dromajo through set of DPI calls.
5. Run the RTL simulation and perform co-simulation.

# Contributing

Check out the [contribution guide](CONTRIBUTING.md)

# Acknowledgements

Thanks to Gian Marti, Thomas Kramer and Thomas E. Benz for implementing the PLIC.
