# Hardware

## Repository

This repository contains the hardware files needed to build the Ariane-SoC and it is organized as follows:

- `deps` contains the core (`cva6`) as a standalone component
- `host` contains the host-system: it wraps the core and plugs it into the `axi_node` to which the slaves are attached
- `tb` contains the testbench
- `fpga` contains the scripts to generate the bitstream

## Architecture 

![alt text](https://github.com/AlSaqr-platform/cva6/blob/FLLs/hardware/docs/RTL.jpg)

## Hello World:

```
git clone https://github.com/AlSaqr-platform/cva6.git

git submodule update --init --recursive
```

To compile the code:

```
source setup.sh

cd software/hello

make clean all

cd ../..

```


### RTL BUILD

First do `make bender` to locally install [bender](https://github.com/pulp-platform/bender) (please have a look at it first) and download the vip RTL modules ( [HYPERRAM](https://www.cypress.com/documentation/models/verilog/s27kl0641-s27ks0641-verilog) and [HYPERFLASH](https://www.cypress.com/verilog/s26ks512s-verilog) ). Then:

```
cd hardware

make update

make scripts_vips

make sim elf-bin=../software/hello/hello.riscv

```

Doing so will load the elf binary through the DMI interface, driven by the SimDTM, communicating with FESVR, the host.

To load the code through JTAG interface, you can add the `localjtag=1` option and do `make localjtag=1 scripts_vip`. Be aware that the preload of the code is slower in this case. 

### FPGA Emulation

We now support emulation on Xilinx ZCU102. You first need to purchase an HyperRAM, where the core is stored during the boot. Then, you'll need to plug it in to the FMC board following the mapping provided in `cva6/hardware/fpga/alsaqr/tcl/fmc_board_zcu102.xdc`. From this folder:

```
make scripts-bender-fpga

cd fpga

source setup.sh 

```
select ZCU102, we'll soon provide VCU118 support as well.

```
cd alsaqr/tcl/ips/boot_rom/

make clean all

cd ../../../../

cd alsaqr/tcl/ips/clk_mngr/

make clean all

cd ../../../../

vivado-2018.2 vivado -mode batch -source run.tcl

```


