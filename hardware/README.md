# Hardware

## Repository

This repository contains the hardware files needed to build the Ariane-SoC and it is organized as follows:

- `deps` contains the core (`cva6`) as a standalone component
- `host` contains the host-system: it wraps the core and plugs it into the `axi_node` to which the slaves are attached
- `tb` contains the testbench

## Hello World:

To compile the code, from this folder:

```
cd ..

source setup.sh

cd software/hello

make clean all

```


### RTL BUILD

First do `make bender` to locally install bender. Then:

```
cd hardware

make update

make scripts

make sim elf-bin=../software/hello/hello.riscv

```

