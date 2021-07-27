
# Dromajo - Esperanto Technology's RISC-V Reference Model

Functional verification is key to have a strong RISC-V ecosystem.
Esperanto is releasing Dromajo to help the RISC-V community.  Dromajo
is the Esperanto translation for an emu bird. It is a RISC-V RV64GC
emulator designed for RTL co-simulation.  This is the emulator used
for cosimulation inside Esperanto, but it is designed with a simple
API that can be leveraged to other RTL RISC-V cores.

Dromajo enables executing application (such as benchmarks running on
Linux) under fast software simulation, generating checkpoints after a
given number of cycles, and resuming such checkpoints for HW/SW
co-simulation.  This has proven to be a very powerful way to capture
bugs, especially in combination with randomized tests.

Dromajo's semantic model is based on Fabrice Bellard's RISCVEMU (later
renamed TinyEMU), but extensively verified, bug-fixed, and enhanced to
take it to ISA 2.3/priv 1.11.

## Building

```
make -C src
```

The resulting artifacts are the `dromajo` simulator and the
`libdromajo_cosim.a` library with associated `dromajo_cosim.h`
header file.

Check the [setup.md](run/setup.md) for instructions how to compile tests like
booting Linux and baremetal for dromajo.

## Usage

The co-simulation environment will link with the libraries and usage
will depend on that, but the `src/dromajo.c` utility allows for standalone
simulation of RISC-V ELF binaries.

```
cd src
./dromajo
error: missing config file
usage: ./dromajo [--load snapshot_name] [--save snapshot_name] [--maxinsns N] [--memory_size MB] config
       --load resumes a previously saved snapshot
       --save saves a snapshot upon exit
       --maxinsns terminates execution after a number of instructions
       --terminate-event name of the validate event to terminate execution
       --trace start trace dump after a number of instructions
       --memory_size sets the memory size in MiB (default 256 MiB)

./dromajo path/to/your/coremark.riscv
...
```
