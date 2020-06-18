RISCV            ?= /opt/riscv
RISCV_EXE_PREFIX ?= $(RISCV)/bin/riscv32-unknown-elf-
RISCV_GCC = $(RISCV_EXE_PREFIX)gcc
RISCV_AR = $(RISCV_EXE_PREFIX)ar
SRC = crt0.S handlers.S syscalls.c vectors.S
OBJ = libcv-verif.a crt0.o handlers.o syscalls.o vectors.o
CFLAGS ?= -Os -g -static -mabi=ilp32 -march=rv32imc -Wall -pedantic

all:
	$(RISCV_GCC) $(CFLAGS) -c $(SRC)
	$(RISCV_AR) rcs $(OBJ)

clean:
	rm -f $(OBJ)
