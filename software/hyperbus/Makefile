APP := hyperbus
XLEN:=64

inc_dir := ./../common

RISCV_PREFIX ?= riscv$(XLEN)-unknown-elf-
RISCV_GCC ?= $(RISCV_PREFIX)gcc

RISCV_OBJDUMP ?= $(RISCV_PREFIX)objdump --disassemble-all --disassemble-zeroes --section=.text --section=.text.startup --section=.text.init --section=.data

RISCV_FLAGS     := -mcmodel=medany -static -std=gnu99 -O2 -ffast-math -fno-common -fno-builtin-printf
RISCV_LINK_OPTS := -static -nostdlib -nostartfiles -lm -lgcc

clean:
	rm -f $(APP).riscv
	rm -f $(APP).dump

build:
	$(RISCV_GCC) $(RISCV_FLAGS) -T $(inc_dir)/test.ld $(RISCV_LINK_OPTS) $(inc_dir)/crt.S $(inc_dir)/syscalls.c  -L $(inc_dir) $(APP).c -o $(APP).riscv


dis:
	$(RISCV_OBJDUMP) -g $(APP).riscv > $(APP).dump

all: clean build dis
