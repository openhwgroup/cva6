current_dir = $(shell pwd)

utils_dir = $(SW_HOME)/inc/

directories = . drivers/inc drivers/src string_lib/inc string_lib/src

INC=$(foreach d, $(directories), -I$(utils_dir)$d)

inc_dir := $(SW_HOME)/common/

RISCV_PREFIX ?= riscv$(XLEN)-unknown-elf-
RISCV_GCC ?= $(RISCV_PREFIX)gcc

RISCV_OBJDUMP ?= $(RISCV_PREFIX)objdump --disassemble-all --disassemble-zeroes --section=.text --section=.text.startup --section=.text.init --section=.data

RISCV_FLAGS     := -mcmodel=medany -static -std=gnu99 -O2 -ffast-math -fno-common -fno-builtin-printf $(INC)
RISCV_LINK_OPTS := -static -nostdlib -nostartfiles -lm -lgcc

clean:
	rm -f $(APP).riscv
	rm -f $(APP).dump

build:
	$(RISCV_GCC) $(RISCV_FLAGS) -T $(inc_dir)/test.ld $(RISCV_LINK_OPTS) $(inc_dir)/crt.S $(inc_dir)/syscalls.c -L $(inc_dir) $(APP).c -o $(APP).riscv


dis:
	$(RISCV_OBJDUMP) $(APP).riscv > $(APP).dump

all: clean build dis
