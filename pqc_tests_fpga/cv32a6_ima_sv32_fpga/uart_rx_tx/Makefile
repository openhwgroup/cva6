CC = riscv32-unknown-elf-gcc
OBJCOPY = riscv32-unknown-elf-objcopy

ARCH = -march=rv32ima_zicsr -mabi=ilp32 -mcmodel=medany

CFLAGS = $(ARCH) -O2 -Wall --specs=nosys.specs
LDFLAGS = -T ../link.ld -nostartfiles

SRCS = ../../../verif/bsp/crt0.S \
       ./main.c

TARGET = load.elf

all: $(TARGET)

$(TARGET): $(SRCS)
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ $^

clean:
	rm -f $(TARGET)