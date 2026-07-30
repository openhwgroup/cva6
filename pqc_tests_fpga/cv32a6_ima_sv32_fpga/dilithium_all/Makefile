CC = riscv32-unknown-elf-gcc
OBJCOPY = riscv32-unknown-elf-objcopy

ARCH = -march=rv32ima_zicsr -mabi=ilp32 -mcmodel=medany

# Dilithium parameter set (2, 3, or 5)
DILITHIUM_MODE ?= 2

CFLAGS = $(ARCH) -O2 -Wall --specs=nosys.specs -DDILITHIUM_MODE=$(DILITHIUM_MODE) -I../../../verif/tests/custom/dilithium
LDFLAGS = -T ../link.ld -nostartfiles

SRCS = ../../../verif/bsp/crt0.S \
       ./main.c \
       ../../../verif/tests/custom/dilithium/sign.c \
       ../../../verif/tests/custom/dilithium/packing.c \
       ../../../verif/tests/custom/dilithium/polyvec.c \
       ../../../verif/tests/custom/dilithium/poly.c \
       ../../../verif/tests/custom/dilithium/ntt.c \
       ../../../verif/tests/custom/dilithium/reduce.c \
       ../../../verif/tests/custom/dilithium/rounding.c \
       ../../../verif/tests/custom/dilithium/fips202.c \
       ../../../verif/tests/custom/dilithium/symmetric-shake.c \
       ../../../verif/tests/custom/dilithium/randombytes.c

TARGET = load.elf

all: $(TARGET)

$(TARGET): $(SRCS)
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ $^

clean:
	rm -f $(TARGET)