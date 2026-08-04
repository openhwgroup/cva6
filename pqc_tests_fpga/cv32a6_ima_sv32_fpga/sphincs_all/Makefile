CC = riscv32-unknown-elf-gcc
OBJCOPY = riscv32-unknown-elf-objcopy

ARCH = -march=rv32ima_zicsr -mabi=ilp32 -mcmodel=medany

CFLAGS = $(ARCH) -O2 -Wall --specs=nosys.specs -I../../../verif/tests/custom/sphincs
LDFLAGS = -T ../link.ld -nostartfiles

SRCS = ../../../verif/bsp/crt0.S \
       ./main.c \
       ../../../verif/tests/custom/sphincs/test/test_syscalls.c \
       ../../../verif/tests/custom/sphincs/address.c \
       ../../../verif/tests/custom/sphincs/fips202.c \
       ../../../verif/tests/custom/sphincs/fors.c \
       ../../../verif/tests/custom/sphincs/hash_shake256.c \
       ../../../verif/tests/custom/sphincs/randombytes.c \
       ../../../verif/tests/custom/sphincs/sign.c \
       ../../../verif/tests/custom/sphincs/thash_shake256_simple.c \
       ../../../verif/tests/custom/sphincs/utils.c \
       ../../../verif/tests/custom/sphincs/wots.c

TARGET = load.elf

all: $(TARGET)

$(TARGET): $(SRCS)
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ $^

clean:
	rm -f $(TARGET)