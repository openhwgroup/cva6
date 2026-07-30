CC = riscv32-unknown-elf-gcc
OBJCOPY = riscv32-unknown-elf-objcopy

ARCH = -march=rv32ima_zicsr -mabi=ilp32 -mcmodel=medany

CFLAGS = $(ARCH) -g -O2 -Wall --specs=nosys.specs
LDFLAGS = -T link.ld -nostartfiles

SRCS = ../../../verif/bsp/crt0.S \
       ./kyber_gdb.c \
       ../../../verif/tests/custom/kyber/cbd.c \
       ../../../verif/tests/custom/kyber/fips202.c \
       ../../../verif/tests/custom/kyber/indcpa.c \
       ../../../verif/tests/custom/kyber/kem.c \
       ../../../verif/tests/custom/kyber/ntt.c \
       ../../../verif/tests/custom/kyber/poly.c \
       ../../../verif/tests/custom/kyber/polyvec.c \
       ../../../verif/tests/custom/kyber/randombytes.c \
       ../../../verif/tests/custom/kyber/reduce.c \
       ../../../verif/tests/custom/kyber/symmetric-shake.c \
       ../../../verif/tests/custom/kyber/verify.c

TARGET = load.elf

all: $(TARGET)

$(TARGET): $(SRCS)
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ $^

clean:
	rm -f $(TARGET)