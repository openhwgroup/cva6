CC = riscv32-unknown-elf-gcc
OBJCOPY = riscv32-unknown-elf-objcopy

ARCH = -march=rv32ima_zicsr -mabi=ilp32 -mcmodel=medany

# -ffp-contract=off and -fno-math-errno are highly recommended for Falcon 
# to ensure floating-point emulation behaves deterministically.
CFLAGS = $(ARCH) -O2 -Wall --specs=nosys.specs -ffp-contract=off -fno-math-errno -I../../../verif/tests/custom/falcon
LDFLAGS = -T ../link.ld -nostartfiles

SRCS = ../../../verif/bsp/crt0.S \
       ./main.c \
       ../../../verif/tests/custom/falcon/codec.c \
       ../../../verif/tests/custom/falcon/common.c \
       ../../../verif/tests/custom/falcon/falcon.c \
       ../../../verif/tests/custom/falcon/fft.c \
       ../../../verif/tests/custom/falcon/fpr.c \
       ../../../verif/tests/custom/falcon/keygen.c \
       ../../../verif/tests/custom/falcon/rng.c \
       ../../../verif/tests/custom/falcon/shake.c \
       ../../../verif/tests/custom/falcon/sign.c \
       ../../../verif/tests/custom/falcon/vrfy.c

TARGET = load.elf

all: $(TARGET)

$(TARGET): $(SRCS)
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ $^

clean:
	rm -f $(TARGET)