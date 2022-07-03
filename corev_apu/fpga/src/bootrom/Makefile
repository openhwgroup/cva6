XLEN ?= 64
CROSSCOMPILE ?= riscv64-unknown-elf-
DRAM_SIZE_64 ?= 0x40000000# 1GB
DRAM_SIZE_32 ?= 0x08000000# 128MB
CLOCK_FREQUENCY ?= 50000000# 50MHz
HALF_CLOCK_FREQUENCY ?= 25000000# 25MHz
UART_BITRATE ?= 115200
HAS_ETHERNET ?= 1
CC = ${CROSSCOMPILE}gcc
SED = sed
PYTHON ?= python

PLATFORM_DEFINES = -DCLOCK_FREQUENCY=$(CLOCK_FREQUENCY) -DUART_BITRATE=$(UART_BITRATE)

ifeq ($(XLEN), 64)
CFLAGS = $(PLATFORM_DEFINES) -Os -ggdb -march=rv64imac -mabi=lp64 -Wall -mcmodel=medany -mexplicit-relocs -ffreestanding
else
CFLAGS = $(PLATFORM_DEFINES) -O2 -ggdb  -march=rv32im -mabi=ilp32 -W -Wall -mcmodel=medany -mexplicit-relocs -ffreestanding -fno-builtin
endif

CCASFLAGS = -mcmodel=medany -mexplicit-relocs
LDFLAGS = -nostdlib -nodefaultlibs -nostartfiles

INCLUDES = -I./ -I./src

SRCS_C = src/main.c src/uart.c src/spi.c src/sd.c src/gpt.c
SRCS_ASM = startup.S
OBJS_C = $(SRCS_C:.c=.o)
OBJS_S = $(SRCS_ASM:.S=.o)

MAIN = bootrom_$(XLEN).elf
MAIN_BIN = $(MAIN:.elf=.bin)
MAIN_IMG = $(MAIN:.elf=.img)
MAIN_SV = $(MAIN:.elf=.sv)

DTB = cv$(XLEN)a6.dtb

ifeq ($(HAS_ETHERNET), 1)
SED_DELETE_OPT = -e "/DELETE_ETH/d"
else
SED_DELETE_OPT =
endif


#.PHONY: clean

$(MAIN): $(DTB) $(OBJS_C) $(OBJS_S) linker.lds
	$(CC) $(CFLAGS) $(LDFLAGS) $(INCLUDES) -Tlinker.lds $(OBJS_S) $(OBJS_C) -o $(MAIN)
	@echo "LD    >= $(MAIN)"

%.img: %.bin
	dd if=$< of=$@ bs=128

%.bin: %.elf
	$(CROSSCOMPILE)objcopy -O binary $< $@

%.o: %.c
	@$(CC) $(CFLAGS) $(INCLUDES) -c $<  -o $@
	@echo "CC    <= $<"

%.o: %.S
	@$(CC) $(CFLAGS) $(CCASFLAGS) $(INCLUDES) -c $<  -o $@
	@echo "CC    <= $<"

%.dts: %.dts.in
	$(SED) -e "s/DRAM_SIZE_64/$(DRAM_SIZE_64)/g" \
	       -e "s/DRAM_SIZE_32/$(DRAM_SIZE_32)/g" \
	       -e "s/HALF_CLOCK_FREQUENCY/$(HALF_CLOCK_FREQUENCY)/g" \
	       -e "s/CLOCK_FREQUENCY/$(CLOCK_FREQUENCY)/g" \
	       -e "s/UART_BITRATE/$(UART_BITRATE)/g" \
	       $(SED_DELETE_OPT) $< > $@
	cat $@

%.dtb: %.dts
	dtc -I dts $< -O dtb -o $@

%.sv: %.img
	$(PYTHON) ./gen_rom.py $<
	@echo "PYTHON >= $(MAIN_SV)"

clean:
	$(RM) $(OBJS_C) $(OBJS_S) $(MAIN) $(MAIN_BIN) $(MAIN_IMG) *.dtb *.dts

all: $(MAIN) $(MAIN_BIN) $(MAIN_IMG) $(MAIN_SV)
	@echo "zero stage bootloader has been compiled!"

# DO NOT DELETE THIS LINE -- make depend needs it
