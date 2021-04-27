UART_FREQ ?= 30000000
MAX_HARTS ?= 1
CROSSCOMPILE ?= riscv64-unknown-elf-
CC = ${CROSSCOMPILE}gcc
PYTHON=python

CFLAGS = -DMAX_HARTS=$(MAX_HARTS) -DUART_FREQ=$(UART_FREQ) -Os -ggdb -march=rv64imac -mabi=lp64 -Wall -mcmodel=medany -mexplicit-relocs
CCASFLAGS = -mcmodel=medany -mexplicit-relocs
LDFLAGS = -nostdlib -nodefaultlibs -nostartfiles

INCLUDES = -I./ -I./src

SRCS_C = src/main.c src/uart.c src/spi.c src/sd.c src/gpt.c
SRCS_ASM = startup.S
OBJS_C = $(SRCS_C:.c=.o)
OBJS_S = $(SRCS_ASM:.S=.o)

MAIN = bootrom_linux.elf
MAIN_BIN = $(MAIN:.elf=.bin)
MAIN_IMG = $(MAIN:.elf=.img)
MAIN_SV = $(MAIN:.elf=.sv)

#.PHONY: clean

$(MAIN): ariane.dtb $(OBJS_C) $(OBJS_S) linker.lds
	$(CC) $(CFLAGS) $(LDFLAGS) $(INCLUDES) -Tlinker.lds $(OBJS_S) $(OBJS_C) -o $(MAIN)
	@echo "LD    >= $(MAIN)"

%.img: %.bin
	dd if=$< of=$@ bs=128 

%.bin: %.elf
	$(CROSSCOMPILE)objcopy -O binary $< $@

%.o: %.c
	@echo "MAX_HARTS = $(MAX_HARTS)"
	@$(CC) $(CFLAGS) $(INCLUDES) -c $<  -o $@ 
	@echo "CC    <= $<"

%.o: %.S
	@echo "MAX_HARTS = $(MAX_HARTS)"
	@$(CC) $(CFLAGS) $(CCASFLAGS) $(INCLUDES) -c $<  -o $@ 
	@echo "CC    <= $<"

%.dtb: %.dts
	dtc -I dts $< -O dtb -o $@

%.sv: %.img
	$(PYTHON) ./gen_rom.py $<
	@echo "PYTHON >= $(MAIN_SV)"

clean:
	$(RM) $(OBJS_C) $(OBJS_S) $(MAIN) $(MAIN_BIN) $(MAIN_IMG) *.dtb

all: $(MAIN) $(MAIN_BIN) $(MAIN_IMG) $(MAIN_SV)
	@echo "zero stage bootloader has been compiled!"

# DO NOT DELETE THIS LINE -- make depend needs it
