CV_SW_TOOLCHAIN  ?= /opt/riscv
RISCV            ?= $(CV_SW_TOOLCHAIN)
RISCV_EXE_PREFIX ?= $(RISCV)/bin/riscv32-unknown-elf-
RISCV_CC         ?= gcc
RISCV_GCC = $(RISCV_EXE_PREFIX)$(RISCV_CC)
RISCV_AR = $(RISCV_EXE_PREFIX)ar
RISCV_MARCH ?= rv32im_zca
SRC = crt0.S handlers.S syscalls.c vectors.S
OBJ = crt0.o handlers.o syscalls.o vectors.o
LIBCV-VERIF = libcv-verif.a
CFLAGS ?= -Os -g -static -mabi=ilp32 -march=$(RISCV_MARCH) -Wall -pedantic -mno-relax $(RISCV_CFLAGS)

all: $(LIBCV-VERIF)

$(LIBCV-VERIF): $(OBJ)
	$(RISCV_AR) rcs $@ $(OBJ)

%.o : %.c
	$(RISCV_GCC) $(CFLAGS) -c $< -o $@

%.o : %.S
	$(RISCV_GCC) $(CFLAGS) -c $< -o $@

clean:
	rm -f $(OBJ) $(LIBCV-VERIF)


vars:
	@echo "make bsp variables:"
	@echo "   CV_SW_TOOLCHAIN  = $(CV_SW_TOOLCHAIN)"
	@echo "   RISCV            = $(RISCV)"
	@echo "   RISCV_EXE_PREFIX = $(RISCV_EXE_PREFIX)"
	@echo "   RISCV_GCC        = $(RISCV_GCC)"
	@echo "   RISCV_MARCH      = $(RISCV_MARCH)"
	@echo "   RISCV_CFLAGS     = $(RISCV_CFLAGS)"
	@echo "   CFLAGS           = $(CFLAGS)"
