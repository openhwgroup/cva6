ifndef IMPERAS_HOME
  IMPERAS_ERROR := $(error "IMPERAS_HOME not defined, please setup Imperas/OVP environment")
endif
IMPERAS_HOME := $(shell getpath.exe "$(IMPERAS_HOME)")

#
# The list of ELF files this Makefile will build from C source file(s) in this directory
#
ifeq ($(APP),)
SRC = $(wildcard *.S)
else
SRC = $(wildcard $(APP).S)
endif
XLEN ?= 32

OUT = $(basename $(SRC))
ELF = $(foreach o,$(OUT),$(o).$(CROSS).elf)

OD = $(ELF:.elf=.objdump)
RE = $(ELF:.elf=.readelf)
NM = $(ELF:.elf=.nm)

#
# Include Cross Compilers
#
CROSS?=RISCV$(XLEN)
# include Cross Compiler settings for RISCV(XLEN)
-include $(IMPERAS_HOME)/lib/$(IMPERAS_ARCH)/CrossCompiler/$(CROSS).makefile.include
ifeq ($($(CROSS)_CC),)
	IMPERAS_ERROR := $(error "Error : $(CROSS)_CC not set. Please check installation of toolchain for $(CROSS)")
endif

LINKFLAGS  = -nostdlib -nostartfiles
LINKFLAGS += -Tlink.ld

#
# Rules to build ELF files
#
all: $(ELF) $(NM) $(OD) $(RE)

%.$(CROSS).elf:  %.$(CROSS).o
	@    echo "# Linking $(CROSS) $@"
	$(V) $($(CROSS)_LINK) -o $@ $^ $(LINKFLAGS) 

%.readelf: %.elf
	@    echo "# readelf $<"
	$(V) $($(CROSS)_READELF) -a $^ > $@

%.nm: %.elf
	@    echo "# nm $<"
	$(V) $($(CROSS)_NM) $^ > $@

%.objdump: %.elf
	@    echo "# objdump $<"
	$(V) $($(CROSS)_OBJDUMP) -D $^ > $@

%.$(CROSS).o: %.S
	@    echo "# Compiling $(CROSS) $<"
	$(V) $($(CROSS)_CC) -c -o $@ $< -D$(CROSS) -O0 -g -nostdlib -nostartfiles

clean::
	- rm -f $(ELF) $(NM) $(OD) $(RE)
	
# Simon comamnd line
#riscv-none-embed-gcc -static -mcmodel=medany -fvisibility=hidden -nostdlib -nostartfiles riscv_arithmetic_basic_test_0.S -I/home/simond/git/tmp10/riscv-dv/user_extension -T/home/simond/git/tmp10/riscv-dv/scripts/link.ld  -o ./outdir/asm_tests/riscv_arithm etic_basic_test_0.o  -march=rv32i -mabi=ilp32
	