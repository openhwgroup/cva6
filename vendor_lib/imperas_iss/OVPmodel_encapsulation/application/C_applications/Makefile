ifndef IMPERAS_HOME
  IMPERAS_ERROR := $(error "IMPERAS_HOME not defined, please setup Imperas/OVP environment")
endif
IMPERAS_HOME := $(shell getpath.exe "$(IMPERAS_HOME)")

CROSS?=RISCV32

#
# The list of ELF files this Makefile will build from C source file(s) in this directory
#
ifeq ($(APP),)
SRC = $(wildcard *.c)
else
SRC = $(wildcard $(APP).c)
endif

OUT = $(basename $(SRC))
ELF = $(foreach o,$(OUT),$(o).$(CROSS).elf)

OD = $(ELF:.elf=.objdump)
RE = $(ELF:.elf=.readelf)
NM = $(ELF:.elf=.nm)

#
# Include Cross Compilers
#

# include Cross Compiler settings for $(CROSS)
-include $(IMPERAS_HOME)/lib/$(IMPERAS_ARCH)/CrossCompiler/$(CROSS).makefile.include
ifeq ($($(CROSS)_CC),)
	IMPERAS_ERROR := $(error "Error : $(CROSS)_CC not set. Please check installation of toolchain for $(CROSS)")
endif

SUPPORT$(CROSS) = start.$(CROSS).o support.$(CROSS).o

RESET_ADDR = 0x0
TRAP_ADDR  = 0x1000
TTY_ADDR   = 0x2000
TEXT_ADDR  = 0x10000

LINKFLAGS  = -lm --specs=nosys.specs
LINKFLAGS += -Wl,--section-start=.reset_vector=$(RESET_ADDR)
LINKFLAGS += -Wl,--section-start=.trap_vector=$(TRAP_ADDR)
LINKFLAGS += -Wl,--section-start=.text=$(TEXT_ADDR)
LINKFLAGS += -Wl,--section-start=.tty=$(TTY_ADDR)
LINKFLAGS += -e $(RESET_ADDR)

#
# Rules to build ELF files
#
all: $(ELF) $(NM) $(OD) $(RE)

%.$(CROSS).elf:  %.$(CROSS).o $(SUPPORT$(CROSS))
	@    echo "# Linking $(CROSS) $@"
	$(V) $($(CROSS)_LINK) -o $@ $^ $(LINKFLAGS)

%.readelf: %.elf
	@    echo "# nm $<"
	$(V) $($(CROSS)_READELF) -a $^ > $@

%.nm: %.elf
	@    echo "# nm $<"
	$(V) $($(CROSS)_NM) $^ > $@

%.objdump: %.elf
	@    echo "# objdump $<"
	$(V) $($(CROSS)_OBJDUMP) -D $^ > $@

%.$(CROSS).o: %.c
	@    echo "# Compiling $(CROSS) $<"
	$(V) $($(CROSS)_CC) -Isupport -c -o $@ $< -D$(CROSS) $(DEF) -O0 -g

# support
%.$(CROSS).o: support/%.c
	@    echo "# Compiling $(CROSS) $<"
	$(V) $($(CROSS)_CC) -c -o $@ $< -D$(CROSS) $(DEF) -O0 -g

%.$(CROSS).o: support/%.S
	@    echo "# Assembling $(CROSS) $<"
	$(V) $($(CROSS)_CC) -c -o $@ $< -D$(CROSS) $(DEF) 

clean::
	- rm -f $(SUPPORT$(CROSS)) $(ELF) $(NM) $(OD) $(RE)
	