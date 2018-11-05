#/=======================================================================
# UCB VLSI FLOW: Makefile for riscv-bmarks/mt
#-----------------------------------------------------------------------
# Henry Cook (hcook@cs.berkeley.edu)
#

default: all

bmarkdir = .
common = ../benchmarks/common

instname = riscv-bmarks-mt
instbasedir = $(UCB_VLSI_HOME)/install

#--------------------------------------------------------------------
# Sources
#--------------------------------------------------------------------

bmarks_matmul = \
ad_matmul\
ae_matmul\
af_matmul\
ag_matmul\
ai_matmul\
ak_matmul\
al_matmul\
am_matmul\
an_matmul\
ap_matmul\
aq_matmul\
ar_matmul\
at_matmul\
av_matmul\
ay_matmul\
az_matmul\
bb_matmul\
bc_matmul\
bf_matmul\
bh_matmul\
bj_matmul\
bk_matmul\
bm_matmul\
bo_matmul\
br_matmul\
bs_matmul\
ce_matmul\
cf_matmul\
cg_matmul\
ci_matmul\
ck_matmul\
cl_matmul\
cm_matmul\
cs_matmul\
cv_matmul\
cy_matmul\
dc_matmul\
df_matmul\
dm_matmul\
do_matmul\
dr_matmul\
ds_matmul\
du_matmul\
dv_matmul\

bmarks_vvadd = \
vvadd0\
vvadd1\
vvadd2\
vvadd3\
vvadd4\

bmarks = $(bmarks_vvadd) $(bmarks_matmul)

#--------------------------------------------------------------------
# Build rules
#--------------------------------------------------------------------

RISCV_PREFIX=riscv$(XLEN)-unknown-elf-
RISCV_GCC = $(RISCV_PREFIX)gcc
RISCV_GCC_OPTS = -std=gnu99 -O2 -ffast-math
RISCV_LINK = $(RISCV_GCC) -T $(common)/test.ld $(incs)
RISCV_LINK_OPTS = -nostdlib -nostartfiles -ffast-math -lc
RISCV_OBJDUMP = $(RISCV_PREFIX)objdump --disassemble-all --disassemble-zeroes --section=.text --section=.text.startup --section=.data
RISCV_SIM = spike -p2

VPATH += $(common) $(common)/../mt-matmul $(common)/../mt-vvadd 

incs  += -I. -I$(bmarkdir)/../env -I$(common) -I$(common)/../mt-matmul -I$(common)/../mt-vvadd
objs  :=

#include $(patsubst %, $(bmarkdir)/%/bmark.mk, $(bmarks))

#------------------------------------------------------------
# Build and run benchmarks on riscv simulator
#------------------------------------------------------------

bmarks_riscv_obj  = $(addsuffix .o,  $(bmarks))
bmarks_riscv_matmul_bin  = $(addsuffix .riscv,  $(bmarks_matmul))
bmarks_riscv_vvadd_bin  = $(addsuffix .riscv,  $(bmarks_vvadd))
bmarks_riscv_dump = $(addsuffix .riscv.dump, $(bmarks))
bmarks_riscv_hex = $(addsuffix .riscv.hex, $(bmarks))
bmarks_riscv_out  = $(addsuffix .riscv.out,  $(bmarks))
bmarks_riscv_bin = $(bmarks_riscv_matmul_bin) $(bmarks_riscv_vvadd_bin)

bmarks_defs   = -DPREALLOCATE=1 -DHOST_DEBUG=0
bmarks_cycles = 80000

%.hex: %
	elf2hex 16 32768 $< > $@

$(bmarks_riscv_vvadd_bin): %.riscv: %.o mt-vvadd.o syscalls.o crt.o
	$(RISCV_LINK) $< mt-vvadd.o syscalls.o crt.o $(RISCV_LINK_OPTS) -o $@

$(bmarks_riscv_matmul_bin): %.riscv: %.o mt-matmul.o syscalls.o crt.o
	$(RISCV_LINK) $< mt-matmul.o syscalls.o crt.o $(RISCV_LINK_OPTS) -o $@

$(bmarks_riscv_dump): %.riscv.dump: %.riscv
	$(RISCV_OBJDUMP) $< > $@

$(bmarks_riscv_out): %.riscv.out: %.riscv
	$(RISCV_SIM) $< > $@

%.o: %.c
	$(RISCV_GCC) $(RISCV_GCC_OPTS) $(bmarks_defs)  -D__ASSEMBLY__=1 \
	             -c $(incs) $< -o $@

%.o: %.S
	$(RISCV_GCC) $(RISCV_GCC_OPTS) $(bmarks_defs) \
	             -c $(incs) $< -o $@

riscv: $(bmarks_riscv_dump) $(bmarks_riscv_hex)
run-riscv: $(bmarks_riscv_out)
	echo; perl -ne 'print "  [$$1] $$ARGV \t$$2\n" if /\*{3}(.{8})\*{3}(.*)/' \
 
junk += $(bmarks_riscv_bin) $(bmarks_riscv_dump) $(bmarks_riscv_hex) $(bmarks_riscv_out) $(bmarks_riscv_obj)

 
#------------------------------------------------------------
# Default
 
all:  riscv
 
#------------------------------------------------------------
# Install

date_suffix = $(shell date +%Y-%m-%d_%H-%M)
install_dir = $(instbasedir)/$(instname)-$(date_suffix)
latest_install = $(shell ls -1 -d $(instbasedir)/$(instname)* | tail -n 1)

install:
	mkdir $(install_dir)
	cp -r $(bmarks_riscv_bin) $(bmarks_riscv_dump) $(install_dir)

install-link:
	rm -rf $(instbasedir)/$(instname)
	ln -s $(latest_install) $(instbasedir)/$(instname)

#------------------------------------------------------------
# Clean up

clean:
	rm -rf $(objs) $(junk) syscall.o crt.o mt-matmul.o mt-vvadd.o
