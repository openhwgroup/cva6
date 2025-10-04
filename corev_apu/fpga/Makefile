VIVADO ?= vivado
# VIVADOFLAGS ?= -nojournal -mode batch -source scripts/prologue.tcl
VIVADOFLAGS ?= -source scripts/prologue.tcl

work-dir := work-fpga
bit := $(work-dir)/ariane_xilinx.bit
mcs := $(work-dir)/ariane_xilinx.mcs
ip-dir := xilinx
ips := xlnx_blk_mem_gen.xci \
       xlnx_processing_system7.xci \
	   xlnx_axi_clock_converter.xci  \
       xlnx_axi_dwidth_converter.xci \
       xlnx_axi_dwidth_converter_dm_master.xci \
       xlnx_axi_dwidth_converter_dm_slave.xci \
       xlnx_clk_gen.xci              \

# Only include MIG if not zedboard
ifneq ($(BOARD), zedboard)
	ips += xlnx_mig_7_ddr3.xci           \
        	xlnx_axi_quad_spi.xci         \
       		xlnx_axi_gpio.xci              
endif
project_prefix := ariane
ifeq ($(BOARD), zedboard)
	project_prefix := cva6_fpga
endif
# Vivado project artifact directories to remove
project_dirs := \
  $(project_prefix).runs \
  $(project_prefix).gen  \
  $(project_prefix).sim  \
  $(project_prefix).srcs

ips := $(addprefix $(work-dir)/, $(ips))
ips-target := $(join $(addsuffix /ip/, $(addprefix $(ip-dir)/, $(basename $(ips)))), $(ips))

all: $(mcs)

# Generate mcs from bitstream
$(mcs): $(bit)
	$(VIVADO) $(VIVADOFLAGS) -source scripts/write_cfgmem.tcl -tclargs $@ $^

$(bit): $(ips)
	mkdir -p $(work-dir)
	$(VIVADO) $(VIVADOFLAGS) -source scripts/run.tcl
	cp ariane.runs/impl_1/ariane_xilinx* ./$(work-dir)
	
$(ips): %.xci :
	mkdir -p $(work-dir)
	@echo Generating $(@F)
	@cd $(ip-dir)/$(basename $(@F)) && make clean && make
	@cp $(ip-dir)/$(basename $(@F))/$(basename $(@F)).srcs/sources_1/ip/$(basename $(@F))/$(@F) $@

mcs: $(mcs)

program:
	$(VIVADO) $(VIVADOFLAGS) -source scripts/program.tcl

clean:
	rm -rf *.log *.jou *.str *.rpt *.mif *.xpr \
		$(work-dir) \
		$(project_prefix).cache \
		$(project_prefix).hw \
		$(project_prefix).ip_user_files \
		$(project_dirs) \
		reports \
		scripts/vivado*
.PHONY:
	clean

