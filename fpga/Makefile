VIVADO ?= vivado
VIVADOFLAGS ?= -nojournal -mode batch -source scripts/prologue.tcl

work-dir := work-fpga
bit := $(work-dir)/ariane_xilinx.bit
mcs := $(work-dir)/ariane_xilinx.mcs
ips := xlnx_axi_clock_converter  \
       xlnx_axi_dwidth_converter \
       xlnx_axi_quad_spi         \
       xlnx_clk_gen              \
       xlnx_mig_7_ddr

all: $(mcs)

# Generate mcs from bitstream
$(mcs): $(bit)
	$(VIVADO) $(VIVADOFLAGS) -source scripts/write_cfgmem.tcl -tclargs $@ $^

$(bit):
	mkdir -p $(work-dir)
	$(VIVADO) $(VIVADOFLAGS) -source scripts/run.tcl
	cp ariane.runs/impl_1/ariane_xilinx.bit ./$(work-dir)

$(ips):
	cd xilinx/$@; make clean; make

mcs: $(mcs)

program:
	$(VIVADO) $(VIVADOFLAGS) -source scripts/program.tcl

clean:
	rm -rf *.log *.jou *.str $(work-dir)

.PHONY:
	clean
