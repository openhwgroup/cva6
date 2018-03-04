V = ../src/ariane_top_tb.sv ../include/ariane_pkg.sv ../src/ariane_nexys4ddr.sv ../src/ariane_top.sv ../src/socip/nasti/channel.sv ../src/socip/nasti/nasti_buf.sv ../src/socip/nasti/nasti_mux.sv ../src/socip/nasti/nasti_demux.sv ../src/socip/nasti/nasti_crossbar.sv  ../src/socip/nasti/nasti_combiner.sv  ../src/socip/nasti/nasti_slicer.sv  ../src/socip/util/arbiter.sv  ../src/util/crossbar_socip.sv ../src/util/slave_adapter.sv  ../src/util/nasti_converter.sv  ../src/util/if_converter.sv ../src/axi_if/axi_if.sv ../include/nbdcache_pkg.sv ../src/alu.sv ../src/ariane.sv ../src/branch_unit.sv ../src/cache_ctrl.sv ../src/commit_stage.sv ../src/compressed_decoder.sv ../src/controller.sv ../src/csr_buffer.sv ../src/csr_regfile.sv ../src/debug_unit.sv ../src/decoder.sv ../src/ex_stage.sv ../src/fetch_fifo.sv ../src/fifo.sv ../src/icache.sv ../src/id_stage.sv ../src/if_stage.sv ../src/instr_realigner.sv ../src/issue_read_operands.sv ../src/issue_stage.sv ../src/lfsr.sv ../src/load_unit.sv ../src/lsu.sv ../src/lsu_arbiter.sv ../src/miss_handler.sv ../src/mmu.sv ../src/mult.sv ../src/nbdcache.sv ../src/pcgen_stage.sv ../src/perf_counters.sv ../src/ptw.sv ../src/regfile_ff.sv ../src/scoreboard.sv ../src/store_buffer.sv ../src/store_unit.sv ../src/tlb.sv ../src/util/infer_ram.sv ../src/btb.sv ../src/ariane_wrapped.sv ../src/axi_mem_if/axi2mem.sv ../src/jtag_xilinx/jtag_addr.v  ../src/jtag_xilinx/jtag_dummy.v ../src/jtag_xilinx/jtag_rom.v ../src/util/behav_sram.sv

simv: $V
	vcs -sverilog -gui -assert svaext +lint=TFIPC,ONGS,CAWM-L -y $(XILINX_VIVADO)/data/verilog/src/retarget -y $(XILINX_VIVADO)/data/verilog/src/unisims -y ../ariane_top/ariane_top.srcs/sources_1/ip/clk_wiz_ariane +libext+.v $(XILINX_VIVADO)/data/verilog/src/glbl.v $V | tee vcs.log

gui: simv
	./simv

clean:
	rm -rf simv.daidir csrc simv

