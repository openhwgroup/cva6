B = ../jtag_vpi/bench
X = /opt/Xilinx/Vivado/2015.4/data/verilog/src
S = ../src
U = $S/util
D = ../debug_wrap/debug_wrap.srcs
V = \
$B/include/tap_defines.v \
$U/cluster_clock_gating.sv \
$U/generic_fifo.sv \
$S/axi_slice/axi_w_buffer.sv \
$S/axi_slice/axi_r_buffer.sv \
$S/axi_slice/axi_b_buffer.sv \
$S/axi_slice/axi_aw_buffer.sv \
$S/axi_slice/axi_ar_buffer.sv \
$S/soc/sd_crc_7.v \
$S/soc/sd_crc_16.v \
$S/soc/eth_lfsr.v \
$S/socip/nasti/channel.sv \
$S/socip/util/arbiter.sv \
$S/axi_mem_if/axi_mem_if.sv \
$S/soc/sd_data_serial_host.sv \
$S/soc/sd_cmd_serial_host.v \
$S/soc/ps2_translation_table.v \
$S/soc/ps2_keyboard.v \
$S/soc/dualmem.v \
$S/soc/axis_gmii_tx.v \
$S/soc/axis_gmii_rx.v \
$S/socip/nasti/nasti_combiner.sv \
$S/socip/nasti/nasti_mux.sv \
$S/socip/nasti/nasti_demux.sv \
$S/socip/nasti/nasti_buf.sv \
$S/axi_if/axi_if.sv \
$U/slave_adapter.sv \
$D/sources_1/ip/clk_wiz_1/clk_wiz_1_clk_wiz.v \
$D/sources_1/ip/clk_wiz_1/clk_wiz_1.v \
$U/axi_bram_ctrl_ariane.sv \
$U/sevensegment.v \
$U/nexys4ddr_display.v \
$S/soc/uart.v \
$S/soc/sd_top.sv \
$S/soc/rx_delay.v \
$S/soc/ps2.v \
$S/soc/my_fifo.v \
$S/soc/fstore2.v \
$S/soc/framing_top.sv \
$S/socip/nasti/nasti_crossbar.sv \
$S/socip/nasti/nasti_data_mover.sv \
$U/nasti_converter.sv \
$U/if_converter.sv \
$D/sources_1/ip/clk_wiz_ariane/clk_wiz_ariane_clk_wiz.v \
$D/sources_1/ip/clk_wiz_ariane/clk_wiz_ariane.v \
$U/capture_wrap.sv \
$U/dbg_wrap.sv \
$U/axi_ram_wrap_ariane.sv \
$U/display_top.sv \
$S/soc/periph_soc.sv \
$S/soc/sd_verilator_model.sv \
$S/soc/ddr2_model.v \
../include/ariane_pkg.sv \
$S/ariane_nexys4ddr.sv \
$S/socip/nasti/nasti_slicer.sv  \
$S/util/crossbar_socip.sv \
../include/nbdcache_pkg.sv \
$S/alu.sv \
$S/ariane.sv \
$S/branch_unit.sv \
$S/cache_ctrl.sv \
$S/commit_stage.sv \
$S/compressed_decoder.sv \
$S/controller.sv \
$S/csr_buffer.sv \
$S/csr_regfile.sv \
$S/debug_unit.sv \
$S/decoder.sv \
$S/ex_stage.sv \
$S/fetch_fifo.sv \
$S/fifo.sv \
$S/icache.sv \
$S/id_stage.sv \
$S/if_stage.sv \
$S/instr_realigner.sv \
$S/issue_read_operands.sv \
$S/issue_stage.sv \
$S/lfsr.sv \
$S/load_unit.sv \
$S/lsu.sv \
$S/lsu_arbiter.sv \
$S/miss_handler.sv \
$S/mmu.sv \
$S/mult.sv \
$S/nbdcache.sv \
$S/pcgen_stage.sv \
$S/perf_counters.sv \
$S/ptw.sv \
$S/regfile_ff.sv \
$S/scoreboard.sv \
$S/store_buffer.sv \
$S/store_unit.sv \
$S/tlb.sv \
$S/util/infer_ram.sv \
$S/btb.sv \
$S/util/behav_sram.sv \
glbl.v \

J = $B/jtag_tap/jtag_tap.v \
../jtag_vpi/jtag_vpi.v \
../jtag_vpi/jtag_vpi.c \
$S/jtag_xilinx/jtag_dummy.v \
$S/jtag_xilinx/jtag_rom.v \
$S/jtag_xilinx/jtag_addr.v \
ariane_vpi_tb.v \

N = $S/soc/ariane_nexys4ddr_top_tb.sv \

simv: $V $N
	vcs -gui -sverilog -assert svaext +lint=TFIPC,ONGS,CAWM-L +vpi +libext+.v -P ../jtag_vpi/jtag_vpi.tab -debug_access+all \
+incdir+$B/include \
+incdir+$S/soc \
-y $X/retarget \
-y $X/unisims \
$X/unisims/RAMB18E1.v \
$X/unisims/RAMB36E1.v \
$N $V -o $@ +define+NOJTAG+

jtag: $V $J
	vcs -gui -sverilog -assert svaext +lint=TFIPC,ONGS,CAWM-L +vpi +libext+.v -P ../jtag_vpi/jtag_vpi.tab -debug_access+all \
+incdir+$B/include \
+incdir+$S/soc \
-y $X/retarget \
-y $X/unisims \
$X/unisims/RAMB18E1.v \
$X/unisims/RAMB36E1.v \
$V $J -o $@

glbl.v: $X/glbl.v
	sed -e 's/\(SEL[1-4]_GLBL\)\ = 0/\1/' $< > $@

clean:
	rm -rf csrc simv.daidir simv glbl.v
