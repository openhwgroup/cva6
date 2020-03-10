set ROOT [file normalize [file dirname [info script]]/..]
# This script was generated automatically by bender.

vlog -incr -sv \
    +cover=bcfst+/dut -64 -nologo -suppress 13262,2583 -permissive -pedanticerrors -svinputport=compat \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/include" \
    "+incdir+$ROOT/src/util" \
    "$ROOT/deps/common_verification/src/clk_rst_gen.sv" \
    "$ROOT/deps/common_verification/src/rand_id_queue.sv" \
    "$ROOT/deps/common_verification/src/rand_stream_mst.sv" \
    "$ROOT/deps/common_verification/src/rand_synch_holdable_driver.sv" \
    "$ROOT/deps/common_verification/src/rand_verif_pkg.sv" \
    "$ROOT/deps/common_verification/src/rand_synch_driver.sv" \
    "$ROOT/deps/common_verification/src/rand_stream_slv.sv"

vlog -incr -sv \
    +cover=bcfst+/dut -64 -nologo -suppress 13262,2583 -permissive -pedanticerrors -svinputport=compat \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/include" \
    "+incdir+$ROOT/src/util" \
    "$ROOT/deps/tech_cells_generic/src/deprecated/cluster_clk_cells.sv" \
    "$ROOT/deps/tech_cells_generic/src/deprecated/pulp_clk_cells.sv" \
    "$ROOT/deps/tech_cells_generic/src/rtl/tc_clk.sv"

vlog -incr -sv \
    +cover=bcfst+/dut -64 -nologo -suppress 13262,2583 -permissive -pedanticerrors -svinputport=compat \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/include" \
    "+incdir+$ROOT/src/util" \
    "$ROOT/deps/tech_cells_generic/src/deprecated/cluster_pwr_cells.sv" \
    "$ROOT/deps/tech_cells_generic/src/deprecated/generic_memory.sv" \
    "$ROOT/deps/tech_cells_generic/src/deprecated/generic_rom.sv" \
    "$ROOT/deps/tech_cells_generic/src/deprecated/pad_functional.sv" \
    "$ROOT/deps/tech_cells_generic/src/deprecated/pulp_buffer.sv" \
    "$ROOT/deps/tech_cells_generic/src/deprecated/pulp_pwr_cells.sv" \
    "$ROOT/deps/tech_cells_generic/src/tc_pwr.sv"

vlog -incr -sv \
    +cover=bcfst+/dut -64 -nologo -suppress 13262,2583 -permissive -pedanticerrors -svinputport=compat \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/include" \
    "+incdir+$ROOT/src/util" \
    "$ROOT/deps/common_cells/src/addr_decode.sv" \
    "$ROOT/deps/common_cells/src/cdc_2phase.sv" \
    "$ROOT/deps/common_cells/src/cf_math_pkg.sv" \
    "$ROOT/deps/common_cells/src/clk_div.sv" \
    "$ROOT/deps/common_cells/src/delta_counter.sv" \
    "$ROOT/deps/common_cells/src/edge_propagator_tx.sv" \
    "$ROOT/deps/common_cells/src/exp_backoff.sv" \
    "$ROOT/deps/common_cells/src/fifo_v3.sv" \
    "$ROOT/deps/common_cells/src/graycode.sv" \
    "$ROOT/deps/common_cells/src/lfsr.sv" \
    "$ROOT/deps/common_cells/src/lfsr_16bit.sv" \
    "$ROOT/deps/common_cells/src/lfsr_8bit.sv" \
    "$ROOT/deps/common_cells/src/lzc.sv" \
    "$ROOT/deps/common_cells/src/mv_filter.sv" \
    "$ROOT/deps/common_cells/src/onehot_to_bin.sv" \
    "$ROOT/deps/common_cells/src/plru_tree.sv" \
    "$ROOT/deps/common_cells/src/popcount.sv" \
    "$ROOT/deps/common_cells/src/rr_arb_tree.sv" \
    "$ROOT/deps/common_cells/src/rstgen_bypass.sv" \
    "$ROOT/deps/common_cells/src/serial_deglitch.sv" \
    "$ROOT/deps/common_cells/src/shift_reg.sv" \
    "$ROOT/deps/common_cells/src/spill_register.sv" \
    "$ROOT/deps/common_cells/src/stream_demux.sv" \
    "$ROOT/deps/common_cells/src/stream_filter.sv" \
    "$ROOT/deps/common_cells/src/stream_fork.sv" \
    "$ROOT/deps/common_cells/src/stream_mux.sv" \
    "$ROOT/deps/common_cells/src/sub_per_hash.sv" \
    "$ROOT/deps/common_cells/src/sync.sv" \
    "$ROOT/deps/common_cells/src/sync_wedge.sv" \
    "$ROOT/deps/common_cells/src/unread.sv" \
    "$ROOT/deps/common_cells/src/cb_filter.sv" \
    "$ROOT/deps/common_cells/src/cdc_fifo_2phase.sv" \
    "$ROOT/deps/common_cells/src/cdc_fifo_gray.sv" \
    "$ROOT/deps/common_cells/src/counter.sv" \
    "$ROOT/deps/common_cells/src/edge_detect.sv" \
    "$ROOT/deps/common_cells/src/id_queue.sv" \
    "$ROOT/deps/common_cells/src/max_counter.sv" \
    "$ROOT/deps/common_cells/src/rstgen.sv" \
    "$ROOT/deps/common_cells/src/stream_delay.sv" \
    "$ROOT/deps/common_cells/src/fall_through_register.sv" \
    "$ROOT/deps/common_cells/src/stream_arbiter_flushable.sv" \
    "$ROOT/deps/common_cells/src/stream_register.sv" \
    "$ROOT/deps/common_cells/src/stream_arbiter.sv"

vlog -incr -sv \
    +cover=bcfst+/dut -64 -nologo -suppress 13262,2583 -permissive -pedanticerrors -svinputport=compat \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/include" \
    "+incdir+$ROOT/src/util" \
    "$ROOT/deps/common_cells/src/sram.sv"

vlog -incr -sv \
    +cover=bcfst+/dut -64 -nologo -suppress 13262,2583 -permissive -pedanticerrors -svinputport=compat \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/include" \
    "+incdir+$ROOT/src/util" \
    "$ROOT/deps/common_cells/test/addr_decode_tb.sv" \
    "$ROOT/deps/common_cells/test/cb_filter_tb.sv" \
    "$ROOT/deps/common_cells/test/cdc_2phase_tb.sv" \
    "$ROOT/deps/common_cells/test/cdc_fifo_tb.sv" \
    "$ROOT/deps/common_cells/test/fifo_tb.sv" \
    "$ROOT/deps/common_cells/test/graycode_tb.sv" \
    "$ROOT/deps/common_cells/test/id_queue_tb.sv" \
    "$ROOT/deps/common_cells/test/popcount_tb.sv" \
    "$ROOT/deps/common_cells/test/stream_register_tb.sv" \
    "$ROOT/deps/common_cells/test/sub_per_hash_tb.sv"

vlog -incr -sv \
    +cover=bcfst+/dut -64 -nologo -suppress 13262,2583 -permissive -pedanticerrors -svinputport=compat \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/include" \
    "+incdir+$ROOT/src/util" \
    "$ROOT/deps/common_cells/src/deprecated/clock_divider_counter.sv" \
    "$ROOT/deps/common_cells/src/deprecated/find_first_one.sv" \
    "$ROOT/deps/common_cells/src/deprecated/generic_LFSR_8bit.sv" \
    "$ROOT/deps/common_cells/src/deprecated/generic_fifo.sv" \
    "$ROOT/deps/common_cells/src/deprecated/prioarbiter.sv" \
    "$ROOT/deps/common_cells/src/deprecated/pulp_sync.sv" \
    "$ROOT/deps/common_cells/src/deprecated/pulp_sync_wedge.sv" \
    "$ROOT/deps/common_cells/src/deprecated/rrarbiter.sv" \
    "$ROOT/deps/common_cells/src/deprecated/clock_divider.sv" \
    "$ROOT/deps/common_cells/src/deprecated/fifo_v2.sv" \
    "$ROOT/deps/common_cells/src/deprecated/fifo_v1.sv" \
    "$ROOT/deps/common_cells/src/edge_propagator.sv" \
    "$ROOT/deps/common_cells/src/edge_propagator_rx.sv"

vlog -incr -sv \
    +cover=bcfst+/dut -64 -nologo -suppress 13262,2583 -permissive -pedanticerrors -svinputport=compat \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/include" \
    "+incdir+$ROOT/src/util" \
    "$ROOT/deps/axi/src/axi_pkg.sv" \
    "$ROOT/deps/axi/src/axi_intf.sv" \
    "$ROOT/deps/axi/src/axi_atop_filter.sv" \
    "$ROOT/deps/axi/src/axi_burst_splitter.sv" \
    "$ROOT/deps/axi/src/axi_cdc.sv" \
    "$ROOT/deps/axi/src/axi_cut.sv" \
    "$ROOT/deps/axi/src/axi_delayer.sv" \
    "$ROOT/deps/axi/src/axi_demux.sv" \
    "$ROOT/deps/axi/src/axi_dw_downsizer.sv" \
    "$ROOT/deps/axi/src/axi_dw_upsizer.sv" \
    "$ROOT/deps/axi/src/axi_id_prepend.sv" \
    "$ROOT/deps/axi/src/axi_join.sv" \
    "$ROOT/deps/axi/src/axi_lite_demux.sv" \
    "$ROOT/deps/axi/src/axi_lite_join.sv" \
    "$ROOT/deps/axi/src/axi_lite_mailbox.sv" \
    "$ROOT/deps/axi/src/axi_lite_mux.sv" \
    "$ROOT/deps/axi/src/axi_lite_to_apb.sv" \
    "$ROOT/deps/axi/src/axi_lite_to_axi.sv" \
    "$ROOT/deps/axi/src/axi_modify_address.sv" \
    "$ROOT/deps/axi/src/axi_mux.sv" \
    "$ROOT/deps/axi/src/axi_err_slv.sv" \
    "$ROOT/deps/axi/src/axi_dw_converter.sv" \
    "$ROOT/deps/axi/src/axi_multicut.sv" \
    "$ROOT/deps/axi/src/axi_to_axi_lite.sv" \
    "$ROOT/deps/axi/src/axi_lite_xbar.sv" \
    "$ROOT/deps/axi/src/axi_xbar.sv"

vlog -incr -sv \
    +cover=bcfst+/dut -64 -nologo -suppress 13262,2583 -permissive -pedanticerrors -svinputport=compat \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/include" \
    "+incdir+$ROOT/src/util" \
    "$ROOT/deps/axi/src/axi_test.sv"

vlog -incr -sv \
    +cover=bcfst+/dut -64 -nologo -suppress 13262,2583 -permissive -pedanticerrors -svinputport=compat \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/include" \
    "+incdir+$ROOT/src/util" \
    "$ROOT/deps/axi/test/tb_axi_atop_filter.sv" \
    "$ROOT/deps/axi/test/tb_axi_cdc.sv" \
    "$ROOT/deps/axi/test/tb_axi_delayer.sv" \
    "$ROOT/deps/axi/test/tb_axi_dw_downsizer.sv" \
    "$ROOT/deps/axi/test/tb_axi_dw_upsizer.sv" \
    "$ROOT/deps/axi/test/tb_axi_lite_to_apb.sv" \
    "$ROOT/deps/axi/test/tb_axi_lite_to_axi.sv" \
    "$ROOT/deps/axi/test/tb_axi_lite_mailbox.sv" \
    "$ROOT/deps/axi/test/tb_axi_lite_xbar.sv" \
    "$ROOT/deps/axi/test/tb_axi_to_axi_lite.sv" \
    "$ROOT/deps/axi/test/tb_axi_xbar_pkg.sv" \
    "$ROOT/deps/axi/test/tb_axi_xbar.sv"

vlog -incr -sv \
    +cover=bcfst+/dut -64 -nologo -suppress 13262,2583 -permissive -pedanticerrors -svinputport=compat \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/include" \
    "+incdir+$ROOT/src/util" \
    "$ROOT/deps/fpu_div_sqrt_mvp/hdl/defs_div_sqrt_mvp.sv" \
    "$ROOT/deps/fpu_div_sqrt_mvp/hdl/iteration_div_sqrt_mvp.sv" \
    "$ROOT/deps/fpu_div_sqrt_mvp/hdl/control_mvp.sv" \
    "$ROOT/deps/fpu_div_sqrt_mvp/hdl/norm_div_sqrt_mvp.sv" \
    "$ROOT/deps/fpu_div_sqrt_mvp/hdl/preprocess_mvp.sv" \
    "$ROOT/deps/fpu_div_sqrt_mvp/hdl/nrbd_nrsc_mvp.sv" \
    "$ROOT/deps/fpu_div_sqrt_mvp/hdl/div_sqrt_top_mvp.sv" \
    "$ROOT/deps/fpu_div_sqrt_mvp/hdl/div_sqrt_mvp_wrapper.sv"

vlog -incr -sv \
    +cover=bcfst+/dut -64 -nologo -suppress 13262,2583 -permissive -pedanticerrors -svinputport=compat \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/include" \
    "+incdir+$ROOT/src/util" \
    "$ROOT/deps/apb_timer/src/timer.sv" \
    "$ROOT/deps/apb_timer/src/apb_timer.sv"

vcom -2008 \
    -64 -nologo -2008 \
    "$ROOT/deps/apb_uart/src/apb_uart.vhd" \
    "$ROOT/deps/apb_uart/src/slib_clock_div.vhd" \
    "$ROOT/deps/apb_uart/src/slib_counter.vhd" \
    "$ROOT/deps/apb_uart/src/slib_edge_detect.vhd" \
    "$ROOT/deps/apb_uart/src/slib_fifo.vhd" \
    "$ROOT/deps/apb_uart/src/slib_input_filter.vhd" \
    "$ROOT/deps/apb_uart/src/slib_input_sync.vhd" \
    "$ROOT/deps/apb_uart/src/slib_mv_filter.vhd" \
    "$ROOT/deps/apb_uart/src/uart_baudgen.vhd" \
    "$ROOT/deps/apb_uart/src/uart_interrupt.vhd" \
    "$ROOT/deps/apb_uart/src/uart_receiver.vhd" \
    "$ROOT/deps/apb_uart/src/uart_transmitter.vhd"

vlog -incr -sv \
    +cover=bcfst+/dut -64 -nologo -suppress 13262,2583 -permissive -pedanticerrors -svinputport=compat \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/include" \
    "+incdir+$ROOT/src/util" \
    "$ROOT/deps/axi_mem_if/src/axi2mem.sv" \
    "$ROOT/deps/axi_mem_if/src/deprecated/axi_mem_if.sv" \
    "$ROOT/deps/axi_mem_if/src/deprecated/axi_mem_if_var_latency.sv" \
    "$ROOT/deps/axi_mem_if/src/deprecated/axi_mem_if_wrap.sv"

vlog -incr -sv \
    +cover=bcfst+/dut -64 -nologo -suppress 13262,2583 -permissive -pedanticerrors -svinputport=compat \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/include" \
    "+incdir+$ROOT/src/util" \
    "$ROOT/deps/axi_riscv_atomics/src/axi_res_tbl.sv" \
    "$ROOT/deps/axi_riscv_atomics/src/axi_riscv_amos_alu.sv" \
    "$ROOT/deps/axi_riscv_atomics/src/axi_riscv_amos.sv" \
    "$ROOT/deps/axi_riscv_atomics/src/axi_riscv_lrsc.sv" \
    "$ROOT/deps/axi_riscv_atomics/src/axi_riscv_atomics.sv" \
    "$ROOT/deps/axi_riscv_atomics/src/axi_riscv_lrsc_wrap.sv" \
    "$ROOT/deps/axi_riscv_atomics/src/axi_riscv_atomics_wrap.sv"

vlog -incr -sv \
    +cover=bcfst+/dut -64 -nologo -suppress 13262,2583 -permissive -pedanticerrors -svinputport=compat \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/include" \
    "+incdir+$ROOT/src/util" \
    "$ROOT/deps/fpu/src/fpnew_pkg.sv" \
    "$ROOT/deps/fpu/src/fpnew_cast_multi.sv" \
    "$ROOT/deps/fpu/src/fpnew_classifier.sv" \
    "$ROOT/deps/fpu/src/fpnew_divsqrt_multi.sv" \
    "$ROOT/deps/fpu/src/fpnew_fma.sv" \
    "$ROOT/deps/fpu/src/fpnew_fma_multi.sv" \
    "$ROOT/deps/fpu/src/fpnew_noncomp.sv" \
    "$ROOT/deps/fpu/src/fpnew_opgroup_block.sv" \
    "$ROOT/deps/fpu/src/fpnew_opgroup_fmt_slice.sv" \
    "$ROOT/deps/fpu/src/fpnew_opgroup_multifmt_slice.sv" \
    "$ROOT/deps/fpu/src/fpnew_rounding.sv" \
    "$ROOT/deps/fpu/src/fpnew_top.sv"

vlog -incr -sv \
    +cover=bcfst+/dut -64 -nologo -suppress 13262,2583 -permissive -pedanticerrors -svinputport=compat \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/include" \
    "+incdir+$ROOT/src/util" \
    "$ROOT/deps/register_interface/src/reg_intf.sv" \
    "$ROOT/deps/register_interface/src/reg_uniform.sv" \
    "$ROOT/deps/register_interface/src/axi_lite_to_reg.sv" \
    "$ROOT/deps/register_interface/src/apb_to_reg.sv"

vlog -incr -sv \
    +cover=bcfst+/dut -64 -nologo -suppress 13262,2583 -permissive -pedanticerrors -svinputport=compat \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/include" \
    "+incdir+$ROOT/src/util" \
    "$ROOT/deps/register_interface/src/reg_test.sv"

vlog -incr -sv \
    +cover=bcfst+/dut -64 -nologo -suppress 13262,2583 -permissive -pedanticerrors -svinputport=compat \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/include" \
    "+incdir+$ROOT/src/util" \
    "$ROOT/deps/riscv-dbg/src/dm_pkg.sv" \
    "$ROOT/deps/riscv-dbg/debug_rom/debug_rom.sv" \
    "$ROOT/deps/riscv-dbg/src/dm_csrs.sv" \
    "$ROOT/deps/riscv-dbg/src/dm_mem.sv" \
    "$ROOT/deps/riscv-dbg/src/dm_top.sv" \
    "$ROOT/deps/riscv-dbg/src/dmi_cdc.sv" \
    "$ROOT/deps/riscv-dbg/src/dmi_jtag.sv" \
    "$ROOT/deps/riscv-dbg/src/dmi_jtag_tap.sv" \
    "$ROOT/deps/riscv-dbg/src/dm_sba.sv"

vlog -incr -sv \
    +cover=bcfst+/dut -64 -nologo -suppress 13262,2583 -permissive -pedanticerrors -svinputport=compat \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    +define+WT_DCACHE=1 \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/include" \
    "+incdir+$ROOT/src/util" \
    "$ROOT/deps/register_interface/src/reg_intf_pkg.sv" \
    "$ROOT/deps/rv_plic/rtl/top_pkg.sv" \
    "$ROOT/deps/rv_plic/rtl/plic_regmap.sv" \
    "$ROOT/deps/rv_plic/rtl/prim_subreg.sv" \
    "$ROOT/deps/rv_plic/rtl/prim_subreg_ext.sv" \
    "$ROOT/deps/rv_plic/rtl/rv_plic_gateway.sv" \
    "$ROOT/deps/rv_plic/rtl/rv_plic_reg_pkg.sv" \
    "$ROOT/deps/rv_plic/rtl/rv_plic_target.sv" \
    "$ROOT/deps/rv_plic/rtl/tlul_pkg.sv" \
    "$ROOT/deps/rv_plic/rtl/plic_top.sv" \
    "$ROOT/deps/rv_plic/rtl/rv_plic_reg_top.sv" \
    "$ROOT/deps/rv_plic/rtl/rv_plic.sv" \
    "$ROOT/include/riscv_pkg.sv" \
    "$ROOT/src/ariane_regfile_ff.sv" \
    "$ROOT/include/ariane_pkg.sv" \
    "$ROOT/include/std_cache_pkg.sv" \
    "$ROOT/include/wt_cache_pkg.sv" \
    "$ROOT/src/amo_buffer.sv" \
    "$ROOT/src/alu.sv" \
    "$ROOT/src/commit_stage.sv" \
    "$ROOT/src/compressed_decoder.sv" \
    "$ROOT/src/csr_regfile.sv" \
    "$ROOT/src/decoder.sv" \
    "$ROOT/src/branch_unit.sv" \
    "$ROOT/src/controller.sv" \
    "$ROOT/src/csr_buffer.sv" \
    "$ROOT/src/fpu_wrap.sv" \
    "$ROOT/src/frontend/bht.sv" \
    "$ROOT/src/frontend/btb.sv" \
    "$ROOT/src/frontend/instr_queue.sv" \
    "$ROOT/src/frontend/instr_scan.sv" \
    "$ROOT/src/frontend/ras.sv" \
    "$ROOT/src/instr_realign.sv" \
    "$ROOT/src/issue_read_operands.sv" \
    "$ROOT/src/load_unit.sv" \
    "$ROOT/src/multiplier.sv" \
    "$ROOT/src/perf_counters.sv" \
    "$ROOT/src/ptw.sv" \
    "$ROOT/src/re_name.sv" \
    "$ROOT/src/scoreboard.sv" \
    "$ROOT/src/serdiv.sv" \
    "$ROOT/src/store_buffer.sv" \
    "$ROOT/src/tlb.sv" \
    "$ROOT/tb/ariane_soc_pkg.sv" \
    "$ROOT/include/ariane_axi_pkg.sv" \
    "$ROOT/src/cache_subsystem/amo_alu.sv" \
    "$ROOT/src/cache_subsystem/cache_ctrl.sv" \
    "$ROOT/src/cache_subsystem/tag_cmp.sv" \
    "$ROOT/src/cache_subsystem/std_icache.sv" \
    "$ROOT/src/cache_subsystem/wt_dcache_ctrl.sv" \
    "$ROOT/src/cache_subsystem/wt_dcache_mem.sv" \
    "$ROOT/src/cache_subsystem/wt_dcache_missunit.sv" \
    "$ROOT/src/cache_subsystem/wt_dcache_wbuffer.sv" \
    "$ROOT/src/cache_subsystem/wt_icache.sv" \
    "$ROOT/src/cache_subsystem/wt_l15_adapter.sv" \
    "$ROOT/src/frontend/frontend.sv" \
    "$ROOT/src/id_stage.sv" \
    "$ROOT/src/mmu.sv" \
    "$ROOT/src/mult.sv" \
    "$ROOT/src/store_unit.sv" \
    "$ROOT/src/axi_adapter.sv" \
    "$ROOT/src/axi_shim.sv" \
    "$ROOT/src/cache_subsystem/wt_dcache.sv" \
    "$ROOT/src/clint/axi_lite_interface.sv" \
    "$ROOT/src/load_store_unit.sv" \
    "$ROOT/src/issue_stage.sv" \
    "$ROOT/src/util/axi_master_connect.sv" \
    "$ROOT/src/util/axi_slave_connect.sv" \
    "$ROOT/src/util/axi_master_connect_rev.sv" \
    "$ROOT/src/util/axi_slave_connect_rev.sv" \
    "$ROOT/src/cache_subsystem/miss_handler.sv" \
    "$ROOT/src/cache_subsystem/wt_axi_adapter.sv" \
    "$ROOT/src/clint/clint.sv" \
    "$ROOT/src/ex_stage.sv" \
    "$ROOT/src/cache_subsystem/std_nbdcache.sv" \
    "$ROOT/src/cache_subsystem/wt_cache_subsystem.sv" \
    "$ROOT/src/cache_subsystem/std_cache_subsystem.sv" \
    "$ROOT/src/ariane.sv" \
    "$ROOT/fpga/src/ariane_peripherals_xilinx.sv" \
    "$ROOT/deps/fpga-support/rtl/SyncSpRamBeNx64.sv" \
    "$ROOT/src/util/sram.sv"

vlog -incr -sv \
    +cover=bcfst+/dut -64 -nologo -suppress 13262,2583 -permissive -pedanticerrors -svinputport=compat \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    +define+WT_DCACHE=1 \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/include" \
    "+incdir+$ROOT/src/util" \
    "$ROOT/bootrom/bootrom.sv" \
    "$ROOT/tb/common/uart.sv" \
    "$ROOT/tb/common/SimDTM.sv" \
    "$ROOT/tb/common/SimJTAG.sv" \
    "$ROOT/tb/common/mock_uart.sv" \
    "$ROOT/tb/ariane_testharness.sv" \
    "$ROOT/tb/ariane_tb.sv"

vlog -incr -sv \
    +cover=bcfst+/dut -64 -nologo -suppress 13262,2583 -permissive -pedanticerrors -svinputport=compat \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    +define+WT_DCACHE=1 \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/include" \
    "+incdir+$ROOT/src/util" \
    "$ROOT/include/instr_tracer_pkg.sv" \
    "$ROOT/src/util/instr_tracer_if.sv" \
    "$ROOT/src/util/instr_tracer.sv"
