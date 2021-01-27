#!/bin/sh
rm -rf work-ver
echo "[Verilator] Building Model"
verilator \
    +define+WT_DCACHE \
    +incdir+src/axi_node \
    +incdir+src/common_cells/include/ \
    include/riscv_pkg.sv \
    src/riscv-dbg/src/dm_pkg.sv \
    include/ariane_pkg.sv \
    include/std_cache_pkg.sv \
    include/wt_cache_pkg.sv \
    src/axi/src/axi_pkg.sv \
    src/register_interface/src/reg_intf.sv \
    src/register_interface/src/reg_intf_pkg.sv \
    include/axi_intf.sv \
    tb/ariane_soc_pkg.sv \
    include/ariane_axi_pkg.sv \
    src/fpu/src/fpnew_pkg.sv \
    src/fpu/src/fpu_div_sqrt_mvp/hdl/defs_div_sqrt_mvp.sv \
    src/ariane.sv \
    src/serdiv.sv \
    src/ariane_regfile_ff.sv \
    src/amo_buffer.sv \
    src/id_stage.sv \
    src/branch_unit.sv \
    src/dromajo_ram.sv \
    src/controller.sv \
    src/issue_stage.sv \
    src/re_name.sv \
    src/csr_buffer.sv \
    src/tlb.sv \
    src/decoder.sv \
    src/ex_stage.sv \
    src/scoreboard.sv \
    src/mmu.sv \
    src/store_unit.sv \
    src/axi_adapter.sv \
    src/fpu_wrap.sv \
    src/csr_regfile.sv \
    src/load_store_unit.sv \
    src/commit_stage.sv \
    src/multiplier.sv \
    src/store_buffer.sv \
    src/compressed_decoder.sv \
    src/axi_shim.sv \
    src/alu.sv \
    src/instr_realign.sv \
    src/perf_counters.sv \
    src/ptw.sv \
    src/mult.sv \
    src/load_unit.sv \
    src/issue_read_operands.sv \
    src/fpu/src/fpnew_fma.sv \
    src/fpu/src/fpnew_opgroup_fmt_slice.sv \
    src/fpu/src/fpnew_divsqrt_multi.sv \
    src/fpu/src/fpnew_fma_multi.sv \
    src/fpu/src/fpnew_opgroup_multifmt_slice.sv \
    src/fpu/src/fpnew_classifier.sv \
    src/fpu/src/fpnew_noncomp.sv \
    src/fpu/src/fpnew_cast_multi.sv \
    src/fpu/src/fpnew_opgroup_block.sv \
    src/fpu/src/fpnew_rounding.sv \
    src/fpu/src/fpnew_top.sv \
    src/fpu/src/fpu_div_sqrt_mvp/hdl/iteration_div_sqrt_mvp.sv \
    src/fpu/src/fpu_div_sqrt_mvp/hdl/nrbd_nrsc_mvp.sv \
    src/fpu/src/fpu_div_sqrt_mvp/hdl/div_sqrt_top_mvp.sv \
    src/fpu/src/fpu_div_sqrt_mvp/hdl/preprocess_mvp.sv \
    src/fpu/src/fpu_div_sqrt_mvp/hdl/control_mvp.sv \
    src/fpu/src/fpu_div_sqrt_mvp/hdl/norm_div_sqrt_mvp.sv \
    src/fpu/src/fpu_div_sqrt_mvp/hdl/div_sqrt_mvp_wrapper.sv \
    src/frontend/frontend.sv \
    src/frontend/instr_scan.sv \
    src/frontend/instr_queue.sv \
    src/frontend/bht.sv \
    src/frontend/btb.sv \
    src/frontend/ras.sv \
    src/cache_subsystem/wt_dcache.sv \
    src/cache_subsystem/tag_cmp.sv \
    src/cache_subsystem/cache_ctrl.sv \
    src/cache_subsystem/amo_alu.sv \
    src/cache_subsystem/wt_axi_adapter.sv \
    src/cache_subsystem/std_nbdcache.sv \
    src/cache_subsystem/wt_dcache_ctrl.sv \
    src/cache_subsystem/miss_handler.sv \
    src/cache_subsystem/wt_cache_subsystem.sv \
    src/cache_subsystem/wt_dcache_missunit.sv \
    src/cache_subsystem/cva6_icache.sv \
    src/cache_subsystem/wt_dcache_wbuffer.sv \
    src/cache_subsystem/wt_l15_adapter.sv \
    src/cache_subsystem/wt_dcache_mem.sv \
    src/cache_subsystem/std_cache_subsystem.sv \
    src/cache_subsystem/cva6_icache_axi_wrapper.sv \
    bootrom/bootrom.sv \
    bootrom/dromajo_bootrom.sv \
    src/clint/axi_lite_interface.sv \
    src/clint/clint.sv \
    fpga/src/axi2apb/src/axi2apb_wrap.sv \
    fpga/src/axi2apb/src/axi2apb.sv \
    fpga/src/axi2apb/src/axi2apb_64_32.sv \
    fpga/src/apb_timer/apb_timer.sv \
    fpga/src/apb_timer/timer.sv \
    fpga/src/axi_slice/src/axi_w_buffer.sv \
    fpga/src/axi_slice/src/axi_r_buffer.sv \
    fpga/src/axi_slice/src/axi_slice_wrap.sv \
    fpga/src/axi_slice/src/axi_slice.sv \
    fpga/src/axi_slice/src/axi_single_slice.sv \
    fpga/src/axi_slice/src/axi_ar_buffer.sv \
    fpga/src/axi_slice/src/axi_b_buffer.sv \
    fpga/src/axi_slice/src/axi_aw_buffer.sv \
    src/axi_node/src/axi_regs_top.sv \
    src/axi_node/src/axi_BR_allocator.sv \
    src/axi_node/src/axi_BW_allocator.sv \
    src/axi_node/src/axi_address_decoder_BR.sv \
    src/axi_node/src/axi_DW_allocator.sv \
    src/axi_node/src/axi_address_decoder_BW.sv \
    src/axi_node/src/axi_address_decoder_DW.sv \
    src/axi_node/src/axi_node_arbiter.sv \
    src/axi_node/src/axi_response_block.sv \
    src/axi_node/src/axi_request_block.sv \
    src/axi_node/src/axi_AR_allocator.sv \
    src/axi_node/src/axi_AW_allocator.sv \
    src/axi_node/src/axi_address_decoder_AR.sv \
    src/axi_node/src/axi_address_decoder_AW.sv \
    src/axi_node/src/apb_regs_top.sv \
    src/axi_node/src/axi_node_intf_wrap.sv \
    src/axi_node/src/axi_node.sv \
    src/axi_node/src/axi_node_wrap_with_slices.sv \
    src/axi_node/src/axi_multiplexer.sv \
    src/axi_riscv_atomics/src/axi_riscv_amos.sv \
    src/axi_riscv_atomics/src/axi_riscv_atomics.sv \
    src/axi_riscv_atomics/src/axi_res_tbl.sv \
    src/axi_riscv_atomics/src/axi_riscv_lrsc_wrap.sv \
    src/axi_riscv_atomics/src/axi_riscv_amos_alu.sv \
    src/axi_riscv_atomics/src/axi_riscv_lrsc.sv \
    src/axi_riscv_atomics/src/axi_riscv_atomics_wrap.sv \
    src/axi_mem_if/src/axi2mem.sv \
    src/pmp/src/pmp_entry.sv \
    src/pmp/src/pmp.sv \
    src/rv_plic/rtl/rv_plic_target.sv \
    src/rv_plic/rtl/rv_plic_gateway.sv \
    src/rv_plic/rtl/plic_regmap.sv \
    src/rv_plic/rtl/plic_top.sv \
    src/riscv-dbg/src/dmi_cdc.sv \
    src/riscv-dbg/src/dmi_jtag.sv \
    src/riscv-dbg/src/dmi_jtag_tap.sv \
    src/riscv-dbg/src/dm_csrs.sv \
    src/riscv-dbg/src/dm_mem.sv \
    src/riscv-dbg/src/dm_sba.sv \
    src/riscv-dbg/src/dm_top.sv \
    src/riscv-dbg/debug_rom/debug_rom.sv \
    src/register_interface/src/apb_to_reg.sv \
    src/axi/src/axi_multicut.sv \
    src/common_cells/src/deprecated/generic_fifo.sv \
    src/common_cells/src/deprecated/pulp_sync.sv \
    src/common_cells/src/deprecated/find_first_one.sv \
    src/common_cells/src/rstgen_bypass.sv \
    src/common_cells/src/stream_mux.sv \
    src/common_cells/src/stream_demux.sv \
    src/common_cells/src/exp_backoff.sv \
    src/util/axi_master_connect.sv \
    src/util/axi_slave_connect.sv \
    src/util/axi_master_connect_rev.sv \
    src/util/axi_slave_connect_rev.sv \
    src/axi/src/axi_cut.sv \
    src/axi/src/axi_join.sv \
    src/axi/src/axi_delayer.sv \
    src/axi/src/axi_to_axi_lite.sv \
    src/fpga-support/rtl/SyncSpRamBeNx64.sv \
    src/common_cells/src/unread.sv \
    src/common_cells/src/sync.sv \
    src/common_cells/src/cdc_2phase.sv \
    src/common_cells/src/spill_register.sv \
    src/common_cells/src/sync_wedge.sv \
    src/common_cells/src/edge_detect.sv \
    src/common_cells/src/stream_arbiter.sv \
    src/common_cells/src/stream_arbiter_flushable.sv \
    src/common_cells/src/deprecated/fifo_v1.sv \
    src/common_cells/src/deprecated/fifo_v2.sv \
    src/common_cells/src/fifo_v3.sv \
    src/common_cells/src/lzc.sv \
    src/common_cells/src/popcount.sv \
    src/common_cells/src/rr_arb_tree.sv \
    src/common_cells/src/deprecated/rrarbiter.sv \
    src/common_cells/src/stream_delay.sv \
    src/common_cells/src/lfsr_8bit.sv \
    src/common_cells/src/lfsr_16bit.sv \
    src/common_cells/src/delta_counter.sv \
    src/common_cells/src/counter.sv \
    src/common_cells/src/shift_reg.sv \
    src/tech_cells_generic/src/pulp_clock_gating.sv \
    src/tech_cells_generic/src/cluster_clock_inverter.sv \
    src/tech_cells_generic/src/pulp_clock_mux2.sv \
    core_tb/cva6_core_tb.sv \
    src/util/sram.sv \
    --unroll-count 256 \
    -Werror-PINMISSING \
    -Werror-IMPLICIT \
    -Wno-fatal \
    -Wno-PINCONNECTEMPTY \
    -Wno-ASSIGNDLY \
    -Wno-DECLFILENAME \
    -Wno-UNUSED \
    -Wno-UNOPTFLAT \
    -Wno-BLKANDNBLK \
    -Wno-style \
    --trace \
    -LDFLAGS "-L/opt/riscv/lib -L/opt/riscv/lib -Wl,-rpath,/opt/riscv/lib -Wl,-rpath,/opt/riscv/lib -lfesvr  -lpthread" \
    -CFLAGS "-I/include -I/opt/riscv/include -I/opt/riscv/include  -std=c++11 -I../tb/dpi " \
    -Wall \
    --cc \
    --vpi \
    --top-module cva6_testharness \
    --Mdir work-ver -O3 \
    --exe core_tb/cva6_core_tb.cpp

#    --top-module cva6_core_tb \
#    --exe tb/ariane_tb.cpp tb/dpi/SimDTM.cc tb/dpi/SimJTAG.cc tb/dpi/remote_bitbang.cc tb/dpi/msim_helper.cc
