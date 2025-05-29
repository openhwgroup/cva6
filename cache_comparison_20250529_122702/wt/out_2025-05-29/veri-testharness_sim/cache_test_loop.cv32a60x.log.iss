make -C /home/cai/cache_project/sandbox/cva6/ verilate verilator="verilator --no-timing" target=cv32a60x defines=
make[1]: Entering directory '/home/cai/cache_project/sandbox/cva6'
Makefile:153: XCELIUM_HOME not set which is necessary for compiling DPIs when using XCELIUM
[Verilator] Building Model
verilator --no-timing --no-timing verilator_config.vlt -f core/Flist.cva6 core/cva6_rvfi.sv /home/cai/cache_project/sandbox/cva6/corev_apu/tb/ariane_axi_pkg.sv /home/cai/cache_project/sandbox/cva6/corev_apu/tb/axi_intf.sv /home/cai/cache_project/sandbox/cva6/corev_apu/register_interface/src/reg_intf.sv /home/cai/cache_project/sandbox/cva6/corev_apu/tb/ariane_soc_pkg.sv /home/cai/cache_project/sandbox/cva6/corev_apu/riscv-dbg/src/dm_pkg.sv /home/cai/cache_project/sandbox/cva6/corev_apu/tb/ariane_axi_soc_pkg.sv /home/cai/cache_project/sandbox/cva6/core/cva6_rvfi.sv /home/cai/cache_project/sandbox/cva6/corev_apu/src/ariane.sv /home/cai/cache_project/sandbox/cva6/corev_apu/bootrom/bootrom.sv /home/cai/cache_project/sandbox/cva6/corev_apu/clint/axi_lite_interface.sv /home/cai/cache_project/sandbox/cva6/corev_apu/clint/clint.sv /home/cai/cache_project/sandbox/cva6/corev_apu/fpga/src/axi2apb/src/axi2apb_64_32.sv /home/cai/cache_project/sandbox/cva6/corev_apu/fpga/src/axi2apb/src/axi2apb.sv /home/cai/cache_project/sandbox/cva6/corev_apu/fpga/src/axi2apb/src/axi2apb_wrap.sv /home/cai/cache_project/sandbox/cva6/corev_apu/fpga/src/apb_timer/apb_timer.sv /home/cai/cache_project/sandbox/cva6/corev_apu/fpga/src/apb_timer/timer.sv /home/cai/cache_project/sandbox/cva6/corev_apu/fpga/src/axi_slice/src/axi_ar_buffer.sv /home/cai/cache_project/sandbox/cva6/corev_apu/fpga/src/axi_slice/src/axi_aw_buffer.sv /home/cai/cache_project/sandbox/cva6/corev_apu/fpga/src/axi_slice/src/axi_b_buffer.sv /home/cai/cache_project/sandbox/cva6/corev_apu/fpga/src/axi_slice/src/axi_r_buffer.sv /home/cai/cache_project/sandbox/cva6/corev_apu/fpga/src/axi_slice/src/axi_single_slice.sv /home/cai/cache_project/sandbox/cva6/corev_apu/fpga/src/axi_slice/src/axi_slice.sv /home/cai/cache_project/sandbox/cva6/corev_apu/fpga/src/axi_slice/src/axi_slice_wrap.sv /home/cai/cache_project/sandbox/cva6/corev_apu/fpga/src/axi_slice/src/axi_w_buffer.sv /home/cai/cache_project/sandbox/cva6/corev_apu/src/axi_riscv_atomics/src/axi_res_tbl.sv /home/cai/cache_project/sandbox/cva6/corev_apu/src/axi_riscv_atomics/src/axi_riscv_amos_alu.sv /home/cai/cache_project/sandbox/cva6/corev_apu/src/axi_riscv_atomics/src/axi_riscv_amos.sv /home/cai/cache_project/sandbox/cva6/corev_apu/src/axi_riscv_atomics/src/axi_riscv_atomics.sv /home/cai/cache_project/sandbox/cva6/corev_apu/src/axi_riscv_atomics/src/axi_riscv_atomics_wrap.sv /home/cai/cache_project/sandbox/cva6/corev_apu/src/axi_riscv_atomics/src/axi_riscv_lrsc.sv /home/cai/cache_project/sandbox/cva6/corev_apu/src/axi_riscv_atomics/src/axi_riscv_lrsc_wrap.sv /home/cai/cache_project/sandbox/cva6/corev_apu/axi_mem_if/src/axi2mem.sv /home/cai/cache_project/sandbox/cva6/corev_apu/riscv-dbg/src/dm_csrs.sv /home/cai/cache_project/sandbox/cva6/corev_apu/riscv-dbg/src/dmi_cdc.sv /home/cai/cache_project/sandbox/cva6/corev_apu/riscv-dbg/src/dmi_jtag.sv /home/cai/cache_project/sandbox/cva6/corev_apu/riscv-dbg/src/dmi_jtag_tap.sv /home/cai/cache_project/sandbox/cva6/corev_apu/riscv-dbg/src/dm_mem.sv /home/cai/cache_project/sandbox/cva6/corev_apu/riscv-dbg/src/dm_sba.sv /home/cai/cache_project/sandbox/cva6/corev_apu/riscv-dbg/src/dm_top.sv /home/cai/cache_project/sandbox/cva6/corev_apu/rv_plic/rtl/rv_plic_target.sv /home/cai/cache_project/sandbox/cva6/corev_apu/rv_plic/rtl/rv_plic_gateway.sv /home/cai/cache_project/sandbox/cva6/corev_apu/rv_plic/rtl/plic_regmap.sv /home/cai/cache_project/sandbox/cva6/corev_apu/rv_plic/rtl/plic_top.sv /home/cai/cache_project/sandbox/cva6/corev_apu/riscv-dbg/debug_rom/debug_rom.sv /home/cai/cache_project/sandbox/cva6/corev_apu/register_interface/src/apb_to_reg.sv /home/cai/cache_project/sandbox/cva6/vendor/pulp-platform/axi/src/axi_multicut.sv /home/cai/cache_project/sandbox/cva6/vendor/pulp-platform/common_cells/src/rstgen_bypass.sv /home/cai/cache_project/sandbox/cva6/vendor/pulp-platform/common_cells/src/rstgen.sv /home/cai/cache_project/sandbox/cva6/vendor/pulp-platform/common_cells/src/addr_decode.sv /home/cai/cache_project/sandbox/cva6/vendor/pulp-platform/common_cells/src/stream_register.sv /home/cai/cache_project/sandbox/cva6/vendor/pulp-platform/axi/src/axi_cut.sv /home/cai/cache_project/sandbox/cva6/vendor/pulp-platform/axi/src/axi_join.sv /home/cai/cache_project/sandbox/cva6/vendor/pulp-platform/axi/src/axi_delayer.sv /home/cai/cache_project/sandbox/cva6/vendor/pulp-platform/axi/src/axi_to_axi_lite.sv /home/cai/cache_project/sandbox/cva6/vendor/pulp-platform/axi/src/axi_id_prepend.sv /home/cai/cache_project/sandbox/cva6/vendor/pulp-platform/axi/src/axi_atop_filter.sv /home/cai/cache_project/sandbox/cva6/vendor/pulp-platform/axi/src/axi_err_slv.sv /home/cai/cache_project/sandbox/cva6/vendor/pulp-platform/axi/src/axi_mux.sv /home/cai/cache_project/sandbox/cva6/vendor/pulp-platform/axi/src/axi_demux.sv /home/cai/cache_project/sandbox/cva6/vendor/pulp-platform/axi/src/axi_xbar.sv /home/cai/cache_project/sandbox/cva6/vendor/pulp-platform/common_cells/src/cdc_2phase.sv /home/cai/cache_project/sandbox/cva6/vendor/pulp-platform/common_cells/src/spill_register_flushable.sv /home/cai/cache_project/sandbox/cva6/vendor/pulp-platform/common_cells/src/spill_register.sv /home/cai/cache_project/sandbox/cva6/vendor/pulp-platform/common_cells/src/deprecated/fifo_v1.sv /home/cai/cache_project/sandbox/cva6/vendor/pulp-platform/common_cells/src/deprecated/fifo_v2.sv /home/cai/cache_project/sandbox/cva6/vendor/pulp-platform/common_cells/src/stream_delay.sv /home/cai/cache_project/sandbox/cva6/vendor/pulp-platform/common_cells/src/lfsr_16bit.sv /home/cai/cache_project/sandbox/cva6/vendor/pulp-platform/tech_cells_generic/src/deprecated/cluster_clk_cells.sv /home/cai/cache_project/sandbox/cva6/vendor/pulp-platform/tech_cells_generic/src/deprecated/pulp_clk_cells.sv /home/cai/cache_project/sandbox/cva6/vendor/pulp-platform/tech_cells_generic/src/rtl/tc_clk.sv /home/cai/cache_project/sandbox/cva6/core/include/iti_pkg.sv /home/cai/cache_project/sandbox/cva6/corev_apu/tb/ariane_testharness.sv /home/cai/cache_project/sandbox/cva6/corev_apu/tb/ariane_peripherals.sv /home/cai/cache_project/sandbox/cva6/corev_apu/tb/rvfi_tracer.sv /home/cai/cache_project/sandbox/cva6/corev_apu/tb/common/uart.sv /home/cai/cache_project/sandbox/cva6/corev_apu/tb/common/SimDTM.sv /home/cai/cache_project/sandbox/cva6/corev_apu/tb/common/SimJTAG.sv /home/cai/cache_project/sandbox/cva6/core/cva6_iti/instr_to_trace.sv /home/cai/cache_project/sandbox/cva6/core/cva6_iti/iti.sv /home/cai/cache_project/sandbox/cva6/core/cva6_iti/itype_detector.sv +define+ corev_apu/tb/common/mock_uart.sv +incdir+corev_apu/axi_node  --unroll-count 256 -Wall -Werror-PINMISSING -Werror-IMPLICIT -Wno-fatal -Wno-PINCONNECTEMPTY -Wno-ASSIGNDLY -Wno-DECLFILENAME -Wno-UNUSED -Wno-UNOPTFLAT -Wno-BLKANDNBLK -Wno-style  -DPRELOAD=1     -LDFLAGS "-L/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/lib -L/home/cai/cache_project/sandbox/cva6/tools/spike/lib -Wl,-rpath,/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/lib -Wl,-rpath,/home/cai/cache_project/sandbox/cva6/tools/spike/lib -lfesvr -lriscv -ldisasm -lyaml-cpp  -lpthread " -CFLAGS "-I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike"   --cc --vpi  +incdir+/home/cai/cache_project//sandbox/cva6/vendor/pulp-platform/common_cells/include/  +incdir+/home/cai/cache_project//sandbox/cva6/vendor/pulp-platform/axi/include/  +incdir+/home/cai/cache_project//sandbox/cva6/corev_apu/register_interface/include/  +incdir+/home/cai/cache_project//sandbox/cva6/corev_apu/tb/common/  +incdir+/home/cai/cache_project//sandbox/cva6/vendor/pulp-platform/axi/include/  +incdir+/home/cai/cache_project//sandbox/cva6/verif/core-v-verif/lib/uvm_agents/uvma_rvfi/  +incdir+/home/cai/cache_project//sandbox/cva6/verif/core-v-verif/lib/uvm_components/uvmc_rvfi_reference_model/  +incdir+/home/cai/cache_project//sandbox/cva6/verif/core-v-verif/lib/uvm_components/uvmc_rvfi_scoreboard/  +incdir+/home/cai/cache_project//sandbox/cva6/verif/core-v-verif/lib/uvm_agents/uvma_core_cntrl/  +incdir+/home/cai/cache_project//sandbox/cva6/verif/tb/core/  +incdir+/home/cai/cache_project//sandbox/cva6/core/include/  +incdir+/home/cai/cache_project/sandbox/cva6/tools/spike/include/disasm/ --top-module ariane_testharness --threads-dpi none --Mdir work-ver -O3 --exe corev_apu/tb/ariane_tb.cpp corev_apu/tb/dpi/SimDTM.cc corev_apu/tb/dpi/SimJTAG.cc corev_apu/tb/dpi/remote_bitbang.cc corev_apu/tb/dpi/msim_helper.cc
%Warning-MODDUP: /home/cai/cache_project/sandbox/cva6/core/cva6_rvfi.sv:12:8: Duplicate declaration of module: 'cva6_rvfi'
   12 | module cva6_rvfi
      |        ^~~~~~~~~
                 core/cva6_rvfi.sv:12:8: ... Location of original declaration
   12 | module cva6_rvfi
      |        ^~~~~~~~~
                 ... For warning description see https://verilator.org/warn/MODDUP?v=5.008
                 ... Use "/* verilator lint_off MODDUP */" and lint_on around source to disable this message.
%Warning-WIDTHTRUNC: /home/cai/cache_project//sandbox/cva6/core/include/build_config_pkg.sv:161:21: Operator ASSIGN expects 1 bits on the Assign RHS, but Assign RHS's OR generates 32 bits.
                                                                                                  : ... In instance ariane_testharness
  161 |     cfg.AXI_USER_EN = CVA6Cfg.DataUserEn | CVA6Cfg.FetchUserEn;
      |                     ^
%Warning-WIDTHTRUNC: /home/cai/cache_project//sandbox/cva6/core/cache_subsystem/wt_dcache_wbuffer.sv:281:3: Logical operator GENIF expects 1 bit on the If, but If's SEL generates 32 bits.
                                                                                                          : ... In instance ariane_testharness.i_ariane.i_cva6.gen_cache_wt.i_cache_subsystem.i_wt_dcache.i_wt_dcache_wbuffer
  281 |   if (CVA6Cfg.DATA_USER_EN) begin
      |   ^~
%Warning-WIDTHTRUNC: /home/cai/cache_project//sandbox/cva6/common/local/util/sram_cache.sv:42:44: Logical operator COND expects 1 bit on the Conditional Test, but Conditional Test's VARREF 'USER_EN' generates 32 bits.
                                                                                                : ... In instance ariane_testharness.i_ariane.i_cva6.gen_cache_wt.i_cache_subsystem.i_cva6_icache.gen_sram[0].data_sram
   42 |   localparam DATA_AND_USER_WIDTH = USER_EN ? DATA_WIDTH + USER_WIDTH : DATA_WIDTH;
      |                                            ^
%Warning-LITENDIAN: /home/cai/cache_project//sandbox/cva6/core/cvfpu/src/fpnew_pkg.sv:50:28: Big bit endian vector: left < right of bit range: [0:4]
                                                                                           : ... In instance ariane_testharness
   50 |   localparam fp_encoding_t [0:NUM_FP_FORMATS-1] FP_ENCODINGS  = '{
      |                            ^
%Warning-LITENDIAN: /home/cai/cache_project//sandbox/cva6/core/cvfpu/src/fpnew_pkg.sv:59:17: Big bit endian vector: left < right of bit range: [0:4]
                                                                                           : ... In instance ariane_testharness
   59 |   typedef logic [0:NUM_FP_FORMATS-1]       fmt_logic_t;     
      |                 ^
%Warning-LITENDIAN: /home/cai/cache_project//sandbox/cva6/core/cvfpu/src/fpnew_pkg.sv:105:17: Big bit endian vector: left < right of bit range: [0:3]
                                                                                            : ... In instance ariane_testharness
  105 |   typedef logic [0:NUM_INT_FORMATS-1] ifmt_logic_t;  
      |                 ^
%Warning-LITENDIAN: /home/cai/cache_project//sandbox/cva6/core/cvfpu/src/fpnew_pkg.sv:60:17: Big bit endian vector: left < right of bit range: [0:4]
                                                                                           : ... In instance ariane_testharness
   60 |   typedef logic [0:NUM_FP_FORMATS-1][31:0] fmt_unsigned_t;  
      |                 ^
%Warning-LITENDIAN: /home/cai/cache_project//sandbox/cva6/core/cvfpu/src/fpnew_pkg.sv:199:26: Big bit endian vector: left < right of bit range: [0:3]
                                                                                            : ... In instance ariane_testharness
  199 |   typedef fmt_unsigned_t [0:NUM_OPGROUPS-1] opgrp_fmt_unsigned_t;
      |                          ^
%Warning-LITENDIAN: /home/cai/cache_project//sandbox/cva6/core/cvfpu/src/fpnew_pkg.sv:194:23: Big bit endian vector: left < right of bit range: [0:4]
                                                                                            : ... In instance ariane_testharness
  194 |   typedef unit_type_t [0:NUM_FP_FORMATS-1] fmt_unit_types_t;
      |                       ^
%Warning-LITENDIAN: /home/cai/cache_project//sandbox/cva6/core/cvfpu/src/fpnew_pkg.sv:197:28: Big bit endian vector: left < right of bit range: [0:3]
                                                                                            : ... In instance ariane_testharness
  197 |   typedef fmt_unit_types_t [0:NUM_OPGROUPS-1] opgrp_fmt_unit_types_t;
      |                            ^
%Warning-WIDTHTRUNC: /home/cai/cache_project//sandbox/cva6/core/cache_subsystem/wt_dcache_wbuffer.sv:595:13: Logical operator IF expects 1 bit on the If, but If's SEL generates 32 bits.
                                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.gen_cache_wt.i_cache_subsystem.i_wt_dcache.i_wt_dcache_wbuffer
  595 |             if (CVA6Cfg.DATA_USER_EN) begin
      |             ^~
%Warning-WIDTHEXPAND: /home/cai/cache_project//sandbox/cva6/core/cache_subsystem/wt_dcache_missunit.sv:164:30: Operator EQ expects 32 bits on the LHS, but LHS's VARREF 'cnt_q' generates 4 bits.
                                                                                                             : ... In instance ariane_testharness.i_ariane.i_cva6.gen_cache_wt.i_cache_subsystem.i_wt_dcache.i_wt_dcache_missunit
  164 |   assign flush_done = (cnt_q == CVA6Cfg.DCACHE_NUM_WORDS - 1);
      |                              ^~
%Warning-WIDTHTRUNC: /home/cai/cache_project//sandbox/cva6/core/cache_subsystem/wt_dcache_missunit.sv:269:7: Logical operator IF expects 1 bit on the If, but If's SEL generates 32 bits.
                                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.gen_cache_wt.i_cache_subsystem.i_wt_dcache.i_wt_dcache_missunit
  269 |       if (CVA6Cfg.DATA_USER_EN) begin
      |       ^~
%Warning-WIDTHEXPAND: /home/cai/cache_project//sandbox/cva6/core/load_unit.sv:555:118: Operator LT expects 32 or 3 bits on the LHS, but LHS's SEL generates 2 bits.
                                                                                     : ... In instance ariane_testharness.i_ariane.i_cva6.ex_stage_i.lsu_i.i_load_unit
  555 |         ldbuf_w |->  (ldbuf_wdata.operation inside {ariane_pkg::LW, ariane_pkg::LWU}) |-> ldbuf_wdata.address_offset < 5)
      |                                                                                                                      ^
%Warning-WIDTHEXPAND: /home/cai/cache_project//sandbox/cva6/core/load_unit.sv:559:118: Operator LT expects 32 or 3 bits on the LHS, but LHS's SEL generates 2 bits.
                                                                                     : ... In instance ariane_testharness.i_ariane.i_cva6.ex_stage_i.lsu_i.i_load_unit
  559 |         ldbuf_w |->  (ldbuf_wdata.operation inside {ariane_pkg::LH, ariane_pkg::LHU}) |-> ldbuf_wdata.address_offset < 7)
      |                                                                                                                      ^
%Warning-WIDTHEXPAND: /home/cai/cache_project//sandbox/cva6/core/load_unit.sv:563:118: Operator LT expects 32 or 4 bits on the LHS, but LHS's SEL generates 2 bits.
                                                                                     : ... In instance ariane_testharness.i_ariane.i_cva6.ex_stage_i.lsu_i.i_load_unit
  563 |         ldbuf_w |->  (ldbuf_wdata.operation inside {ariane_pkg::LB, ariane_pkg::LBU}) |-> ldbuf_wdata.address_offset < 8)
      |                                                                                                                      ^
%Warning-WIDTHEXPAND: /home/cai/cache_project//sandbox/cva6/core/serdiv.sv:127:35: Operator COND expects 32 bits on the Conditional False, but Conditional False's REPLICATE generates 6 bits.
                                                                                 : ... In instance ariane_testharness.i_ariane.i_cva6.ex_stage_i.i_mult.i_div
  127 |   assign shift_a = (lzc_a_no_one) ? WIDTH : {1'b0, lzc_a_result};
      |                                   ^
%Warning-WIDTHTRUNC: /home/cai/cache_project//sandbox/cva6/core/serdiv.sv:127:18: Operator ASSIGNW expects 6 bits on the Assign RHS, but Assign RHS's COND generates 32 bits.
                                                                                : ... In instance ariane_testharness.i_ariane.i_cva6.ex_stage_i.i_mult.i_div
  127 |   assign shift_a = (lzc_a_no_one) ? WIDTH : {1'b0, lzc_a_result};
      |                  ^
%Warning-WIDTHTRUNC: /home/cai/cache_project//sandbox/cva6/core/multiplier.sv:132:63: Operator ASSIGN expects 32 bits on the Assign RHS, but Assign RHS's FUNCREF 'sext32to64' generates 64 bits.
                                                                                    : ... In instance ariane_testharness.i_ariane.i_cva6.ex_stage_i.i_mult.i_multiplier
  132 |         if (operator_q == MULW && CVA6Cfg.IS_XLEN64) result_o = sext32to64(mult_result_q[31:0]);
      |                                                               ^
%Warning-WIDTHEXPAND: /home/cai/cache_project//sandbox/cva6/core/cache_subsystem/cva6_icache.sv:159:109: Operator SHIFTL expects 32 bits on the LHS, but LHS's REPLICATE generates 4 bits.
                                                                                                       : ... In instance ariane_testharness.i_ariane.i_cva6.gen_cache_wt.i_cache_subsystem.i_cva6_icache
  159 |                          ( paddr_is_nc  & mem_data_req_o ) ? {{ICACHE_OFFSET_WIDTH-1{1'b0}}, cl_offset_q[2]}<<2 :  
      |                                                                                                             ^~
%Warning-WIDTHEXPAND: /home/cai/cache_project//sandbox/cva6/core/cache_subsystem/cva6_icache.sv:159:60: Operator COND expects 32 bits on the Conditional False, but Conditional False's VARREF 'cl_offset_q' generates 4 bits.
                                                                                                      : ... In instance ariane_testharness.i_ariane.i_cva6.gen_cache_wt.i_cache_subsystem.i_cva6_icache
  159 |                          ( paddr_is_nc  & mem_data_req_o ) ? {{ICACHE_OFFSET_WIDTH-1{1'b0}}, cl_offset_q[2]}<<2 :  
      |                                                            ^
%Warning-WIDTHTRUNC: /home/cai/cache_project//sandbox/cva6/core/cache_subsystem/cva6_icache.sv:158:24: Operator ASSIGNW expects 4 bits on the Assign RHS, but Assign RHS's COND generates 32 bits.
                                                                                                     : ... In instance ariane_testharness.i_ariane.i_cva6.gen_cache_wt.i_cache_subsystem.i_cva6_icache
  158 |     assign cl_offset_d = ( dreq_o.ready & dreq_i.req)      ? (dreq_i.vaddr >> CVA6Cfg.FETCH_ALIGN_BITS) << CVA6Cfg.FETCH_ALIGN_BITS :
      |                        ^
%Warning-WIDTHTRUNC: /home/cai/cache_project//sandbox/cva6/core/cache_subsystem/cva6_icache.sv:429:47: Logical operator COND expects 1 bit on the Conditional Test, but Conditional Test's SEL generates 32 bits.
                                                                                                     : ... In instance ariane_testharness.i_ariane.i_cva6.gen_cache_wt.i_cache_subsystem.i_cva6_icache
  429 |     assign cl_user[i] = CVA6Cfg.FETCH_USER_EN ? cl_ruser[i][{cl_offset_q, 3'b0}+:CVA6Cfg.FETCH_USER_WIDTH] : '0;
      |                                               ^
%Warning-WIDTHTRUNC: /home/cai/cache_project//sandbox/cva6/core/cache_subsystem/cva6_icache.sv:444:43: Logical operator COND expects 1 bit on the Conditional Test, but Conditional Test's SEL generates 32 bits.
                                                                                                     : ... In instance ariane_testharness.i_ariane.i_cva6.gen_cache_wt.i_cache_subsystem.i_cva6_icache
  444 |       dreq_o.user = CVA6Cfg.FETCH_USER_EN ? cl_user[hit_idx] : '0;
      |                                           ^
%Warning-WIDTHTRUNC: /home/cai/cache_project//sandbox/cva6/core/cache_subsystem/cva6_icache.sv:447:43: Logical operator COND expects 1 bit on the Conditional Test, but Conditional Test's SEL generates 32 bits.
                                                                                                     : ... In instance ariane_testharness.i_ariane.i_cva6.gen_cache_wt.i_cache_subsystem.i_cva6_icache
  447 |       dreq_o.user = CVA6Cfg.FETCH_USER_EN ? mem_rtrn_i.user[{cl_offset_q, 3'b0}+:CVA6Cfg.FETCH_USER_WIDTH] : '0;
      |                                           ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/load_store_unit.sv:339:33: Extracting 34 bits from only 32 bit number
                                                                                       : ... In instance ariane_testharness.i_ariane.i_cva6.ex_stage_i.lsu_i
  339 |           lsu_paddr <= mmu_vaddr[CVA6Cfg.PLEN-1:0];
      |                                 ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/load_store_unit.sv:339:33: Selection index out of range: 33:0 outside 31:0
                                                                                       : ... In instance ariane_testharness.i_ariane.i_cva6.ex_stage_i.lsu_i
  339 |           lsu_paddr <= mmu_vaddr[CVA6Cfg.PLEN-1:0];
      |                                 ^
%Warning-WIDTHTRUNC: /home/cai/cache_project//sandbox/cva6/core/mult.sv:104:21: Operator ASSIGN expects 32 bits on the Assign RHS, but Assign RHS's FUNCREF 'sext32to64' generates 64 bits.
                                                                              : ... In instance ariane_testharness.i_ariane.i_cva6.ex_stage_i.i_mult
  104 |           operand_a = sext32to64(fu_data_i.operand_a[31:0]);
      |                     ^
%Warning-WIDTHTRUNC: /home/cai/cache_project//sandbox/cva6/core/mult.sv:105:21: Operator ASSIGN expects 32 bits on the Assign RHS, but Assign RHS's FUNCREF 'sext32to64' generates 64 bits.
                                                                              : ... In instance ariane_testharness.i_ariane.i_cva6.ex_stage_i.i_mult
  105 |           operand_b = sext32to64(fu_data_i.operand_b[31:0]);
      |                     ^
%Warning-WIDTHEXPAND: /home/cai/cache_project//sandbox/cva6/core/mult.sv:146:56: Operator COND expects 64 bits on the Conditional False, but Conditional False's VARREF 'result' generates 32 bits.
                                                                               : ... In instance ariane_testharness.i_ariane.i_cva6.ex_stage_i.i_mult
  146 |   assign div_result = (CVA6Cfg.IS_XLEN64 && word_op_q) ? sext32to64(result) : result;
      |                                                        ^
%Warning-WIDTHTRUNC: /home/cai/cache_project//sandbox/cva6/core/mult.sv:146:21: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                                                              : ... In instance ariane_testharness.i_ariane.i_cva6.ex_stage_i.i_mult
  146 |   assign div_result = (CVA6Cfg.IS_XLEN64 && word_op_q) ? sext32to64(result) : result;
      |                     ^
%Warning-WIDTHEXPAND: /home/cai/cache_project//sandbox/cva6/core/alu.sv:336:172: Operator SUB expects 32 bits on the RHS, but RHS's SEL generates 5 bits.
                                                                               : ... In instance ariane_testharness.i_ariane.i_cva6.ex_stage_i.alu_i
  336 |         rolw = ({{CVA6Cfg.XLEN-32{1'b0}},fu_data_i.operand_a[31:0]} << fu_data_i.operand_b[4:0]) | ({{CVA6Cfg.XLEN-32{1'b0}},fu_data_i.operand_a[31:0]} >> (CVA6Cfg.XLEN-32-fu_data_i.operand_b[4:0]));
      |                                                                                                                                                                            ^
%Warning-WIDTHEXPAND: /home/cai/cache_project//sandbox/cva6/core/alu.sv:337:172: Operator SUB expects 32 bits on the RHS, but RHS's SEL generates 5 bits.
                                                                               : ... In instance ariane_testharness.i_ariane.i_cva6.ex_stage_i.alu_i
  337 |         rorw = ({{CVA6Cfg.XLEN-32{1'b0}},fu_data_i.operand_a[31:0]} >> fu_data_i.operand_b[4:0]) | ({{CVA6Cfg.XLEN-32{1'b0}},fu_data_i.operand_a[31:0]} << (CVA6Cfg.XLEN-32-fu_data_i.operand_b[4:0]));
      |                                                                                                                                                                            ^
%Warning-WIDTHEXPAND: /home/cai/cache_project//sandbox/cva6/core/alu.sv:374:132: Operator SUB expects 32 bits on the RHS, but RHS's SEL generates 6 bits.
                                                                               : ... In instance ariane_testharness.i_ariane.i_cva6.ex_stage_i.alu_i
  374 |         result_o = (CVA6Cfg.IS_XLEN64) ? ((fu_data_i.operand_a << fu_data_i.operand_b[5:0]) | (fu_data_i.operand_a >> (CVA6Cfg.XLEN-fu_data_i.operand_b[5:0]))) : ((fu_data_i.operand_a << fu_data_i.operand_b[4:0]) | (fu_data_i.operand_a >> (CVA6Cfg.XLEN-fu_data_i.operand_b[4:0])));
      |                                                                                                                                    ^
%Warning-WIDTHEXPAND: /home/cai/cache_project//sandbox/cva6/core/alu.sv:374:253: Operator SUB expects 32 bits on the RHS, but RHS's SEL generates 5 bits.
                                                                               : ... In instance ariane_testharness.i_ariane.i_cva6.ex_stage_i.alu_i
  374 |         result_o = (CVA6Cfg.IS_XLEN64) ? ((fu_data_i.operand_a << fu_data_i.operand_b[5:0]) | (fu_data_i.operand_a >> (CVA6Cfg.XLEN-fu_data_i.operand_b[5:0]))) : ((fu_data_i.operand_a << fu_data_i.operand_b[4:0]) | (fu_data_i.operand_a >> (CVA6Cfg.XLEN-fu_data_i.operand_b[4:0])));
      |                                                                                                                                                                                                                                                             ^
%Warning-WIDTHEXPAND: /home/cai/cache_project//sandbox/cva6/core/alu.sv:377:132: Operator SUB expects 32 bits on the RHS, but RHS's SEL generates 6 bits.
                                                                               : ... In instance ariane_testharness.i_ariane.i_cva6.ex_stage_i.alu_i
  377 |         result_o = (CVA6Cfg.IS_XLEN64) ? ((fu_data_i.operand_a >> fu_data_i.operand_b[5:0]) | (fu_data_i.operand_a << (CVA6Cfg.XLEN-fu_data_i.operand_b[5:0]))) : ((fu_data_i.operand_a >> fu_data_i.operand_b[4:0]) | (fu_data_i.operand_a << (CVA6Cfg.XLEN-fu_data_i.operand_b[4:0])));
      |                                                                                                                                    ^
%Warning-WIDTHEXPAND: /home/cai/cache_project//sandbox/cva6/core/alu.sv:377:253: Operator SUB expects 32 bits on the RHS, but RHS's SEL generates 5 bits.
                                                                               : ... In instance ariane_testharness.i_ariane.i_cva6.ex_stage_i.alu_i
  377 |         result_o = (CVA6Cfg.IS_XLEN64) ? ((fu_data_i.operand_a >> fu_data_i.operand_b[5:0]) | (fu_data_i.operand_a << (CVA6Cfg.XLEN-fu_data_i.operand_b[5:0]))) : ((fu_data_i.operand_a >> fu_data_i.operand_b[4:0]) | (fu_data_i.operand_a << (CVA6Cfg.XLEN-fu_data_i.operand_b[4:0])));
      |                                                                                                                                                                                                                                                             ^
%Warning-WIDTHEXPAND: /home/cai/cache_project//sandbox/cva6/core/alu.sv:400:40: Operator COND expects 64 bits on the Conditional True, but Conditional True's REPLICATE generates 32 bits.
                                                                              : ... In instance ariane_testharness.i_ariane.i_cva6.ex_stage_i.alu_i
  400 |         result_o = (CVA6Cfg.IS_XLEN32) ? ({fu_data_i.operand_b[15:0], fu_data_i.operand_a[15:0]}) : ({fu_data_i.operand_b[31:0], fu_data_i.operand_a[31:0]});
      |                                        ^
%Warning-WIDTHTRUNC: /home/cai/cache_project//sandbox/cva6/core/alu.sv:400:18: Operator ASSIGN expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                                                             : ... In instance ariane_testharness.i_ariane.i_cva6.ex_stage_i.alu_i
  400 |         result_o = (CVA6Cfg.IS_XLEN32) ? ({fu_data_i.operand_b[15:0], fu_data_i.operand_a[15:0]}) : ({fu_data_i.operand_b[31:0], fu_data_i.operand_a[31:0]});
      |                  ^
%Warning-WIDTHEXPAND: /home/cai/cache_project//sandbox/cva6/core/alu.sv:402:40: Operator COND expects 64 bits on the Conditional True, but Conditional True's REPLICATE generates 32 bits.
                                                                              : ... In instance ariane_testharness.i_ariane.i_cva6.ex_stage_i.alu_i
  402 |         result_o = (CVA6Cfg.IS_XLEN32) ? ({16'b0, fu_data_i.operand_b[7:0], fu_data_i.operand_a[7:0]}) : ({48'b0, fu_data_i.operand_b[7:0], fu_data_i.operand_a[7:0]});
      |                                        ^
%Warning-WIDTHTRUNC: /home/cai/cache_project//sandbox/cva6/core/alu.sv:402:18: Operator ASSIGN expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                                                             : ... In instance ariane_testharness.i_ariane.i_cva6.ex_stage_i.alu_i
  402 |         result_o = (CVA6Cfg.IS_XLEN32) ? ({16'b0, fu_data_i.operand_b[7:0], fu_data_i.operand_a[7:0]}) : ({48'b0, fu_data_i.operand_b[7:0], fu_data_i.operand_a[7:0]});
      |                  ^
%Warning-WIDTHTRUNC: /home/cai/cache_project//sandbox/cva6/core/alu.sv:409:18: Operator ASSIGN expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                                                             : ... In instance ariane_testharness.i_ariane.i_cva6.ex_stage_i.alu_i
  409 |         result_o = {
      |                  ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:580:69: Selection index out of range: 2:2 outside 1:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  580 |         if (OPERANDS_PER_INSTR == 3 && ~x_issue_resp_i.register_read[2]) begin
      |                                                                     ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:594:18: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  594 |         stall_raw[1] = 1'b1;
      |                  ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:602:18: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  602 |         stall_raw[1] = 1'b1;
      |                  ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:613:18: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  613 |         stall_raw[1] = 1'b1;
      |                  ^
%Warning-WIDTHTRUNC: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:622:28: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 63 bits.
                                                                                             : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  622 |     assign imm_forward_rs3 = {{CVA6Cfg.XLEN - CVA6Cfg.FLen{1'b0}}, rs3_res[0]};
      |                            ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:830:20: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  830 |         issue_ack_o[1] = 1'b0;
      |                    ^
%Warning-WIDTHTRUNC: /home/cai/cache_project//sandbox/cva6/core/scoreboard.sv:297:30: Operator ASSIGNW expects 2 bits on the Assign RHS, but Assign RHS's VARREF 'issue_pointer' generates 4 bits.
                                                                                    : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_scoreboard
  297 |   assign fwd_o.issue_pointer = issue_pointer;
      |                              ^
%Warning-WIDTHTRUNC: /home/cai/cache_project//sandbox/cva6/core/frontend/instr_queue.sv:372:40: Operator ASSIGN expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                                                                              : ... In instance ariane_testharness.i_ariane.i_cva6.i_frontend.i_instr_queue
  372 |             fetch_entry_o[NID].ex.tval = {{64 - CVA6Cfg.VLEN{1'b0}}, instr_data_out[i].ex_vaddr};
      |                                        ^
%Warning-WIDTHTRUNC: /home/cai/cache_project//sandbox/cva6/core/cvxif_example/instr_decoder.sv:64:36: Operator ASSIGN expects 2 bits on the Assign RHS, but Assign RHS's SEL generates 3 bits.
                                                                                                    : ... In instance ariane_testharness.i_ariane.gen_cvxif.gen_COPRO_EXAMPLE.i_cvxif_coprocessor.instr_decoder_i
   64 |         issue_resp_o.register_read = CoproInstr[i].resp.register_read;  
      |                                    ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/cvxif_example/instr_decoder.sv:68:102: Selection index out of range: 2:2 outside 1:0
                                                                                                   : ... In instance ariane_testharness.i_ariane.gen_cvxif.gen_COPRO_EXAMPLE.i_cvxif_coprocessor.instr_decoder_i
   68 |           rs3_ready = NrRgprPorts == 3 ? (~CoproInstr[i].resp.register_read[2] || register_i.rs_valid[2]) : 1'b1;
      |                                                                                                      ^
%Warning-WIDTHEXPAND: /home/cai/cache_project//sandbox/cva6/core/csr_regfile.sv:469:41: Operator OR expects 32 bits on the RHS, but RHS's VARREF 'fiom_q' generates 1 bits.
                                                                                      : ... In instance ariane_testharness.i_ariane.i_cva6.csr_regfile_i
  469 |         if (CVA6Cfg.RVS) csr_rdata = '0 | fiom_q;
      |                                         ^
%Warning-WIDTHEXPAND: /home/cai/cache_project//sandbox/cva6/core/csr_regfile.sv:552:43: Operator OR expects 32 bits on the RHS, but RHS's VARREF 'fiom_q' generates 1 bits.
                                                                                      : ... In instance ariane_testharness.i_ariane.i_cva6.csr_regfile_i
  552 |           if (CVA6Cfg.RVU) csr_rdata = '0 | fiom_q;
      |                                           ^
%Warning-WIDTHTRUNC: /home/cai/cache_project//sandbox/cva6/core/csr_regfile.sv:787:64: Operator ASSIGN expects 4 bits on the Assign RHS, but Assign RHS's SUB generates 12 bits.
                                                                                     : ... In instance ariane_testharness.i_ariane.i_cva6.csr_regfile_i
  787 |           automatic logic [3:0] index = csr_addr.address[11:0] - riscv::CSR_PMPCFG0;
      |                                                                ^
%Warning-WIDTHTRUNC: /home/cai/cache_project//sandbox/cva6/core/csr_regfile.sv:1372:28: Operator ASSIGN expects 1 bits on the Assign RHS, but Assign RHS's ENUMITEMREF 'Off' generates 2 bits.
                                                                                      : ... In instance ariane_testharness.i_ariane.i_cva6.csr_regfile_i
 1372 |             mstatus_d.sie  = riscv::Off;
      |                            ^
%Warning-WIDTHTRUNC: /home/cai/cache_project//sandbox/cva6/core/csr_regfile.sv:1373:28: Operator ASSIGN expects 1 bits on the Assign RHS, but Assign RHS's ENUMITEMREF 'Off' generates 2 bits.
                                                                                      : ... In instance ariane_testharness.i_ariane.i_cva6.csr_regfile_i
 1373 |             mstatus_d.spie = riscv::Off;
      |                            ^
%Warning-WIDTHTRUNC: /home/cai/cache_project//sandbox/cva6/core/csr_regfile.sv:1374:28: Operator ASSIGN expects 1 bits on the Assign RHS, but Assign RHS's ENUMITEMREF 'Off' generates 2 bits.
                                                                                      : ... In instance ariane_testharness.i_ariane.i_cva6.csr_regfile_i
 1374 |             mstatus_d.spp  = riscv::Off;
      |                            ^
%Warning-WIDTHTRUNC: /home/cai/cache_project//sandbox/cva6/core/csr_regfile.sv:1375:28: Operator ASSIGN expects 1 bits on the Assign RHS, but Assign RHS's ENUMITEMREF 'Off' generates 2 bits.
                                                                                      : ... In instance ariane_testharness.i_ariane.i_cva6.csr_regfile_i
 1375 |             mstatus_d.sum  = riscv::Off;
      |                            ^
%Warning-WIDTHTRUNC: /home/cai/cache_project//sandbox/cva6/core/csr_regfile.sv:1376:28: Operator ASSIGN expects 1 bits on the Assign RHS, but Assign RHS's ENUMITEMREF 'Off' generates 2 bits.
                                                                                      : ... In instance ariane_testharness.i_ariane.i_cva6.csr_regfile_i
 1376 |             mstatus_d.mxr  = riscv::Off;
      |                            ^
%Warning-WIDTHTRUNC: /home/cai/cache_project//sandbox/cva6/core/csr_regfile.sv:1377:28: Operator ASSIGN expects 1 bits on the Assign RHS, but Assign RHS's ENUMITEMREF 'Off' generates 2 bits.
                                                                                      : ... In instance ariane_testharness.i_ariane.i_cva6.csr_regfile_i
 1377 |             mstatus_d.tvm  = riscv::Off;
      |                            ^
%Warning-WIDTHTRUNC: /home/cai/cache_project//sandbox/cva6/core/csr_regfile.sv:1378:28: Operator ASSIGN expects 1 bits on the Assign RHS, but Assign RHS's ENUMITEMREF 'Off' generates 2 bits.
                                                                                      : ... In instance ariane_testharness.i_ariane.i_cva6.csr_regfile_i
 1378 |             mstatus_d.tsr  = riscv::Off;
      |                            ^
%Warning-WIDTHTRUNC: /home/cai/cache_project//sandbox/cva6/core/csr_regfile.sv:1381:28: Operator ASSIGN expects 1 bits on the Assign RHS, but Assign RHS's ENUMITEMREF 'Off' generates 2 bits.
                                                                                      : ... In instance ariane_testharness.i_ariane.i_cva6.csr_regfile_i
 1381 |             mstatus_d.tw   = riscv::Off;
      |                            ^
%Warning-WIDTHTRUNC: /home/cai/cache_project//sandbox/cva6/core/csr_regfile.sv:1382:28: Operator ASSIGN expects 1 bits on the Assign RHS, but Assign RHS's ENUMITEMREF 'Off' generates 2 bits.
                                                                                      : ... In instance ariane_testharness.i_ariane.i_cva6.csr_regfile_i
 1382 |             mstatus_d.mprv = riscv::Off;
      |                            ^
%Warning-WIDTHTRUNC: /home/cai/cache_project//sandbox/cva6/core/csr_regfile.sv:1773:20: Operator ASSIGN expects 1 bits on the Assign RHS, but Assign RHS's ENUMITEMREF 'Off' generates 2 bits.
                                                                                      : ... In instance ariane_testharness.i_ariane.i_cva6.csr_regfile_i
 1773 |       mstatus_d.sd = riscv::Off;
      |                    ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/ex_stage.sv:297:27: Selection index out of range: 1:1 outside 0:0
                                                                                : ... In instance ariane_testharness.i_ariane.i_cva6.ex_stage_i
  297 |       if (one_cycle_select[1]) begin
      |                           ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/ex_stage.sv:393:23: Selection index out of range: 1:1 outside 0:0
                                                                                : ... In instance ariane_testharness.i_ariane.i_cva6.ex_stage_i
  393 |       if (mult_valid_i[1]) begin
      |                       ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/ex_stage.sv:526:22: Selection index out of range: 1:1 outside 0:0
                                                                                : ... In instance ariane_testharness.i_ariane.i_cva6.ex_stage_i
  526 |       if (lsu_valid_i[1]) begin
      |                      ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/ex_stage.sv:617:22: Selection index out of range: 1:1 outside 0:0
                                                                                : ... In instance ariane_testharness.i_ariane.i_cva6.ex_stage_i
  617 |         if (x_valid_i[1]) begin
      |                      ^
%Warning-WIDTHCONCAT: /home/cai/cache_project//sandbox/cva6/core/frontend/frontend.sv:379:64: Unsized numbers/parameters not allowed in concatenations.
                                                                                            : ... In instance ariane_testharness.i_ariane.i_cva6.i_frontend
  379 |         fetch_address[CVA6Cfg.VLEN-1:CVA6Cfg.FETCH_ALIGN_BITS] + 1, {CVA6Cfg.FETCH_ALIGN_BITS{1'b0}}
      |                                                                ^
%Warning-WIDTHCONCAT: /home/cai/cache_project//sandbox/cva6/core/frontend/frontend.sv:379:67: Unsized numbers/parameters not allowed in replications.
                                                                                            : ... In instance ariane_testharness.i_ariane.i_cva6.i_frontend
  379 |         fetch_address[CVA6Cfg.VLEN-1:CVA6Cfg.FETCH_ALIGN_BITS] + 1, {CVA6Cfg.FETCH_ALIGN_BITS{1'b0}}
      |                                                                   ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:387:37: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 37 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  387 |             rvfi_csr_o.fflags.rdata <= {{CVA6Cfg.XLEN - $bits(csr.fcsr_q.fflags)}, csr.fcsr_q.fflags}; 
      |                                     ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:387:36: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 37 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  387 |     assign rvfi_csr_o.fflags.wdata = CVA6Cfg.FpPresent ? { {{CVA6Cfg.XLEN-$bits(csr.fcsr_q.fflags)}, csr.fcsr_q.fflags} } : 0; 
      |                                    ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:387:63: Operator NEQ expects 37 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  387 |     assign rvfi_csr_o.fflags.wmask = (rvfi_csr_o.fflags.rdata != {{CVA6Cfg.XLEN - $bits(csr.fcsr_q.fflags)}, csr.fcsr_q.fflags}) && CVA6Cfg.FpPresent;
      |                                                               ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:387:36: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  387 |     assign rvfi_csr_o.fflags.wmask = (rvfi_csr_o.fflags.rdata != {{CVA6Cfg.XLEN - $bits(csr.fcsr_q.fflags)}, csr.fcsr_q.fflags}) && CVA6Cfg.FpPresent;
      |                                    ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:388:34: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 35 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  388 |             rvfi_csr_o.frm.rdata <= {{CVA6Cfg.XLEN - $bits(csr.fcsr_q.frm)}, csr.fcsr_q.frm}; 
      |                                  ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:388:33: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 35 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  388 |     assign rvfi_csr_o.frm.wdata = CVA6Cfg.FpPresent ? { {{CVA6Cfg.XLEN-$bits(csr.fcsr_q.frm)}, csr.fcsr_q.frm} } : 0; 
      |                                 ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:388:57: Operator NEQ expects 35 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  388 |     assign rvfi_csr_o.frm.wmask = (rvfi_csr_o.frm.rdata != {{CVA6Cfg.XLEN - $bits(csr.fcsr_q.frm)}, csr.fcsr_q.frm}) && CVA6Cfg.FpPresent;
      |                                                         ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:388:33: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  388 |     assign rvfi_csr_o.frm.wmask = (rvfi_csr_o.frm.rdata != {{CVA6Cfg.XLEN - $bits(csr.fcsr_q.frm)}, csr.fcsr_q.frm}) && CVA6Cfg.FpPresent;
      |                                 ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:389:35: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 40 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  389 |             rvfi_csr_o.fcsr.rdata <= {{CVA6Cfg.XLEN - $bits({csr.fcsr_q.frm, csr.fcsr_q.fflags})}, {csr.fcsr_q.frm, csr.fcsr_q.fflags}}; 
      |                                   ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:389:34: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 40 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  389 |     assign rvfi_csr_o.fcsr.wdata = CVA6Cfg.FpPresent ? { {{CVA6Cfg.XLEN-$bits({csr.fcsr_q.frm, csr.fcsr_q.fflags})}, {csr.fcsr_q.frm, csr.fcsr_q.fflags}} } : 0; 
      |                                  ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:389:59: Operator NEQ expects 40 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  389 |     assign rvfi_csr_o.fcsr.wmask = (rvfi_csr_o.fcsr.rdata != {{CVA6Cfg.XLEN - $bits({csr.fcsr_q.frm, csr.fcsr_q.fflags})}, {csr.fcsr_q.frm, csr.fcsr_q.fflags}}) && CVA6Cfg.FpPresent;
      |                                                           ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:389:34: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  389 |     assign rvfi_csr_o.fcsr.wmask = (rvfi_csr_o.fcsr.rdata != {{CVA6Cfg.XLEN - $bits({csr.fcsr_q.frm, csr.fcsr_q.fflags})}, {csr.fcsr_q.frm, csr.fcsr_q.fflags}}) && CVA6Cfg.FpPresent;
      |                                  ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:391:36: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 39 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  391 |             rvfi_csr_o.ftran.rdata <= {{CVA6Cfg.XLEN - $bits(csr.fcsr_q.fprec)}, csr.fcsr_q.fprec}; 
      |                                    ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:391:35: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 39 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  391 |     assign rvfi_csr_o.ftran.wdata = CVA6Cfg.FpPresent ? { {{CVA6Cfg.XLEN-$bits(csr.fcsr_q.fprec)}, csr.fcsr_q.fprec} } : 0; 
      |                                   ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:391:61: Operator NEQ expects 39 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  391 |     assign rvfi_csr_o.ftran.wmask = (rvfi_csr_o.ftran.rdata != {{CVA6Cfg.XLEN - $bits(csr.fcsr_q.fprec)}, csr.fcsr_q.fprec}) && CVA6Cfg.FpPresent;
      |                                                             ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:391:35: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  391 |     assign rvfi_csr_o.ftran.wmask = (rvfi_csr_o.ftran.rdata != {{CVA6Cfg.XLEN - $bits(csr.fcsr_q.fprec)}, csr.fcsr_q.fprec}) && CVA6Cfg.FpPresent;
      |                                   ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:392:35: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  392 |             rvfi_csr_o.dcsr.rdata <= {{CVA6Cfg.XLEN - $bits(csr.dcsr_q)}, csr.dcsr_q}; 
      |                                   ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:392:34: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  392 |     assign rvfi_csr_o.dcsr.wdata = CVA6Cfg.FpPresent ? { {{CVA6Cfg.XLEN-$bits(csr.dcsr_q)}, csr.dcsr_q} } : 0; 
      |                                  ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:392:59: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  392 |     assign rvfi_csr_o.dcsr.wmask = (rvfi_csr_o.dcsr.rdata != {{CVA6Cfg.XLEN - $bits(csr.dcsr_q)}, csr.dcsr_q}) && CVA6Cfg.FpPresent;
      |                                                           ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:392:34: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  392 |     assign rvfi_csr_o.dcsr.wmask = (rvfi_csr_o.dcsr.rdata != {{CVA6Cfg.XLEN - $bits(csr.dcsr_q)}, csr.dcsr_q}) && CVA6Cfg.FpPresent;
      |                                  ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:394:34: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  394 |             rvfi_csr_o.dpc.rdata <= {{CVA6Cfg.XLEN - $bits(csr.dpc_q)}, csr.dpc_q}; 
      |                                  ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:394:33: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  394 |     assign rvfi_csr_o.dpc.wdata = CVA6Cfg.DebugEn ? { {{CVA6Cfg.XLEN-$bits(csr.dpc_q)}, csr.dpc_q} } : 0; 
      |                                 ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:394:57: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  394 |     assign rvfi_csr_o.dpc.wmask = (rvfi_csr_o.dpc.rdata != {{CVA6Cfg.XLEN - $bits(csr.dpc_q)}, csr.dpc_q}) && CVA6Cfg.DebugEn;
      |                                                         ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:394:33: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  394 |     assign rvfi_csr_o.dpc.wmask = (rvfi_csr_o.dpc.rdata != {{CVA6Cfg.XLEN - $bits(csr.dpc_q)}, csr.dpc_q}) && CVA6Cfg.DebugEn;
      |                                 ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:396:40: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  396 |             rvfi_csr_o.dscratch0.rdata <= {{CVA6Cfg.XLEN - $bits(csr.dscratch0_q)}, csr.dscratch0_q}; 
      |                                        ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:396:39: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  396 |     assign rvfi_csr_o.dscratch0.wdata = CVA6Cfg.DebugEn ? { {{CVA6Cfg.XLEN-$bits(csr.dscratch0_q)}, csr.dscratch0_q} } : 0; 
      |                                       ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:396:69: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  396 |     assign rvfi_csr_o.dscratch0.wmask = (rvfi_csr_o.dscratch0.rdata != {{CVA6Cfg.XLEN - $bits(csr.dscratch0_q)}, csr.dscratch0_q}) && CVA6Cfg.DebugEn;
      |                                                                     ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:396:39: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  396 |     assign rvfi_csr_o.dscratch0.wmask = (rvfi_csr_o.dscratch0.rdata != {{CVA6Cfg.XLEN - $bits(csr.dscratch0_q)}, csr.dscratch0_q}) && CVA6Cfg.DebugEn;
      |                                       ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:397:40: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  397 |             rvfi_csr_o.dscratch1.rdata <= {{CVA6Cfg.XLEN - $bits(csr.dscratch1_q)}, csr.dscratch1_q}; 
      |                                        ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:397:39: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  397 |     assign rvfi_csr_o.dscratch1.wdata = CVA6Cfg.DebugEn ? { {{CVA6Cfg.XLEN-$bits(csr.dscratch1_q)}, csr.dscratch1_q} } : 0; 
      |                                       ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:397:69: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  397 |     assign rvfi_csr_o.dscratch1.wmask = (rvfi_csr_o.dscratch1.rdata != {{CVA6Cfg.XLEN - $bits(csr.dscratch1_q)}, csr.dscratch1_q}) && CVA6Cfg.DebugEn;
      |                                                                     ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:397:39: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  397 |     assign rvfi_csr_o.dscratch1.wmask = (rvfi_csr_o.dscratch1.rdata != {{CVA6Cfg.XLEN - $bits(csr.dscratch1_q)}, csr.dscratch1_q}) && CVA6Cfg.DebugEn;
      |                                       ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:400:38: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  400 |             rvfi_csr_o.sstatus.rdata <= {{CVA6Cfg.XLEN - $bits(csr.mstatus_extended & SMODE_STATUS_READ_MASK[CVA6Cfg.XLEN-1:0])}, csr.mstatus_extended & SMODE_STATUS_READ_MASK[CVA6Cfg.XLEN-1:0]}; 
      |                                      ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:400:37: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  400 |     assign rvfi_csr_o.sstatus.wdata = CVA6Cfg.RVS ? { {{CVA6Cfg.XLEN-$bits(csr.mstatus_extended & SMODE_STATUS_READ_MASK[CVA6Cfg.XLEN-1:0])}, csr.mstatus_extended & SMODE_STATUS_READ_MASK[CVA6Cfg.XLEN-1:0]} } : 0; 
      |                                     ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:400:65: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  400 |     assign rvfi_csr_o.sstatus.wmask = (rvfi_csr_o.sstatus.rdata != {{CVA6Cfg.XLEN - $bits(csr.mstatus_extended & SMODE_STATUS_READ_MASK[CVA6Cfg.XLEN-1:0])}, csr.mstatus_extended & SMODE_STATUS_READ_MASK[CVA6Cfg.XLEN-1:0]}) && CVA6Cfg.RVS;
      |                                                                 ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:400:37: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  400 |     assign rvfi_csr_o.sstatus.wmask = (rvfi_csr_o.sstatus.rdata != {{CVA6Cfg.XLEN - $bits(csr.mstatus_extended & SMODE_STATUS_READ_MASK[CVA6Cfg.XLEN-1:0])}, csr.mstatus_extended & SMODE_STATUS_READ_MASK[CVA6Cfg.XLEN-1:0]}) && CVA6Cfg.RVS;
      |                                     ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:402:34: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  402 |             rvfi_csr_o.sie.rdata <= {{CVA6Cfg.XLEN - $bits(csr.mie_q & csr.mideleg_q)}, csr.mie_q & csr.mideleg_q}; 
      |                                  ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:402:33: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  402 |     assign rvfi_csr_o.sie.wdata = CVA6Cfg.RVS ? { {{CVA6Cfg.XLEN-$bits(csr.mie_q & csr.mideleg_q)}, csr.mie_q & csr.mideleg_q} } : 0; 
      |                                 ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:402:57: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  402 |     assign rvfi_csr_o.sie.wmask = (rvfi_csr_o.sie.rdata != {{CVA6Cfg.XLEN - $bits(csr.mie_q & csr.mideleg_q)}, csr.mie_q & csr.mideleg_q}) && CVA6Cfg.RVS;
      |                                                         ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:402:33: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  402 |     assign rvfi_csr_o.sie.wmask = (rvfi_csr_o.sie.rdata != {{CVA6Cfg.XLEN - $bits(csr.mie_q & csr.mideleg_q)}, csr.mie_q & csr.mideleg_q}) && CVA6Cfg.RVS;
      |                                 ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:403:34: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  403 |             rvfi_csr_o.sip.rdata <= {{CVA6Cfg.XLEN - $bits(csr.mip_q & csr.mideleg_q)}, csr.mip_q & csr.mideleg_q}; 
      |                                  ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:403:33: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  403 |     assign rvfi_csr_o.sip.wdata = CVA6Cfg.RVS ? { {{CVA6Cfg.XLEN-$bits(csr.mip_q & csr.mideleg_q)}, csr.mip_q & csr.mideleg_q} } : 0; 
      |                                 ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:403:57: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  403 |     assign rvfi_csr_o.sip.wmask = (rvfi_csr_o.sip.rdata != {{CVA6Cfg.XLEN - $bits(csr.mip_q & csr.mideleg_q)}, csr.mip_q & csr.mideleg_q}) && CVA6Cfg.RVS;
      |                                                         ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:403:33: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  403 |     assign rvfi_csr_o.sip.wmask = (rvfi_csr_o.sip.rdata != {{CVA6Cfg.XLEN - $bits(csr.mip_q & csr.mideleg_q)}, csr.mip_q & csr.mideleg_q}) && CVA6Cfg.RVS;
      |                                 ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:405:36: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  405 |             rvfi_csr_o.stvec.rdata <= {{CVA6Cfg.XLEN - $bits(csr.stvec_q)}, csr.stvec_q}; 
      |                                    ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:405:35: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  405 |     assign rvfi_csr_o.stvec.wdata = CVA6Cfg.RVS ? { {{CVA6Cfg.XLEN-$bits(csr.stvec_q)}, csr.stvec_q} } : 0; 
      |                                   ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:405:61: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  405 |     assign rvfi_csr_o.stvec.wmask = (rvfi_csr_o.stvec.rdata != {{CVA6Cfg.XLEN - $bits(csr.stvec_q)}, csr.stvec_q}) && CVA6Cfg.RVS;
      |                                                             ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:405:35: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  405 |     assign rvfi_csr_o.stvec.wmask = (rvfi_csr_o.stvec.rdata != {{CVA6Cfg.XLEN - $bits(csr.stvec_q)}, csr.stvec_q}) && CVA6Cfg.RVS;
      |                                   ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:407:41: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  407 |             rvfi_csr_o.scounteren.rdata <= {{CVA6Cfg.XLEN - $bits(csr.scounteren_q)}, csr.scounteren_q}; 
      |                                         ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:407:40: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  407 |     assign rvfi_csr_o.scounteren.wdata = CVA6Cfg.RVS ? { {{CVA6Cfg.XLEN-$bits(csr.scounteren_q)}, csr.scounteren_q} } : 0; 
      |                                        ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:407:71: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  407 |     assign rvfi_csr_o.scounteren.wmask = (rvfi_csr_o.scounteren.rdata != {{CVA6Cfg.XLEN - $bits(csr.scounteren_q)}, csr.scounteren_q}) && CVA6Cfg.RVS;
      |                                                                       ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:407:40: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  407 |     assign rvfi_csr_o.scounteren.wmask = (rvfi_csr_o.scounteren.rdata != {{CVA6Cfg.XLEN - $bits(csr.scounteren_q)}, csr.scounteren_q}) && CVA6Cfg.RVS;
      |                                        ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:409:39: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  409 |             rvfi_csr_o.sscratch.rdata <= {{CVA6Cfg.XLEN - $bits(csr.sscratch_q)}, csr.sscratch_q}; 
      |                                       ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:409:38: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  409 |     assign rvfi_csr_o.sscratch.wdata = CVA6Cfg.RVS ? { {{CVA6Cfg.XLEN-$bits(csr.sscratch_q)}, csr.sscratch_q} } : 0; 
      |                                      ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:409:67: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  409 |     assign rvfi_csr_o.sscratch.wmask = (rvfi_csr_o.sscratch.rdata != {{CVA6Cfg.XLEN - $bits(csr.sscratch_q)}, csr.sscratch_q}) && CVA6Cfg.RVS;
      |                                                                   ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:409:38: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  409 |     assign rvfi_csr_o.sscratch.wmask = (rvfi_csr_o.sscratch.rdata != {{CVA6Cfg.XLEN - $bits(csr.sscratch_q)}, csr.sscratch_q}) && CVA6Cfg.RVS;
      |                                      ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:410:35: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  410 |             rvfi_csr_o.sepc.rdata <= {{CVA6Cfg.XLEN - $bits(csr.sepc_q)}, csr.sepc_q}; 
      |                                   ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:410:34: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  410 |     assign rvfi_csr_o.sepc.wdata = CVA6Cfg.RVS ? { {{CVA6Cfg.XLEN-$bits(csr.sepc_q)}, csr.sepc_q} } : 0; 
      |                                  ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:410:59: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  410 |     assign rvfi_csr_o.sepc.wmask = (rvfi_csr_o.sepc.rdata != {{CVA6Cfg.XLEN - $bits(csr.sepc_q)}, csr.sepc_q}) && CVA6Cfg.RVS;
      |                                                           ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:410:34: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  410 |     assign rvfi_csr_o.sepc.wmask = (rvfi_csr_o.sepc.rdata != {{CVA6Cfg.XLEN - $bits(csr.sepc_q)}, csr.sepc_q}) && CVA6Cfg.RVS;
      |                                  ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:412:37: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  412 |             rvfi_csr_o.scause.rdata <= {{CVA6Cfg.XLEN - $bits(csr.scause_q)}, csr.scause_q}; 
      |                                     ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:412:36: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  412 |     assign rvfi_csr_o.scause.wdata = CVA6Cfg.RVS ? { {{CVA6Cfg.XLEN-$bits(csr.scause_q)}, csr.scause_q} } : 0; 
      |                                    ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:412:63: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  412 |     assign rvfi_csr_o.scause.wmask = (rvfi_csr_o.scause.rdata != {{CVA6Cfg.XLEN - $bits(csr.scause_q)}, csr.scause_q}) && CVA6Cfg.RVS;
      |                                                               ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:412:36: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  412 |     assign rvfi_csr_o.scause.wmask = (rvfi_csr_o.scause.rdata != {{CVA6Cfg.XLEN - $bits(csr.scause_q)}, csr.scause_q}) && CVA6Cfg.RVS;
      |                                    ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:414:36: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  414 |             rvfi_csr_o.stval.rdata <= {{CVA6Cfg.XLEN - $bits(csr.stval_q)}, csr.stval_q}; 
      |                                    ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:414:35: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  414 |     assign rvfi_csr_o.stval.wdata = CVA6Cfg.RVS ? { {{CVA6Cfg.XLEN-$bits(csr.stval_q)}, csr.stval_q} } : 0; 
      |                                   ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:414:61: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  414 |     assign rvfi_csr_o.stval.wmask = (rvfi_csr_o.stval.rdata != {{CVA6Cfg.XLEN - $bits(csr.stval_q)}, csr.stval_q}) && CVA6Cfg.RVS;
      |                                                             ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:414:35: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  414 |     assign rvfi_csr_o.stval.wmask = (rvfi_csr_o.stval.rdata != {{CVA6Cfg.XLEN - $bits(csr.stval_q)}, csr.stval_q}) && CVA6Cfg.RVS;
      |                                   ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:415:35: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  415 |             rvfi_csr_o.satp.rdata <= {{CVA6Cfg.XLEN - $bits(csr.satp_q)}, csr.satp_q}; 
      |                                   ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:415:34: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  415 |     assign rvfi_csr_o.satp.wdata = CVA6Cfg.RVS ? { {{CVA6Cfg.XLEN-$bits(csr.satp_q)}, csr.satp_q} } : 0; 
      |                                  ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:415:59: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  415 |     assign rvfi_csr_o.satp.wmask = (rvfi_csr_o.satp.rdata != {{CVA6Cfg.XLEN - $bits(csr.satp_q)}, csr.satp_q}) && CVA6Cfg.RVS;
      |                                                           ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:415:34: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  415 |     assign rvfi_csr_o.satp.wmask = (rvfi_csr_o.satp.rdata != {{CVA6Cfg.XLEN - $bits(csr.satp_q)}, csr.satp_q}) && CVA6Cfg.RVS;
      |                                  ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:417:38: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  417 |             rvfi_csr_o.mstatus.rdata <= {{CVA6Cfg.XLEN - $bits(csr.mstatus_extended)}, csr.mstatus_extended}; 
      |                                      ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:417:37: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  417 |     assign rvfi_csr_o.mstatus.wdata = 1'b1 ? { {{CVA6Cfg.XLEN-$bits(csr.mstatus_extended)}, csr.mstatus_extended} } : 0; 
      |                                     ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:417:65: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  417 |     assign rvfi_csr_o.mstatus.wmask = (rvfi_csr_o.mstatus.rdata != {{CVA6Cfg.XLEN - $bits(csr.mstatus_extended)}, csr.mstatus_extended}) && 1'b1;
      |                                                                 ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:417:37: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  417 |     assign rvfi_csr_o.mstatus.wmask = (rvfi_csr_o.mstatus.rdata != {{CVA6Cfg.XLEN - $bits(csr.mstatus_extended)}, csr.mstatus_extended}) && 1'b1;
      |                                     ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:420:39: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  420 |             rvfi_csr_o.mstatush.rdata <= {{CVA6Cfg.XLEN - $bits(mstatush_q)}, mstatush_q}; 
      |                                       ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:420:38: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  420 |     assign rvfi_csr_o.mstatush.wdata = 1'b1 ? { {{CVA6Cfg.XLEN-$bits(mstatush_q)}, mstatush_q} } : 0; 
      |                                      ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:420:67: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  420 |     assign rvfi_csr_o.mstatush.wmask = (rvfi_csr_o.mstatush.rdata != {{CVA6Cfg.XLEN - $bits(mstatush_q)}, mstatush_q}) && 1'b1;
      |                                                                   ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:420:38: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  420 |     assign rvfi_csr_o.mstatush.wmask = (rvfi_csr_o.mstatush.rdata != {{CVA6Cfg.XLEN - $bits(mstatush_q)}, mstatush_q}) && 1'b1;
      |                                      ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:422:35: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  422 |             rvfi_csr_o.misa.rdata <= {{CVA6Cfg.XLEN - $bits(IsaCode)}, IsaCode}; 
      |                                   ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:422:34: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  422 |     assign rvfi_csr_o.misa.wdata = 1'b1 ? { {{CVA6Cfg.XLEN-$bits(IsaCode)}, IsaCode} } : 0; 
      |                                  ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:422:59: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  422 |     assign rvfi_csr_o.misa.wmask = (rvfi_csr_o.misa.rdata != {{CVA6Cfg.XLEN - $bits(IsaCode)}, IsaCode}) && 1'b1;
      |                                                           ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:422:34: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  422 |     assign rvfi_csr_o.misa.wmask = (rvfi_csr_o.misa.rdata != {{CVA6Cfg.XLEN - $bits(IsaCode)}, IsaCode}) && 1'b1;
      |                                  ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:424:38: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  424 |             rvfi_csr_o.medeleg.rdata <= {{CVA6Cfg.XLEN - $bits(csr.medeleg_q)}, csr.medeleg_q}; 
      |                                      ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:424:37: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  424 |     assign rvfi_csr_o.medeleg.wdata = CVA6Cfg.RVS ? { {{CVA6Cfg.XLEN-$bits(csr.medeleg_q)}, csr.medeleg_q} } : 0; 
      |                                     ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:424:65: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  424 |     assign rvfi_csr_o.medeleg.wmask = (rvfi_csr_o.medeleg.rdata != {{CVA6Cfg.XLEN - $bits(csr.medeleg_q)}, csr.medeleg_q}) && CVA6Cfg.RVS;
      |                                                                 ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:424:37: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  424 |     assign rvfi_csr_o.medeleg.wmask = (rvfi_csr_o.medeleg.rdata != {{CVA6Cfg.XLEN - $bits(csr.medeleg_q)}, csr.medeleg_q}) && CVA6Cfg.RVS;
      |                                     ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:425:38: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  425 |             rvfi_csr_o.mideleg.rdata <= {{CVA6Cfg.XLEN - $bits(csr.mideleg_q)}, csr.mideleg_q}; 
      |                                      ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:425:37: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  425 |     assign rvfi_csr_o.mideleg.wdata = CVA6Cfg.RVS ? { {{CVA6Cfg.XLEN-$bits(csr.mideleg_q)}, csr.mideleg_q} } : 0; 
      |                                     ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:425:65: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  425 |     assign rvfi_csr_o.mideleg.wmask = (rvfi_csr_o.mideleg.rdata != {{CVA6Cfg.XLEN - $bits(csr.mideleg_q)}, csr.mideleg_q}) && CVA6Cfg.RVS;
      |                                                                 ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:425:37: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  425 |     assign rvfi_csr_o.mideleg.wmask = (rvfi_csr_o.mideleg.rdata != {{CVA6Cfg.XLEN - $bits(csr.mideleg_q)}, csr.mideleg_q}) && CVA6Cfg.RVS;
      |                                     ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:427:34: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  427 |             rvfi_csr_o.mie.rdata <= {{CVA6Cfg.XLEN - $bits(csr.mie_q)}, csr.mie_q}; 
      |                                  ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:427:33: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  427 |     assign rvfi_csr_o.mie.wdata = 1'b1 ? { {{CVA6Cfg.XLEN-$bits(csr.mie_q)}, csr.mie_q} } : 0; 
      |                                 ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:427:57: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  427 |     assign rvfi_csr_o.mie.wmask = (rvfi_csr_o.mie.rdata != {{CVA6Cfg.XLEN - $bits(csr.mie_q)}, csr.mie_q}) && 1'b1;
      |                                                         ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:427:33: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  427 |     assign rvfi_csr_o.mie.wmask = (rvfi_csr_o.mie.rdata != {{CVA6Cfg.XLEN - $bits(csr.mie_q)}, csr.mie_q}) && 1'b1;
      |                                 ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:428:36: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  428 |             rvfi_csr_o.mtvec.rdata <= {{CVA6Cfg.XLEN - $bits(csr.mtvec_q)}, csr.mtvec_q}; 
      |                                    ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:428:35: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  428 |     assign rvfi_csr_o.mtvec.wdata = 1'b1 ? { {{CVA6Cfg.XLEN-$bits(csr.mtvec_q)}, csr.mtvec_q} } : 0; 
      |                                   ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:428:61: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  428 |     assign rvfi_csr_o.mtvec.wmask = (rvfi_csr_o.mtvec.rdata != {{CVA6Cfg.XLEN - $bits(csr.mtvec_q)}, csr.mtvec_q}) && 1'b1;
      |                                                             ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:428:35: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  428 |     assign rvfi_csr_o.mtvec.wmask = (rvfi_csr_o.mtvec.rdata != {{CVA6Cfg.XLEN - $bits(csr.mtvec_q)}, csr.mtvec_q}) && 1'b1;
      |                                   ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:429:41: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  429 |             rvfi_csr_o.mcounteren.rdata <= {{CVA6Cfg.XLEN - $bits(csr.mcounteren_q)}, csr.mcounteren_q}; 
      |                                         ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:429:40: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  429 |     assign rvfi_csr_o.mcounteren.wdata = 1'b1 ? { {{CVA6Cfg.XLEN-$bits(csr.mcounteren_q)}, csr.mcounteren_q} } : 0; 
      |                                        ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:429:71: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  429 |     assign rvfi_csr_o.mcounteren.wmask = (rvfi_csr_o.mcounteren.rdata != {{CVA6Cfg.XLEN - $bits(csr.mcounteren_q)}, csr.mcounteren_q}) && 1'b1;
      |                                                                       ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:429:40: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  429 |     assign rvfi_csr_o.mcounteren.wmask = (rvfi_csr_o.mcounteren.rdata != {{CVA6Cfg.XLEN - $bits(csr.mcounteren_q)}, csr.mcounteren_q}) && 1'b1;
      |                                        ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:431:39: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  431 |             rvfi_csr_o.mscratch.rdata <= {{CVA6Cfg.XLEN - $bits(csr.mscratch_q)}, csr.mscratch_q}; 
      |                                       ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:431:38: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  431 |     assign rvfi_csr_o.mscratch.wdata = 1'b1 ? { {{CVA6Cfg.XLEN-$bits(csr.mscratch_q)}, csr.mscratch_q} } : 0; 
      |                                      ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:431:67: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  431 |     assign rvfi_csr_o.mscratch.wmask = (rvfi_csr_o.mscratch.rdata != {{CVA6Cfg.XLEN - $bits(csr.mscratch_q)}, csr.mscratch_q}) && 1'b1;
      |                                                                   ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:431:38: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  431 |     assign rvfi_csr_o.mscratch.wmask = (rvfi_csr_o.mscratch.rdata != {{CVA6Cfg.XLEN - $bits(csr.mscratch_q)}, csr.mscratch_q}) && 1'b1;
      |                                      ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:433:35: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  433 |             rvfi_csr_o.mepc.rdata <= {{CVA6Cfg.XLEN - $bits(csr.mepc_q)}, csr.mepc_q}; 
      |                                   ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:433:34: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  433 |     assign rvfi_csr_o.mepc.wdata = 1'b1 ? { {{CVA6Cfg.XLEN-$bits(csr.mepc_q)}, csr.mepc_q} } : 0; 
      |                                  ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:433:59: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  433 |     assign rvfi_csr_o.mepc.wmask = (rvfi_csr_o.mepc.rdata != {{CVA6Cfg.XLEN - $bits(csr.mepc_q)}, csr.mepc_q}) && 1'b1;
      |                                                           ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:433:34: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  433 |     assign rvfi_csr_o.mepc.wmask = (rvfi_csr_o.mepc.rdata != {{CVA6Cfg.XLEN - $bits(csr.mepc_q)}, csr.mepc_q}) && 1'b1;
      |                                  ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:434:37: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  434 |             rvfi_csr_o.mcause.rdata <= {{CVA6Cfg.XLEN - $bits(csr.mcause_q)}, csr.mcause_q}; 
      |                                     ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:434:36: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  434 |     assign rvfi_csr_o.mcause.wdata = 1'b1 ? { {{CVA6Cfg.XLEN-$bits(csr.mcause_q)}, csr.mcause_q} } : 0; 
      |                                    ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:434:63: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  434 |     assign rvfi_csr_o.mcause.wmask = (rvfi_csr_o.mcause.rdata != {{CVA6Cfg.XLEN - $bits(csr.mcause_q)}, csr.mcause_q}) && 1'b1;
      |                                                               ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:434:36: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  434 |     assign rvfi_csr_o.mcause.wmask = (rvfi_csr_o.mcause.rdata != {{CVA6Cfg.XLEN - $bits(csr.mcause_q)}, csr.mcause_q}) && 1'b1;
      |                                    ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:435:36: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  435 |             rvfi_csr_o.mtval.rdata <= {{CVA6Cfg.XLEN - $bits(csr.mtval_q)}, csr.mtval_q}; 
      |                                    ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:435:35: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  435 |     assign rvfi_csr_o.mtval.wdata = 1'b1 ? { {{CVA6Cfg.XLEN-$bits(csr.mtval_q)}, csr.mtval_q} } : 0; 
      |                                   ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:435:61: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  435 |     assign rvfi_csr_o.mtval.wmask = (rvfi_csr_o.mtval.rdata != {{CVA6Cfg.XLEN - $bits(csr.mtval_q)}, csr.mtval_q}) && 1'b1;
      |                                                             ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:435:35: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  435 |     assign rvfi_csr_o.mtval.wmask = (rvfi_csr_o.mtval.rdata != {{CVA6Cfg.XLEN - $bits(csr.mtval_q)}, csr.mtval_q}) && 1'b1;
      |                                   ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:436:34: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  436 |             rvfi_csr_o.mip.rdata <= {{CVA6Cfg.XLEN - $bits(csr.mip_q)}, csr.mip_q}; 
      |                                  ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:436:33: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  436 |     assign rvfi_csr_o.mip.wdata = 1'b1 ? { {{CVA6Cfg.XLEN-$bits(csr.mip_q)}, csr.mip_q} } : 0; 
      |                                 ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:436:57: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  436 |     assign rvfi_csr_o.mip.wmask = (rvfi_csr_o.mip.rdata != {{CVA6Cfg.XLEN - $bits(csr.mip_q)}, csr.mip_q}) && 1'b1;
      |                                                         ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:436:33: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  436 |     assign rvfi_csr_o.mip.wmask = (rvfi_csr_o.mip.rdata != {{CVA6Cfg.XLEN - $bits(csr.mip_q)}, csr.mip_q}) && 1'b1;
      |                                 ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:438:38: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 33 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  438 |             rvfi_csr_o.menvcfg.rdata <= {{CVA6Cfg.XLEN - $bits(csr.fiom_q)}, csr.fiom_q}; 
      |                                      ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:438:37: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 33 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  438 |     assign rvfi_csr_o.menvcfg.wdata = 1'b1 ? { {{CVA6Cfg.XLEN-$bits(csr.fiom_q)}, csr.fiom_q} } : 0; 
      |                                     ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:438:65: Operator NEQ expects 33 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  438 |     assign rvfi_csr_o.menvcfg.wmask = (rvfi_csr_o.menvcfg.rdata != {{CVA6Cfg.XLEN - $bits(csr.fiom_q)}, csr.fiom_q}) && 1'b1;
      |                                                                 ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:438:37: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  438 |     assign rvfi_csr_o.menvcfg.wmask = (rvfi_csr_o.menvcfg.rdata != {{CVA6Cfg.XLEN - $bits(csr.fiom_q)}, csr.fiom_q}) && 1'b1;
      |                                     ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:440:39: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  440 |             rvfi_csr_o.menvcfgh.rdata <= {{CVA6Cfg.XLEN - $bits(32'h0)}, 32'h0}; 
      |                                       ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:440:38: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  440 |     assign rvfi_csr_o.menvcfgh.wdata = CVA6Cfg.XLEN == 32 ? { {{CVA6Cfg.XLEN-$bits(32'h0)}, 32'h0} } : 0; 
      |                                      ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:440:67: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  440 |     assign rvfi_csr_o.menvcfgh.wmask = (rvfi_csr_o.menvcfgh.rdata != {{CVA6Cfg.XLEN - $bits(32'h0)}, 32'h0}) && CVA6Cfg.XLEN == 32;
      |                                                                   ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:440:38: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  440 |     assign rvfi_csr_o.menvcfgh.wmask = (rvfi_csr_o.menvcfgh.rdata != {{CVA6Cfg.XLEN - $bits(32'h0)}, 32'h0}) && CVA6Cfg.XLEN == 32;
      |                                      ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:442:40: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  442 |             rvfi_csr_o.mvendorid.rdata <= {{CVA6Cfg.XLEN - $bits(OPENHWGROUP_MVENDORID)}, OPENHWGROUP_MVENDORID}; 
      |                                        ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:442:39: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  442 |     assign rvfi_csr_o.mvendorid.wdata = 1'b1 ? { {{CVA6Cfg.XLEN-$bits(OPENHWGROUP_MVENDORID)}, OPENHWGROUP_MVENDORID} } : 0; 
      |                                       ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:442:69: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  442 |     assign rvfi_csr_o.mvendorid.wmask = (rvfi_csr_o.mvendorid.rdata != {{CVA6Cfg.XLEN - $bits(OPENHWGROUP_MVENDORID)}, OPENHWGROUP_MVENDORID}) && 1'b1;
      |                                                                     ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:442:39: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  442 |     assign rvfi_csr_o.mvendorid.wmask = (rvfi_csr_o.mvendorid.rdata != {{CVA6Cfg.XLEN - $bits(OPENHWGROUP_MVENDORID)}, OPENHWGROUP_MVENDORID}) && 1'b1;
      |                                       ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:443:38: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  443 |             rvfi_csr_o.marchid.rdata <= {{CVA6Cfg.XLEN - $bits(ARIANE_MARCHID)}, ARIANE_MARCHID}; 
      |                                      ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:443:37: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  443 |     assign rvfi_csr_o.marchid.wdata = 1'b1 ? { {{CVA6Cfg.XLEN-$bits(ARIANE_MARCHID)}, ARIANE_MARCHID} } : 0; 
      |                                     ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:443:65: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  443 |     assign rvfi_csr_o.marchid.wmask = (rvfi_csr_o.marchid.rdata != {{CVA6Cfg.XLEN - $bits(ARIANE_MARCHID)}, ARIANE_MARCHID}) && 1'b1;
      |                                                                 ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:443:37: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  443 |     assign rvfi_csr_o.marchid.wmask = (rvfi_csr_o.marchid.rdata != {{CVA6Cfg.XLEN - $bits(ARIANE_MARCHID)}, ARIANE_MARCHID}) && 1'b1;
      |                                     ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:444:38: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  444 |             rvfi_csr_o.mhartid.rdata <= {{CVA6Cfg.XLEN - $bits(hart_id_i)}, hart_id_i}; 
      |                                      ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:444:37: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  444 |     assign rvfi_csr_o.mhartid.wdata = 1'b1 ? { {{CVA6Cfg.XLEN-$bits(hart_id_i)}, hart_id_i} } : 0; 
      |                                     ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:444:65: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  444 |     assign rvfi_csr_o.mhartid.wmask = (rvfi_csr_o.mhartid.rdata != {{CVA6Cfg.XLEN - $bits(hart_id_i)}, hart_id_i}) && 1'b1;
      |                                                                 ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:444:37: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  444 |     assign rvfi_csr_o.mhartid.wmask = (rvfi_csr_o.mhartid.rdata != {{CVA6Cfg.XLEN - $bits(hart_id_i)}, hart_id_i}) && 1'b1;
      |                                     ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:446:44: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 41 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  446 |             rvfi_csr_o.mcountinhibit.rdata <= {{CVA6Cfg.XLEN - $bits(csr.mcountinhibit_q)}, csr.mcountinhibit_q}; 
      |                                            ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:446:43: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 41 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  446 |     assign rvfi_csr_o.mcountinhibit.wdata = 1'b1 ? { {{CVA6Cfg.XLEN-$bits(csr.mcountinhibit_q)}, csr.mcountinhibit_q} } : 0; 
      |                                           ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:446:77: Operator NEQ expects 41 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  446 |     assign rvfi_csr_o.mcountinhibit.wmask = (rvfi_csr_o.mcountinhibit.rdata != {{CVA6Cfg.XLEN - $bits(csr.mcountinhibit_q)}, csr.mcountinhibit_q}) && 1'b1;
      |                                                                             ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:446:43: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  446 |     assign rvfi_csr_o.mcountinhibit.wmask = (rvfi_csr_o.mcountinhibit.rdata != {{CVA6Cfg.XLEN - $bits(csr.mcountinhibit_q)}, csr.mcountinhibit_q}) && 1'b1;
      |                                           ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:448:37: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  448 |             rvfi_csr_o.mcycle.rdata <= {{CVA6Cfg.XLEN - $bits(csr.cycle_q[CVA6Cfg.XLEN-1:0])}, csr.cycle_q[CVA6Cfg.XLEN-1:0]}; 
      |                                     ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:448:36: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  448 |     assign rvfi_csr_o.mcycle.wdata = 1'b1 ? { {{CVA6Cfg.XLEN-$bits(csr.cycle_q[CVA6Cfg.XLEN-1:0])}, csr.cycle_q[CVA6Cfg.XLEN-1:0]} } : 0; 
      |                                    ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:448:63: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  448 |     assign rvfi_csr_o.mcycle.wmask = (rvfi_csr_o.mcycle.rdata != {{CVA6Cfg.XLEN - $bits(csr.cycle_q[CVA6Cfg.XLEN-1:0])}, csr.cycle_q[CVA6Cfg.XLEN-1:0]}) && 1'b1;
      |                                                               ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:448:36: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  448 |     assign rvfi_csr_o.mcycle.wmask = (rvfi_csr_o.mcycle.rdata != {{CVA6Cfg.XLEN - $bits(csr.cycle_q[CVA6Cfg.XLEN-1:0])}, csr.cycle_q[CVA6Cfg.XLEN-1:0]}) && 1'b1;
      |                                    ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:449:38: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  449 |             rvfi_csr_o.mcycleh.rdata <= {{CVA6Cfg.XLEN - $bits(csr.cycle_q[63:32])}, csr.cycle_q[63:32]}; 
      |                                      ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:449:37: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  449 |     assign rvfi_csr_o.mcycleh.wdata = CVA6Cfg.XLEN == 32 ? { {{CVA6Cfg.XLEN-$bits(csr.cycle_q[63:32])}, csr.cycle_q[63:32]} } : 0; 
      |                                     ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:449:65: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  449 |     assign rvfi_csr_o.mcycleh.wmask = (rvfi_csr_o.mcycleh.rdata != {{CVA6Cfg.XLEN - $bits(csr.cycle_q[63:32])}, csr.cycle_q[63:32]}) && CVA6Cfg.XLEN == 32;
      |                                                                 ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:449:37: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  449 |     assign rvfi_csr_o.mcycleh.wmask = (rvfi_csr_o.mcycleh.rdata != {{CVA6Cfg.XLEN - $bits(csr.cycle_q[63:32])}, csr.cycle_q[63:32]}) && CVA6Cfg.XLEN == 32;
      |                                     ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:451:39: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  451 |             rvfi_csr_o.minstret.rdata <= {{CVA6Cfg.XLEN - $bits(csr.instret_q[CVA6Cfg.XLEN-1:0])}, csr.instret_q[CVA6Cfg.XLEN-1:0]}; 
      |                                       ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:451:38: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  451 |     assign rvfi_csr_o.minstret.wdata = 1'b1 ? { {{CVA6Cfg.XLEN-$bits(csr.instret_q[CVA6Cfg.XLEN-1:0])}, csr.instret_q[CVA6Cfg.XLEN-1:0]} } : 0; 
      |                                      ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:451:67: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  451 |     assign rvfi_csr_o.minstret.wmask = (rvfi_csr_o.minstret.rdata != {{CVA6Cfg.XLEN - $bits(csr.instret_q[CVA6Cfg.XLEN-1:0])}, csr.instret_q[CVA6Cfg.XLEN-1:0]}) && 1'b1;
      |                                                                   ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:451:38: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  451 |     assign rvfi_csr_o.minstret.wmask = (rvfi_csr_o.minstret.rdata != {{CVA6Cfg.XLEN - $bits(csr.instret_q[CVA6Cfg.XLEN-1:0])}, csr.instret_q[CVA6Cfg.XLEN-1:0]}) && 1'b1;
      |                                      ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:452:40: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  452 |             rvfi_csr_o.minstreth.rdata <= {{CVA6Cfg.XLEN - $bits(csr.instret_q[63:32])}, csr.instret_q[63:32]}; 
      |                                        ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:452:39: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  452 |     assign rvfi_csr_o.minstreth.wdata = CVA6Cfg.XLEN == 32 ? { {{CVA6Cfg.XLEN-$bits(csr.instret_q[63:32])}, csr.instret_q[63:32]} } : 0; 
      |                                       ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:452:69: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  452 |     assign rvfi_csr_o.minstreth.wmask = (rvfi_csr_o.minstreth.rdata != {{CVA6Cfg.XLEN - $bits(csr.instret_q[63:32])}, csr.instret_q[63:32]}) && CVA6Cfg.XLEN == 32;
      |                                                                     ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:452:39: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  452 |     assign rvfi_csr_o.minstreth.wmask = (rvfi_csr_o.minstreth.rdata != {{CVA6Cfg.XLEN - $bits(csr.instret_q[63:32])}, csr.instret_q[63:32]}) && CVA6Cfg.XLEN == 32;
      |                                       ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:454:36: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  454 |             rvfi_csr_o.cycle.rdata <= {{CVA6Cfg.XLEN - $bits(csr.cycle_q[CVA6Cfg.XLEN-1:0])}, csr.cycle_q[CVA6Cfg.XLEN-1:0]}; 
      |                                    ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:454:35: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  454 |     assign rvfi_csr_o.cycle.wdata = 1'b1 ? { {{CVA6Cfg.XLEN-$bits(csr.cycle_q[CVA6Cfg.XLEN-1:0])}, csr.cycle_q[CVA6Cfg.XLEN-1:0]} } : 0; 
      |                                   ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:454:61: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  454 |     assign rvfi_csr_o.cycle.wmask = (rvfi_csr_o.cycle.rdata != {{CVA6Cfg.XLEN - $bits(csr.cycle_q[CVA6Cfg.XLEN-1:0])}, csr.cycle_q[CVA6Cfg.XLEN-1:0]}) && 1'b1;
      |                                                             ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:454:35: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  454 |     assign rvfi_csr_o.cycle.wmask = (rvfi_csr_o.cycle.rdata != {{CVA6Cfg.XLEN - $bits(csr.cycle_q[CVA6Cfg.XLEN-1:0])}, csr.cycle_q[CVA6Cfg.XLEN-1:0]}) && 1'b1;
      |                                   ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:455:37: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  455 |             rvfi_csr_o.cycleh.rdata <= {{CVA6Cfg.XLEN - $bits(csr.cycle_q[63:32])}, csr.cycle_q[63:32]}; 
      |                                     ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:455:36: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  455 |     assign rvfi_csr_o.cycleh.wdata = CVA6Cfg.XLEN == 32 ? { {{CVA6Cfg.XLEN-$bits(csr.cycle_q[63:32])}, csr.cycle_q[63:32]} } : 0; 
      |                                    ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:455:63: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  455 |     assign rvfi_csr_o.cycleh.wmask = (rvfi_csr_o.cycleh.rdata != {{CVA6Cfg.XLEN - $bits(csr.cycle_q[63:32])}, csr.cycle_q[63:32]}) && CVA6Cfg.XLEN == 32;
      |                                                               ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:455:36: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  455 |     assign rvfi_csr_o.cycleh.wmask = (rvfi_csr_o.cycleh.rdata != {{CVA6Cfg.XLEN - $bits(csr.cycle_q[63:32])}, csr.cycle_q[63:32]}) && CVA6Cfg.XLEN == 32;
      |                                    ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:457:38: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  457 |             rvfi_csr_o.instret.rdata <= {{CVA6Cfg.XLEN - $bits(csr.instret_q[CVA6Cfg.XLEN-1:0])}, csr.instret_q[CVA6Cfg.XLEN-1:0]}; 
      |                                      ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:457:37: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  457 |     assign rvfi_csr_o.instret.wdata = 1'b1 ? { {{CVA6Cfg.XLEN-$bits(csr.instret_q[CVA6Cfg.XLEN-1:0])}, csr.instret_q[CVA6Cfg.XLEN-1:0]} } : 0; 
      |                                     ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:457:65: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  457 |     assign rvfi_csr_o.instret.wmask = (rvfi_csr_o.instret.rdata != {{CVA6Cfg.XLEN - $bits(csr.instret_q[CVA6Cfg.XLEN-1:0])}, csr.instret_q[CVA6Cfg.XLEN-1:0]}) && 1'b1;
      |                                                                 ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:457:37: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  457 |     assign rvfi_csr_o.instret.wmask = (rvfi_csr_o.instret.rdata != {{CVA6Cfg.XLEN - $bits(csr.instret_q[CVA6Cfg.XLEN-1:0])}, csr.instret_q[CVA6Cfg.XLEN-1:0]}) && 1'b1;
      |                                     ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:458:39: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  458 |             rvfi_csr_o.instreth.rdata <= {{CVA6Cfg.XLEN - $bits(csr.instret_q[63:32])}, csr.instret_q[63:32]}; 
      |                                       ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:458:38: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  458 |     assign rvfi_csr_o.instreth.wdata = CVA6Cfg.XLEN == 32 ? { {{CVA6Cfg.XLEN-$bits(csr.instret_q[63:32])}, csr.instret_q[63:32]} } : 0; 
      |                                      ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:458:67: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  458 |     assign rvfi_csr_o.instreth.wmask = (rvfi_csr_o.instreth.rdata != {{CVA6Cfg.XLEN - $bits(csr.instret_q[63:32])}, csr.instret_q[63:32]}) && CVA6Cfg.XLEN == 32;
      |                                                                   ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:458:38: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  458 |     assign rvfi_csr_o.instreth.wmask = (rvfi_csr_o.instreth.rdata != {{CVA6Cfg.XLEN - $bits(csr.instret_q[63:32])}, csr.instret_q[63:32]}) && CVA6Cfg.XLEN == 32;
      |                                      ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:460:37: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  460 |             rvfi_csr_o.dcache.rdata <= {{CVA6Cfg.XLEN - $bits(csr.dcache_q)}, csr.dcache_q}; 
      |                                     ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:460:36: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  460 |     assign rvfi_csr_o.dcache.wdata = 1'b1 ? { {{CVA6Cfg.XLEN-$bits(csr.dcache_q)}, csr.dcache_q} } : 0; 
      |                                    ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:460:63: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  460 |     assign rvfi_csr_o.dcache.wmask = (rvfi_csr_o.dcache.rdata != {{CVA6Cfg.XLEN - $bits(csr.dcache_q)}, csr.dcache_q}) && 1'b1;
      |                                                               ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:460:36: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  460 |     assign rvfi_csr_o.dcache.wmask = (rvfi_csr_o.dcache.rdata != {{CVA6Cfg.XLEN - $bits(csr.dcache_q)}, csr.dcache_q}) && 1'b1;
      |                                    ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:461:37: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  461 |             rvfi_csr_o.icache.rdata <= {{CVA6Cfg.XLEN - $bits(csr.icache_q)}, csr.icache_q}; 
      |                                     ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:461:36: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  461 |     assign rvfi_csr_o.icache.wdata = 1'b1 ? { {{CVA6Cfg.XLEN-$bits(csr.icache_q)}, csr.icache_q} } : 0; 
      |                                    ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:461:63: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  461 |     assign rvfi_csr_o.icache.wmask = (rvfi_csr_o.icache.rdata != {{CVA6Cfg.XLEN - $bits(csr.icache_q)}, csr.icache_q}) && 1'b1;
      |                                                               ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:461:36: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  461 |     assign rvfi_csr_o.icache.wmask = (rvfi_csr_o.icache.rdata != {{CVA6Cfg.XLEN - $bits(csr.icache_q)}, csr.icache_q}) && 1'b1;
      |                                    ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:463:39: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  463 |             rvfi_csr_o.acc_cons.rdata <= {{CVA6Cfg.XLEN - $bits(csr.acc_cons_q)}, csr.acc_cons_q}; 
      |                                       ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:463:38: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  463 |     assign rvfi_csr_o.acc_cons.wdata = CVA6Cfg.EnableAccelerator ? { {{CVA6Cfg.XLEN-$bits(csr.acc_cons_q)}, csr.acc_cons_q} } : 0; 
      |                                      ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:463:67: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  463 |     assign rvfi_csr_o.acc_cons.wmask = (rvfi_csr_o.acc_cons.rdata != {{CVA6Cfg.XLEN - $bits(csr.acc_cons_q)}, csr.acc_cons_q}) && CVA6Cfg.EnableAccelerator;
      |                                                                   ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:463:38: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  463 |     assign rvfi_csr_o.acc_cons.wmask = (rvfi_csr_o.acc_cons.rdata != {{CVA6Cfg.XLEN - $bits(csr.acc_cons_q)}, csr.acc_cons_q}) && CVA6Cfg.EnableAccelerator;
      |                                      ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:464:34: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  464 |             rvfi_csr_o.jvt.rdata <= {{CVA6Cfg.XLEN - $bits(csr.jvt_q)}, csr.jvt_q}; 
      |                                  ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:464:33: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  464 |     assign rvfi_csr_o.jvt.wdata = CVA6Cfg.RVZCMT ? { {{CVA6Cfg.XLEN-$bits(csr.jvt_q)}, csr.jvt_q} } : 0; 
      |                                 ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:464:57: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  464 |     assign rvfi_csr_o.jvt.wmask = (rvfi_csr_o.jvt.rdata != {{CVA6Cfg.XLEN - $bits(csr.jvt_q)}, csr.jvt_q}) && CVA6Cfg.RVZCMT;
      |                                                         ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:464:33: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  464 |     assign rvfi_csr_o.jvt.wmask = (rvfi_csr_o.jvt.rdata != {{CVA6Cfg.XLEN - $bits(csr.jvt_q)}, csr.jvt_q}) && CVA6Cfg.RVZCMT;
      |                                 ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:465:38: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  465 |             rvfi_csr_o.pmpcfg0.rdata <= {{CVA6Cfg.XLEN - $bits(csr.pmpcfg_q[CVA6Cfg.XLEN/8-1:0])}, csr.pmpcfg_q[CVA6Cfg.XLEN/8-1:0]}; 
      |                                      ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:465:37: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  465 |     assign rvfi_csr_o.pmpcfg0.wdata = 1'b1 ? { {{CVA6Cfg.XLEN-$bits(csr.pmpcfg_q[CVA6Cfg.XLEN/8-1:0])}, csr.pmpcfg_q[CVA6Cfg.XLEN/8-1:0]} } : 0; 
      |                                     ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:465:65: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  465 |     assign rvfi_csr_o.pmpcfg0.wmask = (rvfi_csr_o.pmpcfg0.rdata != {{CVA6Cfg.XLEN - $bits(csr.pmpcfg_q[CVA6Cfg.XLEN/8-1:0])}, csr.pmpcfg_q[CVA6Cfg.XLEN/8-1:0]}) && 1'b1;
      |                                                                 ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:465:37: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  465 |     assign rvfi_csr_o.pmpcfg0.wmask = (rvfi_csr_o.pmpcfg0.rdata != {{CVA6Cfg.XLEN - $bits(csr.pmpcfg_q[CVA6Cfg.XLEN/8-1:0])}, csr.pmpcfg_q[CVA6Cfg.XLEN/8-1:0]}) && 1'b1;
      |                                     ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:466:38: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  466 |             rvfi_csr_o.pmpcfg1.rdata <= {{CVA6Cfg.XLEN - $bits(csr.pmpcfg_q[7:4])}, csr.pmpcfg_q[7:4]}; 
      |                                      ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:466:37: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  466 |     assign rvfi_csr_o.pmpcfg1.wdata = CVA6Cfg.XLEN == 32 ? { {{CVA6Cfg.XLEN-$bits(csr.pmpcfg_q[7:4])}, csr.pmpcfg_q[7:4]} } : 0; 
      |                                     ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:466:65: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  466 |     assign rvfi_csr_o.pmpcfg1.wmask = (rvfi_csr_o.pmpcfg1.rdata != {{CVA6Cfg.XLEN - $bits(csr.pmpcfg_q[7:4])}, csr.pmpcfg_q[7:4]}) && CVA6Cfg.XLEN == 32;
      |                                                                 ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:466:37: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  466 |     assign rvfi_csr_o.pmpcfg1.wmask = (rvfi_csr_o.pmpcfg1.rdata != {{CVA6Cfg.XLEN - $bits(csr.pmpcfg_q[7:4])}, csr.pmpcfg_q[7:4]}) && CVA6Cfg.XLEN == 32;
      |                                     ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:468:38: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  468 |             rvfi_csr_o.pmpcfg2.rdata <= {{CVA6Cfg.XLEN - $bits(csr.pmpcfg_q[8+:CVA6Cfg.XLEN/8])}, csr.pmpcfg_q[8+:CVA6Cfg.XLEN/8]}; 
      |                                      ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:468:37: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  468 |     assign rvfi_csr_o.pmpcfg2.wdata = 1'b1 ? { {{CVA6Cfg.XLEN-$bits(csr.pmpcfg_q[8+:CVA6Cfg.XLEN/8])}, csr.pmpcfg_q[8+:CVA6Cfg.XLEN/8]} } : 0; 
      |                                     ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:468:65: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  468 |     assign rvfi_csr_o.pmpcfg2.wmask = (rvfi_csr_o.pmpcfg2.rdata != {{CVA6Cfg.XLEN - $bits(csr.pmpcfg_q[8+:CVA6Cfg.XLEN/8])}, csr.pmpcfg_q[8+:CVA6Cfg.XLEN/8]}) && 1'b1;
      |                                                                 ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:468:37: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  468 |     assign rvfi_csr_o.pmpcfg2.wmask = (rvfi_csr_o.pmpcfg2.rdata != {{CVA6Cfg.XLEN - $bits(csr.pmpcfg_q[8+:CVA6Cfg.XLEN/8])}, csr.pmpcfg_q[8+:CVA6Cfg.XLEN/8]}) && 1'b1;
      |                                     ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:469:38: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  469 |             rvfi_csr_o.pmpcfg3.rdata <= {{CVA6Cfg.XLEN - $bits(csr.pmpcfg_q[15:12])}, csr.pmpcfg_q[15:12]}; 
      |                                      ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:469:37: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  469 |     assign rvfi_csr_o.pmpcfg3.wdata = CVA6Cfg.XLEN == 32 ? { {{CVA6Cfg.XLEN-$bits(csr.pmpcfg_q[15:12])}, csr.pmpcfg_q[15:12]} } : 0; 
      |                                     ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:469:65: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  469 |     assign rvfi_csr_o.pmpcfg3.wmask = (rvfi_csr_o.pmpcfg3.rdata != {{CVA6Cfg.XLEN - $bits(csr.pmpcfg_q[15:12])}, csr.pmpcfg_q[15:12]}) && CVA6Cfg.XLEN == 32;
      |                                                                 ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:469:37: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  469 |     assign rvfi_csr_o.pmpcfg3.wmask = (rvfi_csr_o.pmpcfg3.rdata != {{CVA6Cfg.XLEN - $bits(csr.pmpcfg_q[15:12])}, csr.pmpcfg_q[15:12]}) && CVA6Cfg.XLEN == 32;
      |                                     ^
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:476:41: Operator ASSIGNDLY expects 32 bits on the Assign RHS, but Assign RHS's REPLICATE generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  476 |             rvfi_csr_o.pmpaddr[i].rdata <= {{CVA6Cfg.XLEN - $bits({                         csr.pmpaddr_q[i][CVA6Cfg.PLEN-3:1], pmpcfg_q[i].addr_mode[1]})}, {                         csr.pmpaddr_q[i][CVA6Cfg.PLEN-3:1], pmpcfg_q[i].addr_mode[1]}}; 
      |                                         ^~
%Warning-WIDTHTRUNC: core/cva6_rvfi.sv:476:40: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's COND generates 64 bits.
                                             : ... In instance ariane_testharness.i_cva6_rvfi
  476 |     assign rvfi_csr_o.pmpaddr[i].wdata = 1'b1 ? { {{CVA6Cfg.XLEN-$bits({                         csr.pmpaddr_q[i][CVA6Cfg.PLEN-3:1], pmpcfg_q[i].addr_mode[1]})}, {                         csr.pmpaddr_q[i][CVA6Cfg.PLEN-3:1], pmpcfg_q[i].addr_mode[1]}} } : 0; 
      |                                        ^
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:476:71: Operator NEQ expects 64 bits on the LHS, but LHS's SEL generates 32 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  476 |     assign rvfi_csr_o.pmpaddr[i].wmask = (rvfi_csr_o.pmpaddr[i].rdata != {{CVA6Cfg.XLEN - $bits({                         csr.pmpaddr_q[i][CVA6Cfg.PLEN-3:1], pmpcfg_q[i].addr_mode[1]})}, {                         csr.pmpaddr_q[i][CVA6Cfg.PLEN-3:1], pmpcfg_q[i].addr_mode[1]}}) && 1'b1;
      |                                                                       ^~
%Warning-WIDTHEXPAND: core/cva6_rvfi.sv:476:40: Operator ASSIGNW expects 32 bits on the Assign RHS, but Assign RHS's LOGAND generates 1 bits.
                                              : ... In instance ariane_testharness.i_cva6_rvfi
  476 |     assign rvfi_csr_o.pmpaddr[i].wmask = (rvfi_csr_o.pmpaddr[i].rdata != {{CVA6Cfg.XLEN - $bits({                         csr.pmpaddr_q[i][CVA6Cfg.PLEN-3:1], pmpcfg_q[i].addr_mode[1]})}, {                         csr.pmpaddr_q[i][CVA6Cfg.PLEN-3:1], pmpcfg_q[i].addr_mode[1]}}) && 1'b1;
      |                                        ^
%Warning-WIDTHEXPAND: /home/cai/cache_project/sandbox/cva6/core/cva6_iti/iti.sv:147:35: Operator ASSIGN expects 9 bits on the Assign RHS, but Assign RHS's SEL generates 3 bits.
                                                                                      : ... In instance ariane_testharness.i_iti
  147 |         iti_to_encoder_o.itype[i] = itt_out[i].itype;
      |                                   ^
%Warning-WIDTHEXPAND: /home/cai/cache_project//sandbox/cva6/core/cvfpu/src/fpnew_pkg.sv:100:9: Operator ASSIGN expects 32 bits on the Assign RHS, but Assign RHS's ENUMITEMREF 'INT8' generates 2 bits.
                                                                                             : ... In instance ariane_testharness
  100 |         return INT8;
      |         ^~~~~~
%Warning-WIDTHEXPAND: /home/cai/cache_project//sandbox/cva6/core/cvfpu/src/fpnew_pkg.sv:305:25: Operator SUB expects 32 or 7 bits on the RHS, but RHS's VARREF 'fmt' generates 3 bits.
                                                                                              : ... In instance ariane_testharness
  305 |     return FP_ENCODINGS[fmt].exp_bits + FP_ENCODINGS[fmt].man_bits + 1;
      |                         ^~~
%Warning-WIDTHEXPAND: /home/cai/cache_project//sandbox/cva6/core/cvfpu/src/fpnew_pkg.sv:305:54: Operator SUB expects 32 or 7 bits on the RHS, but RHS's VARREF 'fmt' generates 3 bits.
                                                                                              : ... In instance ariane_testharness
  305 |     return FP_ENCODINGS[fmt].exp_bits + FP_ENCODINGS[fmt].man_bits + 1;
      |                                                      ^~~
%Warning-WIDTHEXPAND: /home/cai/cache_project//sandbox/cva6/core/cvfpu/src/fpnew_pkg.sv:328:25: Operator SUB expects 32 or 7 bits on the RHS, but RHS's VARREF 'fmt' generates 3 bits.
                                                                                              : ... In instance ariane_testharness
  328 |     return FP_ENCODINGS[fmt].exp_bits;
      |                         ^~~
%Warning-WIDTHEXPAND: /home/cai/cache_project//sandbox/cva6/core/cvfpu/src/fpnew_pkg.sv:333:25: Operator SUB expects 32 or 7 bits on the RHS, but RHS's VARREF 'fmt' generates 3 bits.
                                                                                              : ... In instance ariane_testharness
  333 |     return FP_ENCODINGS[fmt].man_bits;
      |                         ^~~
%Warning-WIDTHEXPAND: /home/cai/cache_project//sandbox/cva6/core/cvfpu/src/fpnew_pkg.sv:338:39: Operator SUB expects 32 or 7 bits on the RHS, but RHS's VARREF 'fmt' generates 3 bits.
                                                                                              : ... In instance ariane_testharness
  338 |     return unsigned'(2**(FP_ENCODINGS[fmt].exp_bits-1)-1);  
      |                                       ^~~
%Warning-UNSIGNED: /home/cai/cache_project//sandbox/cva6/core/pmp/src/pmp_data_if.sv:166:27: Comparison is constant due to unsigned arithmetic
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.ex_stage_i.lsu_i.i_pmp_data_if
  166 |         for (int i = 0; i < CVA6Cfg.NrPMPEntries; i++) begin
      |                           ^
%Warning-UNSIGNED: /home/cai/cache_project//sandbox/cva6/core/pmp/src/pmp_data_if.sv:182:27: Comparison is constant due to unsigned arithmetic
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.ex_stage_i.lsu_i.i_pmp_data_if
  182 |         for (int i = 0; i < CVA6Cfg.NrPMPEntries; i++) begin
      |                           ^
%Warning-CMPCONST: /home/cai/cache_project//sandbox/cva6/core/raw_checker.sv:53:41: Comparison is constant due to limited range
                                                                                  : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands.gen_raw_checks[0].i_rs1_last_raw
   53 |     assign same_rd_as_rs_before[i] = (i < issue_pointer_i) && same_rd_as_rs[i];
      |                                         ^
%Warning-CMPCONST: /home/cai/cache_project//sandbox/cva6/core/raw_checker.sv:54:40: Comparison is constant due to limited range
                                                                                  : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands.gen_raw_checks[0].i_rs1_last_raw
   54 |     assign same_rd_as_rs_after[i] = (i >= issue_pointer_i) && same_rd_as_rs[i];
      |                                        ^~
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:329:15: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  329 |       fus_busy[1] = fus_busy[0];
      |               ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:332:15: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  332 |       fus_busy[1].csr = 1'b1;
      |               ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:334:15: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  334 |       fus_busy[1].cvxif = 1'b1;
      |               ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:337:23: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  337 |         NONE: fus_busy[1].none = 1'b1;
      |                       ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:341:21: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  341 |             fus_busy[1].alu = 1'b1;
      |                     ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:342:21: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  342 |             fus_busy[1].ctrl_flow = 1'b1;
      |                     ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:343:21: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  343 |             fus_busy[1].csr = 1'b1;
      |                     ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:345:21: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  345 |             fus_busy[1].load = 1'b1;
      |                     ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:347:21: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  347 |             fus_busy[1].store = 1'b1;
      |                     ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:351:23: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  351 |               fus_busy[1].alu = 1'b1;
      |                       ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:352:23: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  352 |               fus_busy[1].ctrl_flow = 1'b1;
      |                       ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:353:23: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  353 |               fus_busy[1].csr = 1'b1;
      |                       ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:356:23: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  356 |               fus_busy[1] = '1;
      |                       ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:362:21: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  362 |             fus_busy[1].alu2 = 1'b1;
      |                     ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:365:21: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  365 |             fus_busy[1].fpu = 1'b1;
      |                     ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:366:21: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  366 |             fus_busy[1].fpu_vec = 1'b1;
      |                     ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:368:21: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  368 |             fus_busy[1].alu = 1'b1;
      |                     ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:369:21: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  369 |             fus_busy[1].ctrl_flow = 1'b1;
      |                     ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:370:21: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  370 |             fus_busy[1].csr = 1'b1;
      |                     ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:375:19: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  375 |           fus_busy[1] = '1;
      |                   ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:377:23: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  377 |         MULT: fus_busy[1].mult = 1'b1;
      |                       ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:379:19: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  379 |           fus_busy[1].fpu = 1'b1;
      |                   ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:380:19: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  380 |           fus_busy[1].fpu_vec = 1'b1;
      |                   ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:383:19: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  383 |           fus_busy[1].load  = 1'b1;
      |                   ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:384:19: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  384 |           fus_busy[1].store = 1'b1;
      |                   ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:589:25: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  589 |       if (!issue_instr_i[1].use_zimm && (!CVA6Cfg.FpPresent || (is_rs1_fpr(
      |                         ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:593:31: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  593 |           ))) && issue_instr_i[1].rs1 == issue_instr_i[0].rd && issue_instr_i[1].rs1 != '0) begin
      |                               ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:593:78: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  593 |           ))) && issue_instr_i[1].rs1 == issue_instr_i[0].rd && issue_instr_i[1].rs1 != '0) begin
      |                                                                              ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:601:31: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  601 |           ))) && issue_instr_i[1].rs2 == issue_instr_i[0].rd && issue_instr_i[1].rs2 != '0) begin
      |                               ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:601:78: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  601 |           ))) && issue_instr_i[1].rs2 == issue_instr_i[0].rd && issue_instr_i[1].rs2 != '0) begin
      |                                                                              ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:611:28: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  611 |               issue_instr_i[1].op == OFFLOAD && OPERANDS_PER_INSTR == 3 ?
      |                            ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:911:24: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  911 |           issue_instr_i[1].result[4:0], issue_instr_i[1].rs2[4:0], issue_instr_i[1].rs1[4:0]
      |                        ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:911:54: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  911 |           issue_instr_i[1].result[4:0], issue_instr_i[1].rs2[4:0], issue_instr_i[1].rs1[4:0]
      |                                                      ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:911:81: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  911 |           issue_instr_i[1].result[4:0], issue_instr_i[1].rs2[4:0], issue_instr_i[1].rs1[4:0]
      |                                                                                 ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:991:24: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  991 |       if (issue_instr_i[1].fu == CTRL_FLOW) begin
      |                        ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:992:46: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  992 |         pc_n                  = issue_instr_i[1].pc;
      |                                              ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:993:46: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  993 |         is_compressed_instr_n = issue_instr_i[1].is_compressed;
      |                                              ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:994:46: Selection index out of range: 1:1 outside 0:0
                                                                                           : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
  994 |         branch_predict_n      = issue_instr_i[1].bp;
      |                                              ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:1029:26: Selection index out of range: 1:1 outside 0:0
                                                                                            : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
 1029 |         if (issue_instr_i[1].fu == CTRL_FLOW) begin
      |                          ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:1030:49: Selection index out of range: 1:1 outside 0:0
                                                                                            : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
 1030 |           pc_o                  <= issue_instr_i[1].pc;
      |                                                 ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:1031:49: Selection index out of range: 1:1 outside 0:0
                                                                                            : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
 1031 |           is_compressed_instr_o <= issue_instr_i[1].is_compressed;
      |                                                 ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/issue_read_operands.sv:1032:49: Selection index out of range: 1:1 outside 0:0
                                                                                            : ... In instance ariane_testharness.i_ariane.i_cva6.issue_stage_i.i_issue_read_operands
 1032 |           branch_predict_o      <= issue_instr_i[1].bp;
      |                                                 ^
%Warning-UNSIGNED: /home/cai/cache_project//sandbox/cva6/core/csr_regfile.sv:1780:23: Comparison is constant due to unsigned arithmetic
                                                                                    : ... In instance ariane_testharness.i_ariane.i_cva6.csr_regfile_i
 1780 |     for (int i = 0; i < CVA6Cfg.NrPMPEntries; i++) pmpcfg_d[i].reserved = 2'b0;
      |                       ^
%Warning-UNSIGNED: /home/cai/cache_project//sandbox/cva6/core/csr_regfile.sv:2616:15: Comparison is constant due to unsigned arithmetic
                                                                                    : ... In instance ariane_testharness.i_ariane.i_cva6.csr_regfile_i
 2616 |         if (i < CVA6Cfg.NrPMPEntries) begin
      |               ^
%Warning-UNSIGNED: /home/cai/cache_project//sandbox/cva6/core/csr_regfile.sv:2706:13: Comparison is constant due to unsigned arithmetic
                                                                                    : ... In instance ariane_testharness.i_ariane.i_cva6.csr_regfile_i
 2706 |       if (i < CVA6Cfg.NrPMPEntries) begin
      |             ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/ex_stage.sv:298:35: Selection index out of range: 1:1 outside 0:0
                                                                                : ... In instance ariane_testharness.i_ariane.i_cva6.ex_stage_i
  298 |         one_cycle_data = fu_data_i[1];
      |                                   ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/ex_stage.sv:394:30: Selection index out of range: 1:1 outside 0:0
                                                                                : ... In instance ariane_testharness.i_ariane.i_cva6.ex_stage_i
  394 |         mult_data = fu_data_i[1];
      |                              ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/ex_stage.sv:527:30: Selection index out of range: 1:1 outside 0:0
                                                                                : ... In instance ariane_testharness.i_ariane.i_cva6.ex_stage_i
  527 |         lsu_data  = fu_data_i[1];
      |                              ^
%Warning-SELRANGE: /home/cai/cache_project//sandbox/cva6/core/ex_stage.sv:618:33: Selection index out of range: 1:1 outside 0:0
                                                                                : ... In instance ariane_testharness.i_ariane.i_cva6.ex_stage_i
  618 |           cvxif_data = fu_data_i[1];
      |                                 ^
%Warning-IGNOREDRETURN: /home/cai/cache_project/sandbox/cva6/corev_apu/tb/rvfi_tracer.sv:59:13: Ignoring return value of non-void function (IEEE 1800-2017 13.4.1)
   59 |             read_symbol("tohost", TOHOST_ADDR);
      |             ^~~~~~~~~~~
%Warning-SYMRSVDWORD: /home/cai/cache_project/sandbox/cva6/corev_apu/src/ariane.sv:37:24: Symbol matches C++ keyword: 'register'
   37 |     x_register_t       register; 
      |                        ^~~~~~~~
%Warning-LATCH: /home/cai/cache_project//sandbox/cva6/core/cva6_fifo_v3.sv:75:3: Latch inferred for signal 'ariane_testharness.i_ariane.i_cva6.i_frontend.i_instr_queue.i_fifo_address.data_ft_n' (not all control paths of combinational always assign a value)
                                                                               : ... Suggest use of always_latch for intentional latches
   75 |   always_comb begin : read_write_comb
      |   ^~~~~~~~~~~
%Warning-LATCH: /home/cai/cache_project//sandbox/cva6/core/cva6_fifo_v3.sv:75:3: Latch inferred for signal 'ariane_testharness.i_ariane.i_cva6.i_frontend.i_instr_queue.i_fifo_address.fifo_ram_read_address' (not all control paths of combinational always assign a value)
                                                                               : ... Suggest use of always_latch for intentional latches
   75 |   always_comb begin : read_write_comb
      |   ^~~~~~~~~~~
%Warning-LATCH: /home/cai/cache_project//sandbox/cva6/core/cva6_fifo_v3.sv:75:3: Latch inferred for signal 'ariane_testharness.i_ariane.i_cva6.i_frontend.i_instr_queue.gen_instr_fifo[0].i_fifo_instr_data.data_ft_n' (not all control paths of combinational always assign a value)
                                                                               : ... Suggest use of always_latch for intentional latches
   75 |   always_comb begin : read_write_comb
      |   ^~~~~~~~~~~
%Warning-LATCH: /home/cai/cache_project//sandbox/cva6/core/cva6_fifo_v3.sv:75:3: Latch inferred for signal 'ariane_testharness.i_ariane.i_cva6.i_frontend.i_instr_queue.gen_instr_fifo[0].i_fifo_instr_data.fifo_ram_read_address' (not all control paths of combinational always assign a value)
                                                                               : ... Suggest use of always_latch for intentional latches
   75 |   always_comb begin : read_write_comb
      |   ^~~~~~~~~~~
%Warning-LATCH: /home/cai/cache_project//sandbox/cva6/core/cva6_fifo_v3.sv:75:3: Latch inferred for signal 'ariane_testharness.i_ariane.i_cva6.i_frontend.i_instr_queue.gen_instr_fifo[1].i_fifo_instr_data.data_ft_n' (not all control paths of combinational always assign a value)
                                                                               : ... Suggest use of always_latch for intentional latches
   75 |   always_comb begin : read_write_comb
      |   ^~~~~~~~~~~
%Warning-LATCH: /home/cai/cache_project//sandbox/cva6/core/cva6_fifo_v3.sv:75:3: Latch inferred for signal 'ariane_testharness.i_ariane.i_cva6.i_frontend.i_instr_queue.gen_instr_fifo[1].i_fifo_instr_data.fifo_ram_read_address' (not all control paths of combinational always assign a value)
                                                                               : ... Suggest use of always_latch for intentional latches
   75 |   always_comb begin : read_write_comb
      |   ^~~~~~~~~~~
%Warning-LATCH: /home/cai/cache_project//sandbox/cva6/core/csr_regfile.sv:327:3: Latch inferred for signal 'ariane_testharness.i_ariane.i_cva6.csr_regfile_i.csr_read_process.unnamedblk2.index' (not all control paths of combinational always assign a value)
                                                                               : ... Suggest use of always_latch for intentional latches
  327 |   always_comb begin : csr_read_process
      |   ^~~~~~~~~~~
%Warning-LATCH: /home/cai/cache_project//sandbox/cva6/core/csr_regfile.sv:327:3: Latch inferred for signal 'ariane_testharness.i_ariane.i_cva6.csr_regfile_i.csr_read_process.unnamedblk1.index' (not all control paths of combinational always assign a value)
                                                                               : ... Suggest use of always_latch for intentional latches
  327 |   always_comb begin : csr_read_process
      |   ^~~~~~~~~~~
%Warning-LATCH: /home/cai/cache_project//sandbox/cva6/core/csr_regfile.sv:880:3: Latch inferred for signal 'ariane_testharness.i_ariane.i_cva6.csr_regfile_i.csr_update.unnamedblk7.index' (not all control paths of combinational always assign a value)
                                                                               : ... Suggest use of always_latch for intentional latches
  880 |   always_comb begin : csr_update
      |   ^~~~~~~~~~~
%Warning-LATCH: /home/cai/cache_project//sandbox/cva6/core/csr_regfile.sv:880:3: Latch inferred for signal 'ariane_testharness.i_ariane.i_cva6.csr_regfile_i.csr_update.unnamedblk5.index' (not all control paths of combinational always assign a value)
                                                                               : ... Suggest use of always_latch for intentional latches
  880 |   always_comb begin : csr_update
      |   ^~~~~~~~~~~
%Warning-LATCH: /home/cai/cache_project//sandbox/cva6/core/csr_regfile.sv:880:3: Latch inferred for signal 'ariane_testharness.i_ariane.i_cva6.csr_regfile_i.mask' (not all control paths of combinational always assign a value)
                                                                               : ... Suggest use of always_latch for intentional latches
  880 |   always_comb begin : csr_update
      |   ^~~~~~~~~~~
%Warning-LATCH: /home/cai/cache_project//sandbox/cva6/core/csr_regfile.sv:880:3: Latch inferred for signal 'ariane_testharness.i_ariane.i_cva6.csr_regfile_i.csr_update.unnamedblk4.DirVecOnly' (not all control paths of combinational always assign a value)
                                                                               : ... Suggest use of always_latch for intentional latches
  880 |   always_comb begin : csr_update
      |   ^~~~~~~~~~~
%Warning-LATCH: /home/cai/cache_project//sandbox/cva6/core/csr_regfile.sv:880:3: Latch inferred for signal 'ariane_testharness.i_ariane.i_cva6.csr_regfile_i.trap_to_priv_lvl' (not all control paths of combinational always assign a value)
                                                                               : ... Suggest use of always_latch for intentional latches
  880 |   always_comb begin : csr_update
      |   ^~~~~~~~~~~
%Warning-LATCH: /home/cai/cache_project//sandbox/cva6/core/csr_regfile.sv:880:3: Latch inferred for signal 'ariane_testharness.i_ariane.i_cva6.csr_regfile_i.trap_to_v' (not all control paths of combinational always assign a value)
                                                                               : ... Suggest use of always_latch for intentional latches
  880 |   always_comb begin : csr_update
      |   ^~~~~~~~~~~
%Warning-LATCH: /home/cai/cache_project//sandbox/cva6/core/csr_regfile.sv:880:3: Latch inferred for signal 'ariane_testharness.i_ariane.i_cva6.csr_regfile_i.mtval_d' (not all control paths of combinational always assign a value)
                                                                               : ... Suggest use of always_latch for intentional latches
  880 |   always_comb begin : csr_update
      |   ^~~~~~~~~~~
%Warning-LATCH: /home/cai/cache_project//sandbox/cva6/core/csr_regfile.sv:880:3: Latch inferred for signal 'ariane_testharness.i_ariane.i_cva6.csr_regfile_i.en_ld_st_translation_d' (not all control paths of combinational always assign a value)
                                                                               : ... Suggest use of always_latch for intentional latches
  880 |   always_comb begin : csr_update
      |   ^~~~~~~~~~~
%Warning-LATCH: /home/cai/cache_project//sandbox/cva6/core/csr_regfile.sv:880:3: Latch inferred for signal 'ariane_testharness.i_ariane.i_cva6.ld_st_priv_lvl_csr_ex' (not all control paths of combinational always assign a value)
                                                                               : ... Suggest use of always_latch for intentional latches
  880 |   always_comb begin : csr_update
      |   ^~~~~~~~~~~
%Warning-LATCH: /home/cai/cache_project//sandbox/cva6/core/csr_regfile.sv:880:3: Latch inferred for signal 'ariane_testharness.i_ariane.i_cva6.en_ld_st_translation_csr_ex' (not all control paths of combinational always assign a value)
                                                                               : ... Suggest use of always_latch for intentional latches
  880 |   always_comb begin : csr_update
      |   ^~~~~~~~~~~
%Warning-LATCH: /home/cai/cache_project//sandbox/cva6/core/csr_regfile.sv:880:3: Latch inferred for signal 'ariane_testharness.i_ariane.i_cva6.ld_st_v_csr_ex' (not all control paths of combinational always assign a value)
                                                                               : ... Suggest use of always_latch for intentional latches
  880 |   always_comb begin : csr_update
      |   ^~~~~~~~~~~
%Warning-LATCH: /home/cai/cache_project//sandbox/cva6/core/csr_regfile.sv:880:3: Latch inferred for signal 'ariane_testharness.i_ariane.i_cva6.en_ld_st_g_translation_csr_ex' (not all control paths of combinational always assign a value)
                                                                               : ... Suggest use of always_latch for intentional latches
  880 |   always_comb begin : csr_update
      |   ^~~~~~~~~~~
%Warning-LATCH: /home/cai/cache_project//sandbox/cva6/core/cva6_fifo_v3.sv:75:3: Latch inferred for signal 'ariane_testharness.i_ariane.i_cva6.gen_cache_wt.i_cache_subsystem.i_wt_dcache.i_wt_dcache_wbuffer.i_rtrn_id_fifo.data_ft_n' (not all control paths of combinational always assign a value)
                                                                               : ... Suggest use of always_latch for intentional latches
   75 |   always_comb begin : read_write_comb
      |   ^~~~~~~~~~~
%Warning-LATCH: /home/cai/cache_project//sandbox/cva6/core/cva6_fifo_v3.sv:75:3: Latch inferred for signal 'ariane_testharness.i_ariane.i_cva6.gen_cache_wt.i_cache_subsystem.i_wt_dcache.i_wt_dcache_wbuffer.i_rtrn_id_fifo.fifo_ram_read_address' (not all control paths of combinational always assign a value)
                                                                               : ... Suggest use of always_latch for intentional latches
   75 |   always_comb begin : read_write_comb
      |   ^~~~~~~~~~~
%Warning-LATCH: /home/cai/cache_project//sandbox/cva6/core/cva6_fifo_v3.sv:75:3: Latch inferred for signal 'ariane_testharness.i_ariane.i_cva6.gen_cache_wt.i_cache_subsystem.i_adapter.i_icache_data_fifo.data_ft_n' (not all control paths of combinational always assign a value)
                                                                               : ... Suggest use of always_latch for intentional latches
   75 |   always_comb begin : read_write_comb
      |   ^~~~~~~~~~~
%Warning-LATCH: /home/cai/cache_project//sandbox/cva6/core/cva6_fifo_v3.sv:75:3: Latch inferred for signal 'ariane_testharness.i_ariane.i_cva6.gen_cache_wt.i_cache_subsystem.i_adapter.i_icache_data_fifo.fifo_ram_read_address' (not all control paths of combinational always assign a value)
                                                                               : ... Suggest use of always_latch for intentional latches
   75 |   always_comb begin : read_write_comb
      |   ^~~~~~~~~~~
%Warning-LATCH: /home/cai/cache_project//sandbox/cva6/core/cva6_fifo_v3.sv:75:3: Latch inferred for signal 'ariane_testharness.i_ariane.i_cva6.gen_cache_wt.i_cache_subsystem.i_adapter.i_dcache_data_fifo.data_ft_n' (not all control paths of combinational always assign a value)
                                                                               : ... Suggest use of always_latch for intentional latches
   75 |   always_comb begin : read_write_comb
      |   ^~~~~~~~~~~
%Warning-LATCH: /home/cai/cache_project//sandbox/cva6/core/cva6_fifo_v3.sv:75:3: Latch inferred for signal 'ariane_testharness.i_ariane.i_cva6.gen_cache_wt.i_cache_subsystem.i_adapter.i_dcache_data_fifo.fifo_ram_read_address' (not all control paths of combinational always assign a value)
                                                                               : ... Suggest use of always_latch for intentional latches
   75 |   always_comb begin : read_write_comb
      |   ^~~~~~~~~~~
%Warning-LATCH: /home/cai/cache_project//sandbox/cva6/core/cva6_fifo_v3.sv:75:3: Latch inferred for signal 'ariane_testharness.i_ariane.i_cva6.gen_cache_wt.i_cache_subsystem.i_adapter.i_rd_icache_id.data_ft_n' (not all control paths of combinational always assign a value)
                                                                               : ... Suggest use of always_latch for intentional latches
   75 |   always_comb begin : read_write_comb
      |   ^~~~~~~~~~~
%Warning-LATCH: /home/cai/cache_project//sandbox/cva6/core/cva6_fifo_v3.sv:75:3: Latch inferred for signal 'ariane_testharness.i_ariane.i_cva6.gen_cache_wt.i_cache_subsystem.i_adapter.i_rd_icache_id.fifo_ram_read_address' (not all control paths of combinational always assign a value)
                                                                               : ... Suggest use of always_latch for intentional latches
   75 |   always_comb begin : read_write_comb
      |   ^~~~~~~~~~~
%Warning-LATCH: /home/cai/cache_project//sandbox/cva6/core/cva6_fifo_v3.sv:75:3: Latch inferred for signal 'ariane_testharness.i_ariane.i_cva6.gen_cache_wt.i_cache_subsystem.i_adapter.i_rd_dcache_id.data_ft_n' (not all control paths of combinational always assign a value)
                                                                               : ... Suggest use of always_latch for intentional latches
   75 |   always_comb begin : read_write_comb
      |   ^~~~~~~~~~~
%Warning-LATCH: /home/cai/cache_project//sandbox/cva6/core/cva6_fifo_v3.sv:75:3: Latch inferred for signal 'ariane_testharness.i_ariane.i_cva6.gen_cache_wt.i_cache_subsystem.i_adapter.i_rd_dcache_id.fifo_ram_read_address' (not all control paths of combinational always assign a value)
                                                                               : ... Suggest use of always_latch for intentional latches
   75 |   always_comb begin : read_write_comb
      |   ^~~~~~~~~~~
%Warning-LATCH: /home/cai/cache_project//sandbox/cva6/core/cva6_fifo_v3.sv:75:3: Latch inferred for signal 'ariane_testharness.i_ariane.i_cva6.gen_cache_wt.i_cache_subsystem.i_adapter.i_wr_dcache_id.data_ft_n' (not all control paths of combinational always assign a value)
                                                                               : ... Suggest use of always_latch for intentional latches
   75 |   always_comb begin : read_write_comb
      |   ^~~~~~~~~~~
%Warning-LATCH: /home/cai/cache_project//sandbox/cva6/core/cva6_fifo_v3.sv:75:3: Latch inferred for signal 'ariane_testharness.i_ariane.i_cva6.gen_cache_wt.i_cache_subsystem.i_adapter.i_wr_dcache_id.fifo_ram_read_address' (not all control paths of combinational always assign a value)
                                                                               : ... Suggest use of always_latch for intentional latches
   75 |   always_comb begin : read_write_comb
      |   ^~~~~~~~~~~
%Warning-LATCH: /home/cai/cache_project//sandbox/cva6/core/cva6_fifo_v3.sv:75:3: Latch inferred for signal 'ariane_testharness.i_ariane.i_cva6.gen_cache_wt.i_cache_subsystem.i_adapter.i_b_fifo.data_ft_n' (not all control paths of combinational always assign a value)
                                                                               : ... Suggest use of always_latch for intentional latches
   75 |   always_comb begin : read_write_comb
      |   ^~~~~~~~~~~
%Warning-LATCH: /home/cai/cache_project//sandbox/cva6/core/cva6_fifo_v3.sv:75:3: Latch inferred for signal 'ariane_testharness.i_ariane.i_cva6.gen_cache_wt.i_cache_subsystem.i_adapter.i_b_fifo.first_word_n' (not all control paths of combinational always assign a value)
                                                                               : ... Suggest use of always_latch for intentional latches
   75 |   always_comb begin : read_write_comb
      |   ^~~~~~~~~~~
%Warning-LATCH: /home/cai/cache_project//sandbox/cva6/core/cva6_fifo_v3.sv:75:3: Latch inferred for signal 'ariane_testharness.i_ariane.i_cva6.gen_cache_wt.i_cache_subsystem.i_adapter.i_b_fifo.fifo_ram_read_address' (not all control paths of combinational always assign a value)
                                                                               : ... Suggest use of always_latch for intentional latches
   75 |   always_comb begin : read_write_comb
      |   ^~~~~~~~~~~
%Warning-LATCH: /home/cai/cache_project/sandbox/cva6/core/cva6_iti/iti.sv:126:3: Latch inferred for signal 'ariane_testharness.i_iti.valid_o' (not all control paths of combinational always assign a value)
                                                                               : ... Suggest use of always_latch for intentional latches
  126 |   always_comb begin
      |   ^~~~~~~~~~~
cd work-ver && make -j12 -f Variane_testharness.mk
make[2]: Entering directory '/home/cai/cache_project/sandbox/cva6/work-ver'
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike   -Os -c -o ariane_tb.o ../corev_apu/tb/ariane_tb.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike   -Os -c -o verilated.o /home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/verilated.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike   -Os -c -o verilated_dpi.o /home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/verilated_dpi.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike   -Os -c -o verilated_vpi.o /home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/verilated_vpi.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike   -Os -c -o verilated_threads.o /home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/verilated_threads.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike   -Os -c -o Variane_testharness.o Variane_testharness.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike   -Os -c -o Variane_testharness___024root__DepSet_h5fbfe5da__0.o Variane_testharness___024root__DepSet_h5fbfe5da__0.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike   -Os -c -o Variane_testharness___024root__DepSet_h5fbfe5da__1.o Variane_testharness___024root__DepSet_h5fbfe5da__1.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike   -Os -c -o Variane_testharness___024root__DepSet_h5fbfe5da__2.o Variane_testharness___024root__DepSet_h5fbfe5da__2.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike   -Os -c -o Variane_testharness___024root__DepSet_h5fbfe5da__3.o Variane_testharness___024root__DepSet_h5fbfe5da__3.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike   -Os -c -o Variane_testharness___024root__DepSet_h40fa4a98__0.o Variane_testharness___024root__DepSet_h40fa4a98__0.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike   -Os -c -o Variane_testharness___024root__DepSet_h40fa4a98__1.o Variane_testharness___024root__DepSet_h40fa4a98__1.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike   -Os -c -o Variane_testharness___024root__DepSet_h40fa4a98__2.o Variane_testharness___024root__DepSet_h40fa4a98__2.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike   -Os -c -o Variane_testharness___024root__DepSet_h40fa4a98__3.o Variane_testharness___024root__DepSet_h40fa4a98__3.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike   -Os -c -o Variane_testharness___024root__DepSet_h40fa4a98__4.o Variane_testharness___024root__DepSet_h40fa4a98__4.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike   -Os -c -o Variane_testharness___024root__DepSet_h40fa4a98__5.o Variane_testharness___024root__DepSet_h40fa4a98__5.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike   -Os -c -o Variane_testharness___024root__DepSet_h40fa4a98__6.o Variane_testharness___024root__DepSet_h40fa4a98__6.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike   -Os -c -o Variane_testharness___024root__DepSet_h40fa4a98__7.o Variane_testharness___024root__DepSet_h40fa4a98__7.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike   -Os -c -o Variane_testharness___024root__DepSet_h40fa4a98__8.o Variane_testharness___024root__DepSet_h40fa4a98__8.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike   -Os -c -o Variane_testharness___024root__DepSet_h40fa4a98__9.o Variane_testharness___024root__DepSet_h40fa4a98__9.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike   -Os -c -o Variane_testharness___024root__DepSet_h40fa4a98__10.o Variane_testharness___024root__DepSet_h40fa4a98__10.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike   -Os -c -o Variane_testharness___024unit__DepSet_h86bd86a4__0.o Variane_testharness___024unit__DepSet_h86bd86a4__0.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike   -Os -c -o Variane_testharness_uart_bus__DepSet_h03179670__0.o Variane_testharness_uart_bus__DepSet_h03179670__0.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike   -Os -c -o Variane_testharness_AXI_BUS__A40_AB40_AC5_AD20__DepSet_he3904c43__0.o Variane_testharness_AXI_BUS__A40_AB40_AC5_AD20__DepSet_he3904c43__0.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike   -Os -c -o Variane_testharness_REG_BUS__A20_D20__DepSet_ha23f2320__0.o Variane_testharness_REG_BUS__A20_D20__DepSet_ha23f2320__0.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike   -Os -c -o Variane_testharness__Dpi.o Variane_testharness__Dpi.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike    -c -o Variane_testharness__ConstPool_0.o Variane_testharness__ConstPool_0.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike    -c -o Variane_testharness___024root__Slow.o Variane_testharness___024root__Slow.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike    -c -o Variane_testharness___024root__DepSet_h5fbfe5da__0__Slow.o Variane_testharness___024root__DepSet_h5fbfe5da__0__Slow.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike    -c -o Variane_testharness___024root__DepSet_h40fa4a98__0__Slow.o Variane_testharness___024root__DepSet_h40fa4a98__0__Slow.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike    -c -o Variane_testharness___024root__DepSet_h40fa4a98__1__Slow.o Variane_testharness___024root__DepSet_h40fa4a98__1__Slow.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike    -c -o Variane_testharness___024unit__Slow.o Variane_testharness___024unit__Slow.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike    -c -o Variane_testharness___024unit__DepSet_h09fcab4a__0__Slow.o Variane_testharness___024unit__DepSet_h09fcab4a__0__Slow.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike    -c -o Variane_testharness_uart_bus__Slow.o Variane_testharness_uart_bus__Slow.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike    -c -o Variane_testharness_uart_bus__DepSet_h03179670__0__Slow.o Variane_testharness_uart_bus__DepSet_h03179670__0__Slow.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike    -c -o Variane_testharness_AXI_BUS__A40_AB40_AC5_AD20__Slow.o Variane_testharness_AXI_BUS__A40_AB40_AC5_AD20__Slow.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike    -c -o Variane_testharness_AXI_BUS__A40_AB40_AC5_AD20__DepSet_he3904c43__0__Slow.o Variane_testharness_AXI_BUS__A40_AB40_AC5_AD20__DepSet_he3904c43__0__Slow.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike    -c -o Variane_testharness_REG_BUS__A20_D20__Slow.o Variane_testharness_REG_BUS__A20_D20__Slow.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike    -c -o Variane_testharness_REG_BUS__A20_D20__DepSet_ha23f2320__0__Slow.o Variane_testharness_REG_BUS__A20_D20__DepSet_ha23f2320__0__Slow.cpp
g++  -I.  -MMD -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0 -faligned-new -fcf-protection=none -Wno-bool-operation -Wno-sign-compare -Wno-uninitialized -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-variable -Wno-shadow     -I/include -I/include -I/home/cai/cache_project/sandbox/cva6/tools/verilator/share/verilator/include/vltstd -I/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/include -I/home/cai/cache_project/sandbox/cva6/tools/spike/include -std=c++17 -I/home/cai/cache_project//sandbox/cva6/corev_apu/tb/dpi -O3 -DVL_DEBUG -I/home/cai/cache_project/sandbox/cva6/tools/spike    -c -o Variane_testharness__Syms.o Variane_testharness__Syms.cpp
echo "" > Variane_testharness__ALL.verilator_deplist.tmp
Archive ar -rcs Variane_testharness__ALL.a Variane_testharness.o Variane_testharness___024root__DepSet_h5fbfe5da__0.o Variane_testharness___024root__DepSet_h5fbfe5da__1.o Variane_testharness___024root__DepSet_h5fbfe5da__2.o Variane_testharness___024root__DepSet_h5fbfe5da__3.o Variane_testharness___024root__DepSet_h40fa4a98__0.o Variane_testharness___024root__DepSet_h40fa4a98__1.o Variane_testharness___024root__DepSet_h40fa4a98__2.o Variane_testharness___024root__DepSet_h40fa4a98__3.o Variane_testharness___024root__DepSet_h40fa4a98__4.o Variane_testharness___024root__DepSet_h40fa4a98__5.o Variane_testharness___024root__DepSet_h40fa4a98__6.o Variane_testharness___024root__DepSet_h40fa4a98__7.o Variane_testharness___024root__DepSet_h40fa4a98__8.o Variane_testharness___024root__DepSet_h40fa4a98__9.o Variane_testharness___024root__DepSet_h40fa4a98__10.o Variane_testharness___024unit__DepSet_h86bd86a4__0.o Variane_testharness_uart_bus__DepSet_h03179670__0.o Variane_testharness_AXI_BUS__A40_AB40_AC5_AD20__DepSet_he3904c43__0.o Variane_testharness_REG_BUS__A20_D20__DepSet_ha23f2320__0.o Variane_testharness__Dpi.o Variane_testharness__ConstPool_0.o Variane_testharness___024root__Slow.o Variane_testharness___024root__DepSet_h5fbfe5da__0__Slow.o Variane_testharness___024root__DepSet_h40fa4a98__0__Slow.o Variane_testharness___024root__DepSet_h40fa4a98__1__Slow.o Variane_testharness___024unit__Slow.o Variane_testharness___024unit__DepSet_h09fcab4a__0__Slow.o Variane_testharness_uart_bus__Slow.o Variane_testharness_uart_bus__DepSet_h03179670__0__Slow.o Variane_testharness_AXI_BUS__A40_AB40_AC5_AD20__Slow.o Variane_testharness_AXI_BUS__A40_AB40_AC5_AD20__DepSet_he3904c43__0__Slow.o Variane_testharness_REG_BUS__A20_D20__Slow.o Variane_testharness_REG_BUS__A20_D20__DepSet_ha23f2320__0__Slow.o Variane_testharness__Syms.o
g++    ariane_tb.o SimDTM.o SimJTAG.o msim_helper.o remote_bitbang.o verilated.o verilated_dpi.o verilated_vpi.o verilated_threads.o Variane_testharness__ALL.a   -L/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/lib -L/home/cai/cache_project/sandbox/cva6/tools/spike/lib -Wl,-rpath,/home/cai/cache_project/sandbox/cva6/tools/riscv_toolchain/lib -Wl,-rpath,/home/cai/cache_project/sandbox/cva6/tools/spike/lib -lfesvr -lriscv -ldisasm -lyaml-cpp  -lpthread  -pthread -lpthread -latomic   -o Variane_testharness
rm Variane_testharness__ALL.verilator_deplist.tmp
make[2]: Leaving directory '/home/cai/cache_project/sandbox/cva6/work-ver'
make[1]: Leaving directory '/home/cai/cache_project/sandbox/cva6'
/home/cai/cache_project/sandbox/cva6//work-ver/Variane_testharness   /home/cai/cache_project/sandbox/cva6/verif/sim/out_2025-05-29/directed_tests/cache_test_loop.o +debug_disable=1 +ntb_random_seed=1777533877 \
  ++/home/cai/cache_project/sandbox/cva6/verif/sim/out_2025-05-29/directed_tests/cache_test_loop.o +elf_file=/home/cai/cache_project/sandbox/cva6/verif/sim/out_2025-05-29/directed_tests/cache_test_loop.o +core_name=cv32a60x +config_file=/home/cai/cache_project//sandbox/cva6/config/gen_from_riscv_config/cv32a60x/spike/spike.yaml +tohost_addr=80001000 +signature=/home/cai/cache_project/sandbox/cva6/verif/sim/out_2025-05-29/directed_tests/cache_test_loop.o.signature_output +UVM_TESTNAME=uvmt_cva6_firmware_test_c +report_file=/home/cai/cache_project/sandbox/cva6/verif/sim/out_2025-05-29/veri-testharness_sim/cache_test_loop.cv32a60x.log.yaml +core_name=cv32a60x
This emulator compiled with JTAG Remote Bitbang client. To enable, use +jtag_rbb_enable=1.
Listening on port 43169
/home/cai/cache_project/sandbox/cva6/verif/sim/out_2025-05-29/directed_tests/cache_test_loop.o *** SUCCESS *** (tohost = 0) after 163622 cycles
*** [rvfi_tracer] INFO: Simulation terminated after     163610 cycles!

CPU time used: 26891.44 ms
Wall clock time passed: 26907.53 ms
# If present, move default waveform files to log directory.
# Keep track of target in waveform file name.
[ ! -f verilator.fst ] || mv verilator.fst `dirname /home/cai/cache_project/sandbox/cva6/verif/sim/out_2025-05-29/veri-testharness_sim/cache_test_loop.cv32a60x.log`/`basename /home/cai/cache_project/sandbox/cva6/verif/sim/out_2025-05-29/veri-testharness_sim/cache_test_loop.cv32a60x.log .log`.fst
[ ! -f verilator.vcd ] || mv verilator.vcd `dirname /home/cai/cache_project/sandbox/cva6/verif/sim/out_2025-05-29/veri-testharness_sim/cache_test_loop.cv32a60x.log`/`basename /home/cai/cache_project/sandbox/cva6/verif/sim/out_2025-05-29/veri-testharness_sim/cache_test_loop.cv32a60x.log .log`.vcd
# Generate disassembled log.
/home/cai/cache_project/sandbox/cva6/tools/spike/bin/spike-dasm --isa=rv32imc_zba_zbb_zbs_zbc_zicsr_zifencei < ./trace_rvfi_hart_00.dasm > /home/cai/cache_project/sandbox/cva6/verif/sim/out_2025-05-29/veri-testharness_sim/cache_test_loop.cv32a60x.log
# Copy improved format log to output directory
cp ./trace_rvfi_hart_00.dasm.v2 `dirname /home/cai/cache_project/sandbox/cva6/verif/sim/out_2025-05-29/veri-testharness_sim/cache_test_loop.cv32a60x.log`/`basename /home/cai/cache_project/sandbox/cva6/verif/sim/out_2025-05-29/veri-testharness_sim/cache_test_loop.cv32a60x.log .log`.log.v2
grep 0x0000000080000000 ./trace_rvfi_hart_00.dasm
0core   0: 0x0000000080000000 (0x00004081) DASM(00004081)	###3 0x0000000080000000 (0x4081) x 1 0x00000000
