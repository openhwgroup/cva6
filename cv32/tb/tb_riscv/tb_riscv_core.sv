// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

/////////////////////////////////////////////////////////////////////////////////////////////////
//                                                                                             //
// Author:                        Francesco Minervini - minervif@student.ethz.ch               //
//                                                                                             //
// Additional contributions by:                                                                //
//                                                                                             //
// Design Name:                   Top level module including riscv core and perturbation       //
//                                module                                                       //
// Project Name:                  TB RISC-V                                                    //
// Language:                      SystemVerilog                                                //
//                                                                                             //
// Description:                   This module is instantiated in the core_region.sv code       //
//                                when the parameter TB_RISCV is set to 1.                     //
//                                This module instantiates one between zero_riscy or riscy     //
//                                core depending on the value of USE_ZERO_RISCY, then          //
//                                it also instantiates and connects the core to the            //
//                                perturbation module.                                         //
//                                                                                             //
/////////////////////////////////////////////////////////////////////////////////////////////////

module tb_riscv_core
#(
  parameter N_EXT_PERF_COUNTERS =  0,
  parameter INSTR_RDATA_WIDTH   = 32,
  parameter PULP_SECURE         =  0,
  parameter N_PMP_ENTRIES       = 16,
  parameter PULP_CLUSTER        =  1,
  parameter FPU                 =  0,
  parameter SHARED_FP           =  0,
  parameter SHARED_DSP_MULT     =  0,
  parameter SHARED_INT_DIV      =  0,
  parameter SHARED_FP_DIVSQRT   =  0,
  parameter WAPUTYPE            =  0,
  parameter APU_NARGS_CPU       =  3,
  parameter APU_WOP_CPU         =  6,
  parameter APU_NDSFLAGS_CPU    = 15,
  parameter APU_NUSFLAGS_CPU    =  5,
  parameter SIMCHECKER          =  0
)
(
  // Clock and Reset
  input  logic        clk_i,
  input  logic        rst_ni,

  input  logic        clock_en_i,    // enable clock, otherwise it is gated
  input  logic        test_en_i,     // enable all clock gates for testing

  input  logic        fregfile_disable_i,  // disable the fp regfile, using int regfile instead

  // Core ID, Cluster ID and boot address are considered more or less static
  input  logic [31:0] boot_addr_i,
  input  logic [ 3:0] core_id_i,
  input  logic [ 5:0] cluster_id_i,

  // Instruction memory interface
  output logic                         instr_req_o,
  input  logic                         instr_gnt_i,
  input  logic                         instr_rvalid_i,
  output logic                  [31:0] instr_addr_o,
  input  logic [INSTR_RDATA_WIDTH-1:0] instr_rdata_i,

  // Data memory interface
  output logic        data_req_o,
  input  logic        data_gnt_i,
  input  logic        data_rvalid_i,
  output logic        data_we_o,
  output logic [3:0]  data_be_o,
  output logic [31:0] data_addr_o,
  output logic [31:0] data_wdata_o,
  input  logic [31:0] data_rdata_i,
  // apu-interconnect
  // handshake signals
  output logic                       apu_master_req_o,
  output logic                       apu_master_ready_o,
  input logic                        apu_master_gnt_i,
  // request channel
  output logic [31:0]                 apu_master_operands_o [APU_NARGS_CPU-1:0],
  output logic [APU_WOP_CPU-1:0]      apu_master_op_o,
  output logic [WAPUTYPE-1:0]         apu_master_type_o,
  output logic [APU_NDSFLAGS_CPU-1:0] apu_master_flags_o,
  // response channel
  input logic                        apu_master_valid_i,
  input logic [31:0]                 apu_master_result_i,
  input logic [APU_NUSFLAGS_CPU-1:0] apu_master_flags_i,

  // Interrupt inputs
  input  logic        irq_i,                 // level sensitive IR lines
  input  logic [4:0]  irq_id_i,
  output logic        irq_ack_o,
  output logic [4:0]  irq_id_o,
  input  logic        irq_sec_i,

  output logic        sec_lvl_o,

  // Debug Interface
  input  logic        debug_req_i,
  output logic        debug_gnt_o,
  output logic        debug_rvalid_o,
  input  logic [14:0] debug_addr_i,
  input  logic        debug_we_i,
  input  logic [31:0] debug_wdata_i,
  output logic [31:0] debug_rdata_o,
  output logic        debug_halted_o,
  input  logic        debug_halt_i,
  input  logic        debug_resume_i,

  // CPU Control Signals
  input  logic        fetch_enable_i,
  output logic        core_busy_o,

  input  logic [N_EXT_PERF_COUNTERS-1:0] ext_perf_counters_i
);

localparam PERT_REGS = 15;

//////////////////////////////////////////////////////////////
//Internal signals to connect core and perturbation module
/////////////////////////////////////////////////////////////

// Additional instruction signals

logic                          instr_req_int;
logic                          instr_grant_int;
logic                          instr_rvalid_int;
logic [31:0]                   instr_addr_int;
logic [INSTR_RDATA_WIDTH-1:0]  instr_rdata_int;

// Additional data signals
logic                          data_req_int;
logic                          data_grant_int;
logic                          data_rvalid_int;
logic                          data_we_int;
logic [3:0]                    data_be_int;
logic [31:0]                   data_addr_int;
logic [31:0]                   data_wdata_int;
logic [31:0]                   data_rdata_int;

// Additional signals for pertubation/debug registers
logic                          debug_req_int;
logic                          debug_grant_int;
logic                          debug_rvalid_int;
logic                          debug_we_int;
logic [14:0]                   debug_addr_int;
logic [31:0]                   debug_wdata_int;
logic [31:0]                   debug_rdata_int;

// Additional interrupt signals
logic                          irq_int;
logic                          irq_ack_int;
logic [4:0]                    irq_id_int;
logic [4:0]                    irq_core_resp_id_int;



  riscv_core
  #(
    .N_EXT_PERF_COUNTERS            ( N_EXT_PERF_COUNTERS      ),
    .INSTR_RDATA_WIDTH              ( INSTR_RDATA_WIDTH        ),
    .PULP_SECURE                    ( PULP_SECURE              ),
    .N_PMP_ENTRIES                  ( N_PMP_ENTRIES            ),
    .FPU                            ( FPU                      ),
    .SHARED_FP                      ( SHARED_FP                ),
    .SHARED_DSP_MULT                ( SHARED_DSP_MULT          ),
    .SHARED_INT_DIV                 ( SHARED_INT_DIV           ),
    .SHARED_FP_DIVSQRT              ( SHARED_FP_DIVSQRT        ),
    .WAPUTYPE                       ( WAPUTYPE                 ),
    .APU_NARGS_CPU                  ( APU_NARGS_CPU            ),
    .APU_WOP_CPU                    ( APU_WOP_CPU              ),
    .APU_NDSFLAGS_CPU               ( APU_NDSFLAGS_CPU         ),
    .APU_NUSFLAGS_CPU               ( APU_NUSFLAGS_CPU         )
    )
  RISCV_CORE
  (
    .clk_i                          ( clk_i                   ),
    .rst_ni                         ( rst_ni                  ),

    .clock_en_i                     ( clock_en_i              ),
    .test_en_i                      ( test_en_i               ),

    .fregfile_disable_i             ( fregfile_disable_i      ),

    .boot_addr_i                    ( boot_addr_i             ),
    .core_id_i                      ( core_id_i               ),
    .cluster_id_i                   ( cluster_id_i            ),

    .instr_req_o                    ( instr_req_int           ),
    .instr_gnt_i                    ( instr_grant_int         ),
    .instr_rvalid_i                 ( instr_rvalid_int        ),
    .instr_addr_o                   ( instr_addr_int          ),
    .instr_rdata_i                  ( instr_rdata_int         ),

    .data_req_o                     ( data_req_int            ),
    .data_gnt_i                     ( data_grant_int          ),
    .data_rvalid_i                  ( data_rvalid_int         ),
    .data_we_o                      ( data_we_int             ),
    .data_be_o                      ( data_be_int             ),
    .data_addr_o                    ( data_addr_int           ),
    .data_wdata_o                   ( data_wdata_int          ),
    .data_rdata_i                   ( data_rdata_int          ),

    .apu_master_req_o               ( apu_master_req_o        ),
    .apu_master_ready_o             ( apu_master_ready_o      ),
    .apu_master_gnt_i               ( apu_master_gnt_i        ),
    .apu_master_operands_o          ( apu_master_operands_o   ),
    .apu_master_op_o                ( apu_master_op_o         ),
    .apu_master_type_o              ( apu_master_type_o       ),
    .apu_master_flags_o             ( apu_master_flags_o      ),

    .apu_master_valid_i             ( apu_master_valid_i      ),
    .apu_master_result_i            ( apu_master_result_i     ),
    .apu_master_flags_i             ( apu_master_flags_i      ),

    .irq_i                          ( irq_int                 ),
    .irq_id_i                       ( irq_id_int              ),
    .irq_ack_o                      ( irq_ack_int             ),
    .irq_id_o                       ( irq_core_resp_id_int    ),
    .irq_sec_i                      ( irq_sec_i               ),

    .sec_lvl_o                      ( sec_lvl_o               ),

    .debug_req_i                    ( debug_req_int           ),
    .debug_gnt_o                    ( debug_grant_int         ),
    .debug_rvalid_o                 ( debug_rvalid_int        ),
    .debug_addr_i                   ( debug_addr_int          ),
    .debug_we_i                     ( debug_we_int            ),
    .debug_wdata_i                  ( debug_wdata_int         ),
    .debug_rdata_o                  ( debug_rdata_int         ),
    .debug_halted_o                 ( debug_halted_o          ),
    .debug_halt_i                   ( debug_halt_i            ),
    .debug_resume_i                 ( debug_resume_i          ),

    .fetch_enable_i                 ( fetch_enable_i          ),
    .core_busy_o                    ( core_busy_o             ),

    .ext_perf_counters_i            ( ext_perf_counters_i     )
  );

  // Perturbation module instance
  riscv_perturbation
  #(
   .PERT_REGS                      ( PERT_REGS         ),
   .INSTR_RDATA_WIDTH              ( INSTR_RDATA_WIDTH )
  )
  riscv_perturbation_i
  (
    .clk_i                         ( clk_i                  ),
    .rst_ni                        ( rst_ni                 ),

    .pert_instr_req_i              ( instr_req_int          ),
    .pert_instr_req_o              ( instr_req_o            ),
    .pert_instr_grant_i            ( instr_gnt_i            ),
    .pert_instr_grant_o            ( instr_grant_int        ),
    .pert_instr_rvalid_i           ( instr_rvalid_i         ),
    .pert_instr_rvalid_o           ( instr_rvalid_int       ),
    .pert_instr_addr_i             ( instr_addr_int         ),
    .pert_instr_addr_o             ( instr_addr_o           ),
    .pert_instr_rdata_i            ( instr_rdata_i          ),
    .pert_instr_rdata_o            ( instr_rdata_int        ),

    .pert_data_req_i               ( data_req_int           ),
    .pert_data_req_o               ( data_req_o             ),
    .pert_data_grant_i             ( data_gnt_i             ),
    .pert_data_grant_o             ( data_grant_int         ),
    .pert_data_rvalid_i            ( data_rvalid_i          ),
    .pert_data_rvalid_o            ( data_rvalid_int        ),
    .pert_data_we_i                ( data_we_int            ),
    .pert_data_we_o                ( data_we_o              ),
    .pert_data_be_i                ( data_be_int            ),
    .pert_data_be_o                ( data_be_o              ),
    .pert_data_addr_i              ( data_addr_int          ),
    .pert_data_addr_o              ( data_addr_o            ),
    .pert_data_wdata_i             ( data_wdata_int         ),
    .pert_data_wdata_o             ( data_wdata_o           ),
    .pert_data_rdata_i             ( data_rdata_i           ),
    .pert_data_rdata_o             ( data_rdata_int         ),

    .pert_debug_req_i              ( debug_req_i            ),
    .pert_debug_req_o              ( debug_req_int          ),
    .pert_debug_gnt_i              ( debug_grant_int        ),
    .pert_debug_gnt_o              ( debug_gnt_o            ),
    .pert_debug_rvalid_i           ( debug_rvalid_int       ),
    .pert_debug_rvalid_o           ( debug_rvalid_o         ),
    .pert_debug_we_i               ( debug_we_i             ),
    .pert_debug_we_o               ( debug_we_int           ),
    .pert_debug_addr_i             ( debug_addr_i           ),
    .pert_debug_addr_o             ( debug_addr_int         ),
    .pert_debug_wdata_i            ( debug_wdata_i          ),
    .pert_debug_wdata_o            ( debug_wdata_int        ),
    .pert_debug_rdata_i            ( debug_rdata_int        ),
    .pert_debug_rdata_o            ( debug_rdata_o          ),

    .pert_irq_i                    ( irq_i                  ),
    .pert_irq_o                    ( irq_int                ),
    .pert_irq_id_i                 ( irq_id_i               ),
    .pert_irq_id_o                 ( irq_id_int             ),
    .pert_irq_ack_i                ( irq_ack_int            ),
    .pert_irq_ack_o                ( irq_ack_o              ),
    .pert_irq_core_resp_id_i       ( irq_core_resp_id_int   ),
    .pert_irq_core_resp_id_o       ( irq_id_o               ),
    .pert_pc_id_i                  ( RISCV_CORE.pc_id  )
  );


   `ifndef VERILATOR
   generate
       if(SIMCHECKER) begin: ri5cy_simchecker
          riscv_simchecker riscv_simchecker_i
          (
            .clk              ( RISCV_CORE.clk_i                                ),
            .rst_n            ( RISCV_CORE.rst_ni                               ),

            .fetch_enable     ( RISCV_CORE.fetch_enable_i                       ),
            .boot_addr        ( RISCV_CORE.boot_addr_i                          ),
            .core_id          ( RISCV_CORE.core_id_i                            ),
            .cluster_id       ( RISCV_CORE.cluster_id_i                         ),

            .instr_compressed ( RISCV_CORE.if_stage_i.fetch_rdata[15:0]         ),
            .if_valid         ( RISCV_CORE.if_stage_i.if_valid                  ),
            .pc_set           ( RISCV_CORE.pc_set                               ),


            .pc               ( RISCV_CORE.id_stage_i.pc_id_i                   ),
            .instr            ( RISCV_CORE.id_stage_i.instr                     ),
            .is_compressed    ( RISCV_CORE.is_compressed_id                     ),
            .id_valid         ( RISCV_CORE.id_stage_i.id_valid_o                ),
            .is_decoding      ( RISCV_CORE.id_stage_i.is_decoding_o             ),
            .is_illegal       ( RISCV_CORE.id_stage_i.illegal_insn_dec          ),
            .is_interrupt     ( RISCV_CORE.is_interrupt                         ),
            .irq_no           ( RISCV_CORE.irq_id_i                             ),
            .pipe_flush       ( RISCV_CORE.id_stage_i.controller_i.pipe_flush_i ),
            .irq_i            ( RISCV_CORE.irq_i                                ),
            .is_mret          ( RISCV_CORE.id_stage_i.controller_i.mret_insn_i  ),

            .int_enable       ( RISCV_CORE.id_stage_i.m_irq_enable_i            ),

            .lsu_ready_wb     ( RISCV_CORE.lsu_ready_wb                         ),
            .apu_ready_wb     ( RISCV_CORE.apu_ready_wb                         ),
            .wb_contention    ( RISCV_CORE.ex_stage_i.wb_contention             ),

            .apu_en_id        ( RISCV_CORE.id_stage_i.apu_en                    ),
            .apu_req          ( RISCV_CORE.ex_stage_i.apu_req                   ),
            .apu_gnt          ( RISCV_CORE.ex_stage_i.apu_gnt                   ),
            .apu_valid        ( RISCV_CORE.ex_stage_i.apu_valid                 ),
            .apu_singlecycle  ( RISCV_CORE.ex_stage_i.apu_singlecycle           ),
            .apu_multicycle   ( RISCV_CORE.ex_stage_i.apu_multicycle            ),
            .apu_latency      ( RISCV_CORE.ex_stage_i.apu_lat_i                 ),
            .apu_active       ( RISCV_CORE.ex_stage_i.apu_active                ),
            .apu_en_ex        ( RISCV_CORE.ex_stage_i.apu_en_i                  ),

            .ex_valid         ( RISCV_CORE.ex_valid                             ),
            .ex_reg_addr      ( RISCV_CORE.id_stage_i.registers_i.waddr_b_i     ),

            .ex_reg_we        ( RISCV_CORE.id_stage_i.registers_i.we_b_i        ),
            .ex_reg_wdata     ( RISCV_CORE.id_stage_i.registers_i.wdata_b_i     ),

            .ex_data_req      ( RISCV_CORE.data_req_o                           ),
            .ex_data_gnt      ( RISCV_CORE.data_gnt_i                           ),
            .ex_data_we       ( RISCV_CORE.data_we_o                            ),
            .ex_data_addr     ( RISCV_CORE.data_addr_o                          ),
            .ex_data_wdata    ( RISCV_CORE.data_wdata_o                         ),

            .lsu_misaligned   ( RISCV_CORE.data_misaligned                      ),
            .wb_bypass        ( RISCV_CORE.ex_stage_i.branch_in_ex_i            ),

            .wb_valid         ( RISCV_CORE.wb_valid                             ),
            .wb_reg_addr      ( RISCV_CORE.id_stage_i.registers_i.waddr_a_i     ),
            .wb_reg_we        ( RISCV_CORE.id_stage_i.registers_i.we_a_i        ),
            .wb_reg_wdata     ( RISCV_CORE.id_stage_i.registers_i.wdata_a_i     ),
            .wb_data_rvalid   ( RISCV_CORE.data_rvalid_i                        ),
            .wb_data_rdata    ( RISCV_CORE.data_rdata_i                         )
          );
        end
   endgenerate
   `endif

endmodule // tb_riscv_core