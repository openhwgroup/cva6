// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Renzo Andri - andrire@student.ethz.ch                      //
//                                                                            //
// Additional contributions by:                                               //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    Execute stage                                              //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Execution stage: Hosts ALU and MAC unit                    //
//                 ALU: computes additions/subtractions/comparisons           //
//                 MULT: computes normal multiplications                      //
//                 APU_DISP: offloads instructions to the shared unit.        //
//                 SHARED_DSP_MULT, SHARED_INT_DIV allow                      //
//                 to offload also dot-product, int-div, int-mult to the      //
//                 shared unit.                                               //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

`include "apu_macros.sv"

import apu_core_package::*;
import riscv_defines::*;

module riscv_ex_stage
#(
  parameter FPU              =  0,
  parameter FP_DIVSQRT       =  0,
  parameter SHARED_FP        =  0,
  parameter SHARED_DSP_MULT  =  0,
  parameter SHARED_INT_DIV   =  0,
  parameter APU_NARGS_CPU    =  3,
  parameter APU_WOP_CPU      =  6,
  parameter APU_NDSFLAGS_CPU = 15,
  parameter APU_NUSFLAGS_CPU =  5
)
(
  input  logic        clk,
  input  logic        rst_n,

  // ALU signals from ID stage
  input  logic [ALU_OP_WIDTH-1:0] alu_operator_i,
  input  logic [31:0] alu_operand_a_i,
  input  logic [31:0] alu_operand_b_i,
  input  logic [31:0] alu_operand_c_i,
  input  logic        alu_en_i,
  input  logic [ 4:0] bmask_a_i,
  input  logic [ 4:0] bmask_b_i,
  input  logic [ 1:0] imm_vec_ext_i,
  input  logic [ 1:0] alu_vec_mode_i,
  input  logic        alu_is_clpx_i,
  input  logic        alu_is_subrot_i,
  input  logic [ 1:0] alu_clpx_shift_i,

  // Multiplier signals
  input  logic [ 2:0] mult_operator_i,
  input  logic [31:0] mult_operand_a_i,
  input  logic [31:0] mult_operand_b_i,
  input  logic [31:0] mult_operand_c_i,
  input  logic        mult_en_i,
  input  logic        mult_sel_subword_i,
  input  logic [ 1:0] mult_signed_mode_i,
  input  logic [ 4:0] mult_imm_i,

  input  logic [31:0] mult_dot_op_a_i,
  input  logic [31:0] mult_dot_op_b_i,
  input  logic [31:0] mult_dot_op_c_i,
  input  logic [ 1:0] mult_dot_signed_i,
  input  logic        mult_is_clpx_i,
  input  logic [ 1:0] mult_clpx_shift_i,
  input  logic        mult_clpx_img_i,

  output logic        mult_multicycle_o,

  // FPU signals
  input  logic [C_PC-1:0]             fpu_prec_i,
  output logic [C_FFLAG-1:0]          fpu_fflags_o,
  output logic                        fpu_fflags_we_o,

  // APU signals
  input  logic                        apu_en_i,
  input  logic [APU_WOP_CPU-1:0]      apu_op_i,
  input  logic [1:0]                  apu_lat_i,
  input  logic [APU_NARGS_CPU-1:0][31:0] apu_operands_i,
  input  logic [5:0]                  apu_waddr_i,
  input  logic [APU_NDSFLAGS_CPU-1:0] apu_flags_i,

  input  logic [2:0][5:0]             apu_read_regs_i,
  input  logic [2:0]                  apu_read_regs_valid_i,
  output logic                        apu_read_dep_o,
  input  logic [1:0][5:0]             apu_write_regs_i,
  input  logic [1:0]                  apu_write_regs_valid_i,
  output logic                        apu_write_dep_o,

  output logic                        apu_perf_type_o,
  output logic                        apu_perf_cont_o,
  output logic                        apu_perf_wb_o,

  output logic                        apu_busy_o,
  output logic                        apu_ready_wb_o,

  // apu-interconnect
  // handshake signals
  output logic                       apu_master_req_o,
  output logic                       apu_master_ready_o,
  input logic                        apu_master_gnt_i,
  // request channel
  output logic [APU_NARGS_CPU-1:0][31:0] apu_master_operands_o,
  output logic [APU_WOP_CPU-1:0]     apu_master_op_o,
  // response channel
  input logic                        apu_master_valid_i,
  input logic [31:0]                 apu_master_result_i,

  input  logic        lsu_en_i,
  input  logic [31:0] lsu_rdata_i,

  // input from ID stage
  input  logic        branch_in_ex_i,
  input  logic [5:0]  regfile_alu_waddr_i,
  input  logic        regfile_alu_we_i,

  // directly passed through to WB stage, not used in EX
  input  logic        regfile_we_i,
  input  logic [5:0]  regfile_waddr_i,

  // CSR access
  input  logic        csr_access_i,
  input  logic [31:0] csr_rdata_i,

  // Output of EX stage pipeline
  output logic [5:0]  regfile_waddr_wb_o,
  output logic        regfile_we_wb_o,
  output logic [31:0] regfile_wdata_wb_o,

  // Forwarding ports : to ID stage
  output logic  [5:0] regfile_alu_waddr_fw_o,
  output logic        regfile_alu_we_fw_o,
  output logic [31:0] regfile_alu_wdata_fw_o,    // forward to RF and ID/EX pipe, ALU & MUL

  // To IF: Jump and branch target and decision
  output logic [31:0] jump_target_o,
  output logic        branch_decision_o,

  // Stall Control
  input  logic        lsu_ready_ex_i, // EX part of LSU is done
  input  logic        lsu_err_i,

  output logic        ex_ready_o, // EX stage ready for new data
  output logic        ex_valid_o, // EX stage gets new data
  input  logic        wb_ready_i  // WB stage ready for new data
);

  logic [31:0]    alu_result;
  logic [31:0]    mult_result;
  logic           alu_cmp_result;

  logic           regfile_we_lsu;
  logic [5:0]     regfile_waddr_lsu;

  logic           wb_contention;
  logic           wb_contention_lsu;

  logic           alu_ready;
  logic           mult_ready;
  logic           fpu_ready;
  logic           fpu_valid;


  // APU signals
  logic           apu_valid;
  logic [5:0]     apu_waddr;
  logic [31:0]    apu_result;
  logic           apu_stall;
  logic           apu_active;
  logic           apu_singlecycle;
  logic           apu_multicycle;
  logic           apu_req;
  logic           apu_ready;
  logic           apu_gnt;

  // ALU write port mux
  always_comb
  begin
    regfile_alu_wdata_fw_o = '0;
    regfile_alu_waddr_fw_o = '0;
    regfile_alu_we_fw_o    = '0;
    wb_contention          = 1'b0;

    // APU single cycle operations, and multicycle operations (>2cycles) are written back on ALU port
    if (apu_valid & (apu_singlecycle | apu_multicycle)) begin
      regfile_alu_we_fw_o    = 1'b1;
      regfile_alu_waddr_fw_o = apu_waddr;
      regfile_alu_wdata_fw_o = apu_result;

      if(regfile_alu_we_i & ~apu_en_i) begin
        wb_contention = 1'b1;
      end
    end else begin
      regfile_alu_we_fw_o      = regfile_alu_we_i & ~apu_en_i; // private fpu incomplete?
      regfile_alu_waddr_fw_o   = regfile_alu_waddr_i;
      if (alu_en_i)
        regfile_alu_wdata_fw_o = alu_result;
      if (mult_en_i)
        regfile_alu_wdata_fw_o = mult_result;
      if (csr_access_i)
        regfile_alu_wdata_fw_o = csr_rdata_i;
    end
  end

  // LSU write port mux
  always_comb
  begin
    regfile_we_wb_o    = 1'b0;
    regfile_waddr_wb_o = regfile_waddr_lsu;
    regfile_wdata_wb_o = lsu_rdata_i;
    wb_contention_lsu  = 1'b0;

    if (regfile_we_lsu) begin
      regfile_we_wb_o = 1'b1;
      if (apu_valid & (!apu_singlecycle & !apu_multicycle)) begin
         wb_contention_lsu = 1'b1;
//         $error("%t, wb-contention", $time);
      end
    // APU two-cycle operations are written back on LSU port
    end else if (apu_valid & (!apu_singlecycle & !apu_multicycle)) begin
      regfile_we_wb_o    = 1'b1;
      regfile_waddr_wb_o = apu_waddr;
      regfile_wdata_wb_o = apu_result;
    end
  end

  // branch handling
  assign branch_decision_o = alu_cmp_result;
  assign jump_target_o     = alu_operand_c_i;


  ////////////////////////////
  //     _    _    _   _    //
  //    / \  | |  | | | |   //
  //   / _ \ | |  | | | |   //
  //  / ___ \| |__| |_| |   //
  // /_/   \_\_____\___/    //
  //                        //
  ////////////////////////////

  riscv_alu
  #(
    .SHARED_INT_DIV( SHARED_INT_DIV ),
    .FPU           ( FPU            )
    )
   alu_i
  (
    .clk                 ( clk             ),
    .rst_n               ( rst_n           ),
    .enable_i            ( alu_en_i        ),
    .operator_i          ( alu_operator_i  ),
    .operand_a_i         ( alu_operand_a_i ),
    .operand_b_i         ( alu_operand_b_i ),
    .operand_c_i         ( alu_operand_c_i ),

    .vector_mode_i       ( alu_vec_mode_i  ),
    .bmask_a_i           ( bmask_a_i       ),
    .bmask_b_i           ( bmask_b_i       ),
    .imm_vec_ext_i       ( imm_vec_ext_i   ),

    .is_clpx_i           ( alu_is_clpx_i   ),
    .clpx_shift_i        ( alu_clpx_shift_i),
    .is_subrot_i         ( alu_is_subrot_i ),

    .result_o            ( alu_result      ),
    .comparison_result_o ( alu_cmp_result  ),

    .ready_o             ( alu_ready       ),
    .ex_ready_i          ( ex_ready_o      )
  );


  ////////////////////////////////////////////////////////////////
  //  __  __ _   _ _   _____ ___ ____  _     ___ _____ ____     //
  // |  \/  | | | | | |_   _|_ _|  _ \| |   |_ _| ____|  _ \    //
  // | |\/| | | | | |   | |  | || |_) | |    | ||  _| | |_) |   //
  // | |  | | |_| | |___| |  | ||  __/| |___ | || |___|  _ <    //
  // |_|  |_|\___/|_____|_| |___|_|   |_____|___|_____|_| \_\   //
  //                                                            //
  ////////////////////////////////////////////////////////////////

  riscv_mult
  #(
    .SHARED_DSP_MULT(SHARED_DSP_MULT)
   )
   mult_i
  (
    .clk             ( clk                  ),
    .rst_n           ( rst_n                ),

    .enable_i        ( mult_en_i            ),
    .operator_i      ( mult_operator_i      ),

    .short_subword_i ( mult_sel_subword_i   ),
    .short_signed_i  ( mult_signed_mode_i   ),

    .op_a_i          ( mult_operand_a_i     ),
    .op_b_i          ( mult_operand_b_i     ),
    .op_c_i          ( mult_operand_c_i     ),
    .imm_i           ( mult_imm_i           ),

    .dot_op_a_i      ( mult_dot_op_a_i      ),
    .dot_op_b_i      ( mult_dot_op_b_i      ),
    .dot_op_c_i      ( mult_dot_op_c_i      ),
    .dot_signed_i    ( mult_dot_signed_i    ),
    .is_clpx_i       ( mult_is_clpx_i       ),
    .clpx_shift_i    ( mult_clpx_shift_i    ),
    .clpx_img_i      ( mult_clpx_img_i      ),

    .result_o        ( mult_result          ),

    .multicycle_o    ( mult_multicycle_o    ),
    .ready_o         ( mult_ready           ),
    .ex_ready_i      ( ex_ready_o           )
  );

   generate
      if (FPU == 1) begin
         ////////////////////////////////////////////////////
         //     _    ____  _   _   ____ ___ ____  ____     //
         //    / \  |  _ \| | | | |  _ \_ _/ ___||  _ \    //
         //   / _ \ | |_) | | | | | | | | |\___ \| |_) |   //
         //  / ___ \|  __/| |_| | | |_| | | ___) |  __/    //
         // /_/   \_\_|    \___/  |____/___|____/|_|       //
         //                                                //
         ////////////////////////////////////////////////////

         riscv_apu_disp apu_disp_i
         (
         .clk_i              ( clk                            ),
         .rst_ni             ( rst_n                          ),

         .enable_i           ( apu_en_i                       ),
         .apu_lat_i          ( apu_lat_i                      ),
         .apu_waddr_i        ( apu_waddr_i                    ),

         .apu_waddr_o        ( apu_waddr                      ),
         .apu_multicycle_o   ( apu_multicycle                 ),
         .apu_singlecycle_o  ( apu_singlecycle                ),

         .active_o           ( apu_active                     ),
         .stall_o            ( apu_stall                      ),

         .read_regs_i        ( apu_read_regs_i                ),
         .read_regs_valid_i  ( apu_read_regs_valid_i          ),
         .read_dep_o         ( apu_read_dep_o                 ),
         .write_regs_i       ( apu_write_regs_i               ),
         .write_regs_valid_i ( apu_write_regs_valid_i         ),
         .write_dep_o        ( apu_write_dep_o                ),

         .perf_type_o        ( apu_perf_type_o                ),
         .perf_cont_o        ( apu_perf_cont_o                ),

         // apu-interconnect
         // handshake signals
         .apu_master_req_o   ( apu_req                        ),
         .apu_master_ready_o ( apu_ready                      ),
         .apu_master_gnt_i   ( apu_gnt                        ),
         // response channel
         .apu_master_valid_i ( apu_valid                      )
         );

         assign apu_perf_wb_o  = wb_contention | wb_contention_lsu;
         assign apu_ready_wb_o = ~(apu_active | apu_en_i | apu_stall) | apu_valid;

         if ( SHARED_FP ) begin
            assign apu_master_req_o      = apu_req;
            assign apu_master_ready_o    = apu_ready;
            assign apu_gnt               = apu_master_gnt_i;
            assign apu_valid             = apu_master_valid_i;
            assign apu_master_operands_o = apu_operands_i;
            assign apu_master_op_o       = apu_op_i;
            assign apu_result            = apu_master_result_i;
            assign fpu_fflags_we_o       = apu_valid;
            assign fpu_ready             = 1'b1;
         end
         else begin

           //////////////////////////////
           //   ______ _____  _    _   //
           //  |  ____|  __ \| |  | |  //
           //  | |__  | |__) | |  | |  //
           //  |  __| |  ___/| |  | |  //
           //  | |    | |    | |__| |  //
           //  |_|    |_|     \____/   //
           //////////////////////////////


           logic [C_FPNEW_OPBITS-1:0]   fpu_op;
           logic                        fpu_op_mod;
           logic                        fpu_vec_op;

           logic [C_FPNEW_FMTBITS-1:0]  fpu_dst_fmt;
           logic [C_FPNEW_FMTBITS-1:0]  fpu_src_fmt;
           logic [C_FPNEW_IFMTBITS-1:0] fpu_int_fmt;
           logic [C_RM-1:0]             fp_rnd_mode;

           assign {fpu_vec_op, fpu_op_mod, fpu_op} = apu_op_i;
           assign {fpu_int_fmt, fpu_src_fmt, fpu_dst_fmt, fp_rnd_mode} = apu_flags_i;

           localparam C_DIV = FP_DIVSQRT ? fpnew_pkg::MERGED : fpnew_pkg::DISABLED;

           logic FPU_ready_int;

          // -----------
          // FPU Config
          // -----------
          // Features (enabled formats, vectors etc.)
          localparam fpnew_pkg::fpu_features_t FPU_FEATURES = '{
            Width:         C_FLEN,
            EnableVectors: C_XFVEC,
            EnableNanBox:  1'b0,
            FpFmtMask:     {C_RVF, C_RVD, C_XF16, C_XF8, C_XF16ALT},
            IntFmtMask:    {C_XFVEC && C_XF8, C_XFVEC && (C_XF16 || C_XF16ALT), 1'b1, 1'b0}
          };

          // Implementation (number of registers etc)
          localparam fpnew_pkg::fpu_implementation_t FPU_IMPLEMENTATION = '{
            PipeRegs:  '{// FP32, FP64, FP16, FP8, FP16alt
                         '{C_LAT_FP32, C_LAT_FP64, C_LAT_FP16, C_LAT_FP8, C_LAT_FP16ALT}, // ADDMUL
                         '{default: C_LAT_DIVSQRT}, // DIVSQRT
                         '{default: C_LAT_NONCOMP}, // NONCOMP
                         '{default: C_LAT_CONV}},   // CONV
            UnitTypes: '{'{default: fpnew_pkg::MERGED}, // ADDMUL
                         '{default: C_DIV},               // DIVSQRT
                         '{default: fpnew_pkg::PARALLEL}, // NONCOMP
                         '{default: fpnew_pkg::MERGED}},  // CONV
            PipeConfig: fpnew_pkg::AFTER
          };

          //---------------
          // FPU instance
          //---------------

          fpnew_top #(
            .Features       ( FPU_FEATURES       ),
            .Implementation ( FPU_IMPLEMENTATION ),
            .TagType        ( logic              )
          ) i_fpnew_bulk (
            .clk_i          ( clk                                   ),
            .rst_ni         ( rst_n                                 ),
            .operands_i     ( apu_operands_i                        ),
            .rnd_mode_i     ( fpnew_pkg::roundmode_e'(fp_rnd_mode)  ),
            .op_i           ( fpnew_pkg::operation_e'(fpu_op)       ),
            .op_mod_i       ( fpu_op_mod                            ),
            .src_fmt_i      ( fpnew_pkg::fp_format_e'(fpu_src_fmt)  ),
            .dst_fmt_i      ( fpnew_pkg::fp_format_e'(fpu_dst_fmt)  ),
            .int_fmt_i      ( fpnew_pkg::int_format_e'(fpu_int_fmt) ),
            .vectorial_op_i ( fpu_vec_op                            ),
            .tag_i          ( 1'b0                                  ),
            .in_valid_i     ( apu_req                               ),
            .in_ready_o     ( FPU_ready_int                         ),
            .flush_i        ( 1'b0                                  ),
            .result_o       ( apu_result                            ),
            .status_o       ( fpu_fflags_o                          ),
            .tag_o          ( /* unused */                          ),
            .out_valid_o    ( apu_valid                             ),
            .out_ready_i    ( 1'b1                                  ),
            .busy_o         ( /* unused */                          )
          );

          assign fpu_fflags_we_o          = apu_valid;
          assign apu_master_req_o         = '0;
          assign apu_master_ready_o       = 1'b1;
          assign apu_master_operands_o[0] = '0;
          assign apu_master_operands_o[1] = '0;
          assign apu_master_operands_o[2] = '0;
          assign apu_master_op_o          = '0;
          assign apu_gnt                  = 1'b1;

          assign fpu_ready = (FPU_ready_int & apu_req) | (~apu_req);

        end

      end
      else begin
         // default assignements for the case when no FPU/APU is attached.
         assign apu_master_req_o         = '0;
         assign apu_master_ready_o       = 1'b1;
         assign apu_master_operands_o[0] = '0;
         assign apu_master_operands_o[1] = '0;
         assign apu_master_operands_o[2] = '0;
         assign apu_master_op_o          = '0;
         assign apu_valid       = 1'b0;
         assign apu_waddr       = 6'b0;
         assign apu_stall       = 1'b0;
         assign apu_active      = 1'b0;
         assign apu_ready_wb_o  = 1'b1;
         assign apu_perf_wb_o   = 1'b0;
         assign apu_perf_cont_o = 1'b0;
         assign apu_perf_type_o = 1'b0;
         assign apu_singlecycle = 1'b0;
         assign apu_multicycle  = 1'b0;
         assign apu_read_dep_o  = 1'b0;
         assign apu_write_dep_o = 1'b0;
         assign fpu_fflags_we_o = 1'b0;
         assign fpu_fflags_o    = '0;
         // we need this because we want ex_ready_o to go high otherwise the
         // pipeline can't progress
         assign fpu_ready       = 1'b1;

      end
   endgenerate

   assign apu_busy_o = apu_active;

  ///////////////////////////////////////
  // EX/WB Pipeline Register           //
  ///////////////////////////////////////
  always_ff @(posedge clk, negedge rst_n)
  begin : EX_WB_Pipeline_Register
    if (~rst_n)
    begin
      regfile_waddr_lsu   <= '0;
      regfile_we_lsu      <= 1'b0;
    end
    else
    begin
      if (ex_valid_o) // wb_ready_i is implied
      begin
        regfile_we_lsu    <= regfile_we_i & ~lsu_err_i;
        if (regfile_we_i & ~lsu_err_i ) begin
          regfile_waddr_lsu <= regfile_waddr_i;
        end
      end else if (wb_ready_i) begin
        // we are ready for a new instruction, but there is none available,
        // so we just flush the current one out of the pipe
        regfile_we_lsu    <= 1'b0;
      end
    end
  end

  // As valid always goes to the right and ready to the left, and we are able
  // to finish branches without going to the WB stage, ex_valid does not
  // depend on ex_ready.
  assign ex_ready_o = (~apu_stall & alu_ready & mult_ready & lsu_ready_ex_i
                       & wb_ready_i & ~wb_contention & fpu_ready) | (branch_in_ex_i);
  assign ex_valid_o = (apu_valid | alu_en_i | mult_en_i | csr_access_i | lsu_en_i)
                       & (alu_ready & mult_ready & lsu_ready_ex_i & wb_ready_i);

endmodule
