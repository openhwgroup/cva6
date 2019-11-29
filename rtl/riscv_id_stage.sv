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
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    Instruction Decode Stage                                   //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Decode stage of the core. It decodes the instructions      //
//                 and hosts the register file.                               //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

import riscv_defines::*;
import apu_core_package::*;


// Source/Destination register instruction index
`define REG_S1 19:15
`define REG_S2 24:20
`define REG_S4 31:27
`define REG_D  11:07

module riscv_id_stage
#(
  parameter N_HWLP            =  2,
  parameter N_HWLP_BITS       =  $clog2(N_HWLP),
  parameter PULP_SECURE       =  0,
  parameter APU               =  0,
  parameter FPU               =  0,
  parameter Zfinx             =  0,
  parameter FP_DIVSQRT        =  0,
  parameter SHARED_FP         =  0,
  parameter SHARED_DSP_MULT   =  0,
  parameter SHARED_INT_MULT   =  0,
  parameter SHARED_INT_DIV    =  0,
  parameter SHARED_FP_DIVSQRT =  0,
  parameter WAPUTYPE          =  0,
  parameter APU_NARGS_CPU     =  3,
  parameter APU_WOP_CPU       =  6,
  parameter APU_NDSFLAGS_CPU  = 15,
  parameter APU_NUSFLAGS_CPU  =  5
)
(
    input  logic        clk,
    input  logic        rst_n,

    input  logic        test_en_i,
    input  logic        fregfile_disable_i,

    input  logic        fetch_enable_i,
    output logic        ctrl_busy_o,
    output logic        core_ctrl_firstfetch_o,
    output logic        is_decoding_o,

    // Interface to IF stage
    input  logic [N_HWLP-1:0] hwlp_dec_cnt_i,
    input  logic              is_hwlp_i,
    input  logic              instr_valid_i,
    input  logic       [31:0] instr_rdata_i,      // comes from pipeline of IF stage
    output logic              instr_req_o,


    // Jumps and branches
    output logic        branch_in_ex_o,
    input  logic        branch_decision_i,
    output logic [31:0] jump_target_o,

    // IF and ID stage signals
    output logic        clear_instr_valid_o,
    output logic        pc_set_o,
    output logic [2:0]  pc_mux_o,
    output logic [2:0]  exc_pc_mux_o,
    output logic        trap_addr_mux_o,

    input  logic        illegal_c_insn_i,
    input  logic        is_compressed_i,
    input  logic        is_fetch_failed_i,

    input  logic [31:0] pc_if_i,
    input  logic [31:0] pc_id_i,

    // Stalls
    output logic        halt_if_o,      // controller requests a halt of the IF stage

    output logic        id_ready_o,     // ID stage is ready for the next instruction
    input  logic        ex_ready_i,     // EX stage is ready for the next instruction
    input  logic        wb_ready_i,     // WB stage is ready for the next instruction

    output logic        id_valid_o,     // ID stage is done
    input  logic        ex_valid_i,     // EX stage is done

    // Pipeline ID/EX
    output logic [31:0] pc_ex_o,

    output logic [31:0] alu_operand_a_ex_o,
    output logic [31:0] alu_operand_b_ex_o,
    output logic [31:0] alu_operand_c_ex_o,
    output logic [ 4:0] bmask_a_ex_o,
    output logic [ 4:0] bmask_b_ex_o,
    output logic [ 1:0] imm_vec_ext_ex_o,
    output logic [ 1:0] alu_vec_mode_ex_o,

    output logic [5:0]  regfile_waddr_ex_o,
    output logic        regfile_we_ex_o,

    output logic [5:0]  regfile_alu_waddr_ex_o,
    output logic        regfile_alu_we_ex_o,

    // ALU
    output logic        alu_en_ex_o,
    output logic [ALU_OP_WIDTH-1:0] alu_operator_ex_o,
    output logic        alu_is_clpx_ex_o,
    output logic        alu_is_subrot_ex_o,
    output logic [ 1:0] alu_clpx_shift_ex_o,


    // MUL
    output logic [ 2:0] mult_operator_ex_o,
    output logic [31:0] mult_operand_a_ex_o,
    output logic [31:0] mult_operand_b_ex_o,
    output logic [31:0] mult_operand_c_ex_o,
    output logic        mult_en_ex_o,
    output logic        mult_sel_subword_ex_o,
    output logic [ 1:0] mult_signed_mode_ex_o,
    output logic [ 4:0] mult_imm_ex_o,

    output logic [31:0] mult_dot_op_a_ex_o,
    output logic [31:0] mult_dot_op_b_ex_o,
    output logic [31:0] mult_dot_op_c_ex_o,
    output logic [ 1:0] mult_dot_signed_ex_o,
    output logic        mult_is_clpx_ex_o,
    output logic [ 1:0] mult_clpx_shift_ex_o,
    output logic        mult_clpx_img_ex_o,

    // APU
    output logic                        apu_en_ex_o,
    output logic [WAPUTYPE-1:0]         apu_type_ex_o,
    output logic [APU_WOP_CPU-1:0]      apu_op_ex_o,
    output logic [1:0]                  apu_lat_ex_o,
    output logic [APU_NARGS_CPU-1:0][31:0]                 apu_operands_ex_o,
    output logic [APU_NDSFLAGS_CPU-1:0] apu_flags_ex_o,
    output logic [5:0]                  apu_waddr_ex_o,

    output logic [2:0][5:0]            apu_read_regs_o,
    output logic [2:0]                 apu_read_regs_valid_o,
    input  logic                       apu_read_dep_i,
    output logic [1:0][5:0]            apu_write_regs_o,
    output logic [1:0]                 apu_write_regs_valid_o,
    input  logic                       apu_write_dep_i,
    output logic                       apu_perf_dep_o,
    input  logic                       apu_busy_i,
    input  logic [C_RM-1:0]            frm_i,

    // CSR ID/EX
    output logic        csr_access_ex_o,
    output logic [1:0]  csr_op_ex_o,
    input  PrivLvl_t    current_priv_lvl_i,
    output logic        csr_irq_sec_o,
    output logic [5:0]  csr_cause_o,
    output logic        csr_save_if_o,
    output logic        csr_save_id_o,
    output logic        csr_save_ex_o,
    output logic        csr_restore_mret_id_o,
    output logic        csr_restore_uret_id_o,

    output logic        csr_restore_dret_id_o,

    output logic        csr_save_cause_o,

    // hwloop signals
    output logic [N_HWLP-1:0] [31:0] hwlp_start_o,
    output logic [N_HWLP-1:0] [31:0] hwlp_end_o,
    output logic [N_HWLP-1:0] [31:0] hwlp_cnt_o,

    // hwloop signals from CS register
    input  logic   [N_HWLP_BITS-1:0] csr_hwlp_regid_i,
    input  logic               [2:0] csr_hwlp_we_i,
    input  logic              [31:0] csr_hwlp_data_i,

    // Interface to load store unit
    output logic        data_req_ex_o,
    output logic        data_we_ex_o,
    output logic [1:0]  data_type_ex_o,
    output logic [1:0]  data_sign_ext_ex_o,
    output logic [1:0]  data_reg_offset_ex_o,
    output logic        data_load_event_ex_o,

    output logic        data_misaligned_ex_o,

    output logic        prepost_useincr_ex_o,
    input  logic        data_misaligned_i,
    input  logic        data_err_i,
    output logic        data_err_ack_o,
    // Interrupt signals
    input  logic        irq_i,
    input  logic        irq_sec_i,
    input  logic [4:0]  irq_id_i,
    input  logic        m_irq_enable_i,
    input  logic        u_irq_enable_i,
    output logic        irq_ack_o,
    output logic [4:0]  irq_id_o,
    output logic [5:0]  exc_cause_o,

    // Debug Signal
    output logic        debug_mode_o,
    output logic [2:0]  debug_cause_o,
    output logic        debug_csr_save_o,
    input  logic        debug_req_i,
    input  logic        debug_single_step_i,
    input  logic        debug_ebreakm_i,
    input  logic        debug_ebreaku_i,

    // Forward Signals
    input  logic [5:0]  regfile_waddr_wb_i,
    input  logic        regfile_we_wb_i,
    input  logic [31:0] regfile_wdata_wb_i, // From wb_stage: selects data from data memory, ex_stage result and sp rdata

    input  logic [5:0]  regfile_alu_waddr_fw_i,
    input  logic        regfile_alu_we_fw_i,
    input  logic [31:0] regfile_alu_wdata_fw_i,

    // from ALU
    input  logic        mult_multicycle_i,    // when we need multiple cycles in the multiplier and use op c as storage

    // Performance Counters
    output logic        perf_jump_o,          // we are executing a jump instruction
    output logic        perf_jr_stall_o,      // jump-register-hazard
    output logic        perf_ld_stall_o,      // load-use-hazard
    output logic        perf_pipeline_stall_o //extra cycles from elw
);

  logic [31:0] instr;

  // Decoder/Controller ID stage internal signals
  logic        deassert_we;

  logic        illegal_insn_dec;
  logic        ebrk_insn;
  logic        mret_insn_dec;
  logic        uret_insn_dec;

  logic        dret_insn_dec;

  logic        ecall_insn_dec;
  logic        pipe_flush_dec;

  logic        fencei_insn_dec;

  logic        rega_used_dec;
  logic        regb_used_dec;
  logic        regc_used_dec;

  logic        branch_taken_ex;
  logic [1:0]  jump_in_id;
  logic [1:0]  jump_in_dec;

  logic        misaligned_stall;
  logic        jr_stall;
  logic        load_stall;
  logic        csr_apu_stall;
  logic        instr_multicycle;
  logic        hwloop_mask;
  logic        halt_id;


  // Immediate decoding and sign extension
  logic [31:0] imm_i_type;
  logic [31:0] imm_iz_type;
  logic [31:0] imm_s_type;
  logic [31:0] imm_sb_type;
  logic [31:0] imm_u_type;
  logic [31:0] imm_uj_type;
  logic [31:0] imm_z_type;
  logic [31:0] imm_s2_type;
  logic [31:0] imm_bi_type;
  logic [31:0] imm_s3_type;
  logic [31:0] imm_vs_type;
  logic [31:0] imm_vu_type;
  logic [31:0] imm_shuffleb_type;
  logic [31:0] imm_shuffleh_type;
  logic [31:0] imm_shuffle_type;
  logic [31:0] imm_clip_type;

  logic [31:0] imm_a;       // contains the immediate for operand b
  logic [31:0] imm_b;       // contains the immediate for operand b

  logic [31:0] jump_target;       // calculated jump target (-> EX -> IF)



  // Signals running between controller and exception controller
  logic       irq_req_ctrl, irq_sec_ctrl;
  logic [4:0] irq_id_ctrl;
  logic       exc_ack, exc_kill;// handshake

  // Register file interface
  logic [5:0]  regfile_addr_ra_id;
  logic [5:0]  regfile_addr_rb_id;
  logic [5:0]  regfile_addr_rc_id;

  logic        regfile_fp_a;
  logic        regfile_fp_b;
  logic        regfile_fp_c;
  logic        regfile_fp_d;

  logic        fregfile_ena; // whether the fp register file is enabled

  logic [5:0]  regfile_waddr_id;
  logic [5:0]  regfile_alu_waddr_id;
  logic        regfile_alu_we_id, regfile_alu_we_dec_id;

  logic [31:0] regfile_data_ra_id;
  logic [31:0] regfile_data_rb_id;
  logic [31:0] regfile_data_rc_id;

  // ALU Control
  logic        alu_en;
  logic [ALU_OP_WIDTH-1:0] alu_operator;
  logic [2:0]  alu_op_a_mux_sel;
  logic [2:0]  alu_op_b_mux_sel;
  logic [1:0]  alu_op_c_mux_sel;
  logic [1:0]  regc_mux;

  logic [0:0]  imm_a_mux_sel;
  logic [3:0]  imm_b_mux_sel;
  logic [1:0]  jump_target_mux_sel;

  // Multiplier Control
  logic [2:0]  mult_operator;    // multiplication operation selection
  logic        mult_en;          // multiplication is used instead of ALU
  logic        mult_int_en;      // use integer multiplier
  logic        mult_sel_subword; // Select a subword when doing multiplications
  logic [1:0]  mult_signed_mode; // Signed mode multiplication at the output of the controller, and before the pipe registers
  logic        mult_dot_en;      // use dot product
  logic [1:0]  mult_dot_signed;  // Signed mode dot products (can be mixed types)

  // FPU signals
  logic [C_FPNEW_FMTBITS-1:0]  fpu_src_fmt;
  logic [C_FPNEW_FMTBITS-1:0]  fpu_dst_fmt;
  logic [C_FPNEW_IFMTBITS-1:0] fpu_int_fmt;

  // APU signals
  logic                        apu_en;
  logic [WAPUTYPE-1:0]         apu_type;
  logic [APU_WOP_CPU-1:0]      apu_op;
  logic [1:0]                  apu_lat;
  logic [APU_NARGS_CPU-1:0][31:0]                 apu_operands;
  logic [APU_NDSFLAGS_CPU-1:0] apu_flags;
  logic [5:0]                  apu_waddr;

  logic [2:0][5:0]            apu_read_regs;
  logic [2:0]                 apu_read_regs_valid;
  logic [1:0][5:0]            apu_write_regs;
  logic [1:0]                 apu_write_regs_valid;

  logic [WAPUTYPE-1:0]        apu_flags_src;
  logic                       apu_stall;
  logic [2:0]                 fp_rnd_mode;

  // Register Write Control
  logic        regfile_we_id;
  logic        regfile_alu_waddr_mux_sel;

  // Data Memory Control
  logic        data_we_id;
  logic [1:0]  data_type_id;
  logic [1:0]  data_sign_ext_id;
  logic [1:0]  data_reg_offset_id;
  logic        data_req_id;
  logic        data_load_event_id;

  // hwloop signals
  logic [N_HWLP_BITS-1:0] hwloop_regid, hwloop_regid_int;
  logic             [2:0] hwloop_we, hwloop_we_int, hwloop_we_masked;
  logic                   hwloop_target_mux_sel;
  logic                   hwloop_start_mux_sel;
  logic                   hwloop_cnt_mux_sel;

  logic            [31:0] hwloop_target;
  logic            [31:0] hwloop_start, hwloop_start_int;
  logic            [31:0] hwloop_end;
  logic            [31:0] hwloop_cnt, hwloop_cnt_int;

  logic                   hwloop_valid;

  // CSR control
  logic        csr_access;
  logic [1:0]  csr_op;
  logic        csr_status;

  logic        prepost_useincr;

  // Forwarding
  logic [1:0]  operand_a_fw_mux_sel;
  logic [1:0]  operand_b_fw_mux_sel;
  logic [1:0]  operand_c_fw_mux_sel;
  logic [31:0] operand_a_fw_id;
  logic [31:0] operand_b_fw_id;
  logic [31:0] operand_c_fw_id;

  logic [31:0] operand_b, operand_b_vec;
  logic [31:0] operand_c, operand_c_vec;

  logic [31:0] alu_operand_a;
  logic [31:0] alu_operand_b;
  logic [31:0] alu_operand_c;

  // Immediates for ID
  logic [0:0]  bmask_a_mux;
  logic [1:0]  bmask_b_mux;
  logic        alu_bmask_a_mux_sel;
  logic        alu_bmask_b_mux_sel;
  logic [0:0]  mult_imm_mux;

  logic [ 4:0] bmask_a_id_imm;
  logic [ 4:0] bmask_b_id_imm;
  logic [ 4:0] bmask_a_id;
  logic [ 4:0] bmask_b_id;
  logic [ 1:0] imm_vec_ext_id;
  logic [ 4:0] mult_imm_id;

  logic [ 1:0] alu_vec_mode;
  logic        scalar_replication;
  logic        scalar_replication_c;

  // Forwarding detection signals
  logic        reg_d_ex_is_reg_a_id;
  logic        reg_d_ex_is_reg_b_id;
  logic        reg_d_ex_is_reg_c_id;
  logic        reg_d_wb_is_reg_a_id;
  logic        reg_d_wb_is_reg_b_id;
  logic        reg_d_wb_is_reg_c_id;
  logic        reg_d_alu_is_reg_a_id;
  logic        reg_d_alu_is_reg_b_id;
  logic        reg_d_alu_is_reg_c_id;

  logic        is_clpx, is_subrot;

  logic        mret_dec;
  logic        uret_dec;
  logic        dret_dec;

  assign instr = instr_rdata_i;

  // immediate extraction and sign extension
  assign imm_i_type  = { {20 {instr[31]}}, instr[31:20] };
  assign imm_iz_type = {            20'b0, instr[31:20] };
  assign imm_s_type  = { {20 {instr[31]}}, instr[31:25], instr[11:7] };
  assign imm_sb_type = { {19 {instr[31]}}, instr[31], instr[7], instr[30:25], instr[11:8], 1'b0 };
  assign imm_u_type  = { instr[31:12], 12'b0 };
  assign imm_uj_type = { {12 {instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0 };

  // immediate for CSR manipulatin (zero extended)
  assign imm_z_type  = { 27'b0, instr[`REG_S1] };

  assign imm_s2_type = { 27'b0, instr[24:20] };
  assign imm_bi_type = { {27{instr[24]}}, instr[24:20] };
  assign imm_s3_type = { 27'b0, instr[29:25] };
  assign imm_vs_type = { {26 {instr[24]}}, instr[24:20], instr[25] };
  assign imm_vu_type = { 26'b0, instr[24:20], instr[25] };

  // same format as rS2 for shuffle needs, expands immediate
  assign imm_shuffleb_type = {6'b0, instr[28:27], 6'b0, instr[24:23], 6'b0, instr[22:21], 6'b0, instr[20], instr[25]};
  assign imm_shuffleh_type = {15'h0, instr[20], 15'h0, instr[25]};

  // clipping immediate, uses a small barrel shifter to pre-process the
  // immediate and an adder to subtract 1
  // The end result is a mask that has 1's set in the lower part
  // TODO: check if this can be shared with the bit-manipulation unit
  assign imm_clip_type    = (32'h1 << instr[24:20]) - 1;

  //-----------------------------------------------------------------------------
  //-- FPU Register file enable:
  //-- Taken from Cluster Config Reg if FPU reg file exists, or always disabled
  //-----------------------------------------------------------------------------
  assign fregfile_ena = FPU && !Zfinx ? ~fregfile_disable_i : '0;

  //---------------------------------------------------------------------------
  // source register selection regfile_fp_x=1 <=> REG_x is a FP-register
  //---------------------------------------------------------------------------
  assign regfile_addr_ra_id = {fregfile_ena & regfile_fp_a, instr[`REG_S1]};
  assign regfile_addr_rb_id = {fregfile_ena & regfile_fp_b, instr[`REG_S2]};

  // register C mux
  always_comb begin
    unique case (regc_mux)
      REGC_ZERO:  regfile_addr_rc_id = '0;
      REGC_RD:    regfile_addr_rc_id = {fregfile_ena & regfile_fp_c, instr[`REG_D]};
      REGC_S1:    regfile_addr_rc_id = {fregfile_ena & regfile_fp_c, instr[`REG_S1]};
      REGC_S4:    regfile_addr_rc_id = {fregfile_ena & regfile_fp_c, instr[`REG_S4]};
      default:    regfile_addr_rc_id = '0;
    endcase
  end

  //---------------------------------------------------------------------------
  // destination registers regfile_fp_d=1 <=> REG_D is a FP-register
  //---------------------------------------------------------------------------
  assign regfile_waddr_id = {fregfile_ena & regfile_fp_d, instr[`REG_D]};

  // Second Register Write Address Selection
  // Used for prepost load/store and multiplier
  assign regfile_alu_waddr_id = regfile_alu_waddr_mux_sel ?
                                regfile_waddr_id : regfile_addr_ra_id;

  // Forwarding control signals
  assign reg_d_ex_is_reg_a_id  = (regfile_waddr_ex_o     == regfile_addr_ra_id) && (rega_used_dec == 1'b1) && (regfile_addr_ra_id != '0);
  assign reg_d_ex_is_reg_b_id  = (regfile_waddr_ex_o     == regfile_addr_rb_id) && (regb_used_dec == 1'b1) && (regfile_addr_rb_id != '0);
  assign reg_d_ex_is_reg_c_id  = (regfile_waddr_ex_o     == regfile_addr_rc_id) && (regc_used_dec == 1'b1) && (regfile_addr_rc_id != '0);
  assign reg_d_wb_is_reg_a_id  = (regfile_waddr_wb_i     == regfile_addr_ra_id) && (rega_used_dec == 1'b1) && (regfile_addr_ra_id != '0);
  assign reg_d_wb_is_reg_b_id  = (regfile_waddr_wb_i     == regfile_addr_rb_id) && (regb_used_dec == 1'b1) && (regfile_addr_rb_id != '0);
  assign reg_d_wb_is_reg_c_id  = (regfile_waddr_wb_i     == regfile_addr_rc_id) && (regc_used_dec == 1'b1) && (regfile_addr_rc_id != '0);
  assign reg_d_alu_is_reg_a_id = (regfile_alu_waddr_fw_i == regfile_addr_ra_id) && (rega_used_dec == 1'b1) && (regfile_addr_ra_id != '0);
  assign reg_d_alu_is_reg_b_id = (regfile_alu_waddr_fw_i == regfile_addr_rb_id) && (regb_used_dec == 1'b1) && (regfile_addr_rb_id != '0);
  assign reg_d_alu_is_reg_c_id = (regfile_alu_waddr_fw_i == regfile_addr_rc_id) && (regc_used_dec == 1'b1) && (regfile_addr_rc_id != '0);


  // kill instruction in the IF/ID stage by setting the instr_valid_id control
  // signal to 0 for instructions that are done
  assign clear_instr_valid_o = id_ready_o | halt_id | branch_taken_ex;

  assign branch_taken_ex     = branch_in_ex_o & branch_decision_i;


  assign mult_en = mult_int_en | mult_dot_en;

  ///////////////////////////////////////////////
  //  _   ___        ___     ___   ___  ____   //
  // | | | \ \      / / |   / _ \ / _ \|  _ \  //
  // | |_| |\ \ /\ / /| |  | | | | | | | |_) | //
  // |  _  | \ V  V / | |__| |_| | |_| |  __/  //
  // |_| |_|  \_/\_/  |_____\___/ \___/|_|     //
  //                                           //
  ///////////////////////////////////////////////

  // hwloop register id
  assign hwloop_regid_int = instr[7];   // rd contains hwloop register id

  // hwloop target mux
  always_comb begin
    case (hwloop_target_mux_sel)
      1'b0: hwloop_target = pc_id_i + {imm_iz_type[30:0], 1'b0};
      1'b1: hwloop_target = pc_id_i + {imm_z_type[30:0], 1'b0};
    endcase
  end

  // hwloop start mux
  always_comb begin
    case (hwloop_start_mux_sel)
      1'b0: hwloop_start_int = hwloop_target;   // for PC + I imm
      1'b1: hwloop_start_int = pc_if_i;         // for next PC
    endcase
  end


  // hwloop cnt mux
  always_comb begin : hwloop_cnt_mux
    case (hwloop_cnt_mux_sel)
      1'b0: hwloop_cnt_int = imm_iz_type;
      1'b1: hwloop_cnt_int = operand_a_fw_id;
    endcase;
  end

  /*
    when hwloop_mask is 1, the controller is about to take an interrupt
    the xEPC is going to have the hwloop instruction PC, therefore, do not update the
    hwloop registers to make clear that the instruction hasn't been executed.
    Although it may not be a HW bugs causing uninteded behaviours,
    it helps verifications processes when checking the hwloop regs
  */
  assign hwloop_we_masked = hwloop_we_int & ~{3{hwloop_mask}} & {3{id_ready_o}};

  // multiplex between access from instructions and access via CSR registers
  assign hwloop_start = hwloop_we_masked[0] ? hwloop_start_int : csr_hwlp_data_i;
  assign hwloop_end   = hwloop_we_masked[1] ? hwloop_target    : csr_hwlp_data_i;
  assign hwloop_cnt   = hwloop_we_masked[2] ? hwloop_cnt_int   : csr_hwlp_data_i;
  assign hwloop_regid = (|hwloop_we_masked) ? hwloop_regid_int : csr_hwlp_regid_i;
  assign hwloop_we    = (|hwloop_we_masked) ? hwloop_we_masked  : csr_hwlp_we_i;


  //////////////////////////////////////////////////////////////////
  //      _                         _____                    _    //
  //     | |_   _ _ __ ___  _ __   |_   _|_ _ _ __ __ _  ___| |_  //
  //  _  | | | | | '_ ` _ \| '_ \    | |/ _` | '__/ _` |/ _ \ __| //
  // | |_| | |_| | | | | | | |_) |   | | (_| | | | (_| |  __/ |_  //
  //  \___/ \__,_|_| |_| |_| .__/    |_|\__,_|_|  \__, |\___|\__| //
  //                       |_|                    |___/           //
  //////////////////////////////////////////////////////////////////

  always_comb begin : jump_target_mux
    unique case (jump_target_mux_sel)
      JT_JAL:  jump_target = pc_id_i + imm_uj_type;
      JT_COND: jump_target = pc_id_i + imm_sb_type;

      // JALR: Cannot forward RS1, since the path is too long
      JT_JALR: jump_target = regfile_data_ra_id + imm_i_type;
      default:  jump_target = regfile_data_ra_id + imm_i_type;
    endcase
  end

  assign jump_target_o = jump_target;


  ////////////////////////////////////////////////////////
  //   ___                                 _      _     //
  //  / _ \ _ __   ___ _ __ __ _ _ __   __| |    / \    //
  // | | | | '_ \ / _ \ '__/ _` | '_ \ / _` |   / _ \   //
  // | |_| | |_) |  __/ | | (_| | | | | (_| |  / ___ \  //
  //  \___/| .__/ \___|_|  \__,_|_| |_|\__,_| /_/   \_\ //
  //       |_|                                          //
  ////////////////////////////////////////////////////////

  // ALU_Op_a Mux
  always_comb begin : alu_operand_a_mux
    case (alu_op_a_mux_sel)
      OP_A_REGA_OR_FWD:  alu_operand_a = operand_a_fw_id;
      OP_A_REGB_OR_FWD:  alu_operand_a = operand_b_fw_id;
      OP_A_REGC_OR_FWD:  alu_operand_a = operand_c_fw_id;
      OP_A_CURRPC:       alu_operand_a = pc_id_i;
      OP_A_IMM:          alu_operand_a = imm_a;
      default:           alu_operand_a = operand_a_fw_id;
    endcase; // case (alu_op_a_mux_sel)
  end

  always_comb begin : immediate_a_mux
    unique case (imm_a_mux_sel)
      IMMA_Z:      imm_a = imm_z_type;
      IMMA_ZERO:   imm_a = '0;
      default:     imm_a = '0;
    endcase
  end

  // Operand a forwarding mux
  always_comb begin : operand_a_fw_mux
    case (operand_a_fw_mux_sel)
      SEL_FW_EX:    operand_a_fw_id = regfile_alu_wdata_fw_i;
      SEL_FW_WB:    operand_a_fw_id = regfile_wdata_wb_i;
      SEL_REGFILE:  operand_a_fw_id = regfile_data_ra_id;
      default:      operand_a_fw_id = regfile_data_ra_id;
    endcase; // case (operand_a_fw_mux_sel)
  end

  //////////////////////////////////////////////////////
  //   ___                                 _   ____   //
  //  / _ \ _ __   ___ _ __ __ _ _ __   __| | | __ )  //
  // | | | | '_ \ / _ \ '__/ _` | '_ \ / _` | |  _ \  //
  // | |_| | |_) |  __/ | | (_| | | | | (_| | | |_) | //
  //  \___/| .__/ \___|_|  \__,_|_| |_|\__,_| |____/  //
  //       |_|                                        //
  //////////////////////////////////////////////////////

  // Immediate Mux for operand B
  // TODO: check if sign-extension stuff works well here, maybe able to save
  // some area here
  always_comb begin : immediate_b_mux
    unique case (imm_b_mux_sel)
      IMMB_I:      imm_b = imm_i_type;
      IMMB_S:      imm_b = imm_s_type;
      IMMB_U:      imm_b = imm_u_type;
      IMMB_PCINCR: imm_b = (is_compressed_i && (~data_misaligned_i)) ? 32'h2 : 32'h4;
      IMMB_S2:     imm_b = imm_s2_type;
      IMMB_BI:     imm_b = imm_bi_type;
      IMMB_S3:     imm_b = imm_s3_type;
      IMMB_VS:     imm_b = imm_vs_type;
      IMMB_VU:     imm_b = imm_vu_type;
      IMMB_SHUF:   imm_b = imm_shuffle_type;
      IMMB_CLIP:   imm_b = {1'b0, imm_clip_type[31:1]};
      default:     imm_b = imm_i_type;
    endcase
  end

  // ALU_Op_b Mux
  always_comb begin : alu_operand_b_mux
    case (alu_op_b_mux_sel)
      OP_B_REGA_OR_FWD:  operand_b = operand_a_fw_id;
      OP_B_REGB_OR_FWD:  operand_b = operand_b_fw_id;
      OP_B_REGC_OR_FWD:  operand_b = operand_c_fw_id;
      OP_B_IMM:          operand_b = imm_b;
      OP_B_BMASK:        operand_b = $unsigned(operand_b_fw_id[4:0]);
      default:           operand_b = operand_b_fw_id;
    endcase // case (alu_op_b_mux_sel)
  end


  // scalar replication for operand B and shuffle type
  always_comb begin
    if (alu_vec_mode == VEC_MODE8) begin
      operand_b_vec    = {4{operand_b[7:0]}};
      imm_shuffle_type = imm_shuffleb_type;
    end else begin
      operand_b_vec    = {2{operand_b[15:0]}};
      imm_shuffle_type = imm_shuffleh_type;
    end
  end

  // choose normal or scalar replicated version of operand b
  assign alu_operand_b = (scalar_replication == 1'b1) ? operand_b_vec : operand_b;


  // Operand b forwarding mux
  always_comb begin : operand_b_fw_mux
    case (operand_b_fw_mux_sel)
      SEL_FW_EX:    operand_b_fw_id = regfile_alu_wdata_fw_i;
      SEL_FW_WB:    operand_b_fw_id = regfile_wdata_wb_i;
      SEL_REGFILE:  operand_b_fw_id = regfile_data_rb_id;
      default:      operand_b_fw_id = regfile_data_rb_id;
    endcase; // case (operand_b_fw_mux_sel)
  end


  //////////////////////////////////////////////////////
  //   ___                                 _    ____  //
  //  / _ \ _ __   ___ _ __ __ _ _ __   __| |  / ___| //
  // | | | | '_ \ / _ \ '__/ _` | '_ \ / _` | | |     //
  // | |_| | |_) |  __/ | | (_| | | | | (_| | | |___  //
  //  \___/| .__/ \___|_|  \__,_|_| |_|\__,_|  \____| //
  //       |_|                                        //
  //////////////////////////////////////////////////////

  // ALU OP C Mux
  always_comb begin : alu_operand_c_mux
    case (alu_op_c_mux_sel)
      OP_C_REGC_OR_FWD:  operand_c = operand_c_fw_id;
      OP_C_REGB_OR_FWD:  operand_c = operand_b_fw_id;
      OP_C_JT:           operand_c = jump_target;
      default:           operand_c = operand_c_fw_id;
    endcase // case (alu_op_c_mux_sel)
  end


  // scalar replication for operand C and shuffle type
  always_comb begin
    if (alu_vec_mode == VEC_MODE8) begin
      operand_c_vec    = {4{operand_c[7:0]}};
    end else begin
      operand_c_vec    = {2{operand_c[15:0]}};
    end
  end

  // choose normal or scalar replicated version of operand b
  assign alu_operand_c = (scalar_replication_c == 1'b1) ? operand_c_vec : operand_c;


  // Operand c forwarding mux
  always_comb begin : operand_c_fw_mux
    case (operand_c_fw_mux_sel)
      SEL_FW_EX:    operand_c_fw_id = regfile_alu_wdata_fw_i;
      SEL_FW_WB:    operand_c_fw_id = regfile_wdata_wb_i;
      SEL_REGFILE:  operand_c_fw_id = regfile_data_rc_id;
      default:      operand_c_fw_id = regfile_data_rc_id;
    endcase; // case (operand_c_fw_mux_sel)
  end


  ///////////////////////////////////////////////////////////////////////////
  //  ___                              _ _       _              ___ ____   //
  // |_ _|_ __ ___  _ __ ___   ___  __| (_) __ _| |_ ___  ___  |_ _|  _ \  //
  //  | || '_ ` _ \| '_ ` _ \ / _ \/ _` | |/ _` | __/ _ \/ __|  | || | | | //
  //  | || | | | | | | | | | |  __/ (_| | | (_| | ||  __/\__ \  | || |_| | //
  // |___|_| |_| |_|_| |_| |_|\___|\__,_|_|\__,_|\__\___||___/ |___|____/  //
  //                                                                       //
  ///////////////////////////////////////////////////////////////////////////

  always_comb begin
    unique case (bmask_a_mux)
      BMASK_A_ZERO: bmask_a_id_imm = '0;
      BMASK_A_S3:   bmask_a_id_imm = imm_s3_type[4:0];
      default:      bmask_a_id_imm = '0;
    endcase
  end
  always_comb begin
    unique case (bmask_b_mux)
      BMASK_B_ZERO: bmask_b_id_imm = '0;
      BMASK_B_ONE:  bmask_b_id_imm = 5'd1;
      BMASK_B_S2:   bmask_b_id_imm = imm_s2_type[4:0];
      BMASK_B_S3:   bmask_b_id_imm = imm_s3_type[4:0];
      default:      bmask_b_id_imm = '0;
    endcase
  end

  always_comb begin
    unique case (alu_bmask_a_mux_sel)
      BMASK_A_IMM: bmask_a_id = bmask_a_id_imm;
      BMASK_A_REG: bmask_a_id = operand_b_fw_id[9:5];
      default:     bmask_a_id = bmask_a_id_imm;
    endcase
  end
  always_comb begin
    unique case (alu_bmask_b_mux_sel)
      BMASK_B_IMM: bmask_b_id = bmask_b_id_imm;
      BMASK_B_REG: bmask_b_id = operand_b_fw_id[4:0];
      default:     bmask_b_id = bmask_b_id_imm;
    endcase
  end

  assign imm_vec_ext_id = imm_vu_type[1:0];


  always_comb begin
    unique case (mult_imm_mux)
      MIMM_ZERO: mult_imm_id = '0;
      MIMM_S3:   mult_imm_id = imm_s3_type[4:0];
      default:   mult_imm_id = '0;
    endcase
  end

  /////////////////////////////
  // APU operand assignment  //
  /////////////////////////////
  // read regs
  generate
    if (APU == 1) begin : apu_op_preparation

      if (APU_NARGS_CPU >= 1)
       assign apu_operands[0] = alu_operand_a;
      if (APU_NARGS_CPU >= 2)
       assign apu_operands[1] = alu_operand_b;
      if (APU_NARGS_CPU >= 3)
       assign apu_operands[2] = alu_operand_c;

      // write reg
      assign apu_waddr = regfile_alu_waddr_id;

      // flags
      always_comb begin
        unique case (apu_flags_src)
          APU_FLAGS_INT_MULT:
            apu_flags = {7'h0 , mult_imm_id, mult_signed_mode, mult_sel_subword};
          APU_FLAGS_DSP_MULT:
            apu_flags = {13'h0, mult_dot_signed};
          APU_FLAGS_FP:
            if (FPU == 1)
              apu_flags = fp_rnd_mode;
            else
              apu_flags = '0;
          APU_FLAGS_FPNEW:
            if (FPU == 1)
              apu_flags = {fpu_int_fmt, fpu_src_fmt, fpu_dst_fmt, fp_rnd_mode};
            else
              apu_flags = '0;
          default:
            apu_flags = '0;
        endcase
       end

      // dependency checks
      always_comb begin
        unique case (alu_op_a_mux_sel)
          OP_A_REGA_OR_FWD: begin
             apu_read_regs[0]        = regfile_addr_ra_id;
             apu_read_regs_valid [0] = 1'b1;
          end // OP_A_REGA_OR_FWD:
          OP_A_REGB_OR_FWD: begin
             apu_read_regs[0]        = regfile_addr_rb_id;
             apu_read_regs_valid[0]  = 1'b1;
          end
          default: begin
             apu_read_regs[0]        = regfile_addr_ra_id;
             apu_read_regs_valid [0] = 1'b0;
          end
        endcase
       end

      always_comb begin
        unique case (alu_op_b_mux_sel)
          OP_B_REGA_OR_FWD: begin
             apu_read_regs[1]       = regfile_addr_ra_id;
             apu_read_regs_valid[1] = 1'b1;
          end
          OP_B_REGB_OR_FWD: begin
             apu_read_regs[1]       = regfile_addr_rb_id;
             apu_read_regs_valid[1] = 1'b1;
          end
          OP_B_REGC_OR_FWD: begin
             apu_read_regs[1]       = regfile_addr_rc_id;
             apu_read_regs_valid[1] = 1'b1;
          end
          default: begin
             apu_read_regs[1]        = regfile_addr_rb_id;
             apu_read_regs_valid [1] = 1'b0;
          end
        endcase
       end

      always_comb begin
        unique case (alu_op_c_mux_sel)
          OP_C_REGB_OR_FWD: begin
             apu_read_regs[2]       = regfile_addr_rb_id;
             apu_read_regs_valid[2] = 1'b1;
          end
          OP_C_REGC_OR_FWD: begin
             apu_read_regs[2]       = regfile_addr_rc_id;
             apu_read_regs_valid[2] = 1'b1;
          end
          default: begin
             apu_read_regs[2]        = regfile_addr_rc_id;
             apu_read_regs_valid [2] = 1'b0;
          end
        endcase
       end

      assign apu_write_regs[0]        = regfile_alu_waddr_id;
      assign apu_write_regs_valid [0] = regfile_alu_we_id;

      assign apu_write_regs[1]        = regfile_waddr_id;
      assign apu_write_regs_valid[1]  = regfile_we_id;

      assign apu_read_regs_o          = apu_read_regs;
      assign apu_read_regs_valid_o    = apu_read_regs_valid;

      assign apu_write_regs_o         = apu_write_regs;
      assign apu_write_regs_valid_o   = apu_write_regs_valid;
    end else begin
      for (genvar i=0; i<APU_NARGS_CPU; i++) begin : apu_tie_off
        assign apu_operands[i]       = '0;
      end
      assign apu_waddr               = '0;
      assign apu_flags               = '0;
      assign apu_write_regs_o        = '0;
      assign apu_read_regs_o         = '0;
      assign apu_write_regs_valid_o  = '0;
      assign apu_read_regs_valid_o   = '0;
    end
  endgenerate

  assign apu_perf_dep_o      = apu_stall;
  // stall when we access the CSR after a multicycle APU instruction
  assign csr_apu_stall       = (csr_access & (apu_en_ex_o & (apu_lat_ex_o[1] == 1'b1) | apu_busy_i));

`ifndef SYNTHESIS
  always_comb begin
    if (FPU==1 && SHARED_FP!=1) begin
      assert (APU_NDSFLAGS_CPU >= C_RM+2*C_FPNEW_FMTBITS+C_FPNEW_IFMTBITS)
        else $error("[apu] APU_NDSFLAGS_CPU APU flagbits is smaller than %0d", C_RM+2*C_FPNEW_FMTBITS+C_FPNEW_IFMTBITS);
    end
  end
`endif


  /////////////////////////////////////////////////////////
  //  ____  _____ ____ ___ ____ _____ _____ ____  ____   //
  // |  _ \| ____/ ___|_ _/ ___|_   _| ____|  _ \/ ___|  //
  // | |_) |  _|| |  _ | |\___ \ | | |  _| | |_) \___ \  //
  // |  _ <| |__| |_| || | ___) || | | |___|  _ < ___) | //
  // |_| \_\_____\____|___|____/ |_| |_____|_| \_\____/  //
  //                                                     //
  /////////////////////////////////////////////////////////

  register_file_test_wrap
  #(
    .ADDR_WIDTH(6),
    .FPU(FPU),
    .Zfinx(Zfinx)
  )
  registers_i
  (
    .clk                ( clk                ),
    .rst_n              ( rst_n              ),

    .test_en_i          ( test_en_i          ),

    // Read port a
    .raddr_a_i          ( regfile_addr_ra_id ),
    .rdata_a_o          ( regfile_data_ra_id ),

    // Read port b
    .raddr_b_i          ( regfile_addr_rb_id ),
    .rdata_b_o          ( regfile_data_rb_id ),

    // Read port c
    .raddr_c_i          ( regfile_addr_rc_id ),
    .rdata_c_o          ( regfile_data_rc_id ),

    // Write port a
    .waddr_a_i          ( regfile_waddr_wb_i ),
    .wdata_a_i          ( regfile_wdata_wb_i ),
    .we_a_i             ( regfile_we_wb_i    ),

    // Write port b
    .waddr_b_i          ( regfile_alu_waddr_fw_i ),
    .wdata_b_i          ( regfile_alu_wdata_fw_i ),
    .we_b_i             ( regfile_alu_we_fw_i ),

     // BIST ENABLE
     .BIST        ( 1'b0                ), // PLEASE CONNECT ME;

     // BIST ports
     .CSN_T       (                     ), // PLEASE CONNECT ME; Synthesis will remove me if unconnected
     .WEN_T       (                     ), // PLEASE CONNECT ME; Synthesis will remove me if unconnected
     .A_T         (                     ), // PLEASE CONNECT ME; Synthesis will remove me if unconnected
     .D_T         (                     ), // PLEASE CONNECT ME; Synthesis will remove me if unconnected
     .Q_T         (                     )
  );




  ///////////////////////////////////////////////
  //  ____  _____ ____ ___  ____  _____ ____   //
  // |  _ \| ____/ ___/ _ \|  _ \| ____|  _ \  //
  // | | | |  _|| |  | | | | | | |  _| | |_) | //
  // | |_| | |__| |__| |_| | |_| | |___|  _ <  //
  // |____/|_____\____\___/|____/|_____|_| \_\ //
  //                                           //
  ///////////////////////////////////////////////

  riscv_decoder
    #(
      .FPU                 ( FPU                  ),
      .FP_DIVSQRT          ( FP_DIVSQRT           ),
      .PULP_SECURE         ( PULP_SECURE          ),
      .SHARED_FP           ( SHARED_FP            ),
      .SHARED_DSP_MULT     ( SHARED_DSP_MULT      ),
      .SHARED_INT_MULT     ( SHARED_INT_MULT      ),
      .SHARED_INT_DIV      ( SHARED_INT_DIV       ),
      .SHARED_FP_DIVSQRT   ( SHARED_FP_DIVSQRT    ),
      .WAPUTYPE            ( WAPUTYPE             ),
      .APU_WOP_CPU         ( APU_WOP_CPU          )
      )
  decoder_i
  (
    // controller related signals
    .deassert_we_i                   ( deassert_we               ),
    .data_misaligned_i               ( data_misaligned_i         ),
    .mult_multicycle_i               ( mult_multicycle_i         ),
    .instr_multicycle_o              ( instr_multicycle          ),

    .illegal_insn_o                  ( illegal_insn_dec          ),
    .ebrk_insn_o                     ( ebrk_insn                 ),

    .mret_insn_o                     ( mret_insn_dec             ),
    .uret_insn_o                     ( uret_insn_dec             ),
    .dret_insn_o                     ( dret_insn_dec             ),

    .mret_dec_o                      ( mret_dec                  ),
    .uret_dec_o                      ( uret_dec                  ),
    .dret_dec_o                      ( dret_dec                  ),

    .ecall_insn_o                    ( ecall_insn_dec            ),
    .pipe_flush_o                    ( pipe_flush_dec            ),

    .fencei_insn_o                   ( fencei_insn_dec           ),

    .rega_used_o                     ( rega_used_dec             ),
    .regb_used_o                     ( regb_used_dec             ),
    .regc_used_o                     ( regc_used_dec             ),

    .reg_fp_a_o                      ( regfile_fp_a              ),
    .reg_fp_b_o                      ( regfile_fp_b              ),
    .reg_fp_c_o                      ( regfile_fp_c              ),
    .reg_fp_d_o                      ( regfile_fp_d              ),

    .bmask_a_mux_o                   ( bmask_a_mux               ),
    .bmask_b_mux_o                   ( bmask_b_mux               ),
    .alu_bmask_a_mux_sel_o           ( alu_bmask_a_mux_sel       ),
    .alu_bmask_b_mux_sel_o           ( alu_bmask_b_mux_sel       ),

    // from IF/ID pipeline
    .instr_rdata_i                   ( instr                     ),
    .illegal_c_insn_i                ( illegal_c_insn_i          ),

    // ALU signals
    .alu_en_o                        ( alu_en                    ),
    .alu_operator_o                  ( alu_operator              ),
    .alu_op_a_mux_sel_o              ( alu_op_a_mux_sel          ),
    .alu_op_b_mux_sel_o              ( alu_op_b_mux_sel          ),
    .alu_op_c_mux_sel_o              ( alu_op_c_mux_sel          ),
    .alu_vec_mode_o                  ( alu_vec_mode              ),
    .scalar_replication_o            ( scalar_replication        ),
    .scalar_replication_c_o          ( scalar_replication_c      ),
    .imm_a_mux_sel_o                 ( imm_a_mux_sel             ),
    .imm_b_mux_sel_o                 ( imm_b_mux_sel             ),
    .regc_mux_o                      ( regc_mux                  ),
    .is_clpx_o                       ( is_clpx                   ),
    .is_subrot_o                     ( is_subrot                 ),

    // MUL signals
    .mult_operator_o                 ( mult_operator             ),
    .mult_int_en_o                   ( mult_int_en               ),
    .mult_sel_subword_o              ( mult_sel_subword          ),
    .mult_signed_mode_o              ( mult_signed_mode          ),
    .mult_imm_mux_o                  ( mult_imm_mux              ),
    .mult_dot_en_o                   ( mult_dot_en               ),
    .mult_dot_signed_o               ( mult_dot_signed           ),

    // FPU / APU signals
    .frm_i                           ( frm_i                     ),
    .fpu_src_fmt_o                   ( fpu_src_fmt               ),
    .fpu_dst_fmt_o                   ( fpu_dst_fmt               ),
    .fpu_int_fmt_o                   ( fpu_int_fmt               ),
    .apu_en_o                        ( apu_en                    ),
    .apu_type_o                      ( apu_type                  ),
    .apu_op_o                        ( apu_op                    ),
    .apu_lat_o                       ( apu_lat                   ),
    .apu_flags_src_o                 ( apu_flags_src             ),
    .fp_rnd_mode_o                   ( fp_rnd_mode               ),

    // Register file control signals
    .regfile_mem_we_o                ( regfile_we_id             ),
    .regfile_alu_we_o                ( regfile_alu_we_id         ),
    .regfile_alu_we_dec_o            ( regfile_alu_we_dec_id     ),
    .regfile_alu_waddr_sel_o         ( regfile_alu_waddr_mux_sel ),

    // CSR control signals
    .csr_access_o                    ( csr_access                ),
    .csr_status_o                    ( csr_status                ),
    .csr_op_o                        ( csr_op                    ),
    .current_priv_lvl_i              ( current_priv_lvl_i        ),

    // Data bus interface
    .data_req_o                      ( data_req_id               ),
    .data_we_o                       ( data_we_id                ),
    .prepost_useincr_o               ( prepost_useincr           ),
    .data_type_o                     ( data_type_id              ),
    .data_sign_extension_o           ( data_sign_ext_id          ),
    .data_reg_offset_o               ( data_reg_offset_id        ),
    .data_load_event_o               ( data_load_event_id        ),

    // hwloop signals
    .hwloop_we_o                     ( hwloop_we_int             ),
    .hwloop_target_mux_sel_o         ( hwloop_target_mux_sel     ),
    .hwloop_start_mux_sel_o          ( hwloop_start_mux_sel      ),
    .hwloop_cnt_mux_sel_o            ( hwloop_cnt_mux_sel        ),

    // jump/branches
    .jump_in_dec_o                   ( jump_in_dec               ),
    .jump_in_id_o                    ( jump_in_id                ),
    .jump_target_mux_sel_o           ( jump_target_mux_sel       )

  );

  ////////////////////////////////////////////////////////////////////
  //    ____ ___  _   _ _____ ____   ___  _     _     _____ ____    //
  //   / ___/ _ \| \ | |_   _|  _ \ / _ \| |   | |   | ____|  _ \   //
  //  | |  | | | |  \| | | | | |_) | | | | |   | |   |  _| | |_) |  //
  //  | |__| |_| | |\  | | | |  _ <| |_| | |___| |___| |___|  _ <   //
  //   \____\___/|_| \_| |_| |_| \_\\___/|_____|_____|_____|_| \_\  //
  //                                                                //
  ////////////////////////////////////////////////////////////////////

  riscv_controller
  #(
    .FPU ( FPU )
  )
  controller_i
  (
    .clk                            ( clk                    ),
    .rst_n                          ( rst_n                  ),

    .fetch_enable_i                 ( fetch_enable_i         ),
    .ctrl_busy_o                    ( ctrl_busy_o            ),
    .first_fetch_o                  ( core_ctrl_firstfetch_o ),
    .is_decoding_o                  ( is_decoding_o          ),
    .is_fetch_failed_i              ( is_fetch_failed_i      ),

    // decoder related signals
    .deassert_we_o                  ( deassert_we            ),

    .illegal_insn_i                 ( illegal_insn_dec       ),
    .ecall_insn_i                   ( ecall_insn_dec         ),
    .mret_insn_i                    ( mret_insn_dec          ),
    .uret_insn_i                    ( uret_insn_dec          ),

    .dret_insn_i                    ( dret_insn_dec          ),

    .mret_dec_i                     ( mret_dec               ),
    .uret_dec_i                     ( uret_dec               ),
    .dret_dec_i                     ( dret_dec               ),


    .pipe_flush_i                   ( pipe_flush_dec         ),
    .ebrk_insn_i                    ( ebrk_insn              ),
    .fencei_insn_i                  ( fencei_insn_dec        ),
    .csr_status_i                   ( csr_status             ),
    .instr_multicycle_i             ( instr_multicycle       ),

    .hwloop_mask_o                  ( hwloop_mask            ),

    // from IF/ID pipeline
    .instr_valid_i                  ( instr_valid_i          ),

    // from prefetcher
    .instr_req_o                    ( instr_req_o            ),

    // to prefetcher
    .pc_set_o                       ( pc_set_o               ),
    .pc_mux_o                       ( pc_mux_o               ),
    .exc_pc_mux_o                   ( exc_pc_mux_o           ),
    .exc_cause_o                    ( exc_cause_o            ),
    .trap_addr_mux_o                ( trap_addr_mux_o        ),

    // LSU
    .data_req_ex_i                  ( data_req_ex_o          ),
    .data_we_ex_i                   ( data_we_ex_o           ),
    .data_misaligned_i              ( data_misaligned_i      ),
    .data_load_event_i              ( data_load_event_id     ),
    .data_err_i                     ( data_err_i             ),
    .data_err_ack_o                 ( data_err_ack_o         ),

    // ALU
    .mult_multicycle_i              ( mult_multicycle_i      ),

    // APU
    .apu_en_i                       ( apu_en                 ),
    .apu_read_dep_i                 ( apu_read_dep_i         ),
    .apu_write_dep_i                ( apu_write_dep_i        ),

    .apu_stall_o                    ( apu_stall              ),

    // jump/branch control
    .branch_taken_ex_i              ( branch_taken_ex        ),
    .jump_in_id_i                   ( jump_in_id             ),
    .jump_in_dec_i                  ( jump_in_dec            ),

    // Interrupt Controller Signals
    .irq_i                          ( irq_i                  ),
    .irq_req_ctrl_i                 ( irq_req_ctrl           ),
    .irq_sec_ctrl_i                 ( irq_sec_ctrl           ),
    .irq_id_ctrl_i                  ( irq_id_ctrl            ),
    .m_IE_i                         ( m_irq_enable_i         ),
    .u_IE_i                         ( u_irq_enable_i         ),
    .current_priv_lvl_i             ( current_priv_lvl_i     ),

    .irq_ack_o                      ( irq_ack_o              ),
    .irq_id_o                       ( irq_id_o               ),

    .exc_ack_o                      ( exc_ack                ),
    .exc_kill_o                     ( exc_kill               ),

    // Debug Signal
    .debug_mode_o                   ( debug_mode_o           ),
    .debug_cause_o                  ( debug_cause_o          ),
    .debug_csr_save_o               ( debug_csr_save_o       ),
    .debug_req_i                    ( debug_req_i            ),
    .debug_single_step_i            ( debug_single_step_i    ),
    .debug_ebreakm_i                ( debug_ebreakm_i        ),
    .debug_ebreaku_i                ( debug_ebreaku_i        ),

    // CSR Controller Signals
    .csr_save_cause_o               ( csr_save_cause_o       ),
    .csr_cause_o                    ( csr_cause_o            ),
    .csr_save_if_o                  ( csr_save_if_o          ),
    .csr_save_id_o                  ( csr_save_id_o          ),
    .csr_save_ex_o                  ( csr_save_ex_o          ),
    .csr_restore_mret_id_o          ( csr_restore_mret_id_o  ),
    .csr_restore_uret_id_o          ( csr_restore_uret_id_o  ),

    .csr_restore_dret_id_o          ( csr_restore_dret_id_o  ),

    .csr_irq_sec_o                  ( csr_irq_sec_o          ),

    // Write targets from ID
    .regfile_we_id_i                ( regfile_alu_we_dec_id  ),
    .regfile_alu_waddr_id_i         ( regfile_alu_waddr_id   ),

    // Forwarding signals from regfile
    .regfile_we_ex_i                ( regfile_we_ex_o        ),
    .regfile_waddr_ex_i             ( regfile_waddr_ex_o     ),
    .regfile_we_wb_i                ( regfile_we_wb_i        ),

    // regfile port 2
    .regfile_alu_we_fw_i            ( regfile_alu_we_fw_i    ),

    // Forwarding detection signals
    .reg_d_ex_is_reg_a_i            ( reg_d_ex_is_reg_a_id   ),
    .reg_d_ex_is_reg_b_i            ( reg_d_ex_is_reg_b_id   ),
    .reg_d_ex_is_reg_c_i            ( reg_d_ex_is_reg_c_id   ),
    .reg_d_wb_is_reg_a_i            ( reg_d_wb_is_reg_a_id   ),
    .reg_d_wb_is_reg_b_i            ( reg_d_wb_is_reg_b_id   ),
    .reg_d_wb_is_reg_c_i            ( reg_d_wb_is_reg_c_id   ),
    .reg_d_alu_is_reg_a_i           ( reg_d_alu_is_reg_a_id  ),
    .reg_d_alu_is_reg_b_i           ( reg_d_alu_is_reg_b_id  ),
    .reg_d_alu_is_reg_c_i           ( reg_d_alu_is_reg_c_id  ),

    // Forwarding signals
    .operand_a_fw_mux_sel_o         ( operand_a_fw_mux_sel   ),
    .operand_b_fw_mux_sel_o         ( operand_b_fw_mux_sel   ),
    .operand_c_fw_mux_sel_o         ( operand_c_fw_mux_sel   ),

    // Stall signals
    .halt_if_o                      ( halt_if_o              ),
    .halt_id_o                      ( halt_id                ),

    .misaligned_stall_o             ( misaligned_stall       ),
    .jr_stall_o                     ( jr_stall               ),
    .load_stall_o                   ( load_stall             ),

    .id_ready_i                     ( id_ready_o             ),

    .ex_valid_i                     ( ex_valid_i             ),

    .wb_ready_i                     ( wb_ready_i             ),

    // Performance Counters
    .perf_jump_o                    ( perf_jump_o            ),
    .perf_jr_stall_o                ( perf_jr_stall_o        ),
    .perf_ld_stall_o                ( perf_ld_stall_o        ),
    .perf_pipeline_stall_o          ( perf_pipeline_stall_o  )
  );


////////////////////////////////////////////////////////////////////////
//  _____      _       _____             _             _ _            //
// |_   _|    | |     /  __ \           | |           | | |           //
//   | | _ __ | |_    | /  \/ ___  _ __ | |_ _ __ ___ | | | ___ _ __  //
//   | || '_ \| __|   | |    / _ \| '_ \| __| '__/ _ \| | |/ _ \ '__| //
//  _| || | | | |_ _  | \__/\ (_) | | | | |_| | | (_) | | |  __/ |    //
//  \___/_| |_|\__(_)  \____/\___/|_| |_|\__|_|  \___/|_|_|\___|_|    //
//                                                                    //
////////////////////////////////////////////////////////////////////////

  riscv_int_controller
  #(
    .PULP_SECURE(PULP_SECURE)
   )
  int_controller_i
  (
    .clk                  ( clk                ),
    .rst_n                ( rst_n              ),

    // to controller
    .irq_req_ctrl_o       ( irq_req_ctrl       ),
    .irq_sec_ctrl_o       ( irq_sec_ctrl       ),
    .irq_id_ctrl_o        ( irq_id_ctrl        ),

    .ctrl_ack_i           ( exc_ack            ),
    .ctrl_kill_i          ( exc_kill           ),

    // Interrupt signals
    .irq_i                ( irq_i              ),
    .irq_sec_i            ( irq_sec_i          ),
    .irq_id_i             ( irq_id_i           ),

    .m_IE_i               ( m_irq_enable_i     ),
    .u_IE_i               ( u_irq_enable_i     ),
    .current_priv_lvl_i   ( current_priv_lvl_i )

  );


  //////////////////////////////////////////////////////////////////////////
  //          ____ ___  _   _ _____ ____   ___  _     _     _____ ____    //
  //         / ___/ _ \| \ | |_   _|  _ \ / _ \| |   | |   | ____|  _ \   //
  // HWLOOP-| |  | | | |  \| | | | | |_) | | | | |   | |   |  _| | |_) |  //
  //        | |__| |_| | |\  | | | |  _ <| |_| | |___| |___| |___|  _ <   //
  //         \____\___/|_| \_| |_| |_| \_\\___/|_____|_____|_____|_| \_\  //
  //                                                                      //
  //////////////////////////////////////////////////////////////////////////

  riscv_hwloop_regs
  #(
    .N_REGS ( N_HWLP )
  )
  hwloop_regs_i
  (
    .clk                   ( clk                       ),
    .rst_n                 ( rst_n                     ),

    // from ID
    .hwlp_start_data_i     ( hwloop_start              ),
    .hwlp_end_data_i       ( hwloop_end                ),
    .hwlp_cnt_data_i       ( hwloop_cnt                ),
    .hwlp_we_i             ( hwloop_we                 ),
    .hwlp_regid_i          ( hwloop_regid              ),

    // from controller
    .valid_i               ( hwloop_valid              ),

    // to hwloop controller
    .hwlp_start_addr_o     ( hwlp_start_o              ),
    .hwlp_end_addr_o       ( hwlp_end_o                ),
    .hwlp_counter_o        ( hwlp_cnt_o                ),

    // from hwloop controller
    .hwlp_dec_cnt_i        ( hwlp_dec_cnt_i            )
  );

  assign hwloop_valid = instr_valid_i & clear_instr_valid_o & is_hwlp_i;


  /////////////////////////////////////////////////////////////////////////////////
  //   ___ ____        _______  __  ____ ___ ____  _____ _     ___ _   _ _____   //
  //  |_ _|  _ \      | ____\ \/ / |  _ \_ _|  _ \| ____| |   |_ _| \ | | ____|  //
  //   | || | | |_____|  _|  \  /  | |_) | || |_) |  _| | |    | ||  \| |  _|    //
  //   | || |_| |_____| |___ /  \  |  __/| ||  __/| |___| |___ | || |\  | |___   //
  //  |___|____/      |_____/_/\_\ |_|  |___|_|   |_____|_____|___|_| \_|_____|  //
  //                                                                             //
  /////////////////////////////////////////////////////////////////////////////////

  always_ff @(posedge clk, negedge rst_n)
  begin : ID_EX_PIPE_REGISTERS
    if (rst_n == 1'b0)
    begin
      alu_en_ex_o                 <= '0;
      alu_operator_ex_o           <= ALU_SLTU;
      alu_operand_a_ex_o          <= '0;
      alu_operand_b_ex_o          <= '0;
      alu_operand_c_ex_o          <= '0;
      bmask_a_ex_o                <= '0;
      bmask_b_ex_o                <= '0;
      imm_vec_ext_ex_o            <= '0;
      alu_vec_mode_ex_o           <= '0;
      alu_clpx_shift_ex_o         <= 2'b0;
      alu_is_clpx_ex_o            <= 1'b0;
      alu_is_subrot_ex_o          <= 1'b0;

      mult_operator_ex_o          <= '0;
      mult_operand_a_ex_o         <= '0;
      mult_operand_b_ex_o         <= '0;
      mult_operand_c_ex_o         <= '0;
      mult_en_ex_o                <= 1'b0;
      mult_sel_subword_ex_o       <= 1'b0;
      mult_signed_mode_ex_o       <= 2'b00;
      mult_imm_ex_o               <= '0;

      mult_dot_op_a_ex_o          <= '0;
      mult_dot_op_b_ex_o          <= '0;
      mult_dot_op_c_ex_o          <= '0;
      mult_dot_signed_ex_o        <= '0;
      mult_is_clpx_ex_o           <= 1'b0;
      mult_clpx_shift_ex_o        <= 2'b0;
      mult_clpx_img_ex_o          <= 1'b0;

      apu_en_ex_o                 <= '0;
      apu_type_ex_o               <= '0;
      apu_op_ex_o                 <= '0;
      apu_lat_ex_o                <= '0;
      apu_operands_ex_o[0]        <= '0;
      apu_operands_ex_o[1]        <= '0;
      apu_operands_ex_o[2]        <= '0;
      apu_flags_ex_o              <= '0;
      apu_waddr_ex_o              <= '0;


      regfile_waddr_ex_o          <= 6'b0;
      regfile_we_ex_o             <= 1'b0;

      regfile_alu_waddr_ex_o      <= 6'b0;
      regfile_alu_we_ex_o         <= 1'b0;
      prepost_useincr_ex_o        <= 1'b0;

      csr_access_ex_o             <= 1'b0;
      csr_op_ex_o                 <= CSR_OP_NONE;

      data_we_ex_o                <= 1'b0;
      data_type_ex_o              <= 2'b0;
      data_sign_ext_ex_o          <= 2'b0;
      data_reg_offset_ex_o        <= 2'b0;
      data_req_ex_o               <= 1'b0;
      data_load_event_ex_o        <= 1'b0;

      data_misaligned_ex_o        <= 1'b0;

      pc_ex_o                     <= '0;

      branch_in_ex_o              <= 1'b0;

    end
    else if (data_misaligned_i) begin
      // misaligned data access case
      if (ex_ready_i)
      begin // misaligned access case, only unstall alu operands

        // if we are using post increments, then we have to use the
        // original value of the register for the second memory access
        // => keep it stalled
        if (prepost_useincr_ex_o == 1'b1)
        begin
          alu_operand_a_ex_o        <= alu_operand_a;
        end

        alu_operand_b_ex_o          <= alu_operand_b;
        regfile_alu_we_ex_o         <= regfile_alu_we_id;
        prepost_useincr_ex_o        <= prepost_useincr;

        data_misaligned_ex_o        <= 1'b1;
      end
    end else if (mult_multicycle_i) begin
      mult_operand_c_ex_o <= alu_operand_c;
    end
    else begin
      // normal pipeline unstall case

      if (id_valid_o)
      begin // unstall the whole pipeline

        alu_en_ex_o                 <= alu_en | branch_taken_ex;
        if (alu_en | branch_taken_ex)
        begin
          //this prevents divisions or multicycle instructions to keep the EX stage busy
          alu_operator_ex_o           <= branch_taken_ex ? ALU_SLTU : alu_operator;
          if(~branch_taken_ex) begin
            alu_operand_a_ex_o        <= alu_operand_a;
            alu_operand_b_ex_o        <= alu_operand_b;
            alu_operand_c_ex_o        <= alu_operand_c;
            bmask_a_ex_o              <= bmask_a_id;
            bmask_b_ex_o              <= bmask_b_id;
            imm_vec_ext_ex_o          <= imm_vec_ext_id;
            alu_vec_mode_ex_o         <= alu_vec_mode;
            alu_is_clpx_ex_o          <= is_clpx;
            alu_clpx_shift_ex_o       <= instr[14:13];
            alu_is_subrot_ex_o        <= is_subrot;
          end
        end

        mult_en_ex_o                <= mult_en;
        if (mult_int_en) begin
          mult_operator_ex_o        <= mult_operator;
          mult_sel_subword_ex_o     <= mult_sel_subword;
          mult_signed_mode_ex_o     <= mult_signed_mode;
          mult_operand_a_ex_o       <= alu_operand_a;
          mult_operand_b_ex_o       <= alu_operand_b;
          mult_operand_c_ex_o       <= alu_operand_c;
          mult_imm_ex_o             <= mult_imm_id;
        end
        if (mult_dot_en) begin
          mult_operator_ex_o        <= mult_operator;
          mult_dot_signed_ex_o      <= mult_dot_signed;
          mult_dot_op_a_ex_o        <= alu_operand_a;
          mult_dot_op_b_ex_o        <= alu_operand_b;
          mult_dot_op_c_ex_o        <= alu_operand_c;
          mult_is_clpx_ex_o         <= is_clpx;
          mult_clpx_shift_ex_o      <= instr[14:13];
          mult_clpx_img_ex_o        <= instr[25];
        end

        // APU pipeline
        apu_en_ex_o                 <= apu_en;
        if (apu_en) begin
          apu_type_ex_o             <= apu_type;
          apu_op_ex_o               <= apu_op;
          apu_lat_ex_o              <= apu_lat;
          apu_operands_ex_o         <= apu_operands;
          apu_flags_ex_o            <= apu_flags;
          apu_waddr_ex_o            <= apu_waddr;
        end

        regfile_we_ex_o             <= regfile_we_id;
        if (regfile_we_id) begin
          regfile_waddr_ex_o        <= regfile_waddr_id;
        end

        regfile_alu_we_ex_o         <= regfile_alu_we_id;
        if (regfile_alu_we_id) begin
          regfile_alu_waddr_ex_o    <= regfile_alu_waddr_id;
        end

        prepost_useincr_ex_o        <= prepost_useincr;

        csr_access_ex_o             <= csr_access;
        csr_op_ex_o                 <= csr_op;

        data_req_ex_o               <= data_req_id;
        if (data_req_id)
        begin // only needed for LSU when there is an active request
          data_we_ex_o              <= data_we_id;
          data_type_ex_o            <= data_type_id;
          data_sign_ext_ex_o        <= data_sign_ext_id;
          data_reg_offset_ex_o      <= data_reg_offset_id;
          data_load_event_ex_o      <= data_load_event_id;
        end else begin
          data_load_event_ex_o      <= 1'b0;
        end

        data_misaligned_ex_o        <= 1'b0;

        if ((jump_in_id == BRANCH_COND) || data_req_id) begin
          pc_ex_o                   <= pc_id_i;
        end

        branch_in_ex_o              <= jump_in_id == BRANCH_COND;
      end else if(ex_ready_i) begin
        // EX stage is ready but we don't have a new instruction for it,
        // so we set all write enables to 0, but unstall the pipe

        regfile_we_ex_o             <= 1'b0;

        regfile_alu_we_ex_o         <= 1'b0;

        csr_op_ex_o                 <= CSR_OP_NONE;

        data_req_ex_o               <= 1'b0;

        data_load_event_ex_o        <= 1'b0;

        data_misaligned_ex_o        <= 1'b0;

        branch_in_ex_o              <= 1'b0;

        apu_en_ex_o                 <= 1'b0;

        alu_operator_ex_o           <= ALU_SLTU;

        mult_en_ex_o                <= 1'b0;

        alu_en_ex_o                 <= 1'b1;

      end else if (csr_access_ex_o) begin
       //In the EX stage there was a CSR access, to avoid multiple
       //writes to the RF, disable regfile_alu_we_ex_o.
       //Not doing it can overwrite the RF file with the currennt CSR value rather than the old one
       regfile_alu_we_ex_o         <= 1'b0;
      end
    end
  end


  // stall control
  assign id_ready_o = ((~misaligned_stall) & (~jr_stall) & (~load_stall) & (~apu_stall) & (~csr_apu_stall) & ex_ready_i);
  assign id_valid_o = (~halt_id) & id_ready_o;


  //----------------------------------------------------------------------------
  // Assertions
  //----------------------------------------------------------------------------
  `ifndef VERILATOR
    // make sure that branch decision is valid when jumping
    assert property (
      @(posedge clk) (branch_in_ex_o) |-> (branch_decision_i !== 1'bx) ) else begin $display("%t, Branch decision is X in module %m", $time); $stop; end

    // the instruction delivered to the ID stage should always be valid
    assert property (
      @(posedge clk) (instr_valid_i & (~illegal_c_insn_i)) |-> (!$isunknown(instr_rdata_i)) ) else $display("Instruction is valid, but has at least one X");
  `endif
endmodule
