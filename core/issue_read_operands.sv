// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Florian Zaruba, ETH Zurich
// Date: 08.04.2017
// Description: Issues instruction from the scoreboard and fetches the operands
//              This also includes all the forwarding logic


module issue_read_operands
  import ariane_pkg::*;
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter type branchpredict_sbe_t = logic,
    parameter type fu_data_t = logic,
    parameter type scoreboard_entry_t = logic,
    parameter type rs3_len_t = logic
) (
    // Subsystem Clock - SUBSYSTEM
    input logic clk_i,
    // Asynchronous reset active low - SUBSYSTEM
    input logic rst_ni,
    // Flush - CONTROLLER
    input logic flush_i,
    // Stall inserted by Acc dispatcher - ACC_DISPATCHER
    input logic stall_i,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    input scoreboard_entry_t [SUPERSCALAR:0] issue_instr_i,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    input logic [SUPERSCALAR:0][31:0] orig_instr_i,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    input logic [SUPERSCALAR:0] issue_instr_valid_i,
    // Issue stage acknowledge - TO_BE_COMPLETED
    output logic [SUPERSCALAR:0] issue_ack_o,
    // rs1 operand address - scoreboard
    output logic [SUPERSCALAR:0][REG_ADDR_SIZE-1:0] rs1_o,
    // rs1 operand - scoreboard
    input logic [SUPERSCALAR:0][CVA6Cfg.XLEN-1:0] rs1_i,
    // rs1 operand is valid - scoreboard
    input logic [SUPERSCALAR:0] rs1_valid_i,
    // rs2 operand address - scoreboard
    output logic [SUPERSCALAR:0][REG_ADDR_SIZE-1:0] rs2_o,
    // rs2 operand - scoreboard
    input logic [SUPERSCALAR:0][CVA6Cfg.XLEN-1:0] rs2_i,
    // rs2 operand is valid - scoreboard
    input logic [SUPERSCALAR:0] rs2_valid_i,
    // rs3 operand address - scoreboard
    output logic [SUPERSCALAR:0][REG_ADDR_SIZE-1:0] rs3_o,
    // rs3 operand - scoreboard
    input rs3_len_t [SUPERSCALAR:0] rs3_i,
    // rs3 operand is valid - scoreboard
    input logic [SUPERSCALAR:0] rs3_valid_i,
    // get clobber input
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    input fu_t [2**REG_ADDR_SIZE-1:0] rd_clobber_gpr_i,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    input fu_t [2**REG_ADDR_SIZE-1:0] rd_clobber_fpr_i,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    output fu_data_t [SUPERSCALAR:0] fu_data_o,
    // Unregistered version of fu_data_o.operanda - TO_BE_COMPLETED
    output logic [SUPERSCALAR:0][CVA6Cfg.XLEN-1:0] rs1_forwarding_o,
    // Unregistered version of fu_data_o.operandb - TO_BE_COMPLETED
    output logic [SUPERSCALAR:0][CVA6Cfg.XLEN-1:0] rs2_forwarding_o,
    // Instruction pc - TO_BE_COMPLETED
    output logic [CVA6Cfg.VLEN-1:0] pc_o,
    // Is compressed instruction - TO_BE_COMPLETED
    output logic is_compressed_instr_o,
    // Fixed Latency Unit ready to accept new request - TO_BE_COMPLETED
    input logic flu_ready_i,
    // ALU output is valid - TO_BE_COMPLETED
    output logic [SUPERSCALAR:0] alu_valid_o,
    // Branch instruction is valid - TO_BE_COMPLETED
    output logic [SUPERSCALAR:0] branch_valid_o,
    // Transformed instruction - TO_BE_COMPLETED
    output logic [SUPERSCALAR:0][31:0] tinst_o,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    output branchpredict_sbe_t branch_predict_o,
    // Load Store Unit is ready - TO_BE_COMPLETED
    input logic lsu_ready_i,
    // Load Store Unit result is valid - TO_BE_COMPLETED
    output logic [SUPERSCALAR:0] lsu_valid_o,
    // Mult result is valid - TO_BE_COMPLETED
    output logic [SUPERSCALAR:0] mult_valid_o,
    // FPU is ready - TO_BE_COMPLETED
    input logic fpu_ready_i,
    // FPU result is valid - TO_BE_COMPLETED
    output logic [SUPERSCALAR:0] fpu_valid_o,
    // FPU fmt field from instruction - TO_BE_COMPLETED
    output logic [1:0] fpu_fmt_o,
    // FPU rm field from isntruction - TO_BE_COMPLETED
    output logic [2:0] fpu_rm_o,
    // ALU output is valid - TO_BE_COMPLETED
    output logic [SUPERSCALAR:0] alu2_valid_o,
    // CSR result is valid - TO_BE_COMPLETED
    output logic [SUPERSCALAR:0] csr_valid_o,
    // CVXIF result is valid - TO_BE_COMPLETED
    output logic [SUPERSCALAR:0] cvxif_valid_o,
    // CVXIF is ready - TO_BE_COMPLETED
    input logic cvxif_ready_i,
    // CVXIF offloaded instruction - TO_BE_COMPLETED
    output logic [31:0] cvxif_off_instr_o,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    input logic [CVA6Cfg.NrCommitPorts-1:0][4:0] waddr_i,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    input logic [CVA6Cfg.NrCommitPorts-1:0][CVA6Cfg.XLEN-1:0] wdata_i,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    input logic [CVA6Cfg.NrCommitPorts-1:0] we_gpr_i,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    input logic [CVA6Cfg.NrCommitPorts-1:0] we_fpr_i,

    // Stall signal, we do not want to fetch any more entries - TO_BE_COMPLETED
    output logic stall_issue_o
);

  localparam OPERANDS_PER_INSTR = CVA6Cfg.NrRgprPorts >> SUPERSCALAR;

  typedef struct packed {
    logic none, load, store, alu, alu2, ctrl_flow, mult, csr, fpu, fpu_vec, cvxif, accel;
  } fus_busy_t;

  logic [SUPERSCALAR:0] stall;
  logic [SUPERSCALAR:0] fu_busy;  // functional unit is busy
  fus_busy_t [SUPERSCALAR:0] fus_busy;  // which functional units are considered busy
  // operands coming from regfile
  logic [SUPERSCALAR:0][CVA6Cfg.XLEN-1:0] operand_a_regfile, operand_b_regfile;
  // third operand from fp regfile or gp regfile if NR_RGPR_PORTS == 3
  rs3_len_t [SUPERSCALAR:0] operand_c_regfile, operand_c_gpr;
  rs3_len_t operand_c_fpr;
  // output flipflop (ID <-> EX)
  fu_data_t [SUPERSCALAR:0] fu_data_n, fu_data_q;
  logic [CVA6Cfg.XLEN-1:0] imm_forward_rs3;

  logic [   SUPERSCALAR:0] alu_valid_q;
  logic [   SUPERSCALAR:0] mult_valid_q;
  logic [   SUPERSCALAR:0] fpu_valid_q;
  logic [             1:0] fpu_fmt_q;
  logic [             2:0] fpu_rm_q;
  logic [   SUPERSCALAR:0] alu2_valid_q;
  logic [   SUPERSCALAR:0] lsu_valid_q;
  logic [   SUPERSCALAR:0] csr_valid_q;
  logic [   SUPERSCALAR:0] branch_valid_q;
  logic [   SUPERSCALAR:0] cvxif_valid_q;
  logic [            31:0] cvxif_off_instr_q;

  logic [SUPERSCALAR:0][31:0] tinst_n, tinst_q;  // transformed instruction

  // forwarding signals
  logic [SUPERSCALAR:0] forward_rs1, forward_rs2, forward_rs3;

  // original instruction
  riscv::instruction_t orig_instr;
  assign orig_instr = riscv::instruction_t'(orig_instr_i[0]);

  // ID <-> EX registers

  for (genvar i = 0; i <= SUPERSCALAR; i++) begin
    assign rs1_forwarding_o[i] = fu_data_n[i].operand_a[CVA6Cfg.VLEN-1:0];  //forwarding or unregistered rs1 value
    assign rs2_forwarding_o[i] = fu_data_n[i].operand_b[CVA6Cfg.VLEN-1:0];  //forwarding or unregistered rs2 value
  end

  assign fu_data_o = fu_data_q;
  assign alu_valid_o = alu_valid_q;
  assign branch_valid_o = branch_valid_q;
  assign lsu_valid_o = lsu_valid_q;
  assign csr_valid_o = csr_valid_q;
  assign mult_valid_o = mult_valid_q;
  assign fpu_valid_o = fpu_valid_q;
  assign fpu_fmt_o = fpu_fmt_q;
  assign fpu_rm_o = fpu_rm_q;
  assign alu2_valid_o = alu2_valid_q;
  assign cvxif_valid_o = CVA6Cfg.CvxifEn ? cvxif_valid_q : '0;
  assign cvxif_off_instr_o = CVA6Cfg.CvxifEn ? cvxif_off_instr_q : '0;
  assign stall_issue_o = stall[0];
  assign tinst_o = CVA6Cfg.RVH ? tinst_q : '0;
  // ---------------
  // Issue Stage
  // ---------------

  always_comb begin : structural_hazards
    fus_busy = '0;

    if (!flu_ready_i) begin
      fus_busy[0].alu = 1'b1;
      fus_busy[0].ctrl_flow = 1'b1;
      fus_busy[0].csr = 1'b1;
      fus_busy[0].mult = 1'b1;
    end

    // after a multiplication was issued we can only issue another multiplication
    // otherwise we will get contentions on the fixed latency bus
    if (mult_valid_q) begin
      fus_busy[0].alu = 1'b1;
      fus_busy[0].ctrl_flow = 1'b1;
      fus_busy[0].csr = 1'b1;
    end

    if (CVA6Cfg.FpPresent && !fpu_ready_i) begin
      fus_busy[0].fpu = 1'b1;
      fus_busy[0].fpu_vec = 1'b1;
      if (SUPERSCALAR) fus_busy[0].alu2 = 1'b1;
    end

    if (!lsu_ready_i) begin
      fus_busy[0].load  = 1'b1;
      fus_busy[0].store = 1'b1;
    end

    if (!cvxif_ready_i) begin
      fus_busy[0].cvxif = 1'b1;
    end

    if (SUPERSCALAR) begin
      fus_busy[1] = fus_busy[0];

      unique case (issue_instr_i[0].fu)
        NONE:  fus_busy[1].none = 1'b1;
        CTRL_FLOW: begin
          if (ariane_pkg::SPECULATIVE_SB) begin
            // Issue speculative instruction, will be removed on BMISS
            fus_busy[1].alu = 1'b1;
            fus_busy[1].ctrl_flow = 1'b1;
            fus_busy[1].csr = 1'b1;
            // Speculative non-idempotent loads are not supported yet
            fus_busy[1].load = 1'b1;
            // The store buffer cannot be partially flushed yet
            fus_busy[1].store = 1'b1;
          end else begin
            // There are no branch misses on a JAL
            if (issue_instr_i[0].op == ariane_pkg::ADD) begin
              fus_busy[1].alu = 1'b1;
              fus_busy[1].ctrl_flow = 1'b1;
              fus_busy[1].csr = 1'b1;
            end else begin
              // Control hazard
              fus_busy[1] = '1;
            end
          end
        end
        ALU: begin
          if (SUPERSCALAR && !fus_busy[0].alu2) begin
            fus_busy[1].alu2 = 1'b1;
            // TODO is there a minimum float execution time?
            // If so we could issue FPU & ALU2 the same cycle
            fus_busy[1].fpu = 1'b1;
            fus_busy[1].fpu_vec = 1'b1;
          end else begin
            fus_busy[1].alu = 1'b1;
            fus_busy[1].ctrl_flow = 1'b1;
            fus_busy[1].csr = 1'b1;
          end
        end
        CSR: begin
          fus_busy[1].alu = 1'b1;
          fus_busy[1].ctrl_flow = 1'b1;
          fus_busy[1].csr = 1'b1;
        end
        MULT:  fus_busy[1].mult = 1'b1;
        FPU, FPU_VEC: begin
          fus_busy[1].fpu = 1'b1;
          fus_busy[1].fpu_vec = 1'b1;
        end
        LOAD, STORE: begin
          fus_busy[1].load  = 1'b1;
          fus_busy[1].store = 1'b1;
        end
        CVXIF: fus_busy[1].cvxif = 1'b1;
      endcase
    end
  end

  // select the right busy signal
  // this obviously depends on the functional unit we need
  for (genvar i = 0; i <= ariane_pkg::SUPERSCALAR; i++) begin
    always_comb begin
      unique case (issue_instr_i[i].fu)
        NONE: fu_busy[i] = fus_busy[i].none;
        ALU: begin
          if (SUPERSCALAR && !fus_busy[i].alu2) begin
            fu_busy[i] = fus_busy[i].alu2;
          end else begin
            fu_busy[i] = fus_busy[i].alu;
          end
        end
        CTRL_FLOW: fu_busy[i] = fus_busy[i].ctrl_flow;
        CSR: fu_busy[i] = fus_busy[i].csr;
        MULT: fu_busy[i] = fus_busy[i].mult;
        FPU: fu_busy[i] = fus_busy[i].fpu;
        FPU_VEC: fu_busy[i] = fus_busy[i].fpu_vec;
        LOAD: fu_busy[i] = fus_busy[i].load;
        STORE: fu_busy[i] = fus_busy[i].store;
        CVXIF: fu_busy[i] = fus_busy[i].cvxif;
        default: fu_busy[i] = 1'b0;
      endcase
    end
  end

  // ---------------
  // Register stage
  // ---------------
  // check that all operands are available, otherwise stall
  // forward corresponding register
  always_comb begin : operands_available
    stall = '{default: stall_i};
    // operand forwarding signals
    forward_rs1 = '0;
    forward_rs2 = '0;
    forward_rs3 = '0;  // FPR only

    for (int unsigned i = 0; i <= SUPERSCALAR; i++) begin
      // poll the scoreboard for those values
      rs1_o[i] = issue_instr_i[i].rs1;
      rs2_o[i] = issue_instr_i[i].rs2;
      rs3_o[i] = issue_instr_i[i].result[REG_ADDR_SIZE-1:0];  // rs3 is encoded in imm field

      // 0. check that we are not using the zimm type in RS1
      //    as this is an immediate we do not have to wait on anything here
      // 1. check if the source registers are clobbered --> check appropriate clobber list (gpr/fpr)
      // 2. poll the scoreboard
      if (!issue_instr_i[i].use_zimm && ((CVA6Cfg.FpPresent && is_rs1_fpr(
              issue_instr_i[i].op
          )) ? rd_clobber_fpr_i[issue_instr_i[i].rs1] != NONE :
              rd_clobber_gpr_i[issue_instr_i[i].rs1] != NONE)) begin
        // check if the clobbering instruction is not a CSR instruction, CSR instructions can only
        // be fetched through the register file since they can't be forwarded
        // if the operand is available, forward it. CSRs don't write to/from FPR
        if (rs1_valid_i[i] && (CVA6Cfg.FpPresent && is_rs1_fpr(
                issue_instr_i[i].op
            ) ? 1'b1 : ((rd_clobber_gpr_i[issue_instr_i[i].rs1] != CSR) ||
                        (CVA6Cfg.RVS && issue_instr_i[i].op == SFENCE_VMA)))) begin
          forward_rs1[i] = 1'b1;
        end else begin  // the operand is not available -> stall
          stall[i] = 1'b1;
        end
      end

      if ((CVA6Cfg.FpPresent && is_rs2_fpr(
              issue_instr_i[i].op
          )) ? rd_clobber_fpr_i[issue_instr_i[i].rs2] != NONE :
              rd_clobber_gpr_i[issue_instr_i[i].rs2] != NONE) begin
        // if the operand is available, forward it. CSRs don't write to/from FPR
        if (rs2_valid_i[i] && (CVA6Cfg.FpPresent && is_rs2_fpr(
                issue_instr_i[i].op
            ) ? 1'b1 : ((rd_clobber_gpr_i[issue_instr_i[i].rs2] != CSR) ||
                        (CVA6Cfg.RVS && issue_instr_i[i].op == SFENCE_VMA)))) begin
          forward_rs2[i] = 1'b1;
        end else begin  // the operand is not available -> stall
          stall[i] = 1'b1;
        end
      end

      // Only check clobbered gpr for OFFLOADED instruction
      if ((CVA6Cfg.FpPresent && is_imm_fpr(
              issue_instr_i[i].op
          )) ? rd_clobber_fpr_i[issue_instr_i[i].result[REG_ADDR_SIZE-1:0]] != NONE :
              issue_instr_i[i].op == OFFLOAD && CVA6Cfg.NrRgprPorts == 3 ?
              rd_clobber_gpr_i[issue_instr_i[i].result[REG_ADDR_SIZE-1:0]] != NONE : 0) begin
        // if the operand is available, forward it. CSRs don't write to/from FPR so no need to check
        if (rs3_valid_i[i]) begin
          forward_rs3[i] = 1'b1;
        end else begin  // the operand is not available -> stall
          stall[i] = 1'b1;
        end
      end
    end

    if (SUPERSCALAR) begin
      if (!issue_instr_i[1].use_zimm && (!CVA6Cfg.FpPresent || (is_rs1_fpr(
              issue_instr_i[1].op
          ) == is_rd_fpr(
              issue_instr_i[0].op
          ))) && issue_instr_i[1].rs1 == issue_instr_i[0].rd && issue_instr_i[1].rs1 != '0) begin
        stall[1] = 1'b1;
      end

      if ((!CVA6Cfg.FpPresent || (is_rs2_fpr(
              issue_instr_i[1].op
          ) == is_rd_fpr(
              issue_instr_i[0].op
          ))) && issue_instr_i[1].rs2 == issue_instr_i[0].rd && issue_instr_i[1].rs2 != '0) begin
        stall[1] = 1'b1;
      end

      // Only check clobbered gpr for OFFLOADED instruction
      if ((CVA6Cfg.FpPresent && is_imm_fpr(
              issue_instr_i[1].op
          )) ? is_rd_fpr(
              issue_instr_i[0].op
          ) && issue_instr_i[0].rd == issue_instr_i[1].result[REG_ADDR_SIZE-1:0] :
              issue_instr_i[1].op == OFFLOAD && CVA6Cfg.NrRgprPorts == 3 ?
              issue_instr_i[0].rd == issue_instr_i[1].result[REG_ADDR_SIZE-1:0] : 1'b0) begin
        stall[1] = 1'b1;
      end
    end
  end

  // third operand from fp regfile or gp regfile if NR_RGPR_PORTS == 3
  if (CVA6Cfg.NrRgprPorts == 3) begin : gen_gp_rs3
    assign imm_forward_rs3 = rs3_i[0];
  end else begin : gen_fp_rs3
    assign imm_forward_rs3 = {{CVA6Cfg.XLEN - CVA6Cfg.FLen{1'b0}}, rs3_i[0]};
  end

  // Forwarding/Output MUX
  for (genvar i = 0; i <= SUPERSCALAR; i++) begin
    always_comb begin : forwarding_operand_select
      // default is regfiles (gpr or fpr)
      fu_data_n[i].operand_a = operand_a_regfile[i];
      fu_data_n[i].operand_b = operand_b_regfile[i];

      // immediates are the third operands in the store case
      // for FP operations, the imm field can also be the third operand from the regfile
      if (CVA6Cfg.NrRgprPorts == 3) begin
        fu_data_n[i].imm = (CVA6Cfg.FpPresent && is_imm_fpr(issue_instr_i[i].op)) ?
            {{CVA6Cfg.XLEN - CVA6Cfg.FLen{1'b0}}, operand_c_regfile[i]} :
            issue_instr_i[i].op == OFFLOAD ? operand_c_regfile[i] : issue_instr_i[i].result;
      end else begin
        fu_data_n[i].imm = (CVA6Cfg.FpPresent && is_imm_fpr(issue_instr_i[i].op)) ?
            {{CVA6Cfg.XLEN - CVA6Cfg.FLen{1'b0}}, operand_c_regfile[i]} : issue_instr_i[i].result;
      end
      fu_data_n[i].trans_id  = issue_instr_i[i].trans_id;
      fu_data_n[i].fu        = issue_instr_i[i].fu;
      fu_data_n[i].operation = issue_instr_i[i].op;
      if (CVA6Cfg.RVH) begin
        tinst_n[i] = issue_instr_i[i].ex.tinst;
      end

      // or should we forward
      if (forward_rs1[i]) begin
        fu_data_n[i].operand_a = rs1_i[i];
      end
      if (forward_rs2[i]) begin
        fu_data_n[i].operand_b = rs2_i[i];
      end
      if (CVA6Cfg.FpPresent && forward_rs3[i]) begin
        fu_data_n[i].imm = imm_forward_rs3;
      end

      // use the PC as operand a
      if (issue_instr_i[i].use_pc) begin
        fu_data_n[i].operand_a = {
          {CVA6Cfg.XLEN - CVA6Cfg.VLEN{issue_instr_i[i].pc[CVA6Cfg.VLEN-1]}}, issue_instr_i[i].pc
        };
      end

      // use the zimm as operand a
      if (issue_instr_i[i].use_zimm) begin
        // zero extend operand a
        fu_data_n[i].operand_a = {{CVA6Cfg.XLEN - 5{1'b0}}, issue_instr_i[i].rs1[4:0]};
      end
      // or is it an immediate (including PC), this is not the case for a store, control flow, and accelerator instructions
      // also make sure operand B is not already used as an FP operand
      if (issue_instr_i[i].use_imm && (issue_instr_i[i].fu != STORE) && (issue_instr_i[i].fu != CTRL_FLOW) && (issue_instr_i[i].fu != ACCEL) && !(CVA6Cfg.FpPresent && is_rs2_fpr(
              issue_instr_i[i].op
          ))) begin
        fu_data_n[i].operand_b = issue_instr_i[i].result;
      end
    end
  end

  // FU select, assert the correct valid out signal (in the next cycle)
  // This needs to be like this to make verilator happy. I know its ugly.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      alu_valid_q    <= '0;
      lsu_valid_q    <= '0;
      mult_valid_q   <= '0;
      fpu_valid_q    <= '0;
      fpu_fmt_q      <= '0;
      fpu_rm_q       <= '0;
      alu2_valid_q   <= '0;
      csr_valid_q    <= '0;
      branch_valid_q <= '0;
    end else begin
      alu_valid_q    <= '0;
      lsu_valid_q    <= '0;
      mult_valid_q   <= '0;
      fpu_valid_q    <= '0;
      fpu_fmt_q      <= '0;
      fpu_rm_q       <= '0;
      alu2_valid_q   <= '0;
      csr_valid_q    <= '0;
      branch_valid_q <= '0;
      // Exception pass through:
      // If an exception has occurred simply pass it through
      // we do not want to issue this instruction
      for (int unsigned i = 0; i <= SUPERSCALAR; i++) begin
        if (!issue_instr_i[i].ex.valid && issue_instr_valid_i[i] && issue_ack_o[i]) begin
          case (issue_instr_i[i].fu)
            ALU: begin
              if (SUPERSCALAR && !fus_busy[i].alu2) begin
                alu2_valid_q[i] <= 1'b1;
              end else begin
                alu_valid_q[i] <= 1'b1;
              end
            end
            CTRL_FLOW: begin
              branch_valid_q[i] <= 1'b1;
            end
            MULT: begin
              mult_valid_q[i] <= 1'b1;
            end
            LOAD, STORE: begin
              lsu_valid_q[i] <= 1'b1;
            end
            CSR: begin
              csr_valid_q[i] <= 1'b1;
            end
            default: begin
              if (issue_instr_i[i].fu == FPU && CVA6Cfg.FpPresent) begin
                fpu_valid_q[i] <= 1'b1;
                fpu_fmt_q      <= orig_instr.rftype.fmt;  // fmt bits from instruction
                fpu_rm_q       <= orig_instr.rftype.rm;  // rm bits from instruction
              end else if (issue_instr_i[i].fu == FPU_VEC && CVA6Cfg.FpPresent) begin
                fpu_valid_q[i] <= 1'b1;
                fpu_fmt_q      <= orig_instr.rvftype.vfmt;  // vfmt bits from instruction
                fpu_rm_q       <= {2'b0, orig_instr.rvftype.repl};  // repl bit from instruction
              end
            end
          endcase
        end
      end
      // if we got a flush request, de-assert the valid flag, otherwise we will start this
      // functional unit with the wrong inputs
      if (flush_i) begin
        alu_valid_q    <= '0;
        lsu_valid_q    <= '0;
        mult_valid_q   <= '0;
        fpu_valid_q    <= '0;
        alu2_valid_q   <= '0;
        csr_valid_q    <= '0;
        branch_valid_q <= '0;
      end
    end
  end

  if (CVA6Cfg.CvxifEn) begin
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        cvxif_valid_q <= '0;
        cvxif_off_instr_q <= 32'b0;
      end else begin
        cvxif_valid_q <= '0;
        cvxif_off_instr_q <= 32'b0;
        for (int unsigned i = 0; i <= SUPERSCALAR; i++) begin
          if (!issue_instr_i[i].ex.valid && issue_instr_valid_i[i] && issue_ack_o[i]) begin
            case (issue_instr_i[i].fu)
              CVXIF: begin
                cvxif_valid_q[i]  <= 1'b1;
                cvxif_off_instr_q <= orig_instr;
              end
              default: ;
            endcase
          end
        end
        if (flush_i) begin
          cvxif_valid_q <= '0;
          cvxif_off_instr_q <= 32'b0;
        end
      end
    end
  end

  // We can issue an instruction if we do not detect that any other instruction is writing the same
  // destination register.
  // We also need to check if there is an unresolved branch in the scoreboard.
  always_comb begin : issue_scoreboard
    for (int unsigned i = 0; i <= SUPERSCALAR; i++) begin
      // default assignment
      issue_ack_o[i] = 1'b0;
      // check that we didn't stall, that the instruction we got is valid
      // and that the functional unit we need is not busy
      if (issue_instr_valid_i[i] && !fu_busy[i]) begin
        // check that the corresponding functional unit is not busy
        if (!stall[i]) begin
          // -----------------------------------------
          // WAW - Write After Write Dependency Check
          // -----------------------------------------
          // no other instruction has the same destination register -> issue the instruction
          if ((CVA6Cfg.FpPresent && ariane_pkg::is_rd_fpr(
                  issue_instr_i[i].op
              )) ? (rd_clobber_fpr_i[issue_instr_i[i].rd] == NONE) :
                  (rd_clobber_gpr_i[issue_instr_i[i].rd] == NONE)) begin
            issue_ack_o[i] = 1'b1;
          end
          // or check that the target destination register will be written in this cycle by the
          // commit stage
          for (int unsigned c = 0; c < CVA6Cfg.NrCommitPorts; c++) begin
            if ((CVA6Cfg.FpPresent && ariane_pkg::is_rd_fpr(
                    issue_instr_i[i].op
                )) ? (we_fpr_i[c] && waddr_i[c] == issue_instr_i[i].rd[4:0]) :
                    (we_gpr_i[c] && waddr_i[c] == issue_instr_i[i].rd[4:0])) begin
              issue_ack_o[i] = 1'b1;
            end
          end
          if (i > 0) begin
            if ((issue_instr_i[i].rd[4:0] == issue_instr_i[i-1].rd[4:0]) && (issue_instr_i[i].rd[4:0] != '0)) begin
              issue_ack_o[i] = 1'b0;
            end
          end
        end
        // we can also issue the instruction under the following two circumstances:
        // we can do this even if we are stalled or no functional unit is ready (as we don't need one)
        // the decoder needs to make sure that the instruction is marked as valid when it does not
        // need any functional unit or if an exception occurred previous to the execute stage.
        // 1. we already got an exception
        if (issue_instr_i[i].ex.valid) begin
          issue_ack_o[i] = 1'b1;
        end
        // 2. it is an instruction which does not need any functional unit
        if (issue_instr_i[i].fu == NONE) begin
          issue_ack_o[i] = 1'b1;
        end
      end
    end

    if (SUPERSCALAR) begin
      if (!issue_ack_o[0]) begin
        issue_ack_o[1] = 1'b0;
      end
    end
  end

  // ----------------------
  // Integer Register File
  // ----------------------
  logic [  CVA6Cfg.NrRgprPorts-1:0][CVA6Cfg.XLEN-1:0] rdata;
  logic [  CVA6Cfg.NrRgprPorts-1:0][             4:0] raddr_pack;

  // pack signals
  logic [CVA6Cfg.NrCommitPorts-1:0][             4:0] waddr_pack;
  logic [CVA6Cfg.NrCommitPorts-1:0][CVA6Cfg.XLEN-1:0] wdata_pack;
  logic [CVA6Cfg.NrCommitPorts-1:0]                   we_pack;

  for (genvar i = 0; i <= SUPERSCALAR; i++) begin
    assign raddr_pack[i*OPERANDS_PER_INSTR+0] = issue_instr_i[i].rs1[4:0];
    assign raddr_pack[i*OPERANDS_PER_INSTR+1] = issue_instr_i[i].rs2[4:0];
    if (OPERANDS_PER_INSTR == 3) begin
      assign raddr_pack[i*OPERANDS_PER_INSTR+2] = issue_instr_i[i].result[4:0];
    end
  end

  for (genvar i = 0; i < CVA6Cfg.NrCommitPorts; i++) begin : gen_write_back_port
    assign waddr_pack[i] = waddr_i[i];
    assign wdata_pack[i] = wdata_i[i];
    assign we_pack[i]    = we_gpr_i[i];
  end
  if (CVA6Cfg.FpgaEn) begin : gen_fpga_regfile
    ariane_regfile_fpga #(
        .CVA6Cfg      (CVA6Cfg),
        .DATA_WIDTH   (CVA6Cfg.XLEN),
        .NR_READ_PORTS(CVA6Cfg.NrRgprPorts),
        .ZERO_REG_ZERO(1)
    ) i_ariane_regfile_fpga (
        .test_en_i(1'b0),
        .raddr_i  (raddr_pack),
        .rdata_o  (rdata),
        .waddr_i  (waddr_pack),
        .wdata_i  (wdata_pack),
        .we_i     (we_pack),
        .*
    );
  end else begin : gen_asic_regfile
    ariane_regfile #(
        .CVA6Cfg      (CVA6Cfg),
        .DATA_WIDTH   (CVA6Cfg.XLEN),
        .NR_READ_PORTS(CVA6Cfg.NrRgprPorts),
        .ZERO_REG_ZERO(1)
    ) i_ariane_regfile (
        .test_en_i(1'b0),
        .raddr_i  (raddr_pack),
        .rdata_o  (rdata),
        .waddr_i  (waddr_pack),
        .wdata_i  (wdata_pack),
        .we_i     (we_pack),
        .*
    );
  end

  // -----------------------------
  // Floating-Point Register File
  // -----------------------------
  logic [2:0][CVA6Cfg.FLen-1:0] fprdata;

  // pack signals
  logic [2:0][4:0] fp_raddr_pack;
  logic [CVA6Cfg.NrCommitPorts-1:0][CVA6Cfg.XLEN-1:0] fp_wdata_pack;

  always_comb begin : assign_fp_raddr_pack
    fp_raddr_pack = {
      issue_instr_i[0].result[4:0], issue_instr_i[0].rs2[4:0], issue_instr_i[0].rs1[4:0]
    };

    if (SUPERSCALAR) begin
      if (!(issue_instr_i[0].fu inside {FPU, FPU_VEC})) begin
        fp_raddr_pack = {
          issue_instr_i[1].result[4:0], issue_instr_i[1].rs2[4:0], issue_instr_i[1].rs1[4:0]
        };
      end
    end
  end

  generate
    if (CVA6Cfg.FpPresent) begin : float_regfile_gen
      for (genvar i = 0; i < CVA6Cfg.NrCommitPorts; i++) begin : gen_fp_wdata_pack
        assign fp_wdata_pack[i] = {wdata_i[i][CVA6Cfg.FLen-1:0]};
      end
      if (CVA6Cfg.FpgaEn) begin : gen_fpga_fp_regfile
        ariane_regfile_fpga #(
            .CVA6Cfg      (CVA6Cfg),
            .DATA_WIDTH   (CVA6Cfg.FLen),
            .NR_READ_PORTS(3),
            .ZERO_REG_ZERO(0)
        ) i_ariane_fp_regfile_fpga (
            .test_en_i(1'b0),
            .raddr_i  (fp_raddr_pack),
            .rdata_o  (fprdata),
            .waddr_i  (waddr_pack),
            .wdata_i  (fp_wdata_pack),
            .we_i     (we_fpr_i),
            .*
        );
      end else begin : gen_asic_fp_regfile
        ariane_regfile #(
            .CVA6Cfg      (CVA6Cfg),
            .DATA_WIDTH   (CVA6Cfg.FLen),
            .NR_READ_PORTS(3),
            .ZERO_REG_ZERO(0)
        ) i_ariane_fp_regfile (
            .test_en_i(1'b0),
            .raddr_i  (fp_raddr_pack),
            .rdata_o  (fprdata),
            .waddr_i  (waddr_pack),
            .wdata_i  (fp_wdata_pack),
            .we_i     (we_fpr_i),
            .*
        );
      end
    end else begin : no_fpr_gen
      assign fprdata = '{default: '0};
    end
  endgenerate

  if (CVA6Cfg.NrRgprPorts == 3) begin : gen_operand_c
    assign operand_c_fpr = {{CVA6Cfg.XLEN - CVA6Cfg.FLen{1'b0}}, fprdata[2]};
  end else begin
    assign operand_c_fpr = fprdata[2];
  end

  for (genvar i = 0; i <= SUPERSCALAR; i++) begin
    if (CVA6Cfg.NrRgprPorts == 3) begin : gen_operand_c
      assign operand_c_gpr[i] = rdata[i*OPERANDS_PER_INSTR+2];
    end

    assign operand_a_regfile[i] = (CVA6Cfg.FpPresent && is_rs1_fpr(
        issue_instr_i[i].op
    )) ? {{CVA6Cfg.XLEN - CVA6Cfg.FLen{1'b0}}, fprdata[0]} : rdata[i*OPERANDS_PER_INSTR+0];
    assign operand_b_regfile[i] = (CVA6Cfg.FpPresent && is_rs2_fpr(
        issue_instr_i[i].op
    )) ? {{CVA6Cfg.XLEN - CVA6Cfg.FLen{1'b0}}, fprdata[1]} : rdata[i*OPERANDS_PER_INSTR+1];
    assign operand_c_regfile[i] = (CVA6Cfg.NrRgprPorts == 3) ? ((CVA6Cfg.FpPresent && is_imm_fpr(
        issue_instr_i[i].op
    )) ? operand_c_fpr : operand_c_gpr[i]) : operand_c_fpr;
  end

  // ----------------------
  // Registers (ID <-> EX)
  // ----------------------
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      fu_data_q <= '0;
      if (CVA6Cfg.RVH) begin
        tinst_q <= '0;
      end
      pc_o                  <= '0;
      is_compressed_instr_o <= 1'b0;
      branch_predict_o      <= {cf_t'(0), {CVA6Cfg.VLEN{1'b0}}};
    end else begin
      fu_data_q <= fu_data_n;
      if (CVA6Cfg.RVH) begin
        tinst_q <= tinst_n;
      end
      if (SUPERSCALAR) begin
        if (issue_instr_i[1].fu == CTRL_FLOW) begin
          pc_o                  <= issue_instr_i[1].pc;
          is_compressed_instr_o <= issue_instr_i[1].is_compressed;
          branch_predict_o      <= issue_instr_i[1].bp;
        end
      end
      if (issue_instr_i[0].fu == CTRL_FLOW) begin
        pc_o                  <= issue_instr_i[0].pc;
        is_compressed_instr_o <= issue_instr_i[0].is_compressed;
        branch_predict_o      <= issue_instr_i[0].bp;
      end
    end
  end

  //pragma translate_off
  initial begin
    assert (CVA6Cfg.NrRgprPorts == 2 || (CVA6Cfg.NrRgprPorts == 3 && CVA6Cfg.CvxifEn) || SUPERSCALAR)
    else
      $fatal(
          1,
          "If CVXIF is enable, ariane regfile can have either 2 or 3 read ports. Else it has 2 read ports."
      );
  end

  // FPU does not declare that it will return a result the subsequent cycle so
  // it is not possible for issue stage to know when ALU2 can be used if there
  // is an FPU.  As there are discussions to change the FPU, I did not explore
  // its architecture to create this "FPU returns next cycle" signal.  Also, a
  // "lookahead" optimization should be added to be performant with FPU:  when
  // issue port 2 is issuing to FPU, issue port 1 should issue to ALU1 instead
  // of ALU2 so that FPU is not busy.  However, if FPU has a minimum execution
  // time of 2 cycles, it is possible to simply not raise fus_busy[1].alu2.
  initial begin
    assert (!(SUPERSCALAR && CVA6Cfg.FpPresent))
    else
      $fatal(1, "FPU is not yet supported in superscalar CVA6, see comments above this assertion.");
  end

  for (genvar i = 0; i <= SUPERSCALAR; i++) begin
    assert property (@(posedge clk_i) (branch_valid_q) |-> (!$isunknown(
        fu_data_q[i].operand_a
    ) && !$isunknown(
        fu_data_q[i].operand_b
    )))
    else $warning("Got unknown value in one of the operands");
  end
  //pragma translate_on

endmodule
