// Copyright (c), 2024 Darshak Sheladiya, SYSGO GmbH
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

module cva6_tip
  import ariane_pkg::*;
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter type exception_t = logic,
    parameter type scoreboard_entry_t = logic,
    parameter type rvfi_probes_csr_t = logic,
    parameter type bp_resolve_t = logic,
    parameter type rvfi_probes_instr_t = logic,
    parameter type rvfi_probes_t = logic,
    parameter type tip_instr_t = logic

) (
    input logic clk_i,
    input scoreboard_entry_t [CVA6Cfg.NrCommitPorts-1:0] commit_instr_i,
    input exception_t ex_commit_i,
    input riscv::priv_lvl_t priv_lvl_i,
    input logic [CVA6Cfg.NrCommitPorts-1:0] commit_ack_i,
    input logic debug_mode_i,
    input rvfi_probes_csr_t csr_i,
    input logic eret_i,
    input logic ipi_i,
    input logic debug_req_i,  // debug request (async)
    input bp_resolve_t resolved_branch_i,
    input rvfi_probes_t rvfi_probes_i,
    output tip_instr_t [CVA6Cfg.NrCommitPorts-1:0] tip_o
);



  rvfi_probes_instr_t instr = rvfi_probes_i.instr;
  logic debug_mode;

  logic [15:0] itype_signals[0:CVA6Cfg.NrCommitPorts-1];
  logic [3:0] itype_o[0:CVA6Cfg.NrCommitPorts-1];

  riscv::priv_lvl_t priv_lvl;
  //debug_mode
  assign debug_mode = instr.debug_mode;
  assign priv_lvl   = instr.priv_lvl;


  logic [CVA6Cfg.VLEN-1:0] taken_branch_pc_reg, not_taken_branch_pc_reg, uninforable_jump_pc_reg;

  // branch
  always @(posedge clk_i) begin
    if (resolved_branch_i.cf_type == Branch && resolved_branch_i.is_taken == 1) begin
      taken_branch_pc_reg <= resolved_branch_i.pc;  // taken branch
    end else if (resolved_branch_i.cf_type == Branch && resolved_branch_i.is_taken == 0) begin
      not_taken_branch_pc_reg <= resolved_branch_i.pc;  //not taken branch
    end else if (resolved_branch_i.cf_type == JumpR) begin
      uninforable_jump_pc_reg <= resolved_branch_i.pc;  //JumpR
    end
  end


  //  itype signals encoding
  generate
    for (genvar i = 0; i < CVA6Cfg.NrCommitPorts; i++) begin
      assign itype_signals[i][1] = commit_instr_i[i].valid && ex_commit_i.valid; //Exception. An exception that traps occurred following the final retired instruction in the block
      assign itype_signals [i][2] = ( ipi_i || debug_req_i ); //time_irq_i (commit_ack_i[0] && !ex_commit_i.valid) && //Interrupt. An interrupt that traps occurred following the final retired instruction in the block
      assign itype_signals[i][3] = eret_i;  //Exception or interrupt return
      assign itype_signals [i][4] = ((not_taken_branch_pc_reg == commit_instr_i[i].pc) && ~(commit_instr_i[i].pc == 0));//Nontaken branch
      assign itype_signals [i][5] = ( (taken_branch_pc_reg == commit_instr_i[i].pc) && ~(commit_instr_i[i].pc == 0)); //Taken branch
      assign itype_signals [i][6] = ( (uninforable_jump_pc_reg == commit_instr_i[i].pc) && ~(commit_instr_i[i].pc == 0)); //Uninferable jump
    end
  endgenerate

  generate
    for (genvar i = 0; i < CVA6Cfg.NrCommitPorts; i++) begin

      encoder_16_4 ec_0 (
          .in(itype_signals[i]),
          .out(itype_o[i]),
          .valid()
      );

    end
  endgenerate




  //TIP signals
  always_comb begin
    for (int i = 0; i < CVA6Cfg.NrCommitPorts; i++) begin
      logic exception, mem_exception;
      exception = commit_instr_i[i].valid && ex_commit_i.valid;
      mem_exception = exception &&
          (ex_commit_i.cause == riscv::INSTR_ADDR_MISALIGNED ||
           ex_commit_i.cause == riscv::INSTR_ACCESS_FAULT ||
           ex_commit_i.cause == riscv::ILLEGAL_INSTR ||
           ex_commit_i.cause == riscv::LD_ADDR_MISALIGNED ||
           ex_commit_i.cause == riscv::LD_ACCESS_FAULT ||
           ex_commit_i.cause == riscv::ST_ADDR_MISALIGNED ||
           ex_commit_i.cause == riscv::ST_ACCESS_FAULT ||
           ex_commit_i.cause == riscv::INSTR_PAGE_FAULT ||
           ex_commit_i.cause == riscv::LOAD_PAGE_FAULT ||
           ex_commit_i.cause == riscv::STORE_PAGE_FAULT);
      tip_o[i].iretire    = (commit_ack_i[i] && !ex_commit_i.valid) ||
                              (exception && (ex_commit_i.cause == riscv::ENV_CALL_MMODE ||
                               ex_commit_i.cause == riscv::ENV_CALL_SMODE ||
                               ex_commit_i.cause == riscv::ENV_CALL_UMODE));
      tip_o[i].iaddr = commit_instr_i[i].pc;
      tip_o[i].time_t = csr_i.cycle_q;
      tip_o[i].priv    = (((CVA6Cfg.DebugEn && debug_mode) ? 2'b10 : priv_lvl) == 2'b10) ? 2'b01:((CVA6Cfg.DebugEn && debug_mode) ? 2'b10 : priv_lvl) ;//(CVA6Cfg.DebugEn && debug_mode) ? 2'b10 : priv_lvl;//debug_mode_i ? 3'b100 : priv_lvl_i;
      tip_o[i].cause = ex_commit_i.cause;
      tip_o[i].tval = csr_i.mtval_q;
      tip_o[i].itype = itype_o[i];

    end
  end



  //*************************** TIP Signal dumping **************************//

  // int fd = $fopen("./tip_port_0_signals_dump.txt", "w");
  // int fj = $fopen("./tip_port_1_signals_dump.txt", "w");

  //  always@(tip_o[0].iretire == 1) begin

  //         if (fd) begin
  //                 $fwrite(fd, "tip_o_[0].iretire= 0x%h, tip_o_[0].iaddr= 0x%h, tip_o_[0].time_t= 0x%h, tip_o_[0].priv= 0x%h, tip_o_[0].cause= 0x%h, tip_o_[0].tval= 0x%h, tip_o_[0].itype= %h\n", tip_o[0].iretire, tip_o[0].iaddr,tip_o[0].time_t, tip_o[0].priv, tip_o[0].cause, tip_o[0].tval, tip_o[0].itype );
  //         end else begin
  //             $display("Error opening the file.");
  //         end
  //   end

  //  always@(tip_o[1].iretire == 1) begin

  //         if (fj) begin
  //                 $fwrite(fj, "tip_o_[1].iretire= 0x%h, tip_o_[1].iaddr= 0x%h, tip_o_[1].time_t= 0x%h, tip_o_[1].priv= 0x%h, tip_o_[1].cause= 0x%h, tip_o_[1].tval= 0x%h, tip_o_[1].itype= %h\n", tip_o[1].iretire, tip_o[1].iaddr,tip_o[1].time_t, tip_o[1].priv, tip_o[1].cause, tip_o[1].tval, tip_o[1].itype );
  //         end else begin
  //             $display("Error opening the file.");
  //         end
  //   end



endmodule
