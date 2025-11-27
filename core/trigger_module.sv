module trigger_module
  import ariane_pkg::*;
  import triggers_pkg::*;
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg            = config_pkg::cva6_cfg_empty,
    parameter type                   exception_t        = logic,
    parameter type                   scoreboard_entry_t = logic,
    parameter int unsigned           N_Triggers         = 4
) (
    input logic clk_i,
    input logic rst_ni,
    input scoreboard_entry_t commit_instr_i,
    input logic [CVA6Cfg.NrCommitPorts-1:0] commit_ack_i,
    input exception_t ex_i,
    input riscv::priv_lvl_t priv_lvl_i,
    input logic debug_mode_i,
    input logic mret_i,
    input logic sret_i,
    input logic [CVA6Cfg.VLEN-1:0] vaddr_from_lsu_i,
    input logic [CVA6Cfg.NrIssuePorts-1:0][31:0] orig_instr_i,
    input logic [CVA6Cfg.XLEN-1:0] store_result_i,

    input logic [CVA6Cfg.XLEN-1:0] scontext_i,

    input logic [CVA6Cfg.XLEN-1:0] tdata1_i,
    input logic [CVA6Cfg.XLEN-1:0] tdata2_i,
    input logic [CVA6Cfg.XLEN-1:0] tdata3_i,
    input logic [CVA6Cfg.XLEN-1:0] tselect_i,
    input logic tselect_we,
    input logic tdata1_we,
    input logic tdata2_we,
    input logic tdata3_we,

    output logic [CVA6Cfg.XLEN-1:0] tselect_o,
    output logic [CVA6Cfg.XLEN-1:0] tdata1_o,
    output logic [CVA6Cfg.XLEN-1:0] tdata2_o,
    output logic [CVA6Cfg.XLEN-1:0] tdata3_o,
    output logic flush_o,

    output logic break_from_trigger_o,
    output logic debug_from_trigger_o,
    output logic debug_from_mcontrol_o
);

  // Trigger Module Helpers
  logic [N_Triggers-1:0] tselect_q, tselect_d;
  logic [3:0] trigger_type_q[N_Triggers], trigger_type_d[N_Triggers];
  logic [N_Triggers-1:0] priv_match, scontext_match;
  textra32_tdata3_t textra32_tdata3_q[N_Triggers], textra32_tdata3_d[N_Triggers];
  textra64_tdata3_t textra64_tdata3_q[N_Triggers], textra64_tdata3_d[N_Triggers];
  logic [CVA6Cfg.XLEN-1:0] tdata2_q[N_Triggers], tdata2_d[N_Triggers];
  logic mcontrol6_debug_d, mcontrol6_debug_q, matched;
  logic e_matched_q, e_matched_d;
  logic mret_reg_q, mret_reg_d;
  logic break_from_trigger_q, break_from_trigger_d;
  logic in_trap_handler_q, in_trap_handler_d;
  logic debug_from_trigger_q, debug_from_trigger_d;
  icount32_tdata1_t icount32_tdata1_q[N_Triggers], icount32_tdata1_d[N_Triggers];
  mcontrol6_32_tdata1_t mcontrol6_32_tdata1_q[N_Triggers], mcontrol6_32_tdata1_d[N_Triggers];
  etrigger32_tdata1_t etrigger32_tdata1_q[N_Triggers], etrigger32_tdata1_d[N_Triggers];
  itrigger32_tdata1_t itrigger32_tdata1_q[N_Triggers], itrigger32_tdata1_d[N_Triggers];


  // Trigger CSRs write/update logic
  always_comb begin : write_path
    // Trigger module CSRs
    if (tselect_we) begin
      tselect_d = (tselect_i < N_Triggers) ? tselect_i[$clog2(N_Triggers)-1:0] : tselect_q;
    end
    if (tdata1_we) begin
      if ((tdata1_i[31:28] == 4'd3 && CVA6Cfg.IS_XLEN32) || (CVA6Cfg.IS_XLEN64 && tdata1_i[63:60] == 4'd3)) begin
        trigger_type_d[tselect_q] = (CVA6Cfg.IS_XLEN32) ? tdata1_i[31:28] : tdata1_i[63:60];
        icount32_tdata1_d[tselect_q].t_type  = (CVA6Cfg.IS_XLEN32) ? ((tdata1_i[31:28] == 4'd3 || tdata1_i[31:28] == 4'd15) ? tdata1_i[31:28] : trigger_type_q[tselect_q]) : ((tdata1_i[63:60] == 4'd3 || tdata1_i[63:60] == 4'd15) ? tdata1_i[63:60] : trigger_type_q[tselect_q]);
        icount32_tdata1_d[tselect_q].dmode = (CVA6Cfg.IS_XLEN32) ? tdata1_i[27] : tdata1_i[59];
        icount32_tdata1_d[tselect_q].vs = 0;
        icount32_tdata1_d[tselect_q].vu = 0;
        icount32_tdata1_d[tselect_q].hit = tdata1_i[24];
        icount32_tdata1_d[tselect_q].count = tdata1_i[23:10];
        icount32_tdata1_d[tselect_q].m = tdata1_i[9];
        icount32_tdata1_d[tselect_q].pending = tdata1_i[8];
        icount32_tdata1_d[tselect_q].s = tdata1_i[7];
        icount32_tdata1_d[tselect_q].u = tdata1_i[6];
        icount32_tdata1_d[tselect_q].action = tdata1_i[5:0];
        flush_o = 1'b1;
      end else if ((CVA6Cfg.IS_XLEN32 && tdata1_i[31:28] == 4'd6) || (CVA6Cfg.IS_XLEN64 && tdata1_i[63:60] == 4'd6)) begin
        trigger_type_d[tselect_q] = (CVA6Cfg.IS_XLEN32) ? tdata1_i[31:28] : tdata1_i[63:60];
        mcontrol6_32_tdata1_d[tselect_q].t_type  = (CVA6Cfg.IS_XLEN32) ? ((tdata1_i[31:28] == 4'd6 || tdata1_i[31:28] == 4'd15) ? tdata1_i[31:28] : trigger_type_q[tselect_q]) : ((tdata1_i[63:60] == 4'd6 || tdata1_i[63:60] == 4'd15) ? tdata1_i[63:60] : trigger_type_q[tselect_q]);
        mcontrol6_32_tdata1_d[tselect_q].dmode = (CVA6Cfg.IS_XLEN32) ? tdata1_i[27] : tdata1_i[59];
        mcontrol6_32_tdata1_d[tselect_q].uncertain = 0;
        mcontrol6_32_tdata1_d[tselect_q].hit1 = tdata1_i[25];
        mcontrol6_32_tdata1_d[tselect_q].vs = 0;
        mcontrol6_32_tdata1_d[tselect_q].vu = 0;
        mcontrol6_32_tdata1_d[tselect_q].hit0 = tdata1_i[22];
        mcontrol6_32_tdata1_d[tselect_q].select = tdata1_i[21];
        mcontrol6_32_tdata1_d[tselect_q].zeroes = '0;
        mcontrol6_32_tdata1_d[tselect_q].size = tdata1_i[18:16];
        mcontrol6_32_tdata1_d[tselect_q].action = tdata1_i[15:12];
        mcontrol6_32_tdata1_d[tselect_q].chain = 0;
        mcontrol6_32_tdata1_d[tselect_q].match = tdata1_i[10:7];
        mcontrol6_32_tdata1_d[tselect_q].m = tdata1_i[6];
        mcontrol6_32_tdata1_d[tselect_q].uncertainen = 0;
        mcontrol6_32_tdata1_d[tselect_q].s = tdata1_i[4];
        mcontrol6_32_tdata1_d[tselect_q].u = tdata1_i[3];
        mcontrol6_32_tdata1_d[tselect_q].execute = tdata1_i[2];
        mcontrol6_32_tdata1_d[tselect_q].store = tdata1_i[1];
        mcontrol6_32_tdata1_d[tselect_q].load = tdata1_i[0];
        flush_o = 1'b1;
      end else if ((tdata1_i[31:28] == 4'd5 && CVA6Cfg.IS_XLEN32) || (tdata1_i[63:60] == 4'd5 && CVA6Cfg.IS_XLEN64)) begin
        trigger_type_d[tselect_q] = (CVA6Cfg.IS_XLEN32) ? tdata1_i[31:28] : tdata1_i[63:60];
        etrigger32_tdata1_d[tselect_q].t_type  = (CVA6Cfg.IS_XLEN32) ? ((tdata1_i[31:28] == 4'd5 || tdata1_i[31:28] == 4'd15) ? tdata1_i[31:28] : trigger_type_q[tselect_q]) : ((tdata1_i[63:60] == 4'd5 || tdata1_i[63:60] == 4'd15) ? tdata1_i[63:60] : trigger_type_q[tselect_q]);
        etrigger32_tdata1_d[tselect_q].dmode = (CVA6Cfg.IS_XLEN32) ? tdata1_i[27] : tdata1_i[59];
        etrigger32_tdata1_d[tselect_q].hit = (CVA6Cfg.IS_XLEN32) ? tdata1_i[26] : tdata1_i[58];
        etrigger32_tdata1_d[tselect_q].zeroes = '0;
        etrigger32_tdata1_d[tselect_q].vs = 0;
        etrigger32_tdata1_d[tselect_q].vu = 0;
        etrigger32_tdata1_d[tselect_q].zeroed = 0;
        etrigger32_tdata1_d[tselect_q].m = tdata1_i[9];
        etrigger32_tdata1_d[tselect_q].zero = 0;
        etrigger32_tdata1_d[tselect_q].s = tdata1_i[7];
        etrigger32_tdata1_d[tselect_q].u = tdata1_i[6];
        etrigger32_tdata1_d[tselect_q].action = tdata1_i[5:0];
      end else if ((tdata1_i[31:28] == 4'd4 && CVA6Cfg.IS_XLEN32) || (tdata1_i[63:60] == 4'd4 && CVA6Cfg.IS_XLEN64)) begin
        trigger_type_d[tselect_q] = (CVA6Cfg.IS_XLEN32) ? tdata1_i[31:28] : tdata1_i[63:60];
        itrigger32_tdata1_d[tselect_q].t_type  = (CVA6Cfg.IS_XLEN32) ? ((tdata1_i[31:28] == 4'd4 || tdata1_i[31:28] == 4'd15) ? tdata1_i[31:28] : trigger_type_q[tselect_q]) : ((tdata1_i[63:60] == 4'd4 || tdata1_i[63:60] == 4'd15) ? tdata1_i[63:60] : trigger_type_q[tselect_q]);
        itrigger32_tdata1_d[tselect_q].dmode = (CVA6Cfg.IS_XLEN32) ? tdata1_i[27] : tdata1_i[59];
        itrigger32_tdata1_d[tselect_q].hit = (CVA6Cfg.IS_XLEN32) ? tdata1_i[26] : tdata1_i[58];
        itrigger32_tdata1_d[tselect_q].zeroed = '0;
        itrigger32_tdata1_d[tselect_q].vs = 0;
        itrigger32_tdata1_d[tselect_q].vu = 0;
        itrigger32_tdata1_d[tselect_q].nmi = 0;
        itrigger32_tdata1_d[tselect_q].m = tdata1_i[9];
        itrigger32_tdata1_d[tselect_q].zero = 0;
        itrigger32_tdata1_d[tselect_q].s = tdata1_i[7];
        itrigger32_tdata1_d[tselect_q].u = tdata1_i[6];
        itrigger32_tdata1_d[tselect_q].action = tdata1_i[5:0];
      end
    end
    if (tdata2_we) begin
      tdata2_d[tselect_q] = tdata2_i;
    end
    if (tdata3_we) begin
      if (CVA6Cfg.XLEN == 32) begin  // textra32
        textra32_tdata3_d[tselect_q].mhvalue   = '0;
        textra32_tdata3_d[tselect_q].mhselect  = '0;
        textra32_tdata3_d[tselect_q].zeroes    = '0;
        textra32_tdata3_d[tselect_q].sbytemask = tdata3_i[19:18];
        textra32_tdata3_d[tselect_q].svalue    = tdata3_i[17:2];
        textra32_tdata3_d[tselect_q].sselect   = tdata3_i[1:0];
      end
      if (CVA6Cfg.XLEN == 64) begin  // textra64
        textra64_tdata3_d[tselect_q].mhvalue    = '0;
        textra64_tdata3_d[tselect_q].mhselect   = '0;
        textra64_tdata3_d[tselect_q].zeroes     = '0;
        textra64_tdata3_d[tselect_q].sbytemask  = tdata3_i[39:36];
        textra64_tdata3_d[tselect_q].zero_field = '0;
        textra64_tdata3_d[tselect_q].svalue     = tdata3_i[33:2];
        textra64_tdata3_d[tselect_q].sselect    = tdata3_i[1:0];
      end
    end


    // Triggers Match Logic
    if (CVA6Cfg.SDTRIG) begin
      for (int i = 0; i < N_Triggers; i++) begin
        priv_match[i] = 1'b0;
        matched       = 1'b0;
        // icount match logic
        if (trigger_type_d[i] == 4'd3 && CVA6Cfg.Icount) begin
          break_from_trigger_d = 1'b0;
          case(priv_lvl_i) // trigger will only fire if current priv lvl is same as the trigger configuration
            riscv::PRIV_LVL_M: if (icount32_tdata1_d[i].m) priv_match[i] = 1'b1;
            riscv::PRIV_LVL_S: if (icount32_tdata1_d[i].s) priv_match[i] = 1'b1;
            riscv::PRIV_LVL_U: if (icount32_tdata1_d[i].u) priv_match[i] = 1'b1;
            default: priv_match[i] = 1'b0;
          endcase
          // S_MODE context match check
          if (priv_lvl_i == riscv::PRIV_LVL_S && icount32_tdata1_d[i].s) begin
            if (CVA6Cfg.IS_XLEN32) begin
              scontext_match[i] = match_scontext(
                scontext_i,
                textra32_tdata3_d[i].sselect,
                textra32_tdata3_d[i].sbytemask,
                textra32_tdata3_d[i].svalue,
                1'b0
              );
            end else begin
              scontext_match[i] = match_scontext(
                scontext_i,
                textra64_tdata3_d[i].sselect,
                textra64_tdata3_d[i].sbytemask,
                textra64_tdata3_d[i].svalue,
                1'b1
              );
            end
            priv_match[i] &= scontext_match[i];
          end
          if (ex_i.valid) begin
            in_trap_handler_d = 1'b1;
            icount32_tdata1_d[i].count = icount32_tdata1_q[i].count - 1;
          end
          if (commit_ack_i && (mret_i || sret_i)) in_trap_handler_d = 1'b0;
          if (commit_ack_i && !in_trap_handler_d && (icount32_tdata1_q[i].count != 0)) begin
            icount32_tdata1_d[i].count = icount32_tdata1_q[i].count - 1;
          end
          if ((icount32_tdata1_d[i].count == 0) && priv_match[i] && !icount32_tdata1_q[i].pending && !icount32_tdata1_q[i].hit) begin
            icount32_tdata1_d[i].pending = 1'b1;
            case (icount32_tdata1_d[i].action)
              6'd0: break_from_trigger_d = 1'b1;  //breakpoint
              6'd1: debug_from_trigger_d = 1'b1;  //into debug mode
              default: ;
            endcase
          end
          if (break_from_trigger_q) begin
            icount32_tdata1_d[i].hit = 1'b1;
            icount32_tdata1_d[i].pending = 1'b0;
          end
          if (debug_mode_i && icount32_tdata1_d[i].pending) begin
            icount32_tdata1_d[i].pending = 1'b0;
            icount32_tdata1_d[i].hit = 1'b1;
            debug_from_trigger_d = 1'b0;
          end
        end
        // mcontrol6 match logic
        if (trigger_type_d[i] == 4'd6 && CVA6Cfg.Mcontrol6) begin
          case(priv_lvl_i) // trigger will only fire if current priv lvl is same as the trigger configuration
            riscv::PRIV_LVL_M: if (mcontrol6_32_tdata1_d[i].m) priv_match[i] = 1'b1;
            riscv::PRIV_LVL_S: if (mcontrol6_32_tdata1_d[i].s) priv_match[i] = 1'b1;
            riscv::PRIV_LVL_U: if (mcontrol6_32_tdata1_d[i].u) priv_match[i] = 1'b1;
            default: priv_match[i] = 1'b0;
          endcase
          // S_MODE context match check
          if (priv_lvl_i == riscv::PRIV_LVL_S && mcontrol6_32_tdata1_d[i].s) begin
            if (CVA6Cfg.IS_XLEN32) begin
              scontext_match[i] = match_scontext(
                scontext_i,
                textra32_tdata3_d[i].sselect,
                textra32_tdata3_d[i].sbytemask,
                textra32_tdata3_d[i].svalue,
                1'b0
              );
            end else begin
              scontext_match[i] = match_scontext(
                scontext_i,
                textra64_tdata3_d[i].sselect,
                textra64_tdata3_d[i].sbytemask,
                textra64_tdata3_d[i].svalue,
                1'b1
              );
            end
            priv_match[i] &= scontext_match[i];
          end
          // execute with address
          if (mcontrol6_32_tdata1_d[i].execute && !mcontrol6_32_tdata1_d[i].select) begin
            case (mcontrol6_32_tdata1_d[i].match)
              4'd0: matched = (tdata2_d[i] == commit_instr_i.pc && commit_ack_i);
              4'd1: matched = (napot_match(tdata2_d[i], commit_instr_i.pc) && commit_ack_i);
              4'd8: matched = (tdata2_d[i] != commit_instr_i.pc && commit_ack_i);
            endcase
          end
          // execute with instruction
          if (mcontrol6_32_tdata1_d[i].execute && mcontrol6_32_tdata1_d[i].select) begin
            case (mcontrol6_32_tdata1_d[i].match)
              4'd0: matched = (tdata2_d[i] == orig_instr_i);
              4'd1: matched = (napot_match(tdata2_d[i], orig_instr_i));
              4'd8: matched = (tdata2_d[i] != orig_instr_i);
            endcase
          end
          // store with data
          if (mcontrol6_32_tdata1_d[i].store && mcontrol6_32_tdata1_d[i].select) begin
            case (mcontrol6_32_tdata1_d[i].match)
              4'd0: matched = (tdata2_d[i] == store_result_i);
              4'd1: matched = (napot_match(tdata2_d[i], store_result_i));
              4'd8: matched = (tdata2_d[i] != store_result_i);
            endcase
          end
          // store with address
          if (mcontrol6_32_tdata1_d[i].store && !mcontrol6_32_tdata1_d[i].select) begin
            case (mcontrol6_32_tdata1_d[i].match)
              4'd0: matched = (tdata2_d[i] == vaddr_from_lsu_i);
              4'd1: matched = (napot_match(tdata2_d[i], vaddr_from_lsu_i));
              4'd8: matched = (tdata2_d[i] != vaddr_from_lsu_i);
            endcase
          end
          // load with data
          if (mcontrol6_32_tdata1_d[i].load && mcontrol6_32_tdata1_d[i].select) begin
            case (mcontrol6_32_tdata1_d[i].match)
              4'd0: matched = (tdata2_d[i] == commit_instr_i.result && commit_instr_i.op == 8'h27);
              4'd1:
              matched = (napot_match(tdata2_d[i], commit_instr_i.result) &&
                         commit_instr_i.op == 8'h27);
              4'd8: matched = (tdata2_d[i] != commit_instr_i.result && commit_instr_i.op == 8'h27);
            endcase
          end
          // load with address
          if (mcontrol6_32_tdata1_d[i].load && !mcontrol6_32_tdata1_d[i].select) begin
            case (mcontrol6_32_tdata1_d[i].match)
              4'd0: matched = (tdata2_d[i] == vaddr_from_lsu_i);
              4'd1: matched = (napot_match(tdata2_d[i], vaddr_from_lsu_i));
              4'd8: matched = (tdata2_d[i] != vaddr_from_lsu_i);
            endcase
          end
          if (priv_match[i] && matched) begin
            case (mcontrol6_32_tdata1_d[i].action)
              //6'd0: breakpoint action currently not supported
              6'd1: mcontrol6_debug_d = 1'b1;  //into debug mode;
              default: ;
            endcase
          end
          if (debug_mode_i && matched) begin
            matched = 1'b0;
            mcontrol6_32_tdata1_d[i].hit0 = 1'b0;
            mcontrol6_32_tdata1_d[i].hit1 = 1'b1;
            mcontrol6_debug_d = 1'b0;
          end
        end
        // etrigger match logic
        if (trigger_type_d[i] == 4'd5 && CVA6Cfg.Etrigger) begin
          break_from_trigger_d = 1'b0;
          case(priv_lvl_i) // trigger will only fire if current priv lvl is same as the trigger configuration
            riscv::PRIV_LVL_M: if (etrigger32_tdata1_d[i].m) priv_match[i] = 1'b1;
            riscv::PRIV_LVL_S: if (etrigger32_tdata1_d[i].s) priv_match[i] = 1'b1;
            riscv::PRIV_LVL_U: if (etrigger32_tdata1_d[i].u) priv_match[i] = 1'b1;
            default: priv_match[i] = 1'b0;
          endcase
          // S_MODE context match check
          if (priv_lvl_i == riscv::PRIV_LVL_S && etrigger32_tdata1_d[i].s) begin
            if (CVA6Cfg.IS_XLEN32) begin
              scontext_match[i] = match_scontext(
                scontext_i,
                textra32_tdata3_d[i].sselect,
                textra32_tdata3_d[i].sbytemask,
                textra32_tdata3_d[i].svalue,
                1'b0
              );
            end else begin
              scontext_match[i] = match_scontext(
                scontext_i,
                textra64_tdata3_d[i].sselect,
                textra64_tdata3_d[i].sbytemask,
                textra64_tdata3_d[i].svalue,
                1'b1
              );
            end
            priv_match[i] &= scontext_match[i];
          end
          if (tdata2_d[i][ex_i.cause]) e_matched_d = 1'b1;
          if (mret_i || sret_i) mret_reg_d = 1'b1;
          if (e_matched_q && priv_match[i] && mret_reg_q && commit_ack_i) begin
            e_matched_d = 1'b0;
            etrigger32_tdata1_d[i].hit = 1'b1;
            case (etrigger32_tdata1_d[i].action)
              6'd0: break_from_trigger_d = 1'b1;  //breakpoint
              6'd1: debug_from_trigger_d = 1'b1;  //into debug mode;
              default: ;
            endcase
          end
          if (break_from_trigger_q) begin
            etrigger32_tdata1_d[i].hit = 1'b0;
            break_from_trigger_d = 1'b0;
          end
          if (debug_mode_i && debug_from_trigger_d) begin
            etrigger32_tdata1_d[i].hit = 1'b0;
            debug_from_trigger_d = 1'b0;
          end
        end
        // itrigger match logic
        if (trigger_type_d[i] == 4'd4 && CVA6Cfg.Itrigger) begin
          break_from_trigger_d = 1'b0;
          case(priv_lvl_i) // trigger will only fire if current priv lvl is same as the trigger configuration
            riscv::PRIV_LVL_M: if (itrigger32_tdata1_d[i].m) priv_match[i] = 1'b1;
            riscv::PRIV_LVL_S: if (itrigger32_tdata1_d[i].s) priv_match[i] = 1'b1;
            riscv::PRIV_LVL_U: if (itrigger32_tdata1_d[i].u) priv_match[i] = 1'b1;
            default: priv_match[i] = 1'b0;
          endcase
          // S_MODE context match check
          if (priv_lvl_i == riscv::PRIV_LVL_S && itrigger32_tdata1_d[i].s) begin
            if (CVA6Cfg.IS_XLEN32) begin
              scontext_match[i] = match_scontext(
                scontext_i,
                textra32_tdata3_d[i].sselect,
                textra32_tdata3_d[i].sbytemask,
                textra32_tdata3_d[i].svalue,
                1'b0
              );
            end else begin
              scontext_match[i] = match_scontext(
                scontext_i,
                textra64_tdata3_d[i].sselect,
                textra64_tdata3_d[i].sbytemask,
                textra64_tdata3_d[i].svalue,
                1'b1
              );
            end
            priv_match[i] &= scontext_match[i];
          end
          if (ex_i.cause[CVA6Cfg.XLEN-1]) begin
            if (tdata2_d[i][ex_i.cause[4:0]]) e_matched_d = 1'b1;
          end
          if (mret_i || sret_i) mret_reg_d = 1'b1;
          if (e_matched_q && priv_match[i] && mret_reg_q && commit_ack_i) begin
            e_matched_d = 1'b0;
            itrigger32_tdata1_d[i].hit = 1'b1;
            case (itrigger32_tdata1_d[i].action)
              6'd0: break_from_trigger_d = 1'b1;  //breakpoint
              6'd1: debug_from_trigger_d = 1'b1;  //into debug mode;
              default: ;
            endcase
          end
          if (break_from_trigger_q) begin
            itrigger32_tdata1_d[i].hit = 1'b0;
            break_from_trigger_d = 1'b0;
          end
          if (debug_mode_i && debug_from_trigger_d) begin
            itrigger32_tdata1_d[i].hit = 1'b0;
            debug_from_trigger_d = 1'b0;
          end
        end
      end
    end
  end


  always_comb begin : read_path
    tselect_o = '0;
    tdata1_o  = '0;
    tdata2_o  = '0;
    tdata3_o  = '0;

    // TSELECT read
    tselect_o = {{(CVA6Cfg.XLEN - N_Triggers) {1'b0}}, tselect_q};

    // TDATA1 read (depends on trigger type)
    unique case (trigger_type_q[tselect_q])
      4'd3:
      tdata1_o = (CVA6Cfg.IS_XLEN32) ? icount32_tdata1_q[tselect_q] : { icount32_tdata1_q[tselect_q].t_type, icount32_tdata1_q[tselect_q].dmode, 32'd0, icount32_tdata1_q[tselect_q][26:0] };
      4'd6:
      tdata1_o = (CVA6Cfg.IS_XLEN32) ? mcontrol6_32_tdata1_q[tselect_q] : { mcontrol6_32_tdata1_q[tselect_q].t_type, mcontrol6_32_tdata1_q[tselect_q].dmode, 32'd0, mcontrol6_32_tdata1_q[tselect_q][26:0] };
      4'd5:
      tdata1_o = (CVA6Cfg.IS_XLEN32) ? etrigger32_tdata1_q[tselect_q] : { etrigger32_tdata1_q[tselect_q].t_type, etrigger32_tdata1_q[tselect_q].dmode, etrigger32_tdata1_q[tselect_q].hit, 45'd0, etrigger32_tdata1_q[tselect_q][12:0] };
      4'd4:
      tdata1_o = (CVA6Cfg.IS_XLEN32) ? itrigger32_tdata1_q[tselect_q] : { itrigger32_tdata1_q[tselect_q].t_type, itrigger32_tdata1_q[tselect_q].dmode, itrigger32_tdata1_q[tselect_q].hit, 45'd0, itrigger32_tdata1_q[tselect_q][12:0] };
      default: ;
    endcase

    // TDATA2 read
    tdata2_o = tdata2_q[tselect_q];

    // TDATA3 read
    tdata3_o = (CVA6Cfg.XLEN == 32) ? textra32_tdata3_q[tselect_q] : textra64_tdata3_q[tselect_q];
  end


  always_ff @(posedge clk_i or negedge rst_ni) begin : state_update
    if (~rst_ni) begin
      if (CVA6Cfg.SDTRIG) begin
        tselect_q <= '0;
        mcontrol6_debug_q <= 1'b0;
        e_matched_q <= 1'b0;
        mret_reg_q <= 1'b0;
        break_from_trigger_q <= 0;
        debug_from_trigger_q <= 0;
        in_trap_handler_q <= 0;
        for (int i = 0; i < N_Triggers; ++i) begin
          trigger_type_q[i]          <= '0;
          icount32_tdata1_q[i]       <= '0;
          icount32_tdata1_q[i].count <= 1;
          mcontrol6_32_tdata1_q[i]   <= '0;
          textra32_tdata3_q[i]       <= '0;
          textra64_tdata3_q[i]       <= '0;
          tdata2_q[i]                <= '0;
          etrigger32_tdata1_q[i]     <= '0;
          itrigger32_tdata1_q[i]     <= '0;
        end
      end
    end else begin
      if (CVA6Cfg.SDTRIG) begin
        trigger_type_q        <= trigger_type_d;
        tselect_q             <= tselect_d;
        tdata2_q              <= tdata2_d;
        icount32_tdata1_q     <= icount32_tdata1_d;
        mcontrol6_32_tdata1_q <= mcontrol6_32_tdata1_d;
        etrigger32_tdata1_q   <= etrigger32_tdata1_d;
        itrigger32_tdata1_q   <= itrigger32_tdata1_d;
        textra32_tdata3_q     <= textra32_tdata3_d;
        textra64_tdata3_q     <= textra64_tdata3_d;
        mcontrol6_debug_q     <= mcontrol6_debug_d;
        break_from_trigger_q  <= break_from_trigger_d;
        debug_from_trigger_q  <= debug_from_trigger_d;
        in_trap_handler_q     <= in_trap_handler_d;
        e_matched_q           <= e_matched_d;
        mret_reg_q            <= mret_reg_d;
      end
    end
  end

  // Outputs
  assign debug_from_trigger_o  = debug_from_trigger_q;
  assign break_from_trigger_o  = break_from_trigger_q;
  assign debug_from_mcontrol_o = mcontrol6_debug_d & ~mcontrol6_debug_q;

endmodule
