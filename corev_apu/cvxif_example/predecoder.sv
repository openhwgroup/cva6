// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Noam Gallmann <gnoam@live.com>

// Per-extension instruction metadata predecoder

// Modified by Guillaume Chauvon <guillaume.chauvon@thalesgroup.com> 
// to be aligned on the CoreV-eXtension-Interface

module predecoder import cvxif_pkg::*; #(
   parameter int                                  NumInstr               = 1,
   parameter instruction_pkg::copro_issue_resp_t  OffloadInstr[NumInstr] = {0}
)
(
    input   x_issue_req_t      x_issue_req_i,               
    output  x_issue_resp_t     x_issue_resp_o

);

  x_issue_resp_t  [NumInstr-1:0] instr_resp;
  logic           [NumInstr-1:0] instr_sel;

  for (genvar i = 0; i < NumInstr; i++) begin : gen_predecoder_selector
    assign instr_sel[i] =
      ((OffloadInstr[i].mask & x_issue_req_i.instr) == OffloadInstr[i].instr);
  end
  
  for (genvar i = 0; i < NumInstr; i++) begin : gen_predecoder_mux
    assign instr_resp[i].accept     = instr_sel[i] ? 1'b1 : 1'b0;
    assign instr_resp[i].writeback  = instr_sel[i] ? OffloadInstr[i].resp.writeback : '0;
    assign instr_resp[i].dualwrite  = instr_sel[i] ? OffloadInstr[i].resp.dualwrite : '0;
    assign instr_resp[i].dualread   = instr_sel[i] ? OffloadInstr[i].resp.dualread : '0;
    assign instr_resp[i].loadstore  = instr_sel[i] ? OffloadInstr[i].resp.loadstore : '0;
    assign instr_resp[i].exc        = instr_sel[i] ? OffloadInstr[i].resp.exc : '0;
  end
  
   always_comb begin
    x_issue_resp_o.accept     = 1'b0;
    x_issue_resp_o.writeback  = '0;
    x_issue_resp_o.dualwrite  = '0;
    x_issue_resp_o.dualread   = '0;
    x_issue_resp_o.loadstore  = '0;
    x_issue_resp_o.exc        = '0;
    for (int unsigned i = 0; i < NumInstr; i++) begin
      x_issue_resp_o.accept     |= instr_resp[i].accept;
      x_issue_resp_o.writeback  |= instr_resp[i].writeback;
      x_issue_resp_o.dualwrite  |= instr_resp[i].dualwrite;
      x_issue_resp_o.dualread   |= instr_resp[i].dualread;
      x_issue_resp_o.loadstore  |= instr_resp[i].loadstore;
      x_issue_resp_o.exc        |= instr_resp[i].exc;
    end
  end
  
endmodule
