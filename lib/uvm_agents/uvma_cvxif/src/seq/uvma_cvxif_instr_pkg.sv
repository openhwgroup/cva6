// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Zineb EL KACIMI (zineb.el-kacimi@external.thalesgroup.com)


`ifndef __UVMA_CVXIF_INSTR_PKG_SV__
`define __UVMA_CVXIF_INSTR_PKG_SV__


package uvma_cvxif_instr_pkg;

typedef struct packed {
    logic [31:0]               instr;
    logic [31:0]               mask;
    cvxif_pkg::x_issue_resp_t  resp;
} cvxif_issue_resp_t;

// RISCV instructions supported by CVXIF Agent
parameter int unsigned NumInstr = 2;
parameter cvxif_issue_resp_t OffloadInstr[NumInstr] = '{
  '{
    instr: 32'b 00000_00_00000_00000_0_00_00000_0101011, // custom1 opcode
    mask:  32'b 00000_00_00000_00000_0_00_00000_1111111,
    resp : '{
      accept : 1'b1,
      writeback : 1'b1,
      dualwrite : 1'b0,
      dualread : 1'b0,
      loadstore : 1'b0,
      exc : 1'b0
   }
  },
  '{
    instr: 32'b 00000_00_00000_00000_0_00_00000_1011011, // custom2 opcode
    mask:  32'b 00000_00_00000_00000_0_00_00000_1111111,
    resp : '{
      accept : 1'b1,
      writeback : 1'b1,
      dualwrite : 1'b0,
      dualread : 1'b0,
      loadstore : 1'b0,
      exc : 1'b0
   }
  }
};

endpackage


`endif //__UVMA_CVXIF_INSTR_PKG_SV__
