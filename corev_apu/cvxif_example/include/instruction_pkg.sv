// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Guillaume Chauvon (guillaume.chauvon@thalesgroup.com)

package instruction_pkg;

typedef struct packed {
    logic [31:0]               instr;
    logic [31:0]               mask;
    cvxif_pkg::x_issue_resp_t  resp;
} copro_issue_resp_t;

// 9 Possible RISCV instructions for Coprocessor
parameter int unsigned NumInstr = 9;
parameter copro_issue_resp_t OffloadInstr[NumInstr] = '{
  '{
    instr: 32'b 00000_00_00000_00000_0_00_00001_0101011,
    mask: 32'b 00000_11_00000_00000_1_11_11111_1111111,
    resp : '{
      accept : 1'b1,
      writeback : 1'b0,
      dualwrite : 1'b0,
      dualread : 1'b0,
      loadstore : 1'b0,
      exc : 1'b0
   }
  },
  '{
    instr: 32'b 00000_00_00000_00000_1_01_00000_0101011,
    mask: 32'b 11111_11_00000_00000_1_11_00000_1111111,
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
    instr: 32'b 00000_11_00000_00000_0_11_00001_0101011,
    mask: 32'b 00000_11_00000_00000_1_11_11111_1111111,
    resp : '{
      accept : 1'b1,
      writeback : 1'b0,
      dualwrite : 1'b0,
      dualread : 1'b0,
      loadstore : 1'b0,
      exc : 1'b0
   }
  },
  '{
    instr: 32'b 00000_00_00000_00000_0_01_00001_0101011,
    mask: 32'b 00000_11_00000_00000_1_11_11111_1111111,
    resp : '{
      accept : 1'b1,
      writeback : 1'b0,
      dualwrite : 1'b0,
      dualread : 1'b0,
      loadstore : 1'b0,
      exc : 1'b0
   }
  },
  '{
    instr: 32'b 00000_01_00000_00000_0_00_00000_0101011,
    mask: 32'b 00000_11_00000_00000_1_11_11110_1111111,
    resp : '{
      accept : 1'b1,
      writeback : 1'b0,
      dualwrite : 1'b0,
      dualread : 1'b0,
      loadstore : 1'b0,
      exc : 1'b0
   }
  },
  '{
    instr: 32'b 00000_00_00000_00000_0_10_00000_0101011,
    mask: 32'b 00000_11_00000_00000_1_11_11111_1111111,
    resp : '{
      accept : 1'b1,
      writeback : 1'b0,
      dualwrite : 1'b0,
      dualread : 1'b0,
      loadstore : 1'b0,
      exc : 1'b0
   }
  },
  '{
    instr: 32'b 00000_01_00000_00000_0_01_00000_0101011,
    mask: 32'b 00000_11_00000_00000_1_11_11110_1111111,
    resp : '{
      accept : 1'b1,
      writeback : 1'b0,
      dualwrite : 1'b0,
      dualread : 1'b0,
      loadstore : 1'b0,
      exc : 1'b0
   }
  },
  '{
    instr: 32'b 00000_00_00000_00000_0_11_00000_0101011,
    mask: 32'b 00000_11_00000_00000_1_11_11110_1111111,
    resp : '{
      accept : 1'b1,
      writeback : 1'b0,
      dualwrite : 1'b0,
      dualread : 1'b0,
      loadstore : 1'b0,
      exc : 1'b0
   }
  },
  '{
    instr: 32'b 00000_01_00000_00000_0_10_00000_0101011,
    mask: 32'b 00000_11_00000_00000_1_11_11110_1111111,
    resp : '{
      accept : 1'b1,
      writeback : 1'b0,
      dualwrite : 1'b0,
      dualread : 1'b0,
      loadstore : 1'b0,
      exc : 1'b0
   }
  }
};

endpackage
