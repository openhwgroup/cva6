// Author: Florian Zaruba, ETH Zurich
// Date: 3/18/2017
// Description: Scoreboard interface
//              The interface can be used in Master or Slave mode.
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.

// Guard statement proposed by "Easier UVM" (doulos)
`ifndef SCOREBOARD_IF__SV
`define SCOREBOARD_IF_SV

import ariane_pkg::*;

interface scoreboard_if #(parameter int NR_WB_PORTS = 1)(input clk);
    wire                                          full;
    wire                                          flush;
    wire [31:0]                                   rd_clobber;
    wire [4:0]                                    rs1_address;
    wire [63:0]                                   rs1;
    wire                                          rs1_valid;
    wire [4:0]                                    rs2_address;
    wire [63:0]                                   rs2;
    wire                                          rs2_valid;
    scoreboard_entry                              commit_instr;
    wire                                          commit_ack;
    scoreboard_entry                              decoded_instr;
    wire                                          decoded_instr_valid;
    scoreboard_entry                              issue_instr;
    wire                                          issue_instr_valid;
    wire                                          issue_ack;
    wire [NR_WB_PORTS-1:0][TRANS_ID_BITS-1:0]     trans_id;
    wire [NR_WB_PORTS-1:0][63:0]                  wdata;
    wire [NR_WB_PORTS-1:0]                        wb_valid;

    // Scoreboard interface configured as master
    clocking mck @(posedge clk);
        default input #1 output #5; // save timing
        output   flush, rs1_address, rs2_address, commit_ack, decoded_instr, decoded_instr_valid, issue_ack, trans_id, wdata, wb_valid;
        input    full, rd_clobber, rs1, rs1_valid, rs2, rs2_valid, commit_instr, issue_instr, issue_instr_valid;
    endclocking
    // Scoreboard interface configured in passive mode (-> monitor)
    clocking pck @(posedge clk);
        input flush, rs1_address, rs2_address, commit_ack, decoded_instr, decoded_instr_valid, issue_ack, trans_id, wdata, wb_valid,
              full, rd_clobber, rs1, rs1_valid, rs2, rs2_valid, commit_instr, issue_instr, issue_instr_valid;
    endclocking

    modport master  (clocking mck);
    modport passive (clocking pck);

endinterface
`endif
