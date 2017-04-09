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
interface scoreboard_if (input clk);
    wire                                   rst;
    wire                                   full;
    wire                                   flush;
    wire [31:0][7:0]           rd_clobber;
    wire [4:0]                             rs1_address;
    wire [63:0]                            rs1;
    wire                                   rs1_valid;
    wire [4:0]                             rs2_address;
    wire [63:0]                            rs2;
    wire                                   rs2_valid;
    wire                                   commitnstr;
    wire                                   commit_ready;
    wire                                   decodednstr;
    wire                                   decodednstr_valid;
    wire                                   issuenstr;
    wire                                   issuenstr_valid;
    wire                                   issue_ready;
    wire [63:0]                            pc;
    wire [63:0]                            wdata;
    wire                                   wb_valid;

    // Scoreboard interface configured as master
    clocking mck @(posedge clk);
        output   rst, flush, rs1_address, rs2_address, commit_ready, decodednstr, decodednstr_valid, issue_ready, pc, wdata, wb_valid;
        input    full, rd_clobber, rs1, rs1_valid, rs2, rs2_valid, commitnstr, issuenstr, issuenstr_valid;
    endclocking
    // Scoreboard interface configured in passive mode (-> monitor)
    clocking pck @(posedge clk);
        input rst, flush, rs1_address, rs2_address, commit_ready, decodednstr, decodednstr_valid, issue_ready, pc, wdata, wb_valid,
              full, rd_clobber, rs1, rs1_valid, rs2, rs2_valid, commitnstr, issuenstr, issuenstr_valid;
    endclocking

    modport master  (clocking mck);
    modport passive (clocking pck);

endinterface
`endif
