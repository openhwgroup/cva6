// Author: Florian Zaruba, ETH Zurich
// Date: 02.05.2017
// Description: LSU interface
//
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.

// Guard statement proposed by "Easier UVM" (doulos)
`ifndef LSU_IF_SV
`define LSU_IF_SV
import ariane_pkg::*;

interface lsu_if #(
        parameter int OPERAND_SIZE = 64
    )
    (
        input clk
    );

    fu_op                    operator;          // FU operation
    wire [OPERAND_SIZE-1:0]  operand_a;         // Operand A
    wire [OPERAND_SIZE-1:0]  operand_b;         // Operand B
    wire [OPERAND_SIZE-1:0]  imm;               // Operand B
    wire [OPERAND_SIZE-1:0]  result;            // Result
    wire [TRANS_ID_BITS-1:0] lsu_trans_id_id;   // transaction id from ID
    wire [TRANS_ID_BITS-1:0] lsu_trans_id_wb;   // transaction id to WB
    // LSU control signals
    wire                     commit;
    wire                     source_valid;      // Source operands are valid
    wire                     result_valid;      // Result is valid, ready to accept new request
    wire                     ready;             // Sink is ready
    // exceptions
    exception                exception;

    // FU interface configured as master
    clocking mck @(posedge clk);
        output operator, operand_a, operand_b, imm, source_valid, commit, lsu_trans_id_id;
        input  result, lsu_trans_id_wb, result_valid, ready, exception;
    endclocking
    // FU interface configured as slave
    clocking sck @(posedge clk);
        input  operator, operand_a, operand_b, imm, source_valid, commit, lsu_trans_id_id;
        output result, lsu_trans_id_wb, result_valid, ready, exception;
    endclocking
    // FU interface configured in passive mode
    clocking pck @(posedge clk);
        input operator, operand_a, operand_b, imm, source_valid, commit, lsu_trans_id_id,
              result, lsu_trans_id_wb, result_valid, ready, exception ;
    endclocking

    modport master  (clocking mck);
    modport slave   (clocking sck);
    modport passive (clocking pck);

endinterface
`endif
