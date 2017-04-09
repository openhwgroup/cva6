// Author: Florian Zaruba, ETH Zurich
// Date: 3/18/2017
// Description: Generic functional unit interface (fu if)
//              The interface can be used in Master or Slave mode.
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.

// Guard statement proposed by "Easier UVM" (doulos)
`ifndef ALU_IF__SV
`define ALU_IF__SV
interface fu_if #(parameter int OPERATOR_SIZE = 8, parameter int OPERAND_SIZE = 64)(input clk);
    wire [OPERATOR_SIZE-1:0] operator;          // FU operation
    wire [OPERAND_SIZE-1:0]  operand_a;         // Operand A
    wire [OPERAND_SIZE-1:0]  operand_b;         // Operand B
    wire [OPERAND_SIZE-1:0]  operand_c;         // Operand C

    wire [OPERAND_SIZE-1:0]  result;            // Result
    wire                     comparison_result; // Comparison result
    wire                     valid;             // Result is valid, ready to accept new request
    wire                     ready;             // Sink is ready

    // FU interface configured as master
    clocking mck @(posedge clk);
        input   operator, operand_a, operand_b, operand_c, ready;
        output  result, comparison_result, valid;
    endclocking
    // FU interface configured as slave
    clocking sck @(posedge clk);
        output  operator, operand_a, operand_b, operand_c, ready;
        input  result, comparison_result, valid;
    endclocking
    // FU interface configured in passive mode
    clocking pck @(posedge clk);
        input operator, operand_a, operand_b, operand_c, result, ready;
    endclocking

    modport master  (clocking mck);
    modport slave   (clocking sck);
    modport passive (clocking pck);

endinterface
`endif
