/* File:   ariane_pkg.svh
 * Author: Florian Zaruba <zarubaf@ethz.ch>
 * Date:   8.4.2017
 *
 * Copyright (C) 2017 ETH Zurich, University of Bologna
 * All rights reserved.
 *
 * Description: Contains all the necessary defines for Ariane
 *              in one package.
 */
package ariane_pkg;

// ---------------
// Fetch Stage
// ---------------

// Only use struct when signals have same direction
typedef struct packed {
     logic [63:0] pc;
     logic [63:0] branch_target_address;
     logic        valid;
} btb;

// input to the fetch stage
typedef struct packed {
     logic [63:0] ra;           // return address
     logic        is_call;      // is call - pop from stack
     logic        is_return;    // is return - push on stack
} ras;

// exception
typedef struct packed {
     logic [63:0] epc;
     logic [63:0] cause;
     logic        valid;
} exception;

// miss-predict
typedef struct packed {
     logic [63:0] pc;
     logic        valid; // is miss-predict
} misspredict;

typedef enum logic[3:0] {
    NONE, ALU, MULT, LSU, CSR
} fu_t;

// ---------------
// EX Stage
// ---------------

typedef enum logic [7:0]      { ADD, SUB, ADDW, SUBW,                             // basic ALU op
                                XORL, ORL, ANDL,                                  // logic operations
                                SRA, SRL, SLL, SRLW, SLLW, SRAW,                  // shifts
                                LTS, LTU, LES, LEU, GTS, GTU, GES, GEU, EQ, NE,   // comparisons
                                SLTS, SLTU, SLETS, SLETU,                         // set lower than operations
                                MRET, SRET, URET, ECALL, WRITE, READ, SET, CLEAR, // CSR functions
                                LD, SD, LW, SW, LH, SH, LB, SB, LBU, SBU          // LSU functions
                              } alu_op;


// ---------------
// ID/EX/WB Stage
// ---------------
typedef struct packed {
    logic [63:0]    pc;
    fu_t            fu;
    alu_op          op;
    logic [4:0]     rs1;
    logic [4:0]     rs2;
    logic [4:0]     rd;
    logic [63:0]    result;
    logic           valid;
    logic           use_imm;
    logic [63:0]    imm;       // maybe we can get this into the results field
    exception       ex;        // the PC is redundant here
} scoreboard_entry;

endpackage
