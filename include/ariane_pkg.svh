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

    localparam EXC_OFF_RST      = 8'h80;
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
        logic [4:0]     trans_id; // this can potentially be simplified, we could index the scoreboard entry with the transaction id
                                  // in any case make the width more generic
        fu_t            fu;
        alu_op          op;
        logic [4:0]     rs1;
        logic [4:0]     rs2;
        logic [4:0]     rd;
        logic [63:0]    result;
        logic           valid;
        logic           use_imm;
        logic           use_pc;    // set if we need to use the PC as operand A, PC from exception
        logic [63:0]    imm;       // maybe we can get this into the results field
        exception       ex;
    } scoreboard_entry;

    // --------------------
    // Instruction Types
    // --------------------
    typedef struct packed {
        logic [31:25] funct7;
        logic [24:20] rs2;
        logic [19:15] rs1;
        logic [14:12] funct3;
        logic [11:7]  rd;
        logic [6:0]   opcode;
    } rtype;

    typedef struct packed {
        logic [31:20] imm;
        logic [19:15] rs1;
        logic [14:12] funct3;
        logic [11:7]  rd;
        logic [6:0]   opcode;
    } itype;

    typedef struct packed {
        logic [31:25] imm1;
        logic [24:20] rs2;
        logic [19:15] rs1;
        logic [14:12] funct3;
        logic [11:7]  imm0;
        logic [6:0]   opcode;
    } stype;

    typedef struct packed {
        logic [31:12] funct3;
        logic [11:7]  rd;
        logic [6:0]   opcode;
    } utype;

    typedef union packed {
        logic [31:0] instr;
        rtype        rtype;
        itype        itype;
        stype        stype;
        utype        utype;
    } instruction;

    // --------------------
    // Opcodes
    // --------------------
    localparam OPCODE_SYSTEM    = 7'h73;
    localparam OPCODE_FENCE     = 7'h0f;
    localparam OPCODE_OP        = 7'h33;
    localparam OPCODE_OP32      = 7'h3B;
    localparam OPCODE_OPIMM     = 7'h13;
    localparam OPCODE_OPIMM32   = 7'h1B;
    localparam OPCODE_STORE     = 7'h23;
    localparam OPCODE_LOAD      = 7'h03;
    localparam OPCODE_BRANCH    = 7'h63;
    localparam OPCODE_JALR      = 7'h67;
    localparam OPCODE_JAL       = 7'h6f;
    localparam OPCODE_AUIPC     = 7'h17;
    localparam OPCODE_LUI       = 7'h37;

    // --------------------
    // Immediate select
    // --------------------
    typedef enum logic[3:0] {
        NOIMM, PCIMM, IIMM, SIMM, BIMM, UIMM, JIMM
    } imm_sel_t;

    // --------------------
    // Privilege Spec
    // --------------------
    typedef enum logic[1:0] {
      PRIV_LVL_M = 2'b11,
      // PRIV_LVL_H = 2'b10, This mode does not longer exist
      PRIV_LVL_S = 2'b01,
      PRIV_LVL_U = 2'b00
    } priv_lvl_t;

endpackage
