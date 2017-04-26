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
    // Global Config
    // ---------------
    localparam NR_SB_ENTRIES = 4; // number of scoreboard entries
    localparam TRANS_ID_BITS = $clog2(NR_SB_ENTRIES); // depending on the number of scoreboard entries we need that many bits
                                                      // to uniquely identify the entry in the scoreboard
    localparam NR_WB_PORTS   = 2;
    // ---------------
    // Fetch Stage
    // ---------------
    // Only use struct when signals have same direction
    // exception
    typedef struct packed {
         logic [63:0] epc;
         logic [63:0] cause;
         logic        valid;
    } exception;

    // miss-predict
    typedef struct packed {
         logic [63:0] pc;
         logic [63:0] target_address;
         logic        is_taken;
         logic        valid; // is miss-predict
    } misspredict;

    typedef enum logic[3:0] {
        NONE, LSU, ALU, MULT, CSR
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
                                    LD, SD, LW, LWU, SW, LH, LHU, SH, LB, SB, LBU, SBU          // LSU functions
                                  } fu_op;

    // ---------------
    // ID/EX/WB Stage
    // ---------------
    typedef struct packed {
        logic [TRANS_ID_BITS-1:0]     trans_id;      // this can potentially be simplified, we could index the scoreboard entry
                                                     // with the transaction id in any case make the width more generic
        fu_t                          fu;            // functional unit to use
        fu_op                         op;            // operation to perform in each functional unit
        logic [4:0]                   rs1;           // register source address 1
        logic [4:0]                   rs2;           // register source address 2
        logic [4:0]                   rd;            // register destination address
        logic [63:0]                  result;        // for unfinished instructions this field also holds the immediate
        logic                         valid;         // is the result valid
        logic                         use_imm;       // should we use the immediate as operand b?
        logic                         use_pc;        // set if we need to use the PC as operand A, PC from exception
        exception                     ex;            // exception has occurred
        logic                         is_compressed; // signals a compressed instructions, we need this information at the commit stage if
                                                     // we want jump accordingly e.g.: +4, +2
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

    // for some reason verilator complains about this union
    // since I am not using it for simulation anyway and linting only
    // it is not too bad to deactivate it, but a future me (or you)
    // should look into that more thoroughly
    `ifndef verilator
    typedef union packed {
        logic [31:0] instr;
        rtype        rtype;
        itype        itype;
        stype        stype;
        utype        utype;
    } instruction;
    `endif

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

    // memory management, pte
    typedef struct packed {
        logic[37:0] ppn;
        logic[1:0] sw_reserved;
        logic d;
        logic a;
        logic g;
        logic u;
        logic x;
        logic w;
        logic r;
        logic v;
    } pte_t;

    // Bits required for representation of physical address space as 4K pages
    // (e.g. 27*4K == 39bit address space).
    localparam PPN4K_WIDTH = 38;

    // ----------------------
    // Exception Cause Codes
    // ----------------------
    localparam INSTR_ADDR_MISALIGNED = 64'h0;
    localparam INSTR_ACCESS_FAULT    = 64'h1;
    localparam ILLEGAL_INSTR         = 64'h2;
    localparam BREAKPOINT            = 64'h3;
    localparam LD_ADDR_MISALIGNED    = 64'h4;
    localparam LD_ACCESS_FAULT       = 64'h5;
    localparam ST_ADDR_MISALIGNED    = 64'h6;
    localparam ST_ACCESS_FAULT       = 64'h7;
    localparam ENV_CALL_UMODE        = 64'h8;
    localparam ENV_CALL_SMODE        = 64'h9;
    localparam ENV_CALL_MMODE        = 64'hB;
endpackage
