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
    localparam NR_WB_PORTS   = 4;
    localparam ASID_WIDTH    = 1;
    localparam logic [63:0] ISA_CODE = (1 <<  2)  // C - Compressed extension
                                     | (1 <<  8)  // I - RV32I/64I/128I base ISA
                                     | (1 << 12)  // M - Integer Multiply/Divide extension
                                     | (0 << 13)  // N - User level interrupts supported
                                     | (1 << 18)  // S - Supervisor mode implemented
                                     | (1 << 20)  // U - User mode implemented
                                     | (0 << 23)  // X - Non-standard extensions present
                                     | (1 << 63); // RV64

    // ---------------
    // Fetch Stage
    // ---------------
    // Only use struct when signals have same direction
    // exception
    typedef struct packed {
         logic [63:0] cause; // cause of exception
         logic [63:0] tval;  // additional information of causing exception (e.g.: instruction causing it),
                             // address of LD/ST fault
         logic        valid;
    } exception;

    // branch-predict
    // this is the struct we get back from ex stage and we will use it to update
    // all the necessary data structures
    typedef struct packed {
        logic [63:0] pc;              // pc of predict or mis-predict
        logic [63:0] target_address;  // target address at which to jump, or not
        logic        is_mispredict;   // set if this was a mis-predict
        logic        is_taken;        // branch is taken
        logic        is_lower_16;     // branch instruction is compressed and resides
                                      // in the lower 16 bit of the word
        logic        valid;           // prediction with all its values is valid
        logic        clear;           // invalidate this entry
    } branchpredict;

    // branchpredict scoreboard entry
    // this is the struct which we will inject into the pipeline to guide the various
    // units towards the correct branch decision and resolve
    typedef struct packed {
        logic [63:0] predict_address; // target address at which to jump, or not
        logic        predict_taken;   // branch is taken
        logic        is_lower_16;     // branch instruction is compressed and resides
                                      // in the lower 16 bit of the word
        logic        valid;           // this is a valid hint
    } branchpredict_sbe;

    typedef enum logic[3:0] {
        NONE, LOAD, STORE, ALU, CTRL_FLOW, MULT, CSR
    } fu_t;

    localparam EXC_OFF_RST      = 8'h80;

    // ---------------
    // EX Stage
    // ---------------
    typedef enum logic [5:0] { // basic ALU op
                               ADD, SUB, ADDW, SUBW,
                               // logic operations
                               XORL, ORL, ANDL,
                               // shifts
                               SRA, SRL, SLL, SRLW, SLLW, SRAW,
                               // comparisons
                               LTS, LTU, GES, GEU, EQ, NE,
                               // jumps
                               JAL, JALR,
                               // set lower than operations
                               SLTS, SLTU,
                               // CSR functions
                               MRET, SRET, ECALL, CSR_WRITE, CSR_READ, CSR_SET, CSR_CLEAR,
                               // LSU functions
                               LD, SD, LW, LWU, SW, LH, LHU, SH, LB, SB, LBU
                             } fu_op;
    // ---------------
    // IF/ID Stage
    // ---------------
    // store the decompressed instruction
    typedef struct packed {
        branchpredict_sbe branch_predict;
        logic [63:0]      address;
        logic [31:0]      instruction;
        logic             is_compressed;
        logic             is_illegal;
    } fetch_entry;

    // ---------------
    // ID/EX/WB Stage
    // ---------------
    typedef struct packed {
        logic [63:0]              pc;            // PC of instruction
        logic [TRANS_ID_BITS-1:0] trans_id;      // this can potentially be simplified, we could index the scoreboard entry
                                                 // with the transaction id in any case make the width more generic
        fu_t                      fu;            // functional unit to use
        fu_op                     op;            // operation to perform in each functional unit
        logic [4:0]               rs1;           // register source address 1
        logic [4:0]               rs2;           // register source address 2
        logic [4:0]               rd;            // register destination address
        logic [63:0]              result;        // for unfinished instructions this field also holds the immediate
        logic                     valid;         // is the result valid
        logic                     use_imm;       // should we use the immediate as operand b?
        logic                     use_zimm;      // use zimm as operand a
        logic                     use_pc;        // set if we need to use the PC as operand a, PC from exception
        exception                 ex;            // exception has occurred
        branchpredict_sbe         bp;            // branch predict scoreboard data structure
        logic                     is_compressed; // signals a compressed instructions, we need this information at the commit stage if
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
    } rtype_t;

    typedef struct packed {
        logic [31:20] imm;
        logic [19:15] rs1;
        logic [14:12] funct3;
        logic [11:7]  rd;
        logic [6:0]   opcode;
    } itype_t;

    typedef struct packed {
        logic [31:25] imm1;
        logic [24:20] rs2;
        logic [19:15] rs1;
        logic [14:12] funct3;
        logic [11:7]  imm0;
        logic [6:0]   opcode;
    } stype_t;

    typedef struct packed {
        logic [31:12] funct3;
        logic [11:7]  rd;
        logic [6:0]   opcode;
    } utype_t;

    typedef union packed {
        logic [31:0]   instr;
        rtype_t        rtype;
        itype_t        itype;
        stype_t        stype;
        utype_t        utype;
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
    // Privilege Spec
    // --------------------
    typedef enum logic[1:0] {
      PRIV_LVL_M = 2'b11,
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
    localparam ENV_CALL_UMODE        = 64'h8; // environment call from user mode
    localparam ENV_CALL_SMODE        = 64'h9; // environment call from supervisor mode
    localparam ENV_CALL_MMODE        = 64'hB; // environment call from machine mode

    typedef enum logic [11:0] {
        CSR_SSTATUS   = 12'h100,
        CSR_SIE       = 12'h104,
        CSR_STVEC     = 12'h105,
        CSR_SSCRATCH  = 12'h140,
        CSR_SEPC      = 12'h141,
        CSR_SCAUSE    = 12'h142,
        CSR_STVAL     = 12'h143,
        CSR_SIP       = 12'h144,
        CSR_SATP      = 12'h180,

        CSR_MSTATUS   = 12'h300,
        CSR_MISA      = 12'h301,
        CSR_MEDELEG   = 12'h302,
        CSR_MIDELEG   = 12'h303,
        CSR_MIE       = 12'h304,
        CSR_MTVEC     = 12'h305,
        CSR_MSCRATCH  = 12'h340,
        CSR_MEPC      = 12'h341,
        CSR_MCAUSE    = 12'h342,
        CSR_MTVAL     = 12'h343,
        CSR_MIP       = 12'h344,
        CSR_MVENDORID = 12'hF11,
        CSR_MARCHID   = 12'hF12,
        CSR_MIMPID    = 12'hF13,
        CSR_MHARTID   = 12'hF14
    } csr_reg_t;

    // decoded csr address
    typedef struct packed {
        logic [1:0]  rw;
        priv_lvl_t   priv_lvl;
        logic  [7:0] address;
    } csr_addr_t;

    typedef union packed {
        csr_reg_t   address;
        csr_addr_t  csr_decode;
    } csr_t;

endpackage
