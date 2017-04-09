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
     logic [63:0] ra; // return address
     logic        is_call; // is call - pop from stack
     logic        is_return; // is return - push on stack
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
typedef enum logic [7:0]      { ADD, SUB, ADDW, SUBW,                            // basic ALU op
                                XORL, ORL, ANDL,                                 // logic operations
                                SRA, SRL, SLL, SRLW, SLLW, SRAW,                 // shifts
                                LTS, LTU, LES, LEU, GTS, GTU, GES, GEU, EQ, NE,  // comparisons
                                SLTS, SLTU, SLETS, SLETU                         // set lower than operations
                              } alu_op;

typedef enum logic [1:0]      { mode8, mode16 } vec_mode;

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
    logic           in_flight;
    exception       ex;
} scoreboard_entry;
