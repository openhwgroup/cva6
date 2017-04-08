package ariane_pkg;

// ---------------
// Fetch Stage
// ---------------

// Only use struct when signals have same direction
typedef struct {
     logic [63:0] pc,
     logic [63:0] branch_target_address,
     logic        valid
} btb;

// input to the fetch stage
typedef struct {
     logic [63:0] ra, // return address
     logic        is_call, // is call - pop from stack
     logic        is_return // is return - push on stack
} ras;

// exception
typedef struct {
     logic [63:0] epc,
     logic [63:0] cause,
     logic        valid
} exception;

// mispredict
typedef struct {
     logic [63:0] pc,
     logic        valid // is mispredict
} mispredict;

// handshaking signal
// ---------------
// ALU operations
// ---------------
typedef enum logic [7:0]      { add, sub, addu, subu, addr, subr, addur, subug,  // basic ALU op
                                lxor, lor, land,                                 // logic operations
                                sra, srl, ror, sll,                              // shifts
                                // bext, bextu, bins, bclr, bset,                // bit manipulation, currently not implemented
                                ff1, fl1, cnt, clb,                              // bit counting
                                exts, ext,                                       // sign-/zero-extensions
                                lts, ltu, les, leu, gts, gtu, ges, geu, eq, ne,  // comparisons
                                slts, sltu, slets, sletu,                        // set lower than operations
                                abs, clip, clipu,                                // absolute value
                                ins,                                             // insert/extract
                                min, minu, max, maxu                             // min/max
                              } alu_op;

typedef enum logic [1:0]      { mode8, mode16 } vec_mode;

endpackage
