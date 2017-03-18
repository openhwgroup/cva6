package ariane_pkg;

// ---------------
// ALU operations
// ---------------
typedef enum logic [7:0] { add, sub, addu, subu, addr, subr, addur, subug,  // basic ALU op
                     lxor, lor, land,                                    // logic operations
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

typedef enum logic [1:0] { mode8, mode16 } vec_mode;

endpackage
