// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2020 Silicon Labs, Inc.
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.


`ifndef __UVMA_ISACOV_TDEFS_SV__
`define __UVMA_ISACOV_TDEFS_SV__

typedef enum {
  A_EXT,
  B_EXT,
  C_EXT,
  F_EXT,
  I_EXT,
  M_EXT,
  P_EXT,
  Q_EXT,
  ZIFENCEI_EXT,
  ZICSR_EXT,
  ZCE_EXT
} instr_ext_t;

typedef enum {
   // Used for an opcode that cannot be decoded
  UNKNOWN,

  // 32I
  LUI, AUIPC, JAL, JALR,
  BEQ, BNE, BLT, BGE, BLTU, BGEU,
  LB, LH, LW, LBU, LHU, SB, SH, SW,
  ADDI, SLTI, SLTIU, XORI, ORI, ANDI, SLLI, SRLI, SRAI,
  ADD, SUB, SLL, SLT, SLTU, XOR, SRL, SRA, OR, AND,
  FENCE, ECALL, EBREAK, DRET, MRET, WFI,

  // 32M
  MUL, MULH, MULHSU, MULHU,
  DIV, DIVU, REM, REMU,

  // 32C
  C_ADDI4SPN, C_LW, C_SW, C_NOP,
  C_ADDI, C_JAL, C_LI, C_ADDI16SP, C_LUI, C_SRLI, C_SRAI,
  C_ANDI, C_SUB, C_XOR, C_OR, C_AND, C_J, C_BEQZ, C_BNEZ,
  C_SLLI, C_LWSP, C_JR, C_MV, C_EBREAK, C_JALR, C_ADD, C_SWSP,

  // 32A
  LR_W, SC_W,
  AMOSWAP_W, AMOADD_W, AMOXOR_W, AMOAND_W,
  AMOOR_W, AMOMIN_W, AMOMAX_W, AMOMINU_W, AMOMAXU_W,

  // 32B
  SH1ADD, SH2ADD, SH3ADD,
  CLZ, CTZ, CPOP,
  MIN, MAX, MINU, MAXU,
  SEXT_B, SEXT_H, ZEXT_H,
  ANDN, ORN, XNOR, ROR, RORI, ROL,
  REV8, ORC_B,
  CLMUL, CLMULH, CLMULR,
  BSET, BSETI, BCLR, BCLRI, BINV, BINVI, BEXT, BEXTI,

  // Zicsr
  CSRRW, CSRRS, CSRRC,
  CSRRWI, CSRRSI, CSRRCI,

  // Zifencei
  FENCE_I
} instr_name_t;

typedef enum {
  // Used for non-decodable
  UNKNOWN_TYPE,

  // RV32 types
  R_TYPE,
  I_TYPE,
  S_TYPE,
  B_TYPE,
  U_TYPE,
  J_TYPE,

  CI_TYPE,
  CR_TYPE,
  CSS_TYPE,
  CIW_TYPE,
  CL_TYPE,
  CS_TYPE,
  CA_TYPE,
  CB_TYPE,
  CJ_TYPE,

  ZBA_TYPE,
  ZBB_TYPE,
  ZBC_TYPE,
  ZBS_TYPE,

  // CSR* instruction with rs1 operand
  CSR_TYPE,

  // CSR* instruction with immu operand
  CSRI_TYPE

} instr_type_t;

typedef enum {
  // Use for undecodable instructions
  UNKNOWN_GROUP,

  LOAD_GROUP,
  STORE_GROUP,
  MISALIGN_LOAD_GROUP,
  MISALIGN_STORE_GROUP,
  ALU_GROUP,
  BRANCH_GROUP,
  JUMP_GROUP,
  FENCE_GROUP,
  FENCE_I_GROUP,
  RET_GROUP,
  WFI_GROUP,
  CSR_GROUP,
  ENV_GROUP,
  MUL_GROUP,
  MULTI_MUL_GROUP,
  DIV_GROUP,
  ALOAD_GROUP,
  ASTORE_GROUP,
  AMEM_GROUP
} instr_group_t;

typedef enum bit[CSR_ADDR_WL-1:0] {
  USTATUS        = 'h000,
  UIE            = 'h004,
  UTVEC          = 'h005,
  USCRATCH       = 'h040,
  UEPC           = 'h041,
  UCAUSE         = 'h042,
  UTVAL          = 'h043,
  UIP            = 'h044,
  FFLAGS         = 'h001,
  FRM            = 'h002,
  FCSR           = 'h003,
  CYCLE          = 'hC00,
  TIME           = 'hC01,
  INSTRET        = 'hC02,
  HPMCOUNTER3    = 'hC03,
  HPMCOUNTER4    = 'hC04,
  HPMCOUNTER5    = 'hC05,
  HPMCOUNTER6    = 'hC06,
  HPMCOUNTER7    = 'hC07,
  HPMCOUNTER8    = 'hC08,
  HPMCOUNTER9    = 'hC09,
  HPMCOUNTER10   = 'hC0A,
  HPMCOUNTER11   = 'hC0B,
  HPMCOUNTER12   = 'hC0C,
  HPMCOUNTER13   = 'hC0D,
  HPMCOUNTER14   = 'hC0E,
  HPMCOUNTER15   = 'hC0F,
  HPMCOUNTER16   = 'hC10,
  HPMCOUNTER17   = 'hC11,
  HPMCOUNTER18   = 'hC12,
  HPMCOUNTER19   = 'hC13,
  HPMCOUNTER20   = 'hC14,
  HPMCOUNTER21   = 'hC15,
  HPMCOUNTER22   = 'hC16,
  HPMCOUNTER23   = 'hC17,
  HPMCOUNTER24   = 'hC18,
  HPMCOUNTER25   = 'hC19,
  HPMCOUNTER26   = 'hC1A,
  HPMCOUNTER27   = 'hC1B,
  HPMCOUNTER28   = 'hC1C,
  HPMCOUNTER29   = 'hC1D,
  HPMCOUNTER30   = 'hC1E,
  HPMCOUNTER31   = 'hC1F,
  CYCLEH         = 'hC80,
  TIMEH          = 'hC81,
  INSTRETH       = 'hC82,
  HPMCOUNTER3H   = 'hC83,
  HPMCOUNTER4H   = 'hC84,
  HPMCOUNTER5H   = 'hC85,
  HPMCOUNTER6H   = 'hC86,
  HPMCOUNTER7H   = 'hC87,
  HPMCOUNTER8H   = 'hC88,
  HPMCOUNTER9H   = 'hC89,
  HPMCOUNTER10H  = 'hC8A,
  HPMCOUNTER11H  = 'hC8B,
  HPMCOUNTER12H  = 'hC8C,
  HPMCOUNTER13H  = 'hC8D,
  HPMCOUNTER14H  = 'hC8E,
  HPMCOUNTER15H  = 'hC8F,
  HPMCOUNTER16H  = 'hC90,
  HPMCOUNTER17H  = 'hC91,
  HPMCOUNTER18H  = 'hC92,
  HPMCOUNTER19H  = 'hC93,
  HPMCOUNTER20H  = 'hC94,
  HPMCOUNTER21H  = 'hC95,
  HPMCOUNTER22H  = 'hC96,
  HPMCOUNTER23H  = 'hC97,
  HPMCOUNTER24H  = 'hC98,
  HPMCOUNTER25H  = 'hC99,
  HPMCOUNTER26H  = 'hC9A,
  HPMCOUNTER27H  = 'hC9B,
  HPMCOUNTER28H  = 'hC9C,
  HPMCOUNTER29H  = 'hC9D,
  HPMCOUNTER30H  = 'hC9E,
  HPMCOUNTER31H  = 'hC9F,
  SSTATUS        = 'h100,
  SEDELEG        = 'h102,
  SIDELEG        = 'h103,
  SIE            = 'h104,
  STVEC          = 'h105,
  SCOUNTEREN     = 'h106,
  SSCRATCH       = 'h140,
  SEPC           = 'h141,
  SCAUSE         = 'h142,
  STVAL          = 'h143,
  SIP            = 'h144,
  SATP           = 'h180,
  MVENDORID      = 'hF11,
  MARCHID        = 'hF12,
  MIMPID         = 'hF13,
  MHARTID        = 'hF14,
  MSTATUS        = 'h300,
  MISA           = 'h301,
  MEDELEG        = 'h302,
  MIDELEG        = 'h303,
  MIE            = 'h304,
  MTVEC          = 'h305,
  MCOUNTEREN     = 'h306,
  MENVCFG        = 'h30A,
  MSTATUSH       = 'h310,
  MENVCFGH       = 'h31A,
  MSCRATCH       = 'h340,
  MEPC           = 'h341,
  MCAUSE         = 'h342,
  MTVAL          = 'h343,
  MIP            = 'h344,
  PMPCFG0        = 'h3A0,
  PMPCFG1        = 'h3A1,
  PMPCFG2        = 'h3A2,
  PMPCFG3        = 'h3A3,
  PMPCFG4        = 'h3A4,
  PMPCFG5        = 'h3A5,
  PMPCFG6        = 'h3A6,
  PMPCFG7        = 'h3A7,
  PMPCFG8        = 'h3A8,
  PMPCFG9        = 'h3A9,
  PMPCFG10       = 'h3AA,
  PMPCFG11       = 'h3AB,
  PMPCFG12       = 'h3AC,
  PMPCFG13       = 'h3AD,
  PMPCFG14       = 'h3AE,
  PMPCFG15       = 'h3AF,
  PMPADDR0       = 'h3B0,
  PMPADDR1       = 'h3B1,
  PMPADDR2       = 'h3B2,
  PMPADDR3       = 'h3B3,
  PMPADDR4       = 'h3B4,
  PMPADDR5       = 'h3B5,
  PMPADDR6       = 'h3B6,
  PMPADDR7       = 'h3B7,
  PMPADDR8       = 'h3B8,
  PMPADDR9       = 'h3B9,
  PMPADDR10      = 'h3BA,
  PMPADDR11      = 'h3BB,
  PMPADDR12      = 'h3BC,
  PMPADDR13      = 'h3BD,
  PMPADDR14      = 'h3BE,
  PMPADDR15      = 'h3BF,
  PMPADDR16      = 'h3C0,
  PMPADDR17      = 'h3C1,
  PMPADDR18      = 'h3C2,
  PMPADDR19      = 'h3C3,
  PMPADDR20      = 'h3C4,
  PMPADDR21      = 'h3C5,
  PMPADDR22      = 'h3C6,
  PMPADDR23      = 'h3C7,
  PMPADDR24      = 'h3C8,
  PMPADDR25      = 'h3C9,
  PMPADDR26      = 'h3CA,
  PMPADDR27      = 'h3CB,
  PMPADDR28      = 'h3CC,
  PMPADDR29      = 'h3CD,
  PMPADDR30      = 'h3CE,
  PMPADDR31      = 'h3CF,
  PMPADDR32      = 'h3D0,
  PMPADDR33      = 'h3D1,
  PMPADDR34      = 'h3D2,
  PMPADDR35      = 'h3D3,
  PMPADDR36      = 'h3D4,
  PMPADDR37      = 'h3D5,
  PMPADDR38      = 'h3D6,
  PMPADDR39      = 'h3D7,
  PMPADDR40      = 'h3D8,
  PMPADDR41      = 'h3D9,
  PMPADDR42      = 'h3DA,
  PMPADDR43      = 'h3DB,
  PMPADDR44      = 'h3DC,
  PMPADDR45      = 'h3DD,
  PMPADDR46      = 'h3DE,
  PMPADDR47      = 'h3DF,
  PMPADDR48      = 'h3E0,
  PMPADDR49      = 'h3E1,
  PMPADDR50      = 'h3E2,
  PMPADDR51      = 'h3E3,
  PMPADDR52      = 'h3E4,
  PMPADDR53      = 'h3E5,
  PMPADDR54      = 'h3E6,
  PMPADDR55      = 'h3E7,
  PMPADDR56      = 'h3E8,
  PMPADDR57      = 'h3E9,
  PMPADDR58      = 'h3EA,
  PMPADDR59      = 'h3EB,
  PMPADDR60      = 'h3EC,
  PMPADDR61      = 'h3ED,
  PMPADDR62      = 'h3EE,
  PMPADDR63      = 'h3EF,
  MCYCLE         = 'hB00,
  MINSTRET       = 'hB02,
  MHPMCOUNTER3   = 'hB03,
  MHPMCOUNTER4   = 'hB04,
  MHPMCOUNTER5   = 'hB05,
  MHPMCOUNTER6   = 'hB06,
  MHPMCOUNTER7   = 'hB07,
  MHPMCOUNTER8   = 'hB08,
  MHPMCOUNTER9   = 'hB09,
  MHPMCOUNTER10  = 'hB0A,
  MHPMCOUNTER11  = 'hB0B,
  MHPMCOUNTER12  = 'hB0C,
  MHPMCOUNTER13  = 'hB0D,
  MHPMCOUNTER14  = 'hB0E,
  MHPMCOUNTER15  = 'hB0F,
  MHPMCOUNTER16  = 'hB10,
  MHPMCOUNTER17  = 'hB11,
  MHPMCOUNTER18  = 'hB12,
  MHPMCOUNTER19  = 'hB13,
  MHPMCOUNTER20  = 'hB14,
  MHPMCOUNTER21  = 'hB15,
  MHPMCOUNTER22  = 'hB16,
  MHPMCOUNTER23  = 'hB17,
  MHPMCOUNTER24  = 'hB18,
  MHPMCOUNTER25  = 'hB19,
  MHPMCOUNTER26  = 'hB1A,
  MHPMCOUNTER27  = 'hB1B,
  MHPMCOUNTER28  = 'hB1C,
  MHPMCOUNTER29  = 'hB1D,
  MHPMCOUNTER30  = 'hB1E,
  MHPMCOUNTER31  = 'hB1F,
  MCYCLEH        = 'hB80,
  MINSTRETH      = 'hB82,
  MHPMCOUNTER3H  = 'hB83,
  MHPMCOUNTER4H  = 'hB84,
  MHPMCOUNTER5H  = 'hB85,
  MHPMCOUNTER6H  = 'hB86,
  MHPMCOUNTER7H  = 'hB87,
  MHPMCOUNTER8H  = 'hB88,
  MHPMCOUNTER9H  = 'hB89,
  MHPMCOUNTER10H = 'hB8A,
  MHPMCOUNTER11H = 'hB8B,
  MHPMCOUNTER12H = 'hB8C,
  MHPMCOUNTER13H = 'hB8D,
  MHPMCOUNTER14H = 'hB8E,
  MHPMCOUNTER15H = 'hB8F,
  MHPMCOUNTER16H = 'hB90,
  MHPMCOUNTER17H = 'hB91,
  MHPMCOUNTER18H = 'hB92,
  MHPMCOUNTER19H = 'hB93,
  MHPMCOUNTER20H = 'hB94,
  MHPMCOUNTER21H = 'hB95,
  MHPMCOUNTER22H = 'hB96,
  MHPMCOUNTER23H = 'hB97,
  MHPMCOUNTER24H = 'hB98,
  MHPMCOUNTER25H = 'hB99,
  MHPMCOUNTER26H = 'hB9A,
  MHPMCOUNTER27H = 'hB9B,
  MHPMCOUNTER28H = 'hB9C,
  MHPMCOUNTER29H = 'hB9D,
  MHPMCOUNTER30H = 'hB9E,
  MHPMCOUNTER31H = 'hB9F,
  MCOUNTINHIBIT  = 'h320,
  MHPMEVENT3     = 'h323,
  MHPMEVENT4     = 'h324,
  MHPMEVENT5     = 'h325,
  MHPMEVENT6     = 'h326,
  MHPMEVENT7     = 'h327,
  MHPMEVENT8     = 'h328,
  MHPMEVENT9     = 'h329,
  MHPMEVENT10    = 'h32A,
  MHPMEVENT11    = 'h32B,
  MHPMEVENT12    = 'h32C,
  MHPMEVENT13    = 'h32D,
  MHPMEVENT14    = 'h32E,
  MHPMEVENT15    = 'h32F,
  MHPMEVENT16    = 'h330,
  MHPMEVENT17    = 'h331,
  MHPMEVENT18    = 'h332,
  MHPMEVENT19    = 'h333,
  MHPMEVENT20    = 'h334,
  MHPMEVENT21    = 'h335,
  MHPMEVENT22    = 'h336,
  MHPMEVENT23    = 'h337,
  MHPMEVENT24    = 'h338,
  MHPMEVENT25    = 'h339,
  MHPMEVENT26    = 'h33A,
  MHPMEVENT27    = 'h33B,
  MHPMEVENT28    = 'h33C,
  MHPMEVENT29    = 'h33D,
  MHPMEVENT30    = 'h33E,
  MHPMEVENT31    = 'h33F,
  MSECCFG        = 'h747,
  MSECCFGH       = 'h757,
  TSELECT        = 'h7A0,
  TDATA1         = 'h7A1,
  TDATA2         = 'h7A2,
  TDATA3         = 'h7A3,
  TINFO          = 'h7A4,
  MCONTEXT       = 'h7A8,
  SCONTEXT       = 'h7AA,
  DCSR           = 'h7B0,
  DPC            = 'h7B1,
  DSCRATCH0      = 'h7B2,
  DSCRATCH1      = 'h7B3,
  VSTART         = 'h008,
  VXSTAT         = 'h009,
  VXRM           = 'h00A,
  VL             = 'hC20,
  VTYPE          = 'hC21,
  VLENB          = 'hC22,
  MCONFIGPTR     = 'hF15
} instr_csr_t;

bit rs1_is_signed[instr_name_t] = '{
  MULH   : 1,
  MULHSU : 1,
  DIV    : 1,
  REM    : 1,
  ADDI   : 1,
  SLTI   : 1,
  SRA    : 1,
  ADD    : 1,
  SUB    : 1,
  SLT    : 1,
  C_ADDI : 1,
  C_ADDI16SP : 1,
  C_ADD  : 1,
  C_SUB  : 1,
  SH1ADD : 1,
  SH2ADD : 1,
  SH3ADD : 1,
  default: 0
};

bit rs2_is_signed[instr_name_t] = '{
  MULH   : 1,
  DIV    : 1,
  REM    : 1,
  ADD    : 1,
  SUB    : 1,
  SLT    : 1,
  C_ADD  : 1,
  C_SUB  : 1,
  SH1ADD : 1,
  SH2ADD : 1,
  SH3ADD : 1,
  default: 0
};

bit immi_is_signed[instr_name_t] = '{
  JALR   : 1,
  LB     : 1,
  LH     : 1,
  LW     : 1,
  LBU    : 1,
  LHU    : 1,
  SLTI   : 1,
  SLTIU  : 1,
  XORI   : 1,
  ORI    : 1,
  ANDI   : 1,
  ADDI   : 1,
  SLLI   : 0,
  SRLI   : 0,
  SRAI   : 0,
  default: 0
};

bit c_imm_is_signed[instr_name_t] = '{
  C_ADDI:  1,
  C_ADDI16SP: 1,
  C_ANDI:  1,
  C_BEQZ:  1,
  C_BNEZ:  1,
  C_J:     1,
  C_JAL:   1,
  C_LI:    1,
  C_LUI:   1,
  C_NOP:   1,
  default: 0
};

bit c_imm_is_nonzero[instr_name_t] = '{
  C_ADDI4SPN:1,
  C_NOP:   1,
  C_ADDI:  1,
  C_ADDI16SP:1,
  C_LUI:   1,
  C_SRLI:  1,
  C_SRAI:  1,
  C_SLLI:  1,
  default: 0
};

bit rd_is_signed[instr_name_t] = '{
  MULH   : 1,
  MULHSU : 1,
  DIV    : 1,
  REM    : 1,
  LH     : 1,
  LB     : 1,
  ADD    : 1,
  SRA    : 1,
  SUB    : 1,
  ADDI   : 1,
  C_ADDI : 1,
  C_ADDI16SP: 1,
  C_ADD  : 1,
  C_SUB  : 1,
  SH1ADD : 1,
  SH2ADD : 1,
  SH3ADD : 1,
  default: 0
};

bit c_has_rs1[instr_name_t] = '{
  C_LW   : 1,
  C_SW   : 1,
  C_ADDI : 1,
  C_ADDI16SP:1,
  C_SRLI : 1,
  C_SRAI : 1,
  C_ANDI : 1,
  C_SUB  : 1,
  C_XOR  : 1,
  C_OR   : 1,
  C_AND  : 1,
  C_BEQZ : 1,
  C_BNEZ : 1,
  C_SLLI : 1,
  C_JR   : 1,
  C_JALR : 1,
  C_ADD  : 1,
  default: 0
};

typedef enum {
  ZERO,     // For signed and unsigned values
  NON_ZERO, // For unsigned values
  POSITIVE, // For signed values
  NEGATIVE  // For signed values
} instr_value_t;  // TODO:ropeders should be "value_type_t"?

// Package level methods to map instruction to extension
function instr_ext_t get_instr_ext(instr_name_t name);
  if (name inside
    {
      LUI, AUIPC, JAL, JALR,
      BEQ, BNE, BLT, BGE, BLTU, BGEU,
      LB, LH, LW, LBU, LHU, SB, SH, SW,
      ADDI, SLTI, SLTIU, XORI, ORI, ANDI, SLLI, SRLI, SRAI,
      ADD, SUB, SLL, SLT, SLTU, XOR, SRL, SRA, OR, AND,
      FENCE, ECALL, EBREAK, DRET, MRET, WFI
    })
    return I_EXT;

  if (name inside
    {
      MUL, MULH, MULHSU, MULHU,
      DIV, DIVU, REM, REMU
    })
    return M_EXT;

  if (name inside
    {
      C_ADDI4SPN, C_LW, C_SW, C_NOP,
      C_ADDI, C_JAL, C_LI, C_ADDI16SP, C_LUI, C_SRLI, C_SRAI,
      C_ANDI, C_SUB, C_XOR, C_OR, C_AND, C_J, C_BEQZ, C_BNEZ,
      C_SLLI, C_LWSP, C_JR, C_MV, C_EBREAK, C_JALR, C_ADD, C_SWSP
    })
    return C_EXT;

  if (name inside
    {
      LR_W, SC_W,
      AMOSWAP_W, AMOADD_W, AMOXOR_W, AMOAND_W,
      AMOOR_W, AMOMIN_W, AMOMAX_W, AMOMINU_W, AMOMAXU_W
    })
    return A_EXT;

  if (name inside
    {
      SH1ADD, SH2ADD, SH3ADD,
      CLZ, CTZ, CPOP,
      MIN, MAX, MINU, MAXU,
      SEXT_B, SEXT_H, ZEXT_H,
      ANDN, ORN, XNOR, ROR, RORI, ROL,
      REV8, ORC_B,
      CLMUL, CLMULH, CLMULR,
      BSET, BSETI, BCLR, BCLRI, BINV, BINVI, BEXT, BEXTI
    })
    return B_EXT;

  if (name inside
    {
      CSRRW, CSRRS, CSRRC,
      CSRRWI, CSRRSI, CSRRCI
    })
    return ZICSR_EXT;

  if (name inside
    {
      FENCE_I
    })
    return ZIFENCEI_EXT;

endfunction : get_instr_ext


// Package level methods to map instruction to type
function instr_type_t get_instr_type(instr_name_t name);
  static instr_name_t itypes[] = '{
    LB, LH, LW, LBU, LHU,
    ADDI, SLTI, SLTIU, XORI, ORI, ANDI, SLLI, SRLI, SRAI,
    JALR
    };
  static instr_name_t rtypes[] = '{
    // I-ext
    ADD, SUB, SLL, SLT, SLTU, XOR, SRL, SRA, OR, AND,
    // M-ext
    MUL, MULH, MULHSU, MULHU, DIV, DIVU, REM, REMU,
    // A-ext
    LR_W, SC_W, AMOSWAP_W, AMOADD_W, AMOXOR_W, AMOAND_W,
    AMOOR_W, AMOMIN_W, AMOMAX_W, AMOMINU_W, AMOMAXU_W
    };

  if (name inside {rtypes})
    return R_TYPE;

  if (name inside {itypes})
    return I_TYPE;

  if (name inside {C_ADDI,C_ADDI16SP,C_LWSP,C_LI,C_LUI,C_SLLI,C_NOP})
    return CI_TYPE;

  if (name inside {C_SWSP})
    return CSS_TYPE;

  if (name inside {C_MV, C_ADD, C_JR, C_JALR})
    return CR_TYPE;

  if (name inside {C_ADDI4SPN})
    return CIW_TYPE;

  if (name inside {C_LW})
    return CL_TYPE;

  if (name inside {C_SW})
    return CS_TYPE;

  if (name inside {C_AND, C_OR, C_XOR, C_SUB})
    return CA_TYPE;

  if (name inside {C_BEQZ, C_BNEZ, C_ANDI, C_SRAI, C_SRLI})
    return CB_TYPE;

  if (name inside {C_J, C_JAL})
    return CJ_TYPE;

  if (name inside {SB,SH,SW})
    return S_TYPE;

  if (name inside {BEQ,BNE,BLT,BGE,BLTU,BGEU})
    return B_TYPE;

  if (name inside {LUI,AUIPC})
    return U_TYPE;

  if (name inside {JAL})
    return J_TYPE;

  if (name inside {CSRRW,CSRRS,CSRRC})
    return CSR_TYPE;

  if (name inside {CSRRWI,CSRRSI,CSRRCI})
    return CSRI_TYPE;

  if (name inside {SH1ADD,SH2ADD,SH3ADD})
    return ZBA_TYPE;

  if (name inside {CLZ,CTZ,CPOP,MIN,MINU,MAX,MAXU,
                   SEXT_B,SEXT_H,ZEXT_H,ANDN,ORN,XNOR,
                   ROL,ROR,RORI,REV8,ORC_B})
    return ZBB_TYPE;

  if (name inside {CLMUL,CLMULH,CLMULR})
    return ZBC_TYPE;

  if (name inside {BSET,BSETI,BCLR,BCLRI,
                   BINV,BINVI,BEXT,BEXTI})
    return ZBS_TYPE;

  if (name inside {JAL})
    return J_TYPE;

  return UNKNOWN_TYPE;
endfunction : get_instr_type

// Package level methods to map instruction to type
function instr_group_t get_instr_group(instr_name_t name, bit[DEFAULT_XLEN-1:0] mem_addr);

  if (name inside {UNKNOWN})
    return UNKNOWN_GROUP;

  if (name inside {LB,LH,LW,LBU,LHU,C_LW,C_LWSP}) begin
    if (name inside {LH, LHU} && mem_addr[0])
      return MISALIGN_LOAD_GROUP;

    if (name inside {LW, C_LW, C_LWSP} && mem_addr[1:0])
      return MISALIGN_LOAD_GROUP;

    return LOAD_GROUP;
  end

  if (name inside {SB,SH,SW,C_SW,C_SWSP}) begin
    if (name inside {SH} && mem_addr[0])
      return MISALIGN_STORE_GROUP;

    if (name inside {SW, C_SW, C_SWSP} && mem_addr[1:0])
      return MISALIGN_STORE_GROUP;

    return STORE_GROUP;
  end

  if (name inside {SLL,SLLI,SRL,SRLI,SRA,SRAI,
                   ADD,ADDI,SUB,LUI,AUIPC,
                   XOR,XORI,OR,ORI,AND,ANDI,
                   SLT,SLTI,SLTU,SLTIU,
                   C_ADD,C_ADDI,C_ADDI16SP,
                   C_LI,C_LUI,C_MV,C_NOP,
                   C_XOR,C_SRLI,C_AND,C_ANDI,C_OR,
                   C_SUB,C_ADDI4SPN,C_SLLI,C_SRAI,
                   SH1ADD, SH2ADD, SH3ADD,
                   CLZ, CTZ, CPOP,
                   MIN, MAX, MINU, MAXU,
                   SEXT_B, SEXT_H, ZEXT_H,
                   ANDN, ORN, XNOR, ROR, RORI, ROL,
                   REV8, ORC_B,
                   CLMUL, CLMULH, CLMULR,
                   BSET, BSETI, BCLR, BCLRI, BINV, BINVI, BEXT, BEXTI})
    return ALU_GROUP;

  if (name inside {BEQ,BNE,BLT,BGE,BLTU,BGEU,
                   C_BEQZ,C_BNEZ})
    return BRANCH_GROUP;

  if (name inside {JAL,JALR,
                   C_J,C_JR,C_JAL,C_JALR})
    return JUMP_GROUP;

  if (name inside {FENCE})
    return FENCE_GROUP;

  if (name inside {FENCE_I})
    return FENCE_I_GROUP;

  if (name inside {ECALL, EBREAK, C_EBREAK})
    return ENV_GROUP;

  if (name inside {DRET, MRET})
    return RET_GROUP;

  if (name inside {WFI})
    return WFI_GROUP;

  if (name inside {CSRRW,CSRRS,CSRRC,CSRRWI,CSRRSI,CSRRCI})
    return CSR_GROUP;

  if (name inside {MUL})
    return MUL_GROUP;

  if (name inside {MULH,MULHSU,MULHU})
    return MULTI_MUL_GROUP;

  if (name inside {DIV,DIVU,REM,REMU})
    return DIV_GROUP;

  if (name inside {LR_W})
    return ALOAD_GROUP;

  if (name inside {SC_W})
    return ASTORE_GROUP;

  if (name inside {AMOSWAP_W,AMOADD_W,AMOXOR_W,AMOAND_W,
                   AMOOR_W,AMOMIN_W,AMOMAX_W,AMOMINU_W,AMOMAXU_W})
    return AMEM_GROUP;

  `uvm_fatal("ISACOV", $sformatf("Called get_instr_group with unmapped type: %s", name.name()));
endfunction : get_instr_group


`endif // __UVMA_ISACOV_TDEFS_SV__
