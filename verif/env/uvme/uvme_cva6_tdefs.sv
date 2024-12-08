// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2021 Thales DIS Design Services SAS
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
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0


`ifndef __UVME_CVA6_TDEFS_SV__
`define __UVME_CVA6_TDEFS_SV__


// The following pseudo-instructions have been removed:
// BEQZ, BGEZ, BGT,BGTU,BGTZ, BLE,BLEU,BLEZ,BLTZ, BNEZ, ILLEGAL
// J, JR, MV, NOT, NEG, NEGW, RET, SEQZ, SGTZ, SLTZ, SNEZ
// The following compressed instructions have not been added:
// C_FLWSP,C_FLDSP,C_FSWSP,C_FSDSP,C_FLW,C_FLD,C_FSW,C_FSD,
// C_J,C_JR,C_BEQZ,C_BNEZ,C_MV,C_SLLI64,C_SRLI64,C_SRAI64
// The following instructions have been added:
// FENCE
typedef enum {
    ADD,ADDI,AND,ANDI,AUIPC,BEQ,BGE,BGEU
    ,BLTU,BNE,BLT, FENCE, FENCE_I,EBREAK,ECALL
    ,JAL,JALR,LB,LBU,LH,LHU
    ,LUI,LW,OR
    ,ORI, SB, SH,SLL,SLLI
    ,SLT,SLTI,SLTIU,SLTU,SRA,SRAI
    ,SRL,SRLI,SUB,SW,XOR,XORI
    ,MUL,MULH,MULHU,MULHSU
    ,DIV,REM,DIVU,REMU,WFI,MRET,DRET
    ,CSRRW, CSRRC, CSRRS
    ,CSRRCI, CSRRSI, CSRRWI
    ,C_LWSP,C_SWSP,C_LW,C_SW
    ,C_BEQZ,C_BNEZ
    ,C_J,C_JR,C_JAL,C_JALR,C_LI,C_LUI
    ,C_ADDI,C_ADDI16SP,C_ADDI4SPN,C_MV
    ,C_SLLI,C_SRLI,C_SRAI,C_ANDI,C_ADD
    ,C_AND,C_OR,C_XOR,C_SUB,C_EBREAK
} instr_name_t; // assembler


// The following CSR ABI names are not currently included:
// fp, pc
//"gpr_none" CSR ABI name added for JALR instruction check:
typedef enum {
    zero,ra,sp,gp,tp,t0,t1,t2,s0
    ,s1,a0,a1,a2,a3,a4,a5,a6
    ,a7,s2,s3,s4,s5,s6,s7,s8
    ,s9,s10,s11,t3,t4,t5,t6
    ,gpr_none
} gpr_name_t; // ABI name

// TODO: add missing CSRs
typedef enum {
    marchid,mcause,mcountinhibit,mcycle,mcycleh,mepc,mhartid
    ,mie,mcontext,scontext
    ,minstret,minstreth,mip,misa,mscratch,mstatus,mtval,mtvec,mimpid
    ,mvendorid
    ,tselect,tdata1,tdata2,tdata3,tinfo
    ,dscratch0,dscratch1

    ,mhpmevent3
    ,mhpmevent4,mhpmevent5,mhpmevent6,mhpmevent7,mhpmevent8,mhpmevent9
    ,mhpmevent10,mhpmevent11,mhpmevent12,mhpmevent13,mhpmevent14,mhpmevent15,mhpmevent16,mhpmevent17
    ,mhpmevent18,mhpmevent19,mhpmevent20,mhpmevent21,mhpmevent22,mhpmevent23,mhpmevent24,mhpmevent25
    ,mhpmevent26,mhpmevent27,mhpmevent28,mhpmevent29,mhpmevent30,mhpmevent31

    ,mhpmcounter3
    ,mhpmcounter4,mhpmcounter5,mhpmcounter6,mhpmcounter7,mhpmcounter8,mhpmcounter9
    ,mhpmcounter10,mhpmcounter11,mhpmcounter12,mhpmcounter13,mhpmcounter14,mhpmcounter15,mhpmcounter16
    ,mhpmcounter17,mhpmcounter18,mhpmcounter19,mhpmcounter20,mhpmcounter21,mhpmcounter22,mhpmcounter23
    ,mhpmcounter24,mhpmcounter25,mhpmcounter26,mhpmcounter27,mhpmcounter28,mhpmcounter29,mhpmcounter30
    ,mhpmcounter31

    ,mhpmcounterh3
    ,mhpmcounterh4,mhpmcounterh5,mhpmcounterh6,mhpmcounterh7,mhpmcounterh8,mhpmcounterh9
    ,mhpmcounterh10,mhpmcounterh11,mhpmcounterh12,mhpmcounterh13,mhpmcounterh14,mhpmcounterh15,mhpmcounterh16
    ,mhpmcounterh17,mhpmcounterh18,mhpmcounterh19,mhpmcounterh20,mhpmcounterh21,mhpmcounterh22,mhpmcounterh23
    ,mhpmcounterh24,mhpmcounterh25,mhpmcounterh26,mhpmcounterh27,mhpmcounterh28,mhpmcounterh29,mhpmcounterh30
    ,mhpmcounterh31

    ,medeleg,mcounteren
    ,mideleg
    ,pmpaddr0,pmpaddr1,pmpaddr10,pmpaddr11,pmpaddr12,pmpaddr13,pmpaddr14
    ,pmpaddr15,pmpaddr2,pmpaddr3,pmpaddr4,pmpaddr5,pmpaddr6,pmpaddr7,pmpaddr8
    ,pmpaddr9,pmpcfg0,pmpcfg1,pmpcfg2,pmpcfg3
} csr_name_t;

typedef struct {
    string key;
    string val;
} ops_t;

typedef struct {
    string       ins_str;
    instr_name_t asm;
    ops_t        ops[4];
    bit          compressed;
    bit[31:0]    pc;
} ins_t;

typedef struct packed {
      logic                                ready;  // icache is ready
      logic                                valid;  // signals a valid read
      logic [RTLCVA6Cfg.FETCH_WIDTH-1:0]   data;   // 2+ cycle out: tag
      logic [RTLCVA6Cfg.VLEN-1:0]          vaddr;  // virtual address out
} uvme_frontend_icache_req_t;

typedef struct packed {
      logic                       req;      // we request a new word
      logic                       kill_s1;  // kill the current request
      logic                       kill_s2;  // kill the last request
      logic [RTLCVA6Cfg.VLEN-1:0] vaddr;    // 1st cycle: 12 bit index is taken for lookup
} uvme_frontend_icache_rsp_t;

typedef enum logic [2:0] {
  NoCF,    // No control flow prediction
  Branch,  // Branch
  Jump,    // Jump to address from immediate
  JumpR,   // Jump to address from registers
  Return   // Return Address Prediction
} uvme_frontend_prediction_t;

typedef struct packed {
      logic [RTLCVA6Cfg.VLEN-1:0] address;  // instruction word
      logic [31:0]                instruction;  // instruction word
      uvme_frontend_prediction_t  predict; // this field contains branch prediction information regarding the forward branch path
      logic [RTLCVA6Cfg.VLEN-1:0] predicted_address;
} uvme_frontend_fetched_data_t;

typedef  struct packed{
   logic                        valid;           // prediction with all its values is valid
   logic [RTLCVA6Cfg.VLEN-1:0]  pc;              // PC of predict or mis-predict
   logic [RTLCVA6Cfg.VLEN-1:0]  target_address;  // target address at which to jump, or not
   logic                        is_mispredict;   // set if this was a mis-predict
   logic                        is_taken;        // branch is taken
   uvme_frontend_prediction_t   cf_type;         // Type of control flow change
} uvme_frontend_bp_resolve_t;

typedef struct packed {
      logic [1:0]      saturation;
      logic            valid;
} uvme_frontend_bht_t;

typedef struct packed {
      logic [RTLCVA6Cfg.VLEN-1:0] predicted_address;
      logic                       valid;
} uvme_frontend_ras_t;

`endif // __UVME_CVA6_TDEFS_SV__
