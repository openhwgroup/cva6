///////////////////////////////////////////////////////////////////////////////
// Copyright 2020 OpenHW Group
// Copyright 2020 BTA Design Services
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
//
///////////////////////////////////////////////////////////////////////////////
/*
 * Copyright
 * Copyright (c) 2005-2020 Imperas Software Ltd., www.imperas.com
 *
 * The contents of this file are provided under the Software License
 * Agreement that you accepted before downloading this file.
 *
 * This source forms part of the Software and can be used for educational,
 * training, and demonstration purposes but cannot be used for derivative
 * works except in cases where the derivative works require OVP technology
 * to run.
 *
 * For open source models released under licenses that you can use for
 * derivative works, please visit www.OVPworld.org or www.imperas.com
 * for the location of the open source models.
 *
 */

// The following pseudo-instructions have been removed:
// BEQZ, BGEZ, BGT,BGTU,BGTZ, BLE,BLEU,BLEZ,BLTZ, BNEZ, ILLEGAL
// J, JR, MV, NOT, NEG, NEGW, RET, SEQZ, SGTZ, SLTZ, SNEZ
// The following pseudo-instructions have not been added:
// C_FLDSP, C_FSDSP, C_FLD, C_FSD, C_J, C_JR, C_BEQZ, C_BNEZ,
// C_MV, C_SLLI64, C_SRLI64, C_SRAI64
// The following instructions have been added:
// FENCE

typedef enum {
    ADD,ADDI,AND,ANDI,AUIPC,BEQ,BGE,BGEU
    ,BLTU,BNE,BLT, FENCE, EBREAK,ECALL
    ,J,JAL,JALR,LB,LBU,LH,LHU
    ,LUI,LW,NOP,OR
    ,ORI, SB, SH,SLL,SLLI
    ,SLT,SLTI,SLTIU,SLTU,SRA,SRAI
    ,SRL,SRLI,SUB,SW,XOR,XORI
    ,MUL,MULH,MULHU,MULHSU
    ,DIV,REM,DIVU,REMU
    ,C_LWSP,C_FLWSP,C_SWSP
    ,C_FSWSP,C_LW,C_FLW
    ,C_SW,C_FSW
    ,C_JAL,C_JALR,C_LI,C_LUI,C_ADDI
    ,C_ADDI16SP,C_ADDI4SPN,C_SLLI
    ,C_SRLI,C_SRAI,C_ANDI,C_ADD,C_AND
    ,C_OR,C_XOR,C_SUB,C_NOP,C_EBREAK
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

// The following CSRs are not currently included:
// mstatush, mtinst, mtval2, mhpmcounter3, ..., mhpmcounter31,
// mhpmcounter3h, ..., mhpmcounter31h,
//The following CSRs have been removed:
// satp (supervisor-mode address translation and protection)
typedef enum {
    marchid,mcause,mcounteren,mcountinhibit,mcycle,mcycleh,medeleg,mepc,mhartid
    ,mhpmevent10,mhpmevent11,mhpmevent12,mhpmevent13,mhpmevent14,mhpmevent15,mhpmevent16,mhpmevent17
    ,mhpmevent18,mhpmevent19,mhpmevent20,mhpmevent21,mhpmevent22,mhpmevent23,mhpmevent24,mhpmevent25
    ,mhpmevent26,mhpmevent27,mhpmevent28,mhpmevent29,mhpmevent3,mhpmevent30,mhpmevent31,mhpmevent4
    ,mhpmevent5,mhpmevent6,mhpmevent7,mhpmevent8,mhpmevent9,mideleg,mie,mimpid
    ,minstret,minstreth,mip,misa,mscratch,mstatus,mtval,mtvec
    ,mvendorid,pmpaddr0,pmpaddr1,pmpaddr10,pmpaddr11,pmpaddr12,pmpaddr13,pmpaddr14
    ,pmpaddr15,pmpaddr2,pmpaddr3,pmpaddr4,pmpaddr5,pmpaddr6,pmpaddr7,pmpaddr8
    ,pmpaddr9,pmpcfg0,pmpcfg1,pmpcfg2,pmpcfg3
} csr_name_t;

typedef struct {
    string key;
    string val;
} ops_t;

typedef struct {
    string ins_str;
    instr_name_t asm;
    ops_t ops[4];
} ins_t;

class riscv_32isa_coverage;

// The following CSR ABI names are not currently included:
// fp, pc
    function gpr_name_t get_gpr_name (string s, r, asm);
        case (s)
            "zero": return gpr_name_t'(zero);
            "ra": return gpr_name_t'(ra);
            "sp": return gpr_name_t'(sp);
            "gp": return gpr_name_t'(gp);
            "tp": return gpr_name_t'(tp);
            "t0": return gpr_name_t'(t0);
            "t1": return gpr_name_t'(t1);
            "t2": return gpr_name_t'(t2);
            "s0": return gpr_name_t'(s0);
            "s1": return gpr_name_t'(s1);
            "a0": return gpr_name_t'(a0);
            "a1": return gpr_name_t'(a1);
            "a2": return gpr_name_t'(a2);
            "a3": return gpr_name_t'(a3);
            "a4": return gpr_name_t'(a4);
            "a5": return gpr_name_t'(a5);
            "a6": return gpr_name_t'(a6);
            "a7": return gpr_name_t'(a7);
            "s2": return gpr_name_t'(s2);
            "s3": return gpr_name_t'(s3);
            "s4": return gpr_name_t'(s4);
            "s5": return gpr_name_t'(s5);
            "s6": return gpr_name_t'(s6);
            "s7": return gpr_name_t'(s7);
            "s8": return gpr_name_t'(s8);
            "s9": return gpr_name_t'(s9);
            "s10": return gpr_name_t'(s10);
            "s11": return gpr_name_t'(s11);
            "t3": return gpr_name_t'(t3);
            "t4": return gpr_name_t'(t4);
            "t5": return gpr_name_t'(t5);
            "t6": return gpr_name_t'(t6);
            default: begin
                $display("ERROR: get_gpr_name(%0s) not found gpr for op(%0s) in (%0s)", s, r, asm);
                $finish(-1);
            end
        endcase
    endfunction

// The following CSRs are not currently included:
// mstatush, mtinst, mtval2, mhpmcounter3, ..., mhpmcounter31,
// mhpmcounter3h, ..., mhpmcounter31h,
    function csr_name_t get_csr_name (string s, r, asm);
        case (s)
            "marchid": return csr_name_t'(marchid);
            "mcause": return csr_name_t'(mcause);
            "mcounteren": return csr_name_t'(mcounteren);
            "mcountinhibit": return csr_name_t'(mcountinhibit);
            "mcycle": return csr_name_t'(mcycle);
            "mcycleh": return csr_name_t'(mcycleh);
            "medeleg": return csr_name_t'(medeleg);
            "mepc": return csr_name_t'(mepc);
            "mhartid": return csr_name_t'(mhartid);
            "mhpmevent10": return csr_name_t'(mhpmevent10);
            "mhpmevent11": return csr_name_t'(mhpmevent11);
            "mhpmevent12": return csr_name_t'(mhpmevent12);
            "mhpmevent13": return csr_name_t'(mhpmevent13);
            "mhpmevent14": return csr_name_t'(mhpmevent14);
            "mhpmevent15": return csr_name_t'(mhpmevent15);
            "mhpmevent16": return csr_name_t'(mhpmevent16);
            "mhpmevent17": return csr_name_t'(mhpmevent17);
            "mhpmevent18": return csr_name_t'(mhpmevent18);
            "mhpmevent19": return csr_name_t'(mhpmevent19);
            "mhpmevent20": return csr_name_t'(mhpmevent20);
            "mhpmevent21": return csr_name_t'(mhpmevent21);
            "mhpmevent22": return csr_name_t'(mhpmevent22);
            "mhpmevent23": return csr_name_t'(mhpmevent23);
            "mhpmevent24": return csr_name_t'(mhpmevent24);
            "mhpmevent25": return csr_name_t'(mhpmevent25);
            "mhpmevent26": return csr_name_t'(mhpmevent26);
            "mhpmevent27": return csr_name_t'(mhpmevent27);
            "mhpmevent28": return csr_name_t'(mhpmevent28);
            "mhpmevent29": return csr_name_t'(mhpmevent29);
            "mhpmevent3": return csr_name_t'(mhpmevent3);
            "mhpmevent30": return csr_name_t'(mhpmevent30);
            "mhpmevent31": return csr_name_t'(mhpmevent31);
            "mhpmevent4": return csr_name_t'(mhpmevent4);
            "mhpmevent5": return csr_name_t'(mhpmevent5);
            "mhpmevent6": return csr_name_t'(mhpmevent6);
            "mhpmevent7": return csr_name_t'(mhpmevent7);
            "mhpmevent8": return csr_name_t'(mhpmevent8);
            "mhpmevent9": return csr_name_t'(mhpmevent9);
            "mideleg": return csr_name_t'(mideleg);
            "mie": return csr_name_t'(mie);
            "mimpid": return csr_name_t'(mimpid);
            "minstret": return csr_name_t'(minstret);
            "minstreth": return csr_name_t'(minstreth);
            "mip": return csr_name_t'(mip);
            "misa": return csr_name_t'(misa);
            "mscratch": return csr_name_t'(mscratch);
            "mstatus": return csr_name_t'(mstatus);
            "mtval": return csr_name_t'(mtval);
            "mtvec": return csr_name_t'(mtvec);
            "mvendorid": return csr_name_t'(mvendorid);
            "pmpaddr0": return csr_name_t'(pmpaddr0);
            "pmpaddr1": return csr_name_t'(pmpaddr1);
            "pmpaddr10": return csr_name_t'(pmpaddr10);
            "pmpaddr11": return csr_name_t'(pmpaddr11);
            "pmpaddr12": return csr_name_t'(pmpaddr12);
            "pmpaddr13": return csr_name_t'(pmpaddr13);
            "pmpaddr14": return csr_name_t'(pmpaddr14);
            "pmpaddr15": return csr_name_t'(pmpaddr15);
            "pmpaddr2": return csr_name_t'(pmpaddr2);
            "pmpaddr3": return csr_name_t'(pmpaddr3);
            "pmpaddr4": return csr_name_t'(pmpaddr4);
            "pmpaddr5": return csr_name_t'(pmpaddr5);
            "pmpaddr6": return csr_name_t'(pmpaddr6);
            "pmpaddr7": return csr_name_t'(pmpaddr7);
            "pmpaddr8": return csr_name_t'(pmpaddr8);
            "pmpaddr9": return csr_name_t'(pmpaddr9);
            "pmpcfg0": return csr_name_t'(pmpcfg0);
            "pmpcfg1": return csr_name_t'(pmpcfg1);
            "pmpcfg2": return csr_name_t'(pmpcfg2);
            "pmpcfg3": return csr_name_t'(pmpcfg3);
            default: begin
                $display("ERROR: get_csr_name(%0s) not found csr for op(%0s) in (%0s)", s, r, asm);
                $finish(-1);
            end
        endcase
    endfunction

    function int get_imm(string s, asm);
      int val;
        if (s[1] == "x") begin
            s = s.substr(2,s.len()-1);
            val = s.atohex ();
        end else if (s[0] == "-") begin
            s = s.substr(1,s.len()-1);
            val = 0 - s.atoi();
        end else begin
            val = s.atoi();
        end
        return val;
    endfunction


///////////////////////////////////////////////////////////////////////////////
// Coverage of Base Integer Instruction Set, Version 2.1
///////////////////////////////////////////////////////////////////////////////

// TODO : missing check of toggling of all bits on GPRs.
// TODO : missing check of toggling of all bits on immediate operands

// TODO : missing coverage of all combinations of source and destination operands.
// TODO : missing check of overflow/underflow
    covergroup add_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "add");
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "add");
        cp_rs2    : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "add");
    endgroup

// TODO : missing coverage of all combinations of source and destination operands.
// TODO : missing check of overflow/underflow
// TODO : NOP covered by nop_cg cover group
    covergroup addi_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "addi");
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "addi");
        cp_imm11   : coverpoint get_imm(ins.ops[2].val,"addi" ) {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

// TODO : missing coverage of all combinations of source and destination operands.
    covergroup and_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "and");
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "and");
        cp_rs2    : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "and");
    endgroup

// TODO : missing coverage of all combinations of source and destination operands.
    covergroup andi_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "andi");
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "andi");
        cp_imm11   : coverpoint get_imm(ins.ops[2].val,"andi" ) {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

// TODO : missing coverage of all immediate values and destination registers.
    covergroup auipc_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "auipc");
        cp_uimm20   : coverpoint get_imm(ins.ops[1].val,"auipc" ) {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

// TODO : missing check of arbitrary positive and negative immediate values
// TODO : missing check of maximum positive and negative immediate values
    covergroup beq_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rs1    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "beq");
        cp_rs2    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "beq");
        cp_bra12   : coverpoint get_imm(ins.ops[2].val,"beq" ) {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

// TODO : missing check of arbitrary positive and negative immediate values
// TODO : missing check of maximum positive and negative immediate values
    covergroup bge_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rs1    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "bge");
        cp_rs2    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "bge");
        cp_bra12   : coverpoint get_imm(ins.ops[2].val,"bge" ) {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

// TODO : missing check of maximum immediate value
    covergroup bgeu_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rs1    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "bgeu");
        cp_rs2    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "bgeu");
        cp_bra12   : coverpoint get_imm(ins.ops[2].val,"bgeu" ) {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

// TODO : missing check of arbirary positive and negative immediate values
// TODO : missing check of maximum positive and negative immediate values
    covergroup blt_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rs1    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "blt");
        cp_rs2    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "blt");
        cp_bra12   : coverpoint get_imm(ins.ops[2].val,"blt" ) {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

// TODO : missing check of maximum of immediate value
    covergroup bltu_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rs1    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "bltu");
        cp_rs2    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "bltu");
        cp_bra12   : coverpoint get_imm(ins.ops[2].val,"bltu" ) {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

// TODO : missing check of arbirary positive and negative immediate values
// TODO : missing check of maximum positive and negative immediate values
    covergroup bne_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rs1    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "bne");
        cp_rs2    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "bne");
        cp_bra12   : coverpoint get_imm(ins.ops[2].val,"bne" ) {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

// TODO : only counting occurrence, ignoring when not called.
// TODO : verification goal not specified in test plan
    covergroup ebreak_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_asm   : coverpoint ins.asm == EBREAK {
            ignore_bins zero = {0};
        }
    endgroup

// TODO : only counting occurrence, ignoring when not called.
// TODO : verification goal not specified in test plan
    covergroup ecall_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_asm   : coverpoint ins.asm == ECALL {
            ignore_bins zero = {0};
        }
    endgroup

// TODO : only counting occurence, ignoring when not called.
// TODO : verification goal not specified in test plan
    covergroup fence_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_asm   : coverpoint ins.asm == FENCE {
            ignore_bins zero = {0};
        }
    endgroup

// TODO : case when rd = x0 counted but not singled out
    covergroup jal_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "jal");
        cp_jmp19   : coverpoint get_imm(ins.ops[1].val,"jal" ) {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

// TODO : unclear from the code why "key" values for cp_r0 and cp_r1 can be "R" or "C"
// TODO : need to clarify if this is due to the diassembler and unrelated to RTL
// TODO : missing check of arbirary positive and negative immediate values
// TODO : missing check of maximum positive and negative immediate values
    covergroup jalr_cg with function sample(ins_t ins, gpr_name_t r0, gpr_name_t r1);
        //option.per_instance = 1;
        cp_r0    : coverpoint r0 iff (ins.ops[0].key[0] == "R");
        cp_r1    : coverpoint r1 iff (ins.ops[1].key[0] == "R");
        cp_imm0   : coverpoint get_imm(ins.ops[0].val,"jalr" ) iff (ins.ops[0].key[0] == "C") {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
        cp_imm1   : coverpoint get_imm(ins.ops[1].val,"jalr" ) iff (ins.ops[1].key[0] == "C") {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

// FIXME : cp_r shall be renamed to cp_rs1
// FIXME : cover point for rs1 should be on ins.ops[1]
// FIXME : cover point for imm should be on ins.ops[2]
// TODO : missing check of arbirary positive and negative immediate values
// TODO : missing check of maximum positive and negative immediate values
    covergroup lb_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "lb");
        cp_imm    : coverpoint get_imm(ins.ops[1].val, "lb") {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
        cp_r     : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "lb");
    endgroup

// FIXME : cp_r shall be renamed to cp_rs1
// FIXME : cover point for rs1 should be on ins.ops[1]
// FIXME : cover point for imm should be on ins.ops[2]
// TODO : missing check of arbirary positive and negative immediate values
// TODO : missing check of maximum positive and negative immediate values
    covergroup lbu_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "lbu");
        cp_imm    : coverpoint get_imm(ins.ops[1].val, "lbu") {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
        cp_r     : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "lbu");
    endgroup

// FIXME : missing cover point for rs1 for ins.ops[1]
// FIXME : cover point for imm should be on ins.ops[2]
// TODO : missing check of arbirary positive and negative immediate values
// TODO : missing check of maximum positive and negative immediate values
    covergroup lh_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "lh");
        cp_imm    : coverpoint get_imm(ins.ops[1].val, "lh") {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
        cp_r     : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "lh");
    endgroup

// FIXME : missing cover point for rs1 for ins.ops[1]
// FIXME : cover point for imm should be on ins.ops[2]
// TODO : missing check of arbirary positive and negative immediate values
// TODO : missing check of maximum positive and negative immediate values
    covergroup lhu_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "lhu");
        cp_imm    : coverpoint get_imm(ins.ops[1].val, "lhu") {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
        cp_r     : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "lhu");
    endgroup

// TODO : missing coverage of all immediate values and destination registers.
    covergroup lui_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "lui");
        cp_uimm20   : coverpoint get_imm(ins.ops[1].val,"lui" ) {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

// FIXME : missing cover point for rs1 for ins.ops[1]
// FIXME : cover point for imm should be on ins.ops[2]
// TODO : missing check of arbirary positive and negative immediate values
// TODO : missing check of maximum positive and negative immediate values
    covergroup lw_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "lw");
        cp_imm    : coverpoint get_imm(ins.ops[1].val, "lw") {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
        cp_r     : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "lw");
    endgroup

// TODO : cover group for NOP (addi x0, x0, imm), may need to be merged into addi_cg
    covergroup nop_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_asm   : coverpoint ins.asm == NOP {
            ignore_bins zero = {0};
        }
    endgroup

// TODO : missing coverage of all combinations of source and destination operands.
    covergroup or_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "or");
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "or");
        cp_rs2    : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "or");
    endgroup

// TODO : missing coverage of all combinations of source and destination operands.
    covergroup ori_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "ori");
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "ori");
        cp_imm11   : coverpoint get_imm(ins.ops[2].val,"ori" ) {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

// FIXME : cover point for rs1 should be on ins.ops[0]
// FIXME : cover point for rs2 should be on ins.ops[1]
// FIXME : cover point for imm should be on ins.ops[2]
// TODO : missing check of maximum values of rs1 and imm
// TODO "" missing check of overflow conditions"
    covergroup sb_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rs2    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "sb");
        cp_imm    : coverpoint get_imm(ins.ops[1].val, "sb") {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
        cp_r     : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "sb");
    endgroup

// FIXME : cover point for rs1 should be on ins.ops[0]
// FIXME : cover point for rs2 should be on ins.ops[1]
// FIXME : cover point for imm should be on ins.ops[2]
// TODO : missing check of maximum values of rs1 and imm
// TODO " missing check of overflow conditions
    covergroup sh_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rs2    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "sh");
        cp_imm    : coverpoint get_imm(ins.ops[1].val, "sh") {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
        cp_r     : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "sh");
    endgroup

// TODO : missing coverage of all combinations of source and destination operands.
    covergroup sll_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "sll");
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "sll");
        cp_rs2    : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "sll");
    endgroup

// TODO : missing coverage of all combinations of source and destination operands.
    covergroup slli_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "slli");
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "slli");
        cp_shamt5   : coverpoint get_imm(ins.ops[2].val,"slli" ) {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

// TODO : missing coverage of all combinations of source and destination operands.
    covergroup slt_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "slt");
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "slt");
        cp_rs2    : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "slt");
    endgroup

// TODO : missing coverage of all combinations of source and destination operands.
    covergroup slti_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "slti");
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "slti");
        cp_imm11   : coverpoint get_imm(ins.ops[2].val,"slti" ) {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

// TODO : missing coverage of all combinations of source and destination operands.
// TODO : missing check of arbirary positive and negative immediate values
    covergroup sltiu_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "sltiu");
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "sltiu");
        cp_imm11   : coverpoint get_imm(ins.ops[2].val,"sltiu" ) {
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

// TODO : missing coverage of all combinations of source and destination operands.
    covergroup sltu_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "sltu");
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "sltu");
        cp_rs2    : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "sltu");
    endgroup

// TODO : missing coverage of all combinations of source and destination operands.
// TODO : missing check of arbirary positive and negative immediate values
// TODO : missing check of maximum positive and negative immediate values
    covergroup sra_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "sra");
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "sra");
        cp_rs2    : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "sra");
    endgroup

// TODO : missing coverage of all combinations of source and destination operands.
// TODO : missing check of arbirary positive and negative immediate values
    covergroup srai_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "srai");
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "srai");
        cp_shamt5   : coverpoint get_imm(ins.ops[2].val,"srai" ) {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

// TODO : missing coverage of all combinations of source and destination operands.
    covergroup srl_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "srl");
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "srl");
        cp_rs2    : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "srl");
    endgroup

// TODO : missing coverage of all combinations of source and destination operands.
    covergroup srli_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "srli");
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "srli");
        cp_shamt5   : coverpoint get_imm(ins.ops[2].val,"srli" ) {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

// TODO : missing coverage of all combinations of source and destination operands.
// TODO : missing check of underflow
    covergroup sub_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "sub");
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "sub");
        cp_rs2    : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "sub");
    endgroup

// FIXME : cover point for rs1 should be on ins.ops[0]
// FIXME : cover point for rs2 should be on ins.ops[1]
// FIXME : cover point for imm should be on ins.ops[2]
// TODO : missing check of maximum values of rs1 and imm
// TODO " missing check of overflow conditions
    covergroup sw_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rs2    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "sw");
        cp_imm    : coverpoint get_imm(ins.ops[1].val, "sw") {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
        cp_r     : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "sw");
    endgroup

// TODO : missing coverage of all combinations of source and destination operands.
// TODO : mising specific cases where one of the sources is -1 (bitwise NOT)
    covergroup xor_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "xor");
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "xor");
        cp_rs2    : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "xor");
    endgroup

// TODO : missing coverage of all combinations of source and destination operands.
// TODO : mising specific cases where one of the sources is -1 (bitwise NOT)
    covergroup xori_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "xori");
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "xori");
        cp_imm11   : coverpoint get_imm(ins.ops[2].val,"xori" ) {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

///////////////////////////////////////////////////////////////////////////////
//Coverage of Std Extension for Integer Multiplication & Division, Version 2.0
///////////////////////////////////////////////////////////////////////////////

// TODO : missing coverage of all combinations of source and destination operands.
// TODO : missing check of overflow/underflow
    covergroup mul_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "mul");
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "mul");
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "mul");
    endgroup

// TODO : missing coverage of all combinations of source and destination operands.
    covergroup mulh_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "mulh");
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "mulh");
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "mulh" ) {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

// TODO : missing coverage of all combinations of source and destination operands.
    covergroup mulhu_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "mulhu");
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "mulhu");
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "mulhu");
    endgroup

// TODO : missing coverage of all combinations of source and destination operands.
// TODO : missing check that rs1 is signed and rs2 is unsigned.
    covergroup mulhsu_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "mulhsu");
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "mulhsu");
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "mulhsu" ) {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

// TODO : missing coverage for sequence of MULH[[S]U] and MUL instructions
//        where micro-architecture fuses/merges them into one isntruction.

// TODO : missing coverage of all combinations of source and destination operands.
// TODO : missing check of overflow/underflow
// TODO : missing check of divide-by-zero
    covergroup div_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "div");
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "div");
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "div" ) {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

// TODO : missing coverage of all combinations of source and destination operands.
// TODO : missing check of overflow/underflow
// TODO : missing check of divide-by-zero
    covergroup rem_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "rem");
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "rem");
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "rem" ) {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

// TODO : missing coverage of all combinations of source and destination operands.
// TODO : missing check of divide-by-zero
    covergroup divu_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "divu");
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "divu");
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "divu" ) {
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

// TODO : missing coverage of all combinations of source and destination operands.
// TODO : missing check of divide-by-zero
    covergroup remu_cg with function sample(ins_t ins);
        //option.per_instance = 1;
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "remu");
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "remu");
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "remu" ) {
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

///////////////////////////////////////////////////////////////////////////////
//Coverage of Std Extension for Compressed Instructions, Version 2.0
///////////////////////////////////////////////////////////////////////////////

// TODO : missing check that 32I & 32C instuctions aligned on 16/32-bit boundaries.


// TODO : missing coverage of all combinations of source and destination operands.
    covergroup c_lwsp_cg     with function sample(ins_t ins);
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.lwsp");
        cp_imm   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.lwsp") {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

// TODO : missing coverage of all combinations of source and destination operands.
    covergroup c_flwsp_cg    with function sample(ins_t ins);
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.flwsp");
        cp_imm   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.flwsp") {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup c_swsp_cg    with function sample(ins_t ins);
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.swsp");
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.swsp");
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "c.swsp" ) {
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup c_fswsp_cg    with function sample(ins_t ins);
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.fswsp");
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.fswsp");
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "c.fswsp" ) {
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup c_lw_cg       with function sample(ins_t ins);
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.lw");
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.lw");
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "c.lw" ) {
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup c_flw_cg      with function sample(ins_t ins);
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.flw");
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.flw");
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "c.flw" ) {
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup c_sw_cg       with function sample(ins_t ins);
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.sw");
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.sw");
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "c.sw" ) {
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup c_fsw_cg       with function sample(ins_t ins);
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.fsw");
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.fsw");
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "c.fsw" ) {
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup c_jal_cg      with function sample(ins_t ins);
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.jal");
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.jal");
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "c.jal" ) {
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup c_jalr_cg with function sample(ins_t ins, gpr_name_t r0, gpr_name_t r1);
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.jalr");
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.jalr");
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "c.jalr" ) {
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup c_li_cg       with function sample(ins_t ins);
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.li");
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.li");
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "c.li" ) {
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup c_lui_cg      with function sample(ins_t ins);
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.lui");
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.lui");
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "c.lui" ) {
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    // MikeT - 20200714: c_addi_cg redefined to reflect single register,
    //                   single immediate op-codes
    //covergroup c_addi_cg     with function sample(ins_t ins);
    //    cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.addi");
    //    cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.addi");
    //    cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "c.addi" ) {
    //        bins zero = {0};
    //        bins pos  = {[1:$]};
    //    }
    //endgroup

    covergroup c_addi_cg with function sample(ins_t ins);
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "addi");
        cp_imm6  : coverpoint get_imm(ins.ops[2].val,"addi" ) {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup
    // MikeT - 20200714

    // MikeT - 20200714: c_addi16sp_cg redefined to reflect single register,
    //                   single immediate op-codes
    //covergroup c_addi16sp_cg with function sample(ins_t ins);
    //    cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.addi16sp");
    //    cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.addi16sp");
    //    cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "c.addi16sp" ) {
    //        bins zero = {0};
    //        bins pos  = {[1:$]};
    //    }
    //endgroup

    covergroup c_addi16sp_cg with function sample(ins_t ins);
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.addi16sp");
        cp_imm6  : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "c.addi16sp" ) {
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup
    // MikeT - 20200714

    // MikeT - 20200714: c_addi4sp_cg redefined to reflect single register,
    //                   single immediate op-codes
    //covergroup c_addi4sp_cg  with function sample(ins_t ins);
    //    cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.addi4sp");
    //    cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.addi4sp");
    //    cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "c.addi4sp" ) {
    //        bins zero = {0};
    //        bins pos  = {[1:$]};
    //    }
    //endgroup

    covergroup c_addi4spn_cg  with function sample(ins_t ins);
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.addi4sp");
        cp_imm8  : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "c.addi4sp" ) {
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup
    // MikeT - 20200714

    covergroup c_slli_cg     with function sample(ins_t ins);
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.slli");
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.slli");
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "c.slli" ) {
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup c_srli_cg     with function sample(ins_t ins);
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.srli");
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.srli");
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "c.srli" ) {
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup c_srai_cg     with function sample(ins_t ins);
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.srai");
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.srai");
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "c.srai" ) {
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup c_andi_cg     with function sample(ins_t ins);
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.andi");
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.andi");
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "c.andi" ) {
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    // MikeT - 20200714: c_addi_cg redefined to reflect single destination register,
    //                   single source register op-codes
    //covergroup c_add_cg      with function sample(ins_t ins);
    //    cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.add");
    //    cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.add");
    //    cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "c.add" ) {
    //        bins zero = {0};
    //        bins pos  = {[1:$]};
    //    }
    //endgroup

    covergroup c_add_cg with function sample(ins_t ins);
        cp_rd     : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "add");
        cp_rs2    : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "add");
    endgroup
    // MikeT - 20200714

    covergroup c_and_cg      with function sample(ins_t ins);
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.and");
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.and");
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "c.and" ) {
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup c_or_cg       with function sample(ins_t ins);
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.or");
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.or");
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "c.or" ) {
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup c_xor_cg      with function sample(ins_t ins);
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.xor");
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.xor");
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "c.xor" ) {
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup c_sub_cg      with function sample(ins_t ins);
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.sub");
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.sub");
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "c.sub" ) {
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup c_nop_cg      with function sample(ins_t ins);
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.nop");
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.nop");
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "c.nop" ) {
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup c_ebreak_cg   with function sample(ins_t ins);
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.ebreak");
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.ebreak");
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "c.ebreak" ) {
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    function new();
        add_cg = new();
        addi_cg = new();
        and_cg = new();
        andi_cg = new();
        auipc_cg = new();
        beq_cg = new();
        bge_cg = new();
        bgeu_cg = new();
        blt_cg = new();
        bltu_cg = new();
        bne_cg = new();
        ebreak_cg = new();
        ecall_cg = new();
        fence_cg = new();
        jal_cg = new();
        jalr_cg = new();
        lb_cg = new();
        lbu_cg = new();
        lh_cg = new();
        lhu_cg = new();
        lui_cg = new();
        lw_cg = new();
        nop_cg = new();
        or_cg = new();
        ori_cg = new();
        sb_cg = new();
        sh_cg = new();
        sll_cg = new();
        slli_cg = new();
        slt_cg = new();
        slti_cg = new();
        sltiu_cg = new();
        sltu_cg = new();
        sra_cg = new();
        srai_cg = new();
        srl_cg = new();
        srli_cg = new();
        sub_cg = new();
        sw_cg = new();
        xor_cg = new();
        xori_cg = new();
        mul_cg = new();
        mulh_cg = new();
        mulhu_cg = new();
        mulhsu_cg = new();
        div_cg = new();
        rem_cg = new();
        divu_cg = new();
        remu_cg = new();
        // The "c_add*_cg are remapped versions of their uncompressed source"
        c_add_cg      = new();
        c_addi_cg     = new();
        c_addi16sp_cg = new();
        c_addi4spn_cg = new();
        // The c_*_cg below are unmodified from the original
        c_or_cg       = new();
        c_lwsp_cg     = new();
        c_flwsp_cg    = new();
        c_swsp_cg     = new();
        c_fswsp_cg    = new();
        c_lw_cg       = new();
        c_flw_cg      = new();
        c_sw_cg       = new();
        c_fsw_cg      = new();
        c_jal_cg      = new();
        c_jalr_cg     = new();
        c_li_cg       = new();
        c_lui_cg      = new();
        c_slli_cg     = new();
        c_srli_cg     = new();
        c_srai_cg     = new();
        c_andi_cg     = new();
        c_and_cg      = new();
        c_xor_cg      = new();
        c_sub_cg      = new();
        c_nop_cg      = new();
        c_ebreak_cg   = new();
    endfunction: new

    function void check_compressed(input ins_t ins);
        case (ins.ins_str)
            "add"      : if ( get_gpr_name(ins.ops[0].val, ins.ops[0].key, "add")  == get_gpr_name(ins.ops[1].val, ins.ops[1].key, "add") ) c_add_cg.sample(ins);

            "addi"     : if ( get_gpr_name(ins.ops[0].val, ins.ops[0].key, "addi") == get_gpr_name(ins.ops[1].val, ins.ops[1].key, "addi")) c_addi_cg.sample(ins);

            "addi16sp" : if ( get_gpr_name(ins.ops[0].val, ins.ops[0].key, "addi") == get_gpr_name(ins.ops[1].val, ins.ops[1].key, "addi") && 
                              get_gpr_name(ins.ops[0].val, ins.ops[0].key, "addi") == "x2") c_addi16sp_cg.sample(ins);

            "addi4spn" : if ( get_gpr_name(ins.ops[0].val, ins.ops[0].key, "addi") == get_gpr_name(ins.ops[1].val, ins.ops[1].key, "addi") && 
                              get_gpr_name(ins.ops[1].val, ins.ops[1].key, "addi") == "x2") c_addi4spn_cg.sample(ins);
 
            default: `uvm_info("RV32ISA Coverage", $sformatf("check_compressed(): ins [%0s] not yet checked", ins.ins_str), UVM_HIGH)
        endcase
    endfunction: check_compressed

    function void sample(input ins_t ins);
        check_compressed(ins);
        case (ins.ins_str)
            "add"    : begin ins.asm=ADD; add_cg.sample(ins); end
            "addi"    : begin ins.asm=ADDI; addi_cg.sample(ins); end
            "and"    : begin ins.asm=AND; and_cg.sample(ins); end
            "andi"    : begin ins.asm=ANDI; andi_cg.sample(ins); end
            "auipc"    : begin ins.asm=AUIPC; auipc_cg.sample(ins); end
            "beq"    : begin ins.asm=BEQ; beq_cg.sample(ins); end
            "bge"    : begin ins.asm=BGE; bge_cg.sample(ins); end
            "bgeu"    : begin ins.asm=BGEU; bgeu_cg.sample(ins); end
            "blt"    : begin ins.asm=BLT; blt_cg.sample(ins); end
            "bltu"    : begin ins.asm=BLTU; bltu_cg.sample(ins); end
            "bne"    : begin ins.asm=BNE; bne_cg.sample(ins); end
            "ebreak"    : begin ins.asm=EBREAK; ebreak_cg.sample(ins); end
            "ecall"    : begin ins.asm=ECALL; ecall_cg.sample(ins); end
            "fence"    : begin ins.asm=FENCE; fence_cg.sample(ins); end
            "jal"    : begin ins.asm=JAL; jal_cg.sample(ins); end
            "jalr"    : begin
                gpr_name_t r0, r1;
                ins.asm=JALR;
                if (ins.ops[0].key[0] == "R")
                    r0 = get_gpr_name(ins.ops[0].val, ins.ops[0].key, "jalr");
                else
                    r0 = gpr_none;
                if (ins.ops[1].key[1] == "R")
                    r1 = get_gpr_name(ins.ops[1].val, ins.ops[1].key, "jalr");
                else
                    r1 = gpr_none;
                jalr_cg.sample(ins, r0, r1);
            end
            "lb"    : begin ins.asm=LB; lb_cg.sample(ins); end
            "lbu"    : begin ins.asm=LBU; lbu_cg.sample(ins); end
            "lh"    : begin ins.asm=LH; lh_cg.sample(ins); end
            "lhu"    : begin ins.asm=LHU; lhu_cg.sample(ins); end
            "lui"    : begin ins.asm=LUI; lui_cg.sample(ins); end
            "lw"    : begin ins.asm=LW; lw_cg.sample(ins); end
            "nop"    : begin ins.asm=NOP; nop_cg.sample(ins); end
            "or"    : begin ins.asm=OR; or_cg.sample(ins); end
            "ori"    : begin ins.asm=ORI; ori_cg.sample(ins); end
            "sb"    : begin ins.asm=SH; sb_cg.sample(ins); end
            "sh"    : begin ins.asm=SH; sh_cg.sample(ins); end
            "sll"    : begin ins.asm=SLL; sll_cg.sample(ins); end
            "slli"    : begin ins.asm=SLLI; slli_cg.sample(ins); end
            "slt"    : begin ins.asm=SLT; slt_cg.sample(ins); end
            "slti"    : begin ins.asm=SLTI; slti_cg.sample(ins); end
            "sltiu"    : begin ins.asm=SLTIU; sltiu_cg.sample(ins); end
            "sltu"    : begin ins.asm=SLTU; sltu_cg.sample(ins); end
            "sra"    : begin ins.asm=SRA; sra_cg.sample(ins); end
            "srai"    : begin ins.asm=SRAI; srai_cg.sample(ins); end
            "srl"    : begin ins.asm=SRL; srl_cg.sample(ins); end
            "srli"    : begin ins.asm=SRLI; srli_cg.sample(ins); end
            "sub"    : begin ins.asm=SUB; sub_cg.sample(ins); end
            "sw"    : begin ins.asm=SW; sw_cg.sample(ins); end
            "xor"    : begin ins.asm=XOR; xor_cg.sample(ins); end
            "xori"    : begin ins.asm=XORI; xori_cg.sample(ins); end
            "mul"    : begin ins.asm=MUL; mul_cg.sample(ins); end
            "mulh"    : begin ins.asm=MULH; mulh_cg.sample(ins); end
            "mulhu"    : begin ins.asm=MULHU; mulhu_cg.sample(ins); end
            "mulhsu"    : begin ins.asm=MULHSU; mulhsu_cg.sample(ins); end
            "div"    : begin ins.asm=DIV; div_cg.sample(ins); end
            "rem"    : begin ins.asm=REM; rem_cg.sample(ins); end
            "divu"    : begin ins.asm=DIVU; divu_cg.sample(ins); end
            "remu"    : begin ins.asm=REMU; remu_cg.sample(ins); end
            "c.lwsp"    : begin ins.asm=C_LWSP; c_lwsp_cg.sample(ins); end
            "c.flwsp"    : begin ins.asm=C_FLWSP; c_flwsp_cg.sample(ins); end
            "c.swsp"    : begin ins.asm=C_SWSP; c_swsp_cg.sample(ins); end
            "c.fswsp"    : begin ins.asm=C_FSWSP; c_fswsp_cg.sample(ins); end
            "c.lw"    : begin ins.asm=C_LW; c_lw_cg.sample(ins); end
            "c.flw"    : begin ins.asm=C_FLW; c_flw_cg.sample(ins); end
            "c.sw"    : begin ins.asm=C_SW; c_sw_cg.sample(ins); end
            "c.fsw"    : begin ins.asm=C_FSW; c_fsw_cg.sample(ins); end
            "c.jal"    : begin ins.asm=C_JAL; c_jal_cg.sample(ins); end
            "c.jalr"    : begin
                gpr_name_t r0, r1;
                ins.asm=C_JALR;
                if (ins.ops[0].key[0] == "R")
                    r0 = get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.jalr");
                else
                    r0 = gpr_none;
                if (ins.ops[1].key[1] == "R")
                    r1 = get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.jalr");
                else
                    r1 = gpr_none;
                c_jalr_cg.sample(ins, r0, r1);
            end
            "c.li"    : begin ins.asm=C_LI; c_li_cg.sample(ins); end
            "c.lui"    : begin ins.asm=C_LUI; c_lui_cg.sample(ins); end
            "c.addi"    : begin ins.asm=C_ADDI; c_addi_cg.sample(ins); end
            "c.addi16sp"    : begin ins.asm=C_ADDI16SP; c_addi16sp_cg.sample(ins); end
            "c.addi4spn"    : begin ins.asm=C_ADDI4SPN; c_addi4spn_cg.sample(ins); end
            "c.slli"    : begin ins.asm=C_SLLI; c_slli_cg.sample(ins); end
            "c.srli"    : begin ins.asm=C_SRLI; c_srli_cg.sample(ins); end
            "c.srai"    : begin ins.asm=C_SRAI; c_srai_cg.sample(ins); end
            "c.andi"    : begin ins.asm=C_ANDI; c_andi_cg.sample(ins); end
            "c.add"    : begin ins.asm=C_ADD; c_add_cg.sample(ins); end
            "c.and"    : begin ins.asm=C_AND; c_and_cg.sample(ins); end
            "c.or"    : begin ins.asm=C_OR; c_or_cg.sample(ins); end
            "c.xor"    : begin ins.asm=C_XOR; c_xor_cg.sample(ins); end
            "c.sub"    : begin ins.asm=C_SUB; c_sub_cg.sample(ins); end
            "c.nop"    : begin ins.asm=C_NOP; c_nop_cg.sample(ins); end
            "c.ebreak"    : begin ins.asm=C_EBREAK; c_ebreak_cg.sample(ins); end
            default: begin ins.asm=NOP; end /*$display("Coverage warning: ins [%0s] not yet included in being covered", ins.ins_str);*/ //end
        endcase
    endfunction: sample


endclass
