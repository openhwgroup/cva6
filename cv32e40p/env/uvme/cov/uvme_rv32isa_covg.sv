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

// Thie coverage model works by copying lots of small strings,
// Not all of these can be converted to const ref, so disable the string-copy performance lint check
//@DVT_LINTER_WAIVER_START "SR20211012_1" disable SVTB.32.2.0

class uvme_rv32isa_covg extends uvm_component;


    uvme_cv32e40p_cntxt_c  cntxt;

    uvm_analysis_port#(uvme_rv32isa_covg_trn_c) ap;

    ins_t ins_prev; // Previous instruction

    // Instruction display method (for debug)
    function string ins_display(ins_t ins);
      string retval;

      retval = $sformatf("\n\tins_str = %s", ins.ins_str);
      retval = {retval, $sformatf("\n\tins.asm = %s", ins.asm.name())};
      foreach (ins.ops[i]) begin
        retval = {retval, $sformatf("\n\tins.ops[%0d].key = %s, ins.ops[%0d].val = %s", i, ins.ops[i].key, i, ins.ops[i].val)};
      end
      retval = {retval, $sformatf("\n\tins.compressed = %0d", ins.compressed)};
      retval = {retval, $sformatf("\n\tins.pc = 32'h%4h_%4h", ins.pc[31:16], ins.pc[15:0])};

      ins_display = retval;
    endfunction

    // The following CSR ABI names are not currently included:
    // fp, pc
    function gpr_name_t get_gpr_name (string s, r, asm);
        `uvm_info("RV32ISA Coverage", $sformatf("get_gpr_name(): GPR [%0s] used by ins %s being validated", s, asm), UVM_DEBUG)
        case (s)
            "zero" : return gpr_name_t'(zero);
            "ra"   : return gpr_name_t'(ra);
            "sp"   : return gpr_name_t'(sp);
            "gp"   : return gpr_name_t'(gp);
            "tp"   : return gpr_name_t'(tp);
            "t0"   : return gpr_name_t'(t0);
            "t1"   : return gpr_name_t'(t1);
            "t2"   : return gpr_name_t'(t2);
            "s0"   : return gpr_name_t'(s0);
            "s1"   : return gpr_name_t'(s1);
            "a0"   : return gpr_name_t'(a0);
            "a1"   : return gpr_name_t'(a1);
            "a2"   : return gpr_name_t'(a2);
            "a3"   : return gpr_name_t'(a3);
            "a4"   : return gpr_name_t'(a4);
            "a5"   : return gpr_name_t'(a5);
            "a6"   : return gpr_name_t'(a6);
            "a7"   : return gpr_name_t'(a7);
            "s2"   : return gpr_name_t'(s2);
            "s3"   : return gpr_name_t'(s3);
            "s4"   : return gpr_name_t'(s4);
            "s5"   : return gpr_name_t'(s5);
            "s6"   : return gpr_name_t'(s6);
            "s7"   : return gpr_name_t'(s7);
            "s8"   : return gpr_name_t'(s8);
            "s9"   : return gpr_name_t'(s9);
            "s10"  : return gpr_name_t'(s10);
            "s11"  : return gpr_name_t'(s11);
            "t3"   : return gpr_name_t'(t3);
            "t4"   : return gpr_name_t'(t4);
            "t5"   : return gpr_name_t'(t5);
            "t6"   : return gpr_name_t'(t6);
            default: begin
                `uvm_info("RV32ISA Coverage", $sformatf("get_gpr_name(): GPR [%0s] used by ins %s not recognized!", s, asm), UVM_HIGH)
            end
        endcase
    endfunction

// These are the General Purpouse Registers for Compressed instructions
    function logic c_check_gpr_name (string s, r, asm);
        `uvm_info("RV32ISA Coverage", $sformatf("c_check_gpr_name(): GPR [%0s] used by ins %s being validated", s, asm), UVM_HIGH)
        case (s)
            "s0": return 1;
            "s1": return 1;
            "a0": return 1;
            "a1": return 1;
            "a2": return 1;
            "a3": return 1;
            "a4": return 1;
            "a5": return 1;
            default: begin
                `uvm_info("RV32ISA Coverage", $sformatf("c_check_gpr_name(): GPR [%0s] used by ins %s not one of: s0,s1,a0,a1,a2,a3,a4,a5", s, asm), UVM_HIGH)
                return 0;
            end
        endcase
    endfunction

// The following CSRs are not included as they do not exist in CV32E40P
// because NUM_HPMCOUNTERS is set to 1:
//    mhpmevent4,    ..., mhpmevent4,
//    mhpmcounter4,  ..., mhpmcounter31,
//    mhpmcounterh4, ..., mhpmcounterh31
    function csr_name_t get_csr_name (string s, r, asm);
        case (s)
            "mcause"       : return csr_name_t'(mcause);
            "mcountinhibit": return csr_name_t'(mcountinhibit);
            "mcycle"       : return csr_name_t'(mcycle);
            "mcycleh"      : return csr_name_t'(mcycleh);
            "mepc"         : return csr_name_t'(mepc);
            "mhartid"      : return csr_name_t'(mhartid);
            "mhpmevent3"   : return csr_name_t'(mhpmevent3);
            //"mhpmevent4"   : return csr_name_t'(mhpmevent4);
            //"mhpmevent5"   : return csr_name_t'(mhpmevent5);
            //"mhpmevent6"   : return csr_name_t'(mhpmevent6);
            //"mhpmevent7"   : return csr_name_t'(mhpmevent7);
            //"mhpmevent8"   : return csr_name_t'(mhpmevent8);
            //"mhpmevent9"   : return csr_name_t'(mhpmevent9);
            //"mhpmevent10"  : return csr_name_t'(mhpmevent10);
            //"mhpmevent11"  : return csr_name_t'(mhpmevent11);
            //"mhpmevent12"  : return csr_name_t'(mhpmevent12);
            //"mhpmevent13"  : return csr_name_t'(mhpmevent13);
            //"mhpmevent14"  : return csr_name_t'(mhpmevent14);
            //"mhpmevent15"  : return csr_name_t'(mhpmevent15);
            //"mhpmevent16"  : return csr_name_t'(mhpmevent16);
            //"mhpmevent17"  : return csr_name_t'(mhpmevent17);
            //"mhpmevent18"  : return csr_name_t'(mhpmevent18);
            //"mhpmevent19"  : return csr_name_t'(mhpmevent19);
            //"mhpmevent20"  : return csr_name_t'(mhpmevent20);
            //"mhpmevent21"  : return csr_name_t'(mhpmevent21);
            //"mhpmevent22"  : return csr_name_t'(mhpmevent22);
            //"mhpmevent23"  : return csr_name_t'(mhpmevent23);
            //"mhpmevent24"  : return csr_name_t'(mhpmevent24);
            //"mhpmevent25"  : return csr_name_t'(mhpmevent25);
            //"mhpmevent26"  : return csr_name_t'(mhpmevent26);
            //"mhpmevent27"  : return csr_name_t'(mhpmevent27);
            //"mhpmevent28"  : return csr_name_t'(mhpmevent28);
            //"mhpmevent29"  : return csr_name_t'(mhpmevent29);
            //"mhpmevent30"  : return csr_name_t'(mhpmevent30);
            //"mhpmevent31"  : return csr_name_t'(mhpmevent31);
            "mie"          : return csr_name_t'(mie);
            "minstret"     : return csr_name_t'(minstret);
            "minstreth"    : return csr_name_t'(minstreth);
            "mip"          : return csr_name_t'(mip);
            "misa"         : return csr_name_t'(misa);
            "mscratch"     : return csr_name_t'(mscratch);
            "mstatus"      : return csr_name_t'(mstatus);
            "marchid"      : return csr_name_t'(marchid);
            "mimpid"       : return csr_name_t'(mimpid);
            "mtval"        : return csr_name_t'(mtval);
            "mtvec"        : return csr_name_t'(mtvec);
            "mvendorid"    : return csr_name_t'(mvendorid);
            "mcontext"     : return csr_name_t'(mcontext);
            "scontext"     : return csr_name_t'(scontext);
            "tselect"      : return csr_name_t'(tselect);
            "tdata1"       : return csr_name_t'(tdata1);
            "tdata2"       : return csr_name_t'(tdata2);
            "tdata3"       : return csr_name_t'(tdata3);
            "tinfo"        : return csr_name_t'(tinfo);
            "dscratch0"    : return csr_name_t'(dscratch0);
            "dscratch1"    : return csr_name_t'(dscratch1);
            "mhpmcounter3" : return csr_name_t'(mhpmcounter3);
            //"mhpmcounter4" : return csr_name_t'(mhpmcounter4);
            //"mhpmcounter5" : return csr_name_t'(mhpmcounter5);
            //"mhpmcounter6" : return csr_name_t'(mhpmcounter6);
            //"mhpmcounter7" : return csr_name_t'(mhpmcounter7);
            //"mhpmcounter8" : return csr_name_t'(mhpmcounter8);
            //"mhpmcounter9" : return csr_name_t'(mhpmcounter9);
            //"mhpmcounter10": return csr_name_t'(mhpmcounter10);
            //"mhpmcounter11": return csr_name_t'(mhpmcounter11);
            //"mhpmcounter12": return csr_name_t'(mhpmcounter12);
            //"mhpmcounter13": return csr_name_t'(mhpmcounter13);
            //"mhpmcounter14": return csr_name_t'(mhpmcounter14);
            //"mhpmcounter15": return csr_name_t'(mhpmcounter15);
            //"mhpmcounter16": return csr_name_t'(mhpmcounter16);
            //"mhpmcounter17": return csr_name_t'(mhpmcounter17);
            //"mhpmcounter18": return csr_name_t'(mhpmcounter18);
            //"mhpmcounter19": return csr_name_t'(mhpmcounter19);
            //"mhpmcounter20": return csr_name_t'(mhpmcounter20);
            //"mhpmcounter21": return csr_name_t'(mhpmcounter21);
            //"mhpmcounter22": return csr_name_t'(mhpmcounter22);
            //"mhpmcounter23": return csr_name_t'(mhpmcounter23);
            //"mhpmcounter24": return csr_name_t'(mhpmcounter24);
            //"mhpmcounter25": return csr_name_t'(mhpmcounter25);
            //"mhpmcounter26": return csr_name_t'(mhpmcounter26);
            //"mhpmcounter27": return csr_name_t'(mhpmcounter27);
            //"mhpmcounter28": return csr_name_t'(mhpmcounter28);
            //"mhpmcounter29": return csr_name_t'(mhpmcounter29);
            //"mhpmcounter30": return csr_name_t'(mhpmcounter30);
            //"mhpmcounter31": return csr_name_t'(mhpmcounter31);
            "mhpmcounterh3" : return csr_name_t'(mhpmcounterh3);
            //"mhpmcounterh4" : return csr_name_t'(mhpmcounterh4);
            //"mhpmcounterh5" : return csr_name_t'(mhpmcounterh5);
            //"mhpmcounterh6" : return csr_name_t'(mhpmcounterh6);
            //"mhpmcounterh7" : return csr_name_t'(mhpmcounterh7);
            //"mhpmcounterh8" : return csr_name_t'(mhpmcounterh8);
            //"mhpmcounterh9" : return csr_name_t'(mhpmcounterh9);
            //"mhpmcounterh10": return csr_name_t'(mhpmcounterh10);
            //"mhpmcounterh11": return csr_name_t'(mhpmcounterh11);
            //"mhpmcounterh12": return csr_name_t'(mhpmcounterh12);
            //"mhpmcounterh13": return csr_name_t'(mhpmcounterh13);
            //"mhpmcounterh14": return csr_name_t'(mhpmcounterh14);
            //"mhpmcounterh15": return csr_name_t'(mhpmcounterh15);
            //"mhpmcounterh16": return csr_name_t'(mhpmcounterh16);
            //"mhpmcounterh17": return csr_name_t'(mhpmcounterh17);
            //"mhpmcounterh18": return csr_name_t'(mhpmcounterh18);
            //"mhpmcounterh19": return csr_name_t'(mhpmcounterh19);
            //"mhpmcounterh20": return csr_name_t'(mhpmcounterh20);
            //"mhpmcounterh21": return csr_name_t'(mhpmcounterh21);
            //"mhpmcounterh22": return csr_name_t'(mhpmcounterh22);
            //"mhpmcounterh23": return csr_name_t'(mhpmcounterh23);
            //"mhpmcounterh24": return csr_name_t'(mhpmcounterh24);
            //"mhpmcounterh25": return csr_name_t'(mhpmcounterh25);
            //"mhpmcounterh26": return csr_name_t'(mhpmcounterh26);
            //"mhpmcounterh27": return csr_name_t'(mhpmcounterh27);
            //"mhpmcounterh28": return csr_name_t'(mhpmcounterh28);
            //"mhpmcounterh29": return csr_name_t'(mhpmcounterh29);
            //"mhpmcounterh30": return csr_name_t'(mhpmcounterh30);
            //"mhpmcounterh31": return csr_name_t'(mhpmcounterh31);
            "dcsr", "dpc"   : begin
                `uvm_info("RV32ISA Coverage", $sformatf("get_csr_name(): CSR [%0s] not yet in functional coverage model.", s), UVM_DEBUG)
            end
            "marchid"      : return csr_name_t'(marchid);
            "mimpid"       : return csr_name_t'(mimpid);
            // These CSRs are not supported by CV32E40P
            //"mcounteren"   : return csr_name_t'(mcounteren);
            //"mideleg"      : return csr_name_t'(mideleg);
            //"medeleg"      : return csr_name_t'(medeleg);
            //"pmpaddr0"     : return csr_name_t'(pmpaddr0);
            //"pmpaddr1"     : return csr_name_t'(pmpaddr1);
            //"pmpaddr10"    : return csr_name_t'(pmpaddr10);
            //"pmpaddr11"    : return csr_name_t'(pmpaddr11);
            //"pmpaddr12"    : return csr_name_t'(pmpaddr12);
            //"pmpaddr13"    : return csr_name_t'(pmpaddr13);
            //"pmpaddr14"    : return csr_name_t'(pmpaddr14);
            //"pmpaddr15"    : return csr_name_t'(pmpaddr15);
            //"pmpaddr2"     : return csr_name_t'(pmpaddr2);
            //"pmpaddr3"     : return csr_name_t'(pmpaddr3);
            //"pmpaddr4"     : return csr_name_t'(pmpaddr4);
            //"pmpaddr5"     : return csr_name_t'(pmpaddr5);
            //"pmpaddr6"     : return csr_name_t'(pmpaddr6);
            //"pmpaddr7"     : return csr_name_t'(pmpaddr7);
            //"pmpaddr8"     : return csr_name_t'(pmpaddr8);
            //"pmpaddr9"     : return csr_name_t'(pmpaddr9);
            //"pmpcfg0"      : return csr_name_t'(pmpcfg0);
            //"pmpcfg1"      : return csr_name_t'(pmpcfg1);
            //"pmpcfg2"      : return csr_name_t'(pmpcfg2);
            //"pmpcfg3"      : return csr_name_t'(pmpcfg3);
            default: begin
                `uvm_warning("RV32ISA Coverage", $sformatf("get_csr_name(): CSR [%0s] not recognized!", s))
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
        `uvm_info("RV32ISA Coverage", $sformatf("get_imm: Convert %s (%s) to 0x%0x (%0d)", s, asm, val, val), UVM_DEBUG)

        return val;
    endfunction

    function int get_pc_imm(string s, bit[31:0] pc, string asm);
        // From the Imperas ISS the string should be a 32-bit unsigend PC
        get_pc_imm = s.atohex() - pc;
        `uvm_info("RV32ISA Coverage", $sformatf("get_pc_imm: Convert %s (%s) pc: 0x%08x to %0d", s, asm, pc, get_pc_imm), UVM_DEBUG)
    endfunction

    function logic c_check_imm(string s, asm);
        int val;

        val = get_imm(s, asm);

        if ((val > -127)&&(val < 127)) begin
            return 1;
        end else begin
            `uvm_info("RV32ISA Coverage", $sformatf("c_check_imm(): ins [%0s] not within 16-bit range", s), UVM_HIGH)
            return 0;
        end

    endfunction

///////////////////////////////////////////////////////////////////////////////
// Coverage of Base Integer Instruction Set, Version 2.1
///////////////////////////////////////////////////////////////////////////////
// WAIVED : missing check of overflow/underflow

    covergroup add_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "add") {
            bins gprval[] = {[zero:t6]};
        }
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "add") {
            bins gprval[] = {[zero:t6]};
        }
        cp_rs2    : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "add") {
            bins gprval[] = {[zero:t6]};
        }
    endgroup

    covergroup addi_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "addi") {
            bins gprval[] = {[zero:t6]};
        }
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "addi") {
            bins gprval[] = {[zero:t6]};
        }
        cp_imm11   : coverpoint get_imm(ins.ops[2].val,"addi" ) {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup and_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "and") {
            bins gprval[] = {[zero:t6]};
        }
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "and") {
            bins gprval[] = {[zero:t6]};
        }
        cp_rs2    : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "and") {
            bins gprval[] = {[zero:t6]};
        }
    endgroup

    covergroup andi_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "andi") {
            bins gprval[] = {[zero:t6]};
        }
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "andi") {
            bins gprval[] = {[zero:t6]};
        }
        cp_imm11   : coverpoint get_imm(ins.ops[2].val,"andi" ) {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup auipc_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "auipc") {
            bins gprval[] = {[zero:t6]};
        }
        cp_uimm20   : coverpoint get_imm(ins.ops[1].val,"auipc" ) {
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup beq_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rs1    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "beq") {
            bins gprval[] = {[zero:t6]};
        }
        cp_rs2    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "beq") {
            bins gprval[] = {[zero:t6]};
        }
        cp_offset : coverpoint get_pc_imm(ins.ops[2].val, ins.pc, "beq" ) {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup bge_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rs1    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "bge") {
            bins gprval[] = {[zero:t6]};
        }
        cp_rs2    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "bge") {
            bins gprval[] = {[zero:t6]};
        }
        cp_offset : coverpoint get_pc_imm(ins.ops[2].val, ins.pc, "bge" ) {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup bgeu_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rs1    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "bgeu") {
            bins gprval[] = {[zero:t6]};
        }
        cp_rs2    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "bgeu") {
            bins gprval[] = {[zero:t6]};
        }
        cp_offset : coverpoint get_pc_imm(ins.ops[2].val, ins.pc, "bgeu" ) {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup blt_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rs1    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "blt") {
            bins gprval[] = {[zero:t6]};
        }
        cp_rs2    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "blt") {
            bins gprval[] = {[zero:t6]};
        }
        cp_offset : coverpoint get_pc_imm(ins.ops[2].val, ins.pc, "blt" ) {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup bltu_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rs1    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "bltu") {
            bins gprval[] = {[zero:t6]};
        }
        cp_rs2    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "bltu") {
            bins gprval[] = {[zero:t6]};
        }
        cp_offset : coverpoint get_pc_imm(ins.ops[2].val, ins.pc, "bltu" ) {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup bne_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rs1    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "bne") {
            bins gprval[] = {[zero:t6]};
        }
        cp_rs2    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "bne") {
            bins gprval[] = {[zero:t6]};
        }
        cp_offset : coverpoint get_pc_imm(ins.ops[2].val, ins.pc, "bne" ) {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup ebreak_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_asm   : coverpoint (ins.asm) {
            bins ebreak_bin = {EBREAK};
        }
    endgroup

    covergroup ecall_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_asm   : coverpoint (ins.asm) {
            bins ecall_bin = {ECALL};
        }
    endgroup

    covergroup fence_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_asm   : coverpoint (ins.asm) {
            bins fence_bin = {FENCE};
        }
    endgroup

    covergroup fence_i_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_asm   : coverpoint (ins.asm) {
            bins fence_bin = {FENCE_I};
        }
    endgroup

    covergroup wfi_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_asm   : coverpoint (ins.asm) {
            bins fence_bin = {WFI};
        }
    endgroup

    covergroup mret_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_asm   : coverpoint (ins.asm) {
            bins mret_bin = {MRET};
        }
    endgroup

    covergroup dret_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_asm   : coverpoint (ins.asm) {
            bins dret_bin = {DRET};
        }
    endgroup

    covergroup jal_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "jal") {
            bins zero     = {zero};
            bins gprval[] = {[ra:t6]};
        }
        cp_jmp19   : coverpoint get_pc_imm(ins.ops[1].val, ins.pc,"jal") {
            bins neg  = {[$:-1]};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup jalr_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "jalr") {
            bins gprval[] = {[zero:t6]};
        }
        cp_rs1   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "jalr") {
            bins gprval[] = {[zero:t6]};
        }
        cp_offset: coverpoint get_imm(ins.ops[1].val, "jalr") {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup lb_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "lb") {
            bins gprval[] = {[zero:t6]};
        }
        cp_imm11 : coverpoint get_imm(ins.ops[1].val, "lb") {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
        cp_rs1     : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "lb") {
            bins gprval[] = {[zero:t6]};
        }
    endgroup

    covergroup lbu_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "lbu") {
            bins gprval[] = {[zero:t6]};
        }
        cp_imm11    : coverpoint get_imm(ins.ops[1].val, "lbu") {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
        cp_rs1     : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "lbu") {
            bins gprval[] = {[zero:t6]};
        }
    endgroup

    covergroup lh_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "lh") {
            bins gprval[] = {[zero:t6]};
        }
        cp_imm11    : coverpoint get_imm(ins.ops[1].val, "lh") {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
        cp_rs1     : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "lh") {
            bins gprval[] = {[zero:t6]};
        }
    endgroup

    covergroup lhu_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "lhu") {
            bins gprval[] = {[zero:t6]};
        }
        cp_imm11    : coverpoint get_imm(ins.ops[1].val, "lhu") {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
        cp_rs1     : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "lhu") {
            bins gprval[] = {[zero:t6]};
        }
    endgroup

    covergroup lui_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "lui") {
          bins gprval[] = {[zero:t6]};
        }
        cp_uimm20   : coverpoint get_imm(ins.ops[1].val,"lui" ) {
          bins zero = {0};
          bins pos[16] = {[1:1048575]};
        }
    endgroup

    covergroup lw_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "lw") {
            bins gprval[] = {[zero:t6]};
        }
        cp_imm11 : coverpoint get_imm(ins.ops[1].val, "lw") {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
        cp_rs1     : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "lw") {
            bins gprval[] = {[zero:t6]};
        }
    endgroup

    covergroup or_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "or") {
            bins gprval[] = {[zero:t6]};
        }
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "or") {
            bins gprval[] = {[zero:t6]};
        }
        cp_rs2    : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "or") {
            bins gprval[] = {[zero:t6]};
        }
    endgroup

    covergroup ori_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "ori") {
            bins gprval[] = {[zero:t6]};
        }
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "ori") {
            bins gprval[] = {[zero:t6]};
        }
        cp_imm11   : coverpoint get_imm(ins.ops[2].val,"ori" ) {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup sb_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rs2    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "sb") {
            bins gprval[] = {[zero:t6]};
        }
        cp_imm11  : coverpoint get_imm(ins.ops[1].val, "sb") {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
        cp_rs1     : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "sb") {
            bins gprval[] = {[zero:t6]};
        }
    endgroup

    covergroup sh_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rs2    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "sh") {
            bins gprval[] = {[zero:t6]};
        }
        cp_imm11  : coverpoint get_imm(ins.ops[1].val, "sh") {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
        cp_rs1     : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "sh") {
            bins gprval[] = {[zero:t6]};
        }
    endgroup

    covergroup sll_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "sll") {
            bins gprval[] = {[zero:t6]};
        }
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "sll") {
            bins gprval[] = {[zero:t6]};
        }
        cp_rs2    : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "sll") {
            bins gprval[] = {[zero:t6]};
        }
    endgroup

    covergroup slli_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "slli") {
            bins gprval[] = {[zero:t6]};
        }
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "slli") {
            bins gprval[] = {[zero:t6]};
        }
        cp_shamt5   : coverpoint get_imm(ins.ops[2].val,"slli" ) {
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup slt_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "slt") {
            bins gprval[] = {[zero:t6]};
        }
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "slt") {
            bins gprval[] = {[zero:t6]};
        }
        cp_rs2    : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "slt") {
            bins gprval[] = {[zero:t6]};
        }
    endgroup

    covergroup slti_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "slti") {
            bins gprval[] = {[zero:t6]};
        }
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "slti") {
            bins gprval[] = {[zero:t6]};
        }
        cp_imm11   : coverpoint get_imm(ins.ops[2].val,"slti" ) {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup sltiu_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "sltiu") {
            bins gprval[] = {[zero:t6]};
        }
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "sltiu") {
            bins gprval[] = {[zero:t6]};
        }
        cp_imm11   : coverpoint get_imm(ins.ops[2].val,"sltiu" ) {
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup sltu_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "sltu") {
            bins gprval[] = {[zero:t6]};
        }
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "sltu") {
            bins gprval[] = {[zero:t6]};
        }
        cp_rs2    : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "sltu") {
            bins gprval[] = {[zero:t6]};
        }
    endgroup

    // WAIVED : coverage of maximum positive and negative immediate values
    covergroup sra_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "sra") {
            bins gprval[] = {[zero:t6]};
        }
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "sra") {
            bins gprval[] = {[zero:t6]};
        }
        cp_rs2    : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "sra") {
            bins gprval[] = {[zero:t6]};
        }
    endgroup

    covergroup srai_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "srai") {
            bins gprval[] = {[zero:t6]};
        }
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "srai") {
            bins gprval[] = {[zero:t6]};
        }
        cp_shamt5   : coverpoint get_imm(ins.ops[2].val,"srai" ){
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup srl_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "srl") {
            bins gprval[] = {[zero:t6]};
        }
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "srl") {
            bins gprval[] = {[zero:t6]};
        }
        cp_rs2    : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "srl") {
            bins gprval[] = {[zero:t6]};
        }
    endgroup

    covergroup srli_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "srli") {
            bins gprval[] = {[zero:t6]};
        }
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "srli") {
            bins gprval[] = {[zero:t6]};
        }
        cp_shamt5   : coverpoint get_imm(ins.ops[2].val,"srli" ) {
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup sub_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "sub") {
            bins gprval[] = {[zero:t6]};
        }
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "sub") {
            bins gprval[] = {[zero:t6]};
        }
        cp_rs2    : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "sub") {
            bins gprval[] = {[zero:t6]};
        }
    endgroup

    covergroup sw_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rs2    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "sw") {
            bins gprval[] = {[zero:t6]};
        }
        cp_imm11  : coverpoint get_imm(ins.ops[1].val, "sw") {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
        cp_rs1     : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "sw") {
            bins gprval[] = {[zero:t6]};
        }
    endgroup

    // WAIVED: specific case where one of the sources is -1 (bitwise not)
    //         current version of this env does not support this coverage.
    covergroup xor_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "xor") {
            bins gprval[] = {[zero:t6]};
        }
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "xor") {
            bins gprval[] = {[zero:t6]};
        }
        cp_rs2    : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "xor") {
            bins gprval[] = {[zero:t6]};
        }
    endgroup

    covergroup xori_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "xori") {
            bins gprval[] = {[zero:t6]};
        }
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "xori") {
            bins gprval[] = {[zero:t6]};
        }
        cp_imm11   : coverpoint get_imm(ins.ops[2].val,"xori" ) {
            bins neg  = {[$:-1]};
            bins bwn  = {-1}; // bitwise not
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

///////////////////////////////////////////////////////////////////////////////
//Coverage of Std Extension for Integer Multiplication & Division, Version 2.0
///////////////////////////////////////////////////////////////////////////////
// Note : there is no coverage for sequence of MULH[[S]U] and MUL instructions
//        because the CV32E40P does not implement fused instructions.

    covergroup mul_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "mul") {
          bins gprval[] = {[zero:t6]};
        }
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "mul") {
          bins gprval[] = {[zero:t6]};
        }
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "mul") {
          bins gprval[] = {[zero:t6]};
        }
    endgroup

    covergroup mulh_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "mulh") {
          bins gprval[] = {[zero:t6]};
        }
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "mulh") {
          bins gprval[] = {[zero:t6]};
        }
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "mulh") {
          bins gprval[] = {[zero:t6]};
        }
    endgroup

    covergroup mulhu_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "mulhu") {
          bins gprval[] = {[zero:t6]};
        }
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "mulhu") {
          bins gprval[] = {[zero:t6]};
        }
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "mulhu") {
          bins gprval[] = {[zero:t6]};
        }
    endgroup

    covergroup mulhsu_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "mulhsu") {
          bins gprval[] = {[zero:t6]};
        }
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "mulhsu") {
          bins gprval[] = {[zero:t6]};
        }
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "mulhsu" ) {
          bins gprval[] = {[zero:t6]};
        }
    endgroup


    // WAIVED : missing check of overflow/underflow
    // WAIVED : missing check of divide-by-zero
    covergroup div_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "div") {
          bins gprval[] = {[zero:t6]};
        }
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "div") {
          bins gprval[] = {[zero:t6]};
        }
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "div") {
          bins gprval[] = {[zero:t6]};
        }
    endgroup

    // WAIVED : missing check of overflow/underflow
    // WAIVED : missing check of divide-by-zero
    covergroup rem_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "rem") {
          bins gprval[] = {[zero:t6]};
        }
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "rem") {
          bins gprval[] = {[zero:t6]};
        }
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "rem") {
          bins gprval[] = {[zero:t6]};
        }
    endgroup

    // WAIVED : missing check of overflow/underflow
    // WAIVED : missing check of divide-by-zero
    covergroup divu_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "divu") {
          bins gprval[] = {[zero:t6]};
        }
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "divu") {
          bins gprval[] = {[zero:t6]};
        }
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "divu") {
          bins gprval[] = {[zero:t6]};
        }
    endgroup

    // WAIVED : missing check of overflow/underflow
    // WAIVED : missing check of divide-by-zero
    covergroup remu_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "remu") {
          bins gprval[] = {[zero:t6]};
        }
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "remu") {
          bins gprval[] = {[zero:t6]};
        }
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "remu") {
          bins gprval[] = {[zero:t6]};
        }
    endgroup

///////////////////////////////////////////////////////////////////////////////
//Coverage of CSR access instructions
///////////////////////////////////////////////////////////////////////////////

    covergroup csrrci_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "csrrci") {
          bins gprval[] = {[zero:t6]};
        }
        cp_csr   : coverpoint get_csr_name(ins.ops[1].val, ins.ops[1].key, "csrrci") {
          // RM does not emit coverage transactions for illegal instructions and
          // CV32E40P treats csrrci rd, ro_csrs, zimm as an illegal instruction
          ignore_bins ro_csrs = {mhartid, mimpid, mvendorid};
        }
        cp_zimm  : coverpoint get_imm(ins.ops[2].val, "csrrci") {
          bins low  = {[5'b00000:5'b10000]};
          bins high = {[5'b10001:5'b11111]};
        }
    endgroup

    covergroup csrrc_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "csrrc") {
          bins gprval[] = {[zero:t6]};
        }
        cp_csr   : coverpoint get_csr_name(ins.ops[1].val, ins.ops[1].key, "csrrc");
        cp_rs1   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "csrrc") {
          bins gprval[] = {[zero:t6]};
        }
    endgroup

    covergroup csrrs_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "csrrs") {
          bins gprval[] = {[zero:t6]};
        }
        cp_csr   : coverpoint get_csr_name(ins.ops[1].val, ins.ops[1].key, "csrrs");
        cp_rs1   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "csrrs") {
          bins gprval[] = {[zero:t6]};
        }
    endgroup

    covergroup csrrsi_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "csrrsi") {
          bins gprval[] = {[zero:t6]};
        }
        cp_csr   : coverpoint get_csr_name(ins.ops[1].val, ins.ops[1].key, "csrrsi") {
          // RM does not emit coverage transactions for illegal instructions and
          // CV32E40P treats csrrsi rd, ro_csrs, zimm as an illegal instruction
          ignore_bins ro_csrs = {mhartid, mimpid, mvendorid};
        }
        cp_zimm  : coverpoint get_imm(ins.ops[2].val, "csrrsi") {
          bins low  = {[5'b00000:5'b10000]};
          bins high = {[5'b10001:5'b11111]};
        }
    endgroup

    covergroup csrrw_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "csrrw") {
          bins gprval[] = {[zero:t6]};
        }
        cp_csr   : coverpoint get_csr_name(ins.ops[1].val, ins.ops[1].key, "csrrw") {
          // RM does not emit coverage transactions for illegal instructions and
          // CV32E40P treats csrrw rd, ro_csrs, zimm as an illegal instruction
          ignore_bins ro_csrs = {mhartid, mimpid, mvendorid};
        }
        cp_rs1   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "csrrw") {
          bins gprval[] = {[zero:t6]};
        }
    endgroup

    covergroup csrrwi_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "csrrwi") {
          bins gprval[] = {[zero:t6]};
        }
        cp_csr   : coverpoint get_csr_name(ins.ops[1].val, ins.ops[1].key, "csrrwi") {
          // RM does not emit coverage transactions for illegal instructions and
          // CV32E40P treats csrrwi rd, ro_csrs, zimm as an illegal instruction
          ignore_bins ro_csrs = {mhartid, mimpid, mvendorid};
        }
        cp_zimm  : coverpoint get_imm(ins.ops[2].val, "csrrwi") {
          bins low  = {[5'b00000:5'b10000]};
          bins high = {[5'b10001:5'b11111]};
        }
    endgroup

///////////////////////////////////////////////////////////////////////////////
//Coverage of Std Extension for Compressed Instructions, Version 2.0
///////////////////////////////////////////////////////////////////////////////

// WAIVED : missing check that 32I & 32C instuctions aligned on 16/32-bit boundaries.
// WAIVED : missing coverage of all combinations of source and destination operands.

    covergroup c_lwsp_cg     with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.lwsp") {
            bins gprval[] = {[ra:t6]};
        }
        cp_imm6   : coverpoint get_imm(ins.ops[1].val, "c.lwsp") {
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup c_swsp_cg    with function sample(ins_t ins);
        `per_instance_fcov
        cp_rs2   : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.swsp") {
            bins gprval[] = {[ra:t6]};
        }
        cp_imm6  : coverpoint get_imm(ins.ops[1].val, "c.swsp") {
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup c_lw_cg       with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.lw") {
            bins gprval[] = {[s0:a5]};
        }
        cp_imm5   : coverpoint get_imm(ins.ops[1].val, "c.lw") {
            bins zero = {0};
            bins pos  = {[1:$]};
        }
        cp_rs1     : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "c.lw") {
            bins gprval[] = {[s0:a5]};
        }
    endgroup

    covergroup c_sw_cg       with function sample(ins_t ins);
        `per_instance_fcov
        cp_rs1     : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.sw") {
            bins gprval[] = {[s0:a5]};
        }
        cp_imm5   : coverpoint get_imm(ins.ops[1].val, "c.sw") {
            bins zero = {0};
            bins pos  = {[1:$]};
        }
        cp_rs2     : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "c.sw") {
            bins gprval[] = {[s0:a5]};
        }
    endgroup

    covergroup c_j_cg      with function sample(ins_t ins);
        `per_instance_fcov
        cp_jmp11   : coverpoint get_pc_imm(ins.ops[0].val, ins.pc, "c.j" ) {
            bins neg  = {[$:-1]};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup c_jal_cg      with function sample(ins_t ins);
        `per_instance_fcov
        // Note even though by ISA the instruction is c.jal imm, the ISS places ra into operand0
        // in the decode, putting the offset into operand1q
        cp_jmp11   : coverpoint get_pc_imm(ins.ops[1].val, ins.pc, "c.jal" ) {
            bins neg  = {[$:-1]};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup c_jr_cg      with function sample(ins_t ins);
        `per_instance_fcov
        cp_rs1    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c,jr") {
            bins gprval[] = {[ra:t6]};
        }
    endgroup

    covergroup c_jalr_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rs1    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c,jalr") {
            bins gprval[] = {[ra:t6]};
        }
    endgroup

    covergroup c_beqz_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rs1    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.beqz") {
            bins gprval[] = {[s0:a5]};
        }
        cp_offset : coverpoint get_pc_imm(ins.ops[1].val, ins.pc, "c.beqz" ) {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup c_bnez_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rs1    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.bnez") {
            bins gprval[] = {[s0:a5]};
        }
        cp_offset : coverpoint get_pc_imm(ins.ops[1].val, ins.pc, "c.bnez" ) {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup c_li_cg       with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.li") {
            bins gprval[] = {zero, [ra:t6]};
        }
        cp_imm6   : coverpoint get_imm(ins.ops[1].val,"c.li" ) {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup c_lui_cg      with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.lui") {
            bins gprval[] = {zero,ra,[gp:t6]}; // invalid when rd = x2 (sp)
        }
        cp_imm6   : coverpoint get_imm(ins.ops[1].val,"c.lui" ) {
            // Represents sign-extended negative numbers for nzimm6
            bins neg  = {['hfffe0:'hfffff]};
            // invalid when imm = 0
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup c_addi_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.addi") {
            bins gprval[] = {zero,[s0:a5]}; // Add zero here to map c.nop
        }
        cp_imm6   : coverpoint get_imm(ins.ops[2].val,"c.addi" ) {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup c_addi16sp_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.addi16sp") {
            bins gprval[] = {sp};
        }
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.addi16sp") {
            bins gprval[] = {sp};
        }
        cp_imm6   : coverpoint get_imm(ins.ops[2].val,"c.addi16sp" ) {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup c_addi4spn_cg  with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.addi4spn") {
            bins gprval[] = {[s0:a5]};
        }
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.addi4spn") {
            bins gprval[] = {sp};
        }
        cp_nzuimm8   : coverpoint get_imm(ins.ops[2].val,"c.addi4spn" ) {
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup c_slli_cg     with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.slli") {
            bins gprval[] = {zero, [s0:a5]};
        }
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.slli") {
            bins gprval[] = {[s0:a5]};
        }
        cp_shamt5   : coverpoint get_imm(ins.ops[2].val, "c.slli" ) {
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup c_srli_cg     with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.srli") {
            bins gprval[] = {[s0:a5]};
        }
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.srli") {
            bins gprval[] = {[s0:a5]};
        }
        cp_shamt5   : coverpoint get_imm(ins.ops[2].val, "c.srli" ) {
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup c_srai_cg     with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.srai") {
            bins gprval[] = {[s0:a5]};
        }
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.srai") {
            bins gprval[] = {[s0:a5]};
        }
        cp_shamt5   : coverpoint get_imm(ins.ops[2].val, "c.srai" ) {
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup c_andi_cg     with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.andi") {
            bins gprval[] = {[s0:a5]};
        }
        cp_rs1   : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.andi") {
            bins gprval[] = {[s0:a5]};
        }
        cp_imm6   : coverpoint get_imm(ins.ops[2].val,"c.andi" ) {
            bins neg  = {[$:-1]};
            bins zero = {0};
            bins pos  = {[1:$]};
        }
    endgroup

    covergroup c_add_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd     : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.add") {
          bins gprval[] = {zero, [ra:t6]};
        }
        cp_rs1    : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "c.add") {
          bins gprval[] = {[ra:t6]};
        }
    endgroup

    covergroup c_mv_cg with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd     : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.mv") {
          bins gprval[] = {zero, [ra:t6]};
        }
        cp_rs1    : coverpoint get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.mv") {
          bins gprval[] = {[ra:t6]};
        }
    endgroup

    covergroup c_and_cg      with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.and") {
            bins gprval[] = {[s0:a5]};
        }
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "c.and") {
            bins gprval[] = {[s0:a5]};
        }
    endgroup

    covergroup c_or_cg       with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.or") {
            bins gprval[] = {[s0:a5]};
        }
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "c.or") {
            bins gprval[] = {[s0:a5]};
        }
    endgroup

    covergroup c_xor_cg      with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.xor") {
            bins gprval[] = {[s0:a5]};
        }
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "c.xor") {
            bins gprval[] = {[s0:a5]};
        }
    endgroup

    covergroup c_sub_cg      with function sample(ins_t ins);
        `per_instance_fcov
        cp_rd    : coverpoint get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.sub") {
            bins gprval[] = {[s0:a5]};
        }
        cp_rs2   : coverpoint get_gpr_name(ins.ops[2].val, ins.ops[2].key, "c.sub") {
            bins gprval[] = {[s0:a5]};
        }
    endgroup

    covergroup c_ebreak_cg   with function sample(ins_t ins);
        `per_instance_fcov
        cp_asm   : coverpoint (ins.asm) {
            bins c_ebreak_bin = {C_EBREAK};
        }
    endgroup

///////////////////////////////////////////////////////////////////////////////
// Coverage for every instruction has been followed by every other instruction
///////////////////////////////////////////////////////////////////////////////

`ifdef DSIM
   // dsim handling of per_instance coverage
   covergroup instr_cg with function sample(ins_t ins);
      cp_ins : coverpoint (ins.asm) {
         type_option.weight = 0;
      }
      cp_ins_prev : coverpoint (ins_prev.asm) {
         type_option.weight = 0;
      }
      cr_ins_prev_x_ins: cross cp_ins_prev, cp_ins {
         type_option.weight = 1;
         type_option.comment = "Cross previous with current instruction";
      }
   endgroup // instr_cg
`else
   covergroup instr_cg with function sample(ins_t ins);
      `per_instance_fcov
      cp_ins : coverpoint (ins.asm) {
         option.weight = 0;
      }
      cp_ins_prev : coverpoint (ins_prev.asm) {
         option.weight = 0;
      }
      cr_ins_prev_x_ins: cross cp_ins_prev, cp_ins {
         option.weight = 1;
         option.comment = "Cross previous with current instruction";
      }
   endgroup // instr_cg
`endif // DSIM

    `uvm_component_utils(uvme_rv32isa_covg)

    function new(string name="rv32isa_covg", uvm_component parent=null);
        super.new(name, parent);
        add_cg        = new();
        addi_cg       = new();
        and_cg        = new();
        andi_cg       = new();
        auipc_cg      = new();
        beq_cg        = new();
        bge_cg        = new();
        bgeu_cg       = new();
        blt_cg        = new();
        bltu_cg       = new();
        bne_cg        = new();
        ebreak_cg     = new();
        ecall_cg      = new();
        fence_cg      = new();
        fence_i_cg    = new();
        jal_cg        = new();
        jalr_cg       = new();
        lb_cg         = new();
        lbu_cg        = new();
        lh_cg         = new();
        lhu_cg        = new();
        lui_cg        = new();
        lw_cg         = new();
        or_cg         = new();
        ori_cg        = new();
        sb_cg         = new();
        sh_cg         = new();
        sll_cg        = new();
        slli_cg       = new();
        slt_cg        = new();
        slti_cg       = new();
        sltiu_cg      = new();
        sltu_cg       = new();
        sra_cg        = new();
        srai_cg       = new();
        srl_cg        = new();
        srli_cg       = new();
        sub_cg        = new();
        sw_cg         = new();
        xor_cg        = new();
        xori_cg       = new();
        mul_cg        = new();
        mulh_cg       = new();
        mulhu_cg      = new();
        mulhsu_cg     = new();
        div_cg        = new();
        rem_cg        = new();
        divu_cg       = new();
        remu_cg       = new();
        mret_cg       = new();
        dret_cg       = new();
        wfi_cg        = new();

        csrrc_cg      = new();
        csrrci_cg     = new();
        csrrs_cg      = new();
        csrrsi_cg     = new();
        csrrw_cg      = new();
        csrrwi_cg     = new();

        c_lwsp_cg     = new();
        c_swsp_cg     = new();
        c_lw_cg       = new();
        c_sw_cg       = new();
        c_j_cg        = new();
        c_jal_cg      = new();
        c_jr_cg       = new();
        c_jalr_cg     = new();
        c_li_cg       = new();
        c_lui_cg      = new();
        c_addi_cg     = new();
        c_addi16sp_cg = new();
        c_addi4spn_cg = new();
        c_slli_cg     = new();
        c_srli_cg     = new();
        c_srai_cg     = new();
        c_andi_cg     = new();
        c_add_cg      = new();
        c_mv_cg       = new();
        c_and_cg      = new();
        c_or_cg       = new();
        c_xor_cg      = new();
        c_sub_cg      = new();
        c_ebreak_cg   = new();
        c_beqz_cg     = new();
        c_bnez_cg     = new();

        instr_cg      = new();

        ap = new("ap", this);
    endfunction: new

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        void'(uvm_config_db#(uvme_cv32e40p_cntxt_c)::get(this, "", "cntxt", cntxt));
        if (cntxt == null) begin
            `uvm_fatal("RV32ISACOVG", "No cntxt object passed to model");
        end
    endfunction

    task run_phase(uvm_phase phase);
        super.run_phase(phase);

        `uvm_info("rv32isa_covg", "The RV32ISA coverage model is running", UVM_LOW);

        while (1) begin
            @(cntxt.isa_covg_vif.ins_valid);
            sample(cntxt.isa_covg_vif.ins);
        end
    endtask

    function void check_compressed(inout ins_t ins);
        case (ins.ins_str)
            "lw"    : begin
                `uvm_info("rv32isa_covg", $sformatf("EXPECTING LW: %0s ins.ops[0].val = %0s, ins.ops[1].val = %0s, ins.ops[2].val = %0s", ins.asm.name, ins.ops[0].val, ins.ops[1].val, ins.ops[2].val), UVM_HIGH)
                if ( c_check_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.lw")  && c_check_gpr_name(ins.ops[2].val, ins.ops[2].key, "c.lw")
                     && c_check_imm(ins.ops[1].val, "c.lw")) begin
                    ins.asm=C_LW;
                    c_lw_cg.sample(ins);
                end
                else if ( (get_gpr_name(ins.ops[2].val, ins.ops[2].key, "c.lwsp") == gpr_name_t'(sp))) begin
                    ins.asm=C_LWSP;
                    c_lwsp_cg.sample(ins);
                end
             end
            "sw"    : begin
                if ( c_check_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.sw")  && c_check_gpr_name(ins.ops[2].val, ins.ops[2].key, "c.sw")
                     && c_check_imm(ins.ops[1].val, "c.sw")) begin
                      ins.asm=C_SW;
                      c_sw_cg.sample(ins);
                end
                else if ( (get_gpr_name(ins.ops[2].val, ins.ops[2].key, "c.swsp") == gpr_name_t'(sp))) begin
                    ins.asm=C_SWSP;
                    c_swsp_cg.sample(ins);
                end
             end
            "lui"     : begin ins.asm=C_LUI; c_lui_cg.sample(ins); end
            "addi"    : begin
                `uvm_info("rv32isa_covg", $sformatf("EXPECTING ADDI: ins.ops[0].val = %0s, ins.ops[1].val = %0s", ins.ops[0].val, ins.ops[1].val), UVM_HIGH)
                if ( (get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.addi16sp") == get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.addi16sp")) &&
                          (get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.addi16sp") == gpr_name_t'(sp))) begin
                    ins.asm=C_ADDI16SP;
                    c_addi16sp_cg.sample(ins);
                end
                else if ( (c_check_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.addi4spn")) &&
                          (get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.addi4spn") == gpr_name_t'(sp)) ) begin
                    ins.asm=C_ADDI4SPN;
                    c_addi4spn_cg.sample(ins);
                     end
                else if ( get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.addi") == get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.addi")) begin
                    ins.asm=C_ADDI;
                    c_addi_cg.sample(ins);
                end
            end
            "nop"     : begin
                // Map to C_ADDI x0,0
                ins.asm=C_ADDI;
                ins.ops[0].val = "zero";
                ins.ops[2].val = "0";
                c_addi_cg.sample(ins);
            end
            "slli"    : begin
                if ( get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.slli") == get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.slli")) begin
                    ins.asm=C_SLLI;
                    c_slli_cg.sample(ins);
                end
            end
            "srli"    : begin
                if ( get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.srli") == get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.srli")) begin
                    ins.asm=C_SRLI;
                    c_srli_cg.sample(ins);
                end
            end
            "srai"    : begin
                if ( get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.srai") == get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.srai")) begin
                    ins.asm=C_SRAI;
                    c_srai_cg.sample(ins);
                    `uvm_info("RV32ISA Functional Coverage", $sformatf("c_srai_cg: ins.ops[0].val = %0s", ins.ops[0].val), UVM_HIGH)
                    `uvm_info("RV32ISA Functional Coverage", $sformatf("c_srai_cg: ins.ops[1].val = %0s", ins.ops[1].val), UVM_HIGH)
                    `uvm_info("RV32ISA Functional Coverage", $sformatf("c_srai_cg: ins.ops[2].val = %0s", ins.ops[2].val), UVM_HIGH)
                end
            end
            "andi"    : begin
                if ( get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.andi")  == get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.andi") ) begin
                    ins.asm=C_ANDI;
                    c_andi_cg.sample(ins);
                end
            end
            "add"      : begin
                if ( get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.add")  == get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.add") ) begin
                    ins.asm=C_ADD;
                    c_add_cg.sample(ins);
                end
            end
            "and"         : begin
                if ( get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.and")  == get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.and") ) begin
                    ins.asm=C_AND;
                    c_and_cg.sample(ins);
                end
            end
            "or"          : begin
                if ( get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.or")  == get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.or") ) begin
                    ins.asm=C_OR;
                    c_or_cg.sample(ins);
                end
            end
            "xor"         : begin
                if ( get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.xor")  == get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.xor") ) begin
                    ins.asm=C_XOR;
                    c_xor_cg.sample(ins);
                end
            end
            "sub"         : begin
                if ( get_gpr_name(ins.ops[0].val, ins.ops[0].key, "c.sub")  == get_gpr_name(ins.ops[1].val, ins.ops[1].key, "c.sub") ) begin
                    ins.asm=C_SUB;
                    c_sub_cg.sample(ins);
                end
            end
            "ebreak"      : begin ins.asm=C_EBREAK; c_ebreak_cg.sample(ins); end
            "j"           : begin ins.asm=C_J;      c_j_cg.sample(ins);      end
            "jr"          : begin ins.asm=C_JR;     c_jr_cg.sample(ins);     end
            "jal"         : begin ins.asm=C_JAL;    c_jal_cg.sample(ins);    end
            "jalr"        : begin ins.asm=C_JALR;   c_jalr_cg.sample(ins);   end
            "beqz"        : begin ins.asm=C_BEQZ;   c_beqz_cg.sample(ins);   end
            "bnez"        : begin ins.asm=C_BNEZ;   c_bnez_cg.sample(ins);   end
            "li"          : begin ins.asm=C_LI;     c_li_cg.sample(ins);     end
            "mv"          : begin ins.asm=C_MV;     c_mv_cg.sample(ins);     end

            // UVM warning on a fall-through
            default:    `uvm_warning("RV32ISA Coverage",
                                     $sformatf("check_compressed(): ins [%0s] not mapped to functional coverage",
                                               ins.ins_str))
        endcase
    endfunction: check_compressed

    function void sample(input ins_t ins);
        `uvm_info("RV32ISA", $sformatf("instruction from ISS: %s %s:%s %s:%s %s:%s %s:%s",
                                        ins.ins_str,
                                        ins.ops[0].key, ins.ops[0].val,
                                        ins.ops[1].key, ins.ops[1].val,
                                        ins.ops[2].key, ins.ops[2].val,
                                        ins.ops[3].key, ins.ops[3].val), UVM_DEBUG);
        if (ins.compressed) begin
            check_compressed(ins);
        end
        else begin
            case (ins.ins_str)
                "add"       : begin ins.asm=ADD;    add_cg.sample(ins);    end
                "addi"      : begin
                    ins.asm=ADDI;
                    addi_cg.sample(ins);
                end
                "and"       : begin ins.asm=AND;    and_cg.sample(ins);    end
                "andi"      : begin ins.asm=ANDI;   andi_cg.sample(ins);   end
                "auipc"     : begin ins.asm=AUIPC;  auipc_cg.sample(ins);  end
                "beq"       : begin
                  ins.asm=BEQ;
                  beq_cg.sample(ins);
                  `uvm_info("RV32ISA Functional Coverage", $sformatf("beq_cg: ins.ops[0].val = %0s, ins.ops[1].val = %0s, ins.ops[2].val = %0s, imm = %0h",
                                                                     ins.ops[0].val, ins.ops[1].val, ins.ops[2].val, get_imm(ins.ops[2].val,"beq")), UVM_DEBUG)
                end
                "bge"       : begin ins.asm=BGE;    bge_cg.sample(ins);    end
                "bgeu"      : begin ins.asm=BGEU;   bgeu_cg.sample(ins);   end
                "blt"       : begin ins.asm=BLT;    blt_cg.sample(ins);    end
                "bltu"      : begin ins.asm=BLTU;   bltu_cg.sample(ins);   end
                "bne"       : begin ins.asm=BNE;    bne_cg.sample(ins);    end
                "ebreak"    : begin ins.asm=EBREAK; ebreak_cg.sample(ins); end
                "ecall"     : begin ins.asm=ECALL;  ecall_cg.sample(ins);  end
                "fence"     : begin ins.asm=FENCE;  fence_cg.sample(ins);  end
                "fence.i"   : begin ins.asm=FENCE_I;fence_i_cg.sample(ins);  end
                "jal"       : begin ins.asm=JAL;    jal_cg.sample(ins);    end
                "jalr"      : begin
                    // Usually the Decoder from ISS presents all three operands such as R1:s6 C:785 R2:s6
                    // However it can present only 2 registers, this indicates a zero offset
                    if (ins.ops[1].key == "R2") begin
                        ins.ops[2] = ins.ops[1];
                        ins.ops[1].key = "C"; ins.ops[1].val = "0";
                    end
                    ins.asm = JALR;
                    jalr_cg.sample(ins);
                end
                "lb"        : begin ins.asm=LB;
                                    lb_cg.sample(ins);
                                    `uvm_info("RV32ISA Coverage", $sformatf("LOAD_BYTE: %s", ins_display(ins)), UVM_DEBUG)
                end
                "lbu"       : begin ins.asm=LBU;    lbu_cg.sample(ins);    end
                "lh"        : begin ins.asm=LH;     lh_cg.sample(ins);     end
                "lhu"       : begin ins.asm=LHU;    lhu_cg.sample(ins);    end
                "lui"       : begin ins.asm=LUI;    lui_cg.sample(ins);    end
                "lw"        : begin ins.asm=LW;     lw_cg.sample(ins);     end
                "or"        : begin ins.asm=OR;     or_cg.sample(ins);     end
                "ori"       : begin ins.asm=ORI;    ori_cg.sample(ins);    end
                "sb"        : begin ins.asm=SB;     sb_cg.sample(ins);     end
                "sh"        : begin ins.asm=SH;     sh_cg.sample(ins);     end
                "sll"       : begin ins.asm=SLL;    sll_cg.sample(ins);    end
                "slli"      : begin ins.asm=SLLI;   slli_cg.sample(ins);   end
                "slt"       : begin ins.asm=SLT;    slt_cg.sample(ins);    end
                "slti"      : begin ins.asm=SLTI;   slti_cg.sample(ins);   end
                "sltiu"     : begin ins.asm=SLTIU;  sltiu_cg.sample(ins);  end
                "sltu"      : begin ins.asm=SLTU;   sltu_cg.sample(ins);   end
                "sra"       : begin ins.asm=SRA;    sra_cg.sample(ins);    end
                "srai"      : begin ins.asm=SRAI;   srai_cg.sample(ins);   end
                "srl"       : begin ins.asm=SRL;    srl_cg.sample(ins);    end
                "srli"      : begin ins.asm=SRLI;   srli_cg.sample(ins);   end
                "sub"       : begin ins.asm=SUB;    sub_cg.sample(ins);    end
                "sw"        : begin ins.asm=SW;     sw_cg.sample(ins);     end
                "xor"       : begin ins.asm=XOR;    xor_cg.sample(ins);    end
                "xori"      : begin ins.asm=XORI;   xori_cg.sample(ins);   end
                "mul"       : begin ins.asm=MUL;    mul_cg.sample(ins);    end
                "mulh"      : begin ins.asm=MULH;   mulh_cg.sample(ins);   end
                "mulhu"     : begin ins.asm=MULHU;  mulhu_cg.sample(ins);  end
                "mulhsu"    : begin ins.asm=MULHSU; mulhsu_cg.sample(ins); end
                "div"       : begin ins.asm=DIV;    div_cg.sample(ins);    end
                "rem"       : begin ins.asm=REM;    rem_cg.sample(ins);    end
                "divu"      : begin ins.asm=DIVU;   divu_cg.sample(ins);   end
                "remu"      : begin ins.asm=REMU;   remu_cg.sample(ins);   end

                "csrrw"     : begin ins.asm=CSRRW;  csrrw_cg.sample(ins);  end
                "csrrs"     : begin ins.asm=CSRRS;  csrrs_cg.sample(ins);  end
                "csrrc"     : begin ins.asm=CSRRC;  csrrc_cg.sample(ins);  end
                "csrrwi"    : begin ins.asm=CSRRWI; csrrwi_cg.sample(ins); end
                "csrrci"    : begin
                  ins.asm=CSRRCI;
                  csrrci_cg.sample(ins);
                  `uvm_info("RV32ISA Functional Coverage", $sformatf("csrrci_cg: ins.ops[0].val = %0s, ins.ops[1].val = %0s, ins.ops[2].val = %0s, imm = %0h",
                                                                     ins.ops[0].val, ins.ops[1].val, ins.ops[2].val, get_imm(ins.ops[2].val,"beq")), UVM_DEBUG)
			    end
                "csrrsi"    : begin ins.asm=CSRRSI; csrrsi_cg.sample(ins); end

                "csrw"      : begin ins.asm=CSRRW;  ins.ops[2] = ins.ops[1]; ins.ops[1] = ins.ops[0]; ins.ops[0].val = "zero"; csrrw_cg.sample(ins); end
                "csrr"      : begin ins.asm=CSRRS;  ins.ops[2].val = "zero"; csrrs_cg.sample(ins); end
                "csrs"      : begin ins.asm=CSRRS;  ins.ops[2] = ins.ops[1]; ins.ops[1] = ins.ops[0]; ins.ops[0].val = "zero"; csrrs_cg.sample(ins);   end
                "csrc"      : begin ins.asm=CSRRC;  ins.ops[2] = ins.ops[1]; ins.ops[1] = ins.ops[0]; ins.ops[0].val = "zero"; csrrc_cg.sample(ins);   end

                "csrsi"     : begin ins.asm=CSRRSI; ins.ops[2] = ins.ops[1]; ins.ops[1] = ins.ops[0]; ins.ops[0].val = "zero"; csrrsi_cg.sample(ins); end
                "csrwi"     : begin ins.asm=CSRRWI; ins.ops[2] = ins.ops[1]; ins.ops[1] = ins.ops[0]; ins.ops[0].val = "zero"; csrrwi_cg.sample(ins); end
                "csrci"     : begin ins.asm=CSRRCI; ins.ops[2] = ins.ops[1]; ins.ops[1] = ins.ops[0]; ins.ops[0].val = "zero"; csrrci_cg.sample(ins); end

                "mret"      : begin ins.asm=MRET;   mret_cg.sample(ins);   end
                "dret"      : begin ins.asm=DRET;   dret_cg.sample(ins);   end
                "wfi"       : begin ins.asm=WFI;    wfi_cg.sample(ins);    end

                /*
                * Convert pseduo-ops from ISS to ISA instructions for sampling
                */
                "nop"     : begin
                    // Map to ADDI x0,x0,0
                    ins.asm=C_ADDI;
                    ins.ops[0].val = "zero";
                    ins.ops[1].val = "zero";
                    ins.ops[2].val = "0";
                    addi_cg.sample(ins);
                end

                // j: convert to jal x0,offset
                "j"         : begin ins.asm=JAL;    ins.ops[1] = ins.ops[0]; ins.ops[0].val = "zero"; jal_cg.sample(ins);    end
                // jr: convert to jalr x0,offset(rs) (Technically jr has zero offset but ISS can map a non-zero offset in its decode
                "jr"        : begin ins.asm=JALR;
                    if (ins.ops[0].key == "C") begin
                        ins.ops[2] = ins.ops[1];
                        ins.ops[1] = ins.ops[0];
                    end
                    else begin
                        ins.ops[2] = ins.ops[0];
                        ins.ops[1].key = "C"; ins.ops[1].val = "0";
                    end
                    // rd for "jr" is always x0
                    ins.ops[0].key = "R"; ins.ops[0].val = "zero";
                    `uvm_info("RV32ISA Functional Coverage", $sformatf("jalr_cg: %s:%s %s:%s %s:%s",
                        ins.ops[0].key, ins.ops[0].val,
                        ins.ops[1].key, ins.ops[1].val,
                        ins.ops[2].key, ins.ops[2].val),
                        UVM_DEBUG)

                    jalr_cg.sample(ins);
                end
                // beqz: convert to beq rs, x0, offset
                "beqz"      : begin ins.asm=BEQ;    ins.ops[2] = ins.ops[1]; ins.ops[1].val = "zero"; beq_cg.sample(ins);    end
                // mv: convert to addi rs, rs, 0
                "mv"        : begin ins.asm=ADDI;                                                     addi_cg.sample(ins);   end
                // sltz: convert to slt rd, rs, 0
                "sltz"      : begin ins.asm=SLT;    ins.ops[2].val = "zero";                          slt_cg.sample(ins);    end
                // sgtz: convert to slt rd, rs, 0
                "sgtz"      : begin ins.asm=SLT;    ins.ops[2] = ins.ops[1]; ins.ops[1].val = "zero"; slt_cg.sample(ins);    end
                // bltz: convert to blt rs, x0, offset
                "bltz"      : begin ins.asm=BLT;    ins.ops[2] = ins.ops[1]; ins.ops[1].val = "zero"; blt_cg.sample(ins);    end
                // blez: convert to bge r0, rs, offset
                "blez"      : begin ins.asm=BGE;    ins.ops[2] = ins.ops[1]; ins.ops[1] = ins.ops[0]; ins.ops[0].val = "zero"; bge_cg.sample(ins);   end
                // bgez: convert to bge rs, r0, offset
                "bgez"      : begin ins.asm=BGE;    ins.ops[2] = ins.ops[1]; ins.ops[1].val = "zero"; bge_cg.sample(ins);   end
                // bnez: convert to bne rs, r0, offset
                "bnez"      : begin ins.asm=BNE;    ins.ops[2] = ins.ops[1]; ins.ops[1].val = "zero"; bne_cg.sample(ins);   end
                // bgtz: convert to blt x0, rs, offset
                "bgtz"      : begin ins.asm=BLT;    ins.ops[2] = ins.ops[1]; ins.ops[1] = ins.ops[0]; ins.ops[0].val = "zero"; blt_cg.sample(ins);   end
                // neg: convert to sub rd, x0, rs
                "neg"       : begin ins.asm=SUB;    ins.ops[2] = ins.ops[1]; ins.ops[1].val = "zero"; sub_cg.sample(ins);    end
                // snez: convert to sltu rd, x0, rs
                "snez"      : begin ins.asm=SLTU;   ins.ops[2] = ins.ops[1]; ins.ops[1].val = "zero"; sltu_cg.sample(ins);   end
                // seqz: convert to sltiu rd, rs, 1
                "seqz"      : begin ins.asm=SLTIU;  ins.ops[2].val = "1";                             sltiu_cg.sample(ins);  end
                // not:  convert to xor rd, rs, -1
                "not"       : begin ins.asm=XOR;    ins.ops[2].val = "-1";                            xori_cg.sample(ins);  end
                // ret: convert to jalr x0,x1(0)
                "ret"       : begin ins.asm=JALR;   ins.ops[0].key = "R"; ins.ops[0].val = "zero";
                                                    ins.ops[1].key = "R"; ins.ops[1].val = "ra";
                                                    ins.ops[2].val="0";
                                                    jalr_cg.sample(ins);
                end

                default: begin
                    `uvm_warning("RV32ISA Coverage",
                                 $sformatf("instruction [%0s] not mapped to functional coverage",
                                           ins.ins_str))
                end
            endcase
        end // else branch of if (ins.compressed)

        // Do not call sample until ins_prev is assigned otherwise
        // get a hit on bin [ADD][1st instruction]
        if (ins_prev.ins_str != "")
          instr_cg.sample(ins);

        ins_prev = ins; // Save instruction as previous

        // Send instruction to analysis port
        begin
            uvme_rv32isa_covg_trn_c isa_cov_trn;

            isa_cov_trn = uvme_rv32isa_covg_trn_c::type_id::create("isa_cov_trn");
            isa_cov_trn.ins = ins;
            `uvm_info("RV32ISA Coverage", $sformatf("Passing ISA coverage transaction:\n%s", isa_cov_trn.sprint()), UVM_DEBUG)
            ap.write(isa_cov_trn);
        end
    endfunction: sample

endclass : uvme_rv32isa_covg

//@DVT_LINTER_WAIVER_END "SR20211012_1"
