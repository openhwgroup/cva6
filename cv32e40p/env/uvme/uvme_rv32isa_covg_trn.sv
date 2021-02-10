// Copyright 2020 OpenHW Group
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
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0


`ifndef __UVME_RV32ISA_COVG_TRN_SV__
`define __UVME_RV32ISA_COVG_TRN_SV__


/**
 * Class encapsulation of instruction struct for passing instruction coverage
   through UVM testbench
 */
class uvme_rv32isa_covg_trn_c extends uvml_trn_mon_trn_c;
   
    ins_t ins;

    // Note, structs are not supported in the uvm field macros
    `uvm_object_utils_begin(uvme_rv32isa_covg_trn_c)   
    `uvm_object_utils_end
    
    /**
    * Default constructor.
    */
    extern function new(string name="uvme_rv32isa_covg_trn");
   
    extern function void do_copy(uvm_object rhs);
    extern function void do_print(uvm_printer printer);

endclass : uvme_rv32isa_covg_trn_c


`pragma protect begin

function uvme_rv32isa_covg_trn_c::new(string name="uvme_rv32isa_covg_trn");
   
   super.new(name);
   
endfunction : new

function void uvme_rv32isa_covg_trn_c::do_copy(uvm_object rhs);
    uvme_rv32isa_covg_trn_c rhs_trn;

    super.do_copy(rhs);
    assert($cast(rhs_trn, rhs));

    this.ins.ins_str = rhs_trn.ins.ins_str;    
    this.ins.asm     = rhs_trn.ins.asm;
    foreach (this.ins.ops[i]) begin
        this.ins.ops[i].key = rhs_trn.ins.ops[i].key;
        this.ins.ops[i].val = rhs_trn.ins.ops[i].val;
    end
endfunction : do_copy

function void uvme_rv32isa_covg_trn_c::do_print(uvm_printer printer);
    super.do_print(printer);

    printer.print_string("ins", ins.ins_str);
    printer.print_string("asm", ins.asm.name());
    foreach (this.ins.ops[i]) begin
        printer.print_string($sformatf("op[%0d]", i), $sformatf("%s %s", this.ins.ops[i].key, this.ins.ops[i].val));
    end
endfunction : do_print

`pragma protect end


`endif // __UVME_RV32ISA_COVG_TRN_SV__
