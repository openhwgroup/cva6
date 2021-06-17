// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
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


`ifndef __UVMA_RVVI_STATE_SEQ_ITEM_SV__
`define __UVMA_RVVI_STATE_SEQ_ITEM_SV__

/**
 * Object created by rvvi agent sequences extending uvml_trn_seq_base_c.
 */
class uvma_rvvi_state_seq_item_c#(int ILEN=32, int XLEN=32) extends uvml_trn_seq_item_c;

   rand bit                trap;
   rand bit                halt;
   rand bit                intr;   
   rand bit                valid;
   rand bit [ORDER_WL-1:0] order;
   rand bit [ILEN-1:0]     insn;
   rand uvma_rvvi_mode     mode;
   rand bit [IXL_WL-1:0]   ixl;
   rand bit [ISIZE_WL-1:0] isize;
   rand bit [XLEN-1:0]     pc;
   rand bit [XLEN-1:0]     pcnext;

   bit [XLEN-1:0] gpr_update[int unsigned];

   bit [XLEN-1:0] x[32];

   bit [XLEN-1:0] csr[string];
   
   static protected string _log_format_string = "0x%08x %s 0x%01x 0x%08x";

   `uvm_object_utils_begin(uvma_rvvi_state_seq_item_c)
      `uvm_field_int(trap, UVM_DEFAULT)
      `uvm_field_int(halt, UVM_DEFAULT)
      `uvm_field_int(intr, UVM_DEFAULT)
      `uvm_field_int(order, UVM_DEFAULT)
      `uvm_field_int(insn, UVM_DEFAULT)
      `uvm_field_int(isize, UVM_DEFAULT)
      `uvm_field_enum(uvma_rvvi_mode, mode, UVM_DEFAULT)
      `uvm_field_int(ixl, UVM_DEFAULT)
      `uvm_field_int(pc, UVM_DEFAULT)
      `uvm_field_int(pcnext, UVM_DEFAULT)      
      `uvm_field_aa_int_int_unsigned(gpr_update, UVM_DEFAULT)
      `uvm_field_sarray_int(x, UVM_DEFAULT)
      `uvm_field_aa_int_string(csr, UVM_DEFAULT)
   `uvm_object_utils_end
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_rvvi_seq_item");

   /**
    * One-liner log message
    */
   extern function string convert2string();

   /**
    * Get instruction hex string with compressed instructions displayed
    */
   extern function string get_insn_word_str();

endclass : uvma_rvvi_state_seq_item_c

`pragma protect begin

function uvma_rvvi_state_seq_item_c::new(string name="uvma_rvvi_seq_item");
   
   super.new(name);
   
endfunction : new

function string uvma_rvvi_state_seq_item_c::convert2string();
   convert2string = "";

   if (valid) begin
      convert2string = { convert2string, 
                         $sformatf("Order: %0d, insn: 0x%08x, pc: 0x%08x, mode: %s, ixl: 0x%01x", 
                                   order, insn, pc, mode.name(), ixl)
      };
   end
            
   if (trap)
      convert2string = { convert2string, " TRAP" };
   if (halt)
      convert2string = { convert2string, " HALT" };
   if (intr)
      convert2string = { convert2string, " INTR" };

   foreach (gpr_update[i]) begin
      convert2string = { convert2string, $sformatf(" GPR[%02d]: 0x%08x", i, gpr_update[i]) };
   end
endfunction : convert2string

function string uvma_rvvi_state_seq_item_c::get_insn_word_str();
   if (isize == 2)
      return $sformatf("----%04x", insn[15:0]);
   
   return $sformatf("%08x", insn);
endfunction : get_insn_word_str

`pragma protect end


`endif // __UVMA_RVVI_SEQ_ITEM_SV__
