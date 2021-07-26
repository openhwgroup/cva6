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


`ifndef __UVMA_RVFI_CSR_SEQ_ITEM_SV__
`define __UVMA_RVFI_CSR_SEQ_ITEM_SV__


/**
 * Object created by RVFI agent sequences extending uvma_rvfi_seq_base_c.
 */
class uvma_rvfi_csr_seq_item_c#(int XLEN=DEFAULT_XLEN) extends uvml_trn_seq_item_c;

   rand int unsigned             nret_id;

   string                        csr;
   
   rand bit [XLEN-1:0]           rmask;
   rand bit [XLEN-1:0]           wmask;
   rand bit [XLEN-1:0]           rdata;
   rand bit [XLEN-1:0]           wdata;
   
   static protected string _log_format_string = "0x%08x %s 0x%01x 0x%08x";

   `uvm_object_param_utils_begin(uvma_rvfi_csr_seq_item_c)
      `uvm_field_int(nret_id, UVM_DEFAULT)

      `uvm_field_int(rmask,   UVM_DEFAULT)
      `uvm_field_int(wmask,   UVM_DEFAULT)
      `uvm_field_int(rdata,   UVM_DEFAULT)
      `uvm_field_int(wdata,   UVM_DEFAULT)
   `uvm_object_utils_end
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_rvfi_csr_seq_item");

   /**
    * Fetch the value of the CSR at instruction retirement taking into account write data and write mask
    */
   extern virtual function bit[uvma_rvfi_csr_seq_item_c::XLEN-1:0] get_csr_retirement_data();

   /**
    * One-liner log message
    */
   extern function string convert2string();

endclass : uvma_rvfi_csr_seq_item_c

`pragma protect begin
function uvma_rvfi_csr_seq_item_c::new(string name="uvma_rvfi_csr_seq_item");
   
   super.new(name);
   
endfunction : new

function bit [uvma_rvfi_csr_seq_item_c::XLEN-1:0] uvma_rvfi_csr_seq_item_c::get_csr_retirement_data();

   // Any bits with wmask set should use the wdata
   // All other bits should use the rdata
   // rmask is not used
   return (wmask & wdata) | (~wmask & rdata);

endfunction : get_csr_retirement_data

function string uvma_rvfi_csr_seq_item_c::convert2string();

   convert2string = $sformatf("csr: %s rdata(mask) 0x%08x:0x%08x, wdata(mask) 0x%08x:0x%08x",
                              csr, rdata, rmask, wdata, wmask);
   
endfunction : convert2string

`pragma protect end
`endif // __UVMA_RVFI_CSR_SEQ_ITEM_SV__
