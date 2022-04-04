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


`ifndef __UVMA_RVVI_BASE_SEQ_SV__
`define __UVMA_RVVI_BASE_SEQ_SV__


/**
 * Abstract object from which all other Rvvi agent sequences must extend.
 * Subclasses must be run on Rvvi sequencer (uvma_rvvi_sqr_c) instance.
 */
class uvma_rvvi_base_seq_c#(int ILEN=DEFAULT_ILEN,
                            int XLEN=DEFAULT_XLEN) extends uvm_sequence#(
   .REQ(uvma_rvvi_control_seq_item_c),
   .RSP(uvma_rvvi_control_seq_item_c)
);
   
   // Agent handles
   uvma_rvvi_cfg_c#(ILEN, XLEN)    cfg;
   uvma_rvvi_cntxt_c#(ILEN, XLEN)  cntxt;

   `uvm_object_utils(uvma_rvvi_base_seq_c)
   `uvm_declare_p_sequencer(uvma_rvvi_sqr_c#(ILEN,XLEN))
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_rvvi_base_seq");

   /**
    * Fills in cfg and cntxt
    */
   extern virtual task pre_start();

endclass : uvma_rvvi_base_seq_c


`pragma protect begin


function uvma_rvvi_base_seq_c::new(string name="uvma_rvvi_base_seq");
   
   super.new(name);
   
endfunction : new

task uvma_rvvi_base_seq_c::pre_start();

   cfg = p_sequencer.cfg;
   cntxt = p_sequencer.cntxt;

endtask : pre_start

`pragma protect end


`endif // __UVMA_RVVI_BASE_SEQ_SV__
