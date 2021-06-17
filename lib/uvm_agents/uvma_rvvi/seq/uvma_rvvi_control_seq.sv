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


`ifndef __UVMA_RVVI_CONTROL_SEQ_SV__
`define __UVMA_RVVI_CONTROL_SEQ_SV__


/**
 * Sequence which implements
 */
virtual class uvma_rvvi_control_seq_c#(int ILEN=DEFAULT_ILEN,
                                       int XLEN=DEFAULT_XLEN) extends uvma_rvvi_base_seq_c#(ILEN,XLEN);   
      
   `uvm_declare_p_sequencer(uvma_rvvi_sqr_c#(ILEN,XLEN))
      
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_rvvi_control_seq");

   /**
    * Sequence body
    */
   extern virtual task body();

   /**
    * Step the reference model
    */
   pure virtual task step_rm(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) rvfi_instr);

endclass : uvma_rvvi_control_seq_c


function uvma_rvvi_control_seq_c::new(string name="uvma_rvvi_control_seq");
   
   super.new(name);
   
endfunction : new

task uvma_rvvi_control_seq_c::body();
   while(1) begin
      uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) last_rvfi_instr;

      wait (p_sequencer.rvfi_instr_q.size());
      last_rvfi_instr = p_sequencer.rvfi_instr_q.pop_front();

      `uvm_info("CONTROL", $sformatf("Received RVFI: %0d", last_rvfi_instr.order), UVM_DEBUG);

      // Always step the RM
      step_rm(last_rvfi_instr);
   end
endtask : body

`endif // __UVMA_RVVI_CONTROL_SEQ_SV__
