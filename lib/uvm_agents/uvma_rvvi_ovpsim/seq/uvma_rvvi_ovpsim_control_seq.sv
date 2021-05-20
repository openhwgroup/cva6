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


`ifndef __UVMA_RVVI_OVPSIM_CONTROL_SEQ_SV__
`define __UVMA_RVVI_OVPSIM_CONTROL_SEQ_SV__


/**
 * Sequence which implements
 */
class uvma_rvvi_ovpsim_control_seq_c#(int ILEN=uvma_rvvi_pkg::DEFAULT_ILEN,
                                      int XLEN=uvma_rvvi_pkg::DEFAULT_XLEN) extends uvma_rvvi_control_seq_c#(ILEN,XLEN);
   
   
   `uvm_object_param_utils(uvma_rvvi_ovpsim_control_seq_c#(ILEN,XLEN))
   `uvm_declare_p_sequencer(uvma_rvvi_sqr_c#(ILEN,XLEN))
      
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_rvvi_ovpsim_control_seq");

   /**
    * Step the reference model
    */
   extern virtual task step_rm(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) rvfi_instr);

endclass : uvma_rvvi_ovpsim_control_seq_c


function uvma_rvvi_ovpsim_control_seq_c::new(string name="uvma_rvvi_ovpsim_control_seq");
   
   super.new(name);
   
endfunction : new

task uvma_rvvi_ovpsim_control_seq_c::step_rm(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) rvfi_instr);

   // Send sequence item to step the RM
   uvma_rvvi_ovpsim_control_seq_item_c#(ILEN,XLEN) step_rm_seq;

   step_rm_seq = uvma_rvvi_ovpsim_control_seq_item_c#(ILEN,XLEN)::type_id::create("step_rm_seq");
   start_item(step_rm_seq);
   assert(step_rm_seq.randomize() with {
      action == UVMA_RVVI_STEPI;
      intr == rvfi_instr.intr;
      // FIXME:strichmo:hack to test debug halt...works unless we change debug handler address!
      halt == (rvfi_instr.intr && (rvfi_instr.pc_rdata == 32'h1a11_0800));
      mip == rvfi_instr.csr_mip;
      mcause == rvfi_instr.csr_mcause;
      rd1_addr == rvfi_instr.rd1_addr;
      rd1_wdata == rvfi_instr.rd1_wdata;
   });
   finish_item(step_rm_seq);

endtask : step_rm

`endif // __UVMA_RVVI_OVPSIM_CONTROL_SEQ_SV__
