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
   bit [XLEN-1:0] csr_mip;
   bit [XLEN-1:0] csr_dcsr;

   step_rm_seq = uvma_rvvi_ovpsim_control_seq_item_c#(ILEN,XLEN)::type_id::create("step_rm_seq");
   start_item(step_rm_seq);
   csr_mip  = rvfi_instr.csrs["mip"].get_csr_retirement_data();
   csr_dcsr = rvfi_instr.csrs["dcsr"].get_csr_retirement_data();

   assert(step_rm_seq.randomize() with {
      action == UVMA_RVVI_STEPI;

      intr == rvfi_instr.insn_interrupt;
      intr_id == rvfi_instr.insn_interrupt_id;

      insn_bus_fault == rvfi_instr.insn_bus_fault;
      nmi_load_fault == rvfi_instr.insn_nmi_load_fault;
      nmi_store_fault == rvfi_instr.insn_nmi_store_fault;

      dbg_req == (rvfi_instr.dbg_mode && rvfi_instr.dbg inside {3,5});
      dbg_mode == rvfi_instr.dbg_mode;

      mip == csr_mip;
      rd1_addr == rvfi_instr.rd1_addr;
      rd1_wdata == rvfi_instr.rd1_wdata;

      mem_addr == rvfi_instr.mem_addr;
      mem_rdata == rvfi_instr.mem_rdata;
      mem_rmask == rvfi_instr.mem_rmask;
      mem_wdata == rvfi_instr.mem_wdata;
      mem_wmask == rvfi_instr.mem_wmask;
   });
   finish_item(step_rm_seq);

endtask : step_rm

`endif // __UVMA_RVVI_OVPSIM_CONTROL_SEQ_SV__



