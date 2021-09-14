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


`ifndef __UVMA_RVVI_OVPSIM_OBI_SEQ_SV__
`define __UVMA_RVVI_OVPSIM_OBI_SEQ_SV__


/**
 * Sequence which implements
 */
class uvma_rvvi_ovpsim_obi_seq_c#(int ILEN=uvma_rvvi_pkg::DEFAULT_ILEN,
                                  int XLEN=uvma_rvvi_pkg::DEFAULT_XLEN) extends uvma_rvvi_base_seq_c#(ILEN,XLEN);

   // Convenience handles for storing the RVVI OVPSIM-casted versions of cfg and cntxt
   uvma_rvvi_ovpsim_cfg_c#(ILEN, XLEN)   ovpsim_cfg;
   uvma_rvvi_ovpsim_cntxt_c#(ILEN, XLEN) ovpsim_cntxt;

   // Model of the expected instruction fetch errors
   // Indexed by word-aligned address
   // Any incoming OBI fetch with a error response will set this array
   // If an incoming OBI fetch with okay error reponse is received any previous error is cleared
   bit obi_i_error[bit[XLEN-1:2]];

   `uvm_object_param_utils(uvma_rvvi_ovpsim_obi_seq_c#(ILEN,XLEN))
   `uvm_declare_p_sequencer(uvma_rvvi_sqr_c#(ILEN,XLEN))

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_rvvi_ovpsim_obi_seq");

   /**
    * Main thread of sequence
    */
   extern virtual task body();

   /**
    * Instruction OBI thread
    */
   extern virtual task obi_i();

   /**
    * Data OBI thread
    */
   extern virtual task obi_d();

   /**
     * RVVI monitor thread.  Annotate bus errors on RVVI I fetches when/if necessary
     */
   extern virtual task rvvi_i_mon();

   /**
     * For okay OBI I responses, clear any pending fetch errors
     */
   extern virtual function void clear_i_error(bit[XLEN-1:0] byte_address);

   /**
     * For errored OBI responses, set fetch error
     */
   extern virtual function void set_i_error(bit[XLEN-1:0] byte_address);

   /**
     * Used by RVVI, query if the I fetch should returned error
     */
   extern virtual function bit is_i_error(bit[XLEN-1:0] byte_address);

endclass : uvma_rvvi_ovpsim_obi_seq_c


function uvma_rvvi_ovpsim_obi_seq_c::new(string name="uvma_rvvi_ovpsim_obi_seq");

   super.new(name);

endfunction : new

task uvma_rvvi_ovpsim_obi_seq_c::body();

   if (!$cast(ovpsim_cfg, cfg)) begin
      `uvm_fatal("OBISEQ", $sformatf("Could not cast cfg to an OVPSIM cfg"))
   end

   if (!$cast(ovpsim_cntxt, cntxt)) begin
      `uvm_fatal("OBISEQ", $sformatf("Could not cast cntxt to an OVPSIM cntxt"))
   end

   fork
      obi_i();
      obi_d();

      rvvi_i_mon();
   join

endtask : body

task uvma_rvvi_ovpsim_obi_seq_c::rvvi_i_mon();

   // Model InstructonBusFault generation as a combinatorial decode of IAddr and Ird
   while (1) begin
      @(ovpsim_cntxt.ovpsim_bus_vif.IAddr or ovpsim_cntxt.ovpsim_bus_vif.Ird);
      if (ovpsim_cntxt.ovpsim_bus_vif.Ird && is_i_error(ovpsim_cntxt.ovpsim_bus_vif.IAddr))
         ovpsim_cntxt.ovpsim_bus_vif.InstructionBusFault = 1'b1;
      else
         ovpsim_cntxt.ovpsim_bus_vif.InstructionBusFault = 1'b0;
   end

endtask : rvvi_i_mon

task uvma_rvvi_ovpsim_obi_seq_c::obi_i();

   while(1) begin
      uvma_obi_memory_mon_trn_c trn;

      wait (p_sequencer.obi_i_q.size());
      trn = p_sequencer.obi_i_q.pop_front();
      if (trn.err)
         set_i_error(trn.address);
      else
         clear_i_error(trn.address);
   end

endtask : obi_i

task uvma_rvvi_ovpsim_obi_seq_c::obi_d();

   while(1) begin
      uvma_obi_memory_mon_trn_c trn;

      wait (p_sequencer.obi_d_q.size());
      trn = p_sequencer.obi_d_q.pop_front();
   end

endtask : obi_d

function void uvma_rvvi_ovpsim_obi_seq_c::clear_i_error(bit[XLEN-1:0] byte_address);

   if (obi_i_error.exists(byte_address[XLEN-1:2])) begin
      obi_i_error.delete(byte_address[XLEN-1:2]);
   end

endfunction : clear_i_error

function void uvma_rvvi_ovpsim_obi_seq_c::set_i_error(bit[XLEN-1:0] byte_address);

   obi_i_error[byte_address[XLEN-1:2]] = 1;

endfunction : set_i_error

function bit uvma_rvvi_ovpsim_obi_seq_c::is_i_error(bit[XLEN-1:0] byte_address);

   bit i_error = obi_i_error.exists(byte_address[XLEN-1:2]) ? 1 : 0;

   return i_error;

endfunction : is_i_error

`endif // __UVMA_RVVI_OVPSIM_OBI_SEQ_SV__

