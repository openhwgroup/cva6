// Copyright 2021 OpenHW Group
// Copyright 2021 Datum Technology Corporation
// Copyright 2021 Silicon Labs
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may not use this file except in compliance
// with the License, or, at your option, the Apache License version 2.0.  You may obtain a copy of the License at
//                                        https://solderpad.org/licenses/SHL-2.1/
// Unless required by applicable law or agreed to in writing, any work distributed under the License is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the License for the
// specific language governing permissions and limitations under the License.
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


`ifndef __UVMA_OBI_VSQR_SV__
`define __UVMA_OBI_VSQR_SV__


/**
 * Component running Open Bus Interface sequences extending uvma_obi_base_vseq_c.
 */
class uvma_obi_vsqr_c extends uvm_sequencer #(
   .REQ(uvma_obi_seq_item_c),
   .RSP(uvma_obi_seq_item_c)
);
   
   // Objects
   uvma_obi_cfg_c    cfg  ; ///< Agent configuration handle
   uvma_obi_cntxt_c  cntxt; ///< Agent context handle
   
   // Components
   uvma_obi_mstr_a_sqr_c  mstr_a_sequencer; ///< TODO Describe uvma_obi_vsqr_c::mstr_a_sequencer
   uvma_obi_mstr_r_sqr_c  mstr_r_sequencer; ///< TODO Describe uvma_obi_vsqr_c::mstr_r_sequencer
   uvma_obi_slv_a_sqr_c   slv_a_sequencer ; ///< TODO Describe uvma_obi_vsqr_c::slv_a_sequencer 
   uvma_obi_slv_r_sqr_c   slv_r_sequencer ; ///< TODO Describe uvma_obi_vsqr_c::slv_r_sequencer 
   
   // TLM
   uvm_analysis_port     #(uvma_obi_mon_trn_c       )  mon_trn_ap           ; ///< TODO Describe uvma_obi_vswr_c::mon_trn_ap           
   uvm_analysis_port     #(uvma_obi_seq_item_c      )  seq_item_ap          ; ///< TODO Describe uvma_obi_vswr_c::seq_item_ap          
   uvm_tlm_analysis_fifo #(uvma_obi_mstr_a_mon_trn_c)  mstr_a_mon_trn_fifo  ; ///< TODO Describe uvma_obi_vswr_c::mstr_a_mon_trn_fifo  
   uvm_tlm_analysis_fifo #(uvma_obi_mstr_r_mon_trn_c)  mstr_r_mon_trn_fifo  ; ///< TODO Describe uvma_obi_vswr_c::mstr_r_mon_trn_fifo  
   uvm_tlm_analysis_fifo #(uvma_obi_slv_a_mon_trn_c )  slv_a_mon_trn_fifo   ; ///< TODO Describe uvma_obi_vswr_c::slv_a_mon_trn_fifo   
   uvm_tlm_analysis_fifo #(uvma_obi_slv_r_mon_trn_c )  slv_r_mon_trn_fifo   ; ///< TODO Describe uvma_obi_vswr_c::slv_r_mon_trn_fifo   
   uvm_analysis_export   #(uvma_obi_mstr_a_mon_trn_c)  mstr_a_mon_trn_export; ///< TODO Describe uvma_obi_vswr_c::mstr_a_mon_trn_export
   uvm_analysis_export   #(uvma_obi_mstr_r_mon_trn_c)  mstr_r_mon_trn_export; ///< TODO Describe uvma_obi_vswr_c::mstr_r_mon_trn_export
   uvm_analysis_export   #(uvma_obi_slv_a_mon_trn_c )  slv_a_mon_trn_export ; ///< TODO Describe uvma_obi_vswr_c::slv_a_mon_trn_export 
   uvm_analysis_export   #(uvma_obi_slv_r_mon_trn_c )  slv_r_mon_trn_export ; ///< TODO Describe uvma_obi_vswr_c::slv_r_mon_trn_export 
   
   
   `uvm_component_utils_begin(uvma_obi_vsqr_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_vsqr", uvm_component parent=null);
   
   /**
    * Ensures cfg & cntxt handles are not null
    */
   extern virtual function void build_phase(uvm_phase phase);
   
   /**
    * TODO Describe uvma_obi_vsqr_c::connect_phase()
    */
   extern virtual function void connect_phase(uvm_phase phase);
   
endclass : uvma_obi_vsqr_c


function uvma_obi_vsqr_c::new(string name="uvma_obi_vsqr", uvm_component parent=null);
   
   super.new(name, parent);
   
endfunction : new


function void uvma_obi_vsqr_c::build_phase(uvm_phase phase);
   
   super.build_phase(phase);
   
   void'(uvm_config_db#(uvma_obi_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("OBI_VSQR", "Configuration handle is null")
   end
   
   void'(uvm_config_db#(uvma_obi_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (!cntxt) begin
      `uvm_fatal("OBI_VSQR", "Context handle is null")
   end
   
   // Create components
   mstr_a_sequencer = uvma_obi_mstr_a_sqr_c::type_id::create("mstr_a_sequencer", this);
   mstr_r_sequencer = uvma_obi_mstr_r_sqr_c::type_id::create("mstr_r_sequencer", this);
   slv_a_sequencer  = uvma_obi_slv_a_sqr_c ::type_id::create("slv_a_sequencer" , this);
   slv_r_sequencer  = uvma_obi_slv_r_sqr_c ::type_id::create("slv_r_sequencer" , this);
   
   // Create TLM objects
   mon_trn_ap            = new("mon_trn_ap"           , this);
   seq_item_ap           = new("seq_item_ap"          , this);
   mstr_a_mon_trn_fifo   = new("mstr_a_mon_trn_fifo"  , this);
   mstr_r_mon_trn_fifo   = new("mstr_r_mon_trn_fifo"  , this);
   slv_a_mon_trn_fifo    = new("slv_a_mon_trn_fifo"   , this);
   slv_r_mon_trn_fifo    = new("slv_r_mon_trn_fifo"   , this);
   mstr_a_mon_trn_export = new("mstr_a_mon_trn_export", this);
   mstr_r_mon_trn_export = new("mstr_r_mon_trn_export", this);
   slv_a_mon_trn_export  = new("slv_a_mon_trn_export" , this);
   slv_r_mon_trn_export  = new("slv_r_mon_trn_export" , this);
   
endfunction : build_phase


function void uvma_obi_vsqr_c::connect_phase(uvm_phase phase);
   
   super.connect_phase(phase);
   
   // Connect exports to FIFOs
   mstr_a_mon_trn_export.connect(mstr_a_mon_trn_fifo.analysis_export);
   mstr_r_mon_trn_export.connect(mstr_r_mon_trn_fifo.analysis_export);
   slv_a_mon_trn_export .connect(slv_a_mon_trn_fifo .analysis_export);
   slv_r_mon_trn_export .connect(slv_r_mon_trn_fifo .analysis_export);
   
endfunction : connect_phase


`endif // __UVMA_OBI_VSQR_SV__
