// 
// Copyright 2021 OpenHW Group
// Copyright 2021 Datum Technology Corporation
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// 
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may
// not use this file except in compliance with the License, or, at your option,
// the Apache License version 2.0. You may obtain a copy of the License at
// 
//     https://solderpad.org/licenses/SHL-2.1/
// 
// Unless required by applicable law or agreed to in writing, any work
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
// License for the specific language governing permissions and limitations
// under the License.
// 


`ifndef __UVMA_OBI_SQR_SV__
`define __UVMA_OBI_SQR_SV__


/**
 * Component running Open Bus Interface sequences extending uvma_obi_base_seq_c.
 * Provides sequence items for uvma_obi_drv_c.
 */
class uvma_obi_sqr_c extends uvm_sequencer#(
   .REQ(uvma_obi_base_seq_item_c),
   .RSP(uvma_obi_mon_trn_c      )
);
   
   // Objects
   uvma_obi_cfg_c    cfg;
   uvma_obi_cntxt_c  cntxt;
   
   // TLM
   uvm_tlm_analysis_fifo #(uvma_obi_mon_trn_c)  mon_trn_fifo;
   
   
   `uvm_component_utils_begin(uvma_obi_sqr_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_sqr", uvm_component parent=null);
   
   /**
    * Ensures cfg & cntxt handles are not null
    */
   extern virtual function void build_phase(uvm_phase phase);
   
endclass : uvma_obi_sqr_c


function uvma_obi_sqr_c::new(string name="uvma_obi_sqr", uvm_component parent=null);
   
   super.new(name, parent);
   
endfunction : new


function void uvma_obi_sqr_c::build_phase(uvm_phase phase);
   
   super.build_phase(phase);
   
   void'(uvm_config_db#(uvma_obi_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   
   void'(uvm_config_db#(uvma_obi_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (!cntxt) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end
   
   mon_trn_fifo = new("mon_trn_fifo", this);
   
endfunction : build_phase


`endif // __UVMA_OBI_SQR_SV__
