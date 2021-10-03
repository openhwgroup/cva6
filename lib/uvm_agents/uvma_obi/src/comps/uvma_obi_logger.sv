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


`ifndef __UVMA_OBI_LOGGER_SV__
`define __UVMA_OBI_LOGGER_SV__


/**
 * TODO Describe uvma_obi_logger_c
 */
class uvma_obi_logger_c extends uvm_component;
   
   // Objects
   uvma_obi_cfg_c    cfg  ; ///< Agent configuration handle
   uvma_obi_cntxt_c  cntxt; ///< Agent context handle
   
   // Components
   uvma_obi_mon_trn_logger_c          mon_trn_logger        ; ///< 
   uvma_obi_mstr_a_mon_trn_logger_c   mstr_a_mon_trn_logger ; ///< 
   uvma_obi_mstr_r_mon_trn_logger_c   mstr_r_mon_trn_logger ; ///< 
   uvma_obi_slv_a_mon_trn_logger_c    slv_a_mon_trn_logger  ; ///< 
   uvma_obi_slv_r_mon_trn_logger_c    slv_r_mon_trn_logger  ; ///< 
   uvma_obi_seq_item_logger_c         seq_item_logger       ; ///< 
   uvma_obi_mstr_a_seq_item_logger_c  mstr_a_seq_item_logger; ///< 
   uvma_obi_mstr_r_seq_item_logger_c  mstr_r_seq_item_logger; ///< 
   uvma_obi_slv_a_seq_item_logger_c   slv_a_seq_item_logger ; ///< 
   uvma_obi_slv_r_seq_item_logger_c   slv_r_seq_item_logger ; ///< 
   
   // TLM
   uvm_analysis_export#(uvma_obi_mon_trn_c        )  mon_trn_export        ; ///< 
   uvm_analysis_export#(uvma_obi_mstr_a_mon_trn_c )  mstr_a_mon_trn_export ; ///< 
   uvm_analysis_export#(uvma_obi_mstr_r_mon_trn_c )  mstr_r_mon_trn_export ; ///< 
   uvm_analysis_export#(uvma_obi_slv_a_mon_trn_c  )  slv_a_mon_trn_export  ; ///< 
   uvm_analysis_export#(uvma_obi_slv_r_mon_trn_c  )  slv_r_mon_trn_export  ; ///< 
   uvm_analysis_export#(uvma_obi_seq_item_c       )  seq_item_export       ; ///< 
   uvm_analysis_export#(uvma_obi_mstr_a_seq_item_c)  mstr_a_seq_item_export; ///< 
   uvm_analysis_export#(uvma_obi_mstr_r_seq_item_c)  mstr_r_seq_item_export; ///< 
   uvm_analysis_export#(uvma_obi_slv_a_seq_item_c )  slv_a_seq_item_export ; ///< 
   uvm_analysis_export#(uvma_obi_slv_r_seq_item_c )  slv_r_seq_item_export ; ///< 
   
   
   `uvm_component_utils_begin(uvma_obi_logger_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_logger", uvm_component parent=null);
   
   /**
    * TODO Describe uvma_obi_logger_c::build_phase()
    */
   extern virtual function void build_phase(uvm_phase phase);
   
   /**
    * TODO Describe uvma_obi_logger_c::connect_phase()
    */
   extern virtual function void connect_phase(uvm_phase phase);
   
endclass : uvma_obi_logger_c


function uvma_obi_logger_c::new(string name="uvma_obi_logger", uvm_component parent=null);
   
   super.new(name, parent);
   
endfunction : new


function void uvma_obi_logger_c::build_phase(uvm_phase phase);
   
   super.build_phase(phase);
   
   void'(uvm_config_db#(uvma_obi_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   else begin
      `uvm_info("CFG", $sformatf("Found configuration handle:\n%s", cfg.sprint()), UVM_DEBUG)
      uvm_config_db#(uvma_obi_cfg_c)::set(this, "*", "cfg", cfg);
   end
   
   // Create components
   mon_trn_logger         = uvma_obi_mon_trn_logger_c        ::type_id::create("mon_trn_logger"        , this);
   mstr_a_mon_trn_logger  = uvma_obi_mstr_a_mon_trn_logger_c ::type_id::create("mstr_a_mon_trn_logger" , this);
   mstr_r_mon_trn_logger  = uvma_obi_mstr_r_mon_trn_logger_c ::type_id::create("mstr_r_mon_trn_logger" , this);
   slv_a_mon_trn_logger   = uvma_obi_slv_a_mon_trn_logger_c  ::type_id::create("slv_a_mon_trn_logger"  , this);
   slv_r_mon_trn_logger   = uvma_obi_slv_r_mon_trn_logger_c  ::type_id::create("slv_r_mon_trn_logger"  , this);
   seq_item_logger        = uvma_obi_seq_item_logger_c       ::type_id::create("seq_item_logger"       , this);
   mstr_a_seq_item_logger = uvma_obi_mstr_a_seq_item_logger_c::type_id::create("mstr_a_seq_item_logger", this);
   mstr_r_seq_item_logger = uvma_obi_mstr_r_seq_item_logger_c::type_id::create("mstr_r_seq_item_logger", this);
   slv_a_seq_item_logger  = uvma_obi_slv_a_seq_item_logger_c ::type_id::create("slv_a_seq_item_logger" , this);
   slv_r_seq_item_logger  = uvma_obi_slv_r_seq_item_logger_c ::type_id::create("slv_r_seq_item_logger" , this);
   
endfunction : build_phase


function void uvma_obi_logger_c::connect_phase(uvm_phase phase);
   
   super.connect_phase(phase);
   
   mon_trn_export        = mon_trn_logger        .analysis_export;
   mstr_a_mon_trn_export = mstr_a_mon_trn_logger .analysis_export;
   mstr_r_mon_trn_export = mstr_r_mon_trn_logger .analysis_export;
   slv_a_mon_trn_export  = slv_a_mon_trn_logger  .analysis_export;
   slv_r_mon_trn_export  = slv_r_mon_trn_logger  .analysis_export;
   seq_item_export       = seq_item_logger       .analysis_export;
   mstr_a_seq_item_export= mstr_a_seq_item_logger.analysis_export;
   mstr_r_seq_item_export= mstr_r_seq_item_logger.analysis_export;
   slv_a_seq_item_export = slv_a_seq_item_logger .analysis_export;
   slv_r_seq_item_export = slv_r_seq_item_logger .analysis_export;
   
endfunction : connect_phase


`endif // __UVMA_OBI_LOGGER_SV__
