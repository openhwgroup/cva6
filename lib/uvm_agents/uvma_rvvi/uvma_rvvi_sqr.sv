//
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2020 Silicon Labs, Inc.
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
//


`ifndef __UVMA_RVVI_SQR_SV__
`define __UVMA_RVVI_SQR_SV__

`uvm_analysis_imp_decl(_rvfi_instr)

/**
 * Component running Clock & Reset sequences extending uvma_rvvi_seq_base_c.
 * Provides sequence items for uvma_rvvi_drv_c.
 */
class uvma_rvvi_sqr_c#(int ILEN=DEFAULT_ILEN,
                       int XLEN=DEFAULT_XLEN) extends uvm_sequencer#(
                             .REQ(uvma_rvvi_control_seq_item_c#(ILEN,XLEN)),
                             .RSP(uvma_rvvi_control_seq_item_c#(ILEN,XLEN))
                        );
   // Objects
   uvma_rvvi_cfg_c    cfg;
   uvma_rvvi_cntxt_c  cntxt;

   uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) rvfi_instr_q[$];

   // Analysis port to receive retirement events from the RVFI
   uvm_analysis_imp_rvfi_instr#(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN), uvma_rvvi_sqr_c) rvfi_instr_export;

   `uvm_component_utils_begin(uvma_rvvi_sqr_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_rvvi_sqr", uvm_component parent=null);

   /**
    * Ensures cfg & cntxt handles are not null
    */
   extern virtual function void build_phase(uvm_phase phase);

   /**
    * Analysis port write from RVFI instruction retirement monitor
    */
   extern virtual function void write_rvfi_instr(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) rvfi_instr);

endclass : uvma_rvvi_sqr_c


function uvma_rvvi_sqr_c::new(string name="uvma_rvvi_sqr", uvm_component parent=null);

   super.new(name, parent);

   rvfi_instr_export = new("rvfi_instr_export", this);

endfunction : new


function void uvma_rvvi_sqr_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvma_rvvi_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end

   void'(uvm_config_db#(uvma_rvvi_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (!cntxt) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end

endfunction : build_phase

function void uvma_rvvi_sqr_c::write_rvfi_instr(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) rvfi_instr);

   if (cfg.enabled) begin
      rvfi_instr_q.push_back(rvfi_instr);
   end

endfunction : write_rvfi_instr

`endif // __UVMA_RVVI_SQR_SV__


