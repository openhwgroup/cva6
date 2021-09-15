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


`ifndef __UVMA_FENCEI_MON_TRN_LOGGER_SV__
`define __UVMA_FENCEI_MON_TRN_LOGGER_SV__

/**
 * Component writing Fencei monitor transactions fencei data to disk as plain text.
 */
class uvma_fencei_mon_trn_logger_c extends uvml_logs_mon_trn_logger_c#(
   .T_TRN  (uvml_trn_seq_item_c),
   .T_CFG  (uvma_fencei_cfg_c    ),
   .T_CNTXT(uvma_fencei_cntxt_c  )
);

   uvm_analysis_imp_fencei#(uvma_fencei_seq_item_c, uvma_fencei_mon_trn_logger_c) fencei_export;

   `uvm_component_param_utils(uvma_fencei_mon_trn_logger_c)

   /**
    * Default constructor.
    */
   function new(string name="uvma_fencei_mon_trn_logger", uvm_component parent=null);

      super.new(name, parent);

      fencei_export = new("fencei_export", this);

   endfunction : new

   /**
    * Build phase - attempt to load a firmware itb file (instruction table file)
    */
   function void build_phase(uvm_phase phase);

   endfunction : build_phase


   /**
    * Writes contents of t to disk
    */
   virtual function void write(uvml_trn_seq_item_c t);

   endfunction : write

   virtual function void write_fencei(uvma_fencei_seq_item_c t);

      string instr;

      instr = $sformatf("%s", t.convert2string());

      fwrite(instr);

   endfunction : write_fencei

   /**
    * Writes log header to disk
    */
   virtual function void print_header();

      fwrite("-----------------------------------------------------------");

   endfunction : print_header

endclass : uvma_fencei_mon_trn_logger_c


`endif // __UVMA_FENCEI_MON_TRN_LOGGER_SV__

