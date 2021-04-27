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


`ifndef __UVMA_RVVI_MON_TRN_LOGGER_SV__
`define __UVMA_RVVI_MON_TRN_LOGGER_SV__

`uvm_analysis_imp_decl(_rvvi_state)

/**
 * Component writing Rvvi monitor transactions rvvi data to disk as plain text.
 */
class uvma_rvvi_mon_trn_logger_c#(int ILEN=DEFAULT_ILEN,
                                  int XLEN=DEFAULT_XLEN) extends uvml_logs_mon_trn_logger_c#(
   .T_TRN  (uvml_trn_seq_item_c         ),
   .T_CFG  (uvma_rvvi_cfg_c#(ILEN,XLEN) ),
   .T_CNTXT(uvma_rvvi_cntxt_c#(ILEN,XLEN))
);
      
   uvm_analysis_imp_rvvi_state#(uvma_rvvi_state_seq_item_c, uvma_rvvi_mon_trn_logger_c) state_export;

   `uvm_component_utils(uvma_rvvi_mon_trn_logger_c)

   const string format_header_str = "%15s: RVVI %6s %8s %8s %s %3s %8s";
   const string format_instr_str  = "%15s: RVVI %6d %8x %8s %s x%2s %8s";

   /**
    * Default constructor.
    */
   function new(string name="uvma_rvvi_mon_trn_logger", uvm_component parent=null);
      
      super.new(name, parent);
      
      state_export = new("state_export", this);
   endfunction : new
   
   /**
    * Writes contents of t to disk
    */
   virtual function void write(uvml_trn_seq_item_c t);
      //fwrite($sformatf("%t: %s: %s", $time, agent_name, t.convert2string()));
   endfunction : write
   
   virtual function void write_rvvi_state(uvma_rvvi_state_seq_item_c t);      
      string  gpr_index_str = "--";
      string  gpr_data_str  = "--------";

      if (t.gpr_update.size()) begin
         int unsigned index;
         void'(t.gpr_update.first(index));
         gpr_index_str = $sformatf("%2d", index);
         gpr_data_str = $sformatf("%08x", t.gpr_update[index]);
      end

      fwrite($sformatf(format_instr_str, $sformatf("%t", $time),
                       t.order,
                       t.pc,
                       t.get_insn_word_str(),
                       get_mode_str(t.mode),                       
                       gpr_index_str,
                       gpr_data_str));
   endfunction : write_rvvi_state

   /**
    * Writes log header to disk
    */
   virtual function void print_header();
      fwrite($sformatf(format_header_str, $sformatf("%t", $time),
                       "Order", "PC", "Instr", "M", "rd", "rd_data"));

   endfunction : print_header

endclass : uvma_rvvi_mon_trn_logger_c


`endif // __UVMA_RVVI_MON_TRN_LOGGER_SV__
