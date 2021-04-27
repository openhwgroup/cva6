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


`ifndef __UVMA_RVFI_MON_TRN_LOGGER_SV__
`define __UVMA_RVFI_MON_TRN_LOGGER_SV__

/**
 * Component writing Rvfi monitor transactions rvfi data to disk as plain text.
 */
class uvma_rvfi_mon_trn_logger_c#(int ILEN=DEFAULT_ILEN,
                                  int XLEN=DEFAULT_XLEN) extends uvml_logs_mon_trn_logger_c#(
   .T_TRN  (uvml_trn_seq_item_c),
   .T_CFG  (uvma_rvfi_cfg_c    ),
   .T_CNTXT(uvma_rvfi_cntxt_c  )
);
      
   uvm_analysis_imp_rvfi_instr#(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN), uvma_rvfi_mon_trn_logger_c) instr_export;   

   const string format_header_str = "%15s: RVFI %6s %8s %8s %s %03s %08s %03s %08s %03s %08s %06s %08s %08s";   
   const string format_instr_str  = "%15s: RVFI %6d %8x %8s %s x%2d %08x x%2d %08x x%2d %08x";
   const string format_mem_str    = "%06s %08x %08s";

   `uvm_component_utils(uvma_rvfi_mon_trn_logger_c)
   
   /**
    * Default constructor.
    */
   function new(string name="uvma_rvfi_mon_trn_logger", uvm_component parent=null);
      
      super.new(name, parent);
      
      instr_export = new("instr_export", this);      
   endfunction : new
   
   /**
    * Writes contents of t to disk
    */
   virtual function void write(uvml_trn_seq_item_c t);
   endfunction : write
   
   virtual function void write_rvfi_instr(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) t);      
      string instr;

      instr = $sformatf(format_instr_str, $sformatf("%t", $time),
                        t.order,
                        t.pc_rdata, 
                        t.get_insn_word_str(),
                        get_mode_str(t.mode),
                        t.rs1_addr, t.rs1_rdata, 
                        t.rs2_addr, t.rs2_rdata,
                        t.rd1_addr, t.rd1_wdata);

      if (t.mem_wmask) 
         instr = $sformatf({"%s ", format_mem_str}, instr, "WR", t.mem_addr, t.get_mem_data_string());
      else if (t.mem_rmask)
         instr = $sformatf({"%s ", format_mem_str}, instr, "RD", t.mem_addr, t.get_mem_data_string());
      else
         instr = $sformatf("%s N/A", instr);

      if (t.halt) 
         instr = $sformatf("%s HALT", instr);
      if (t.intr) 
         instr = $sformatf("%s INTR", instr);
      if (t.trap) 
         instr = $sformatf("%s TRAP", instr);

      fwrite(instr);

   endfunction : write_rvfi_instr

   /**
    * Writes log header to disk
    */
   virtual function void print_header();
      fwrite($sformatf(format_header_str, $sformatf("%t", $time),
                       "Order", "PC", "Instr", "M", "rs1", "rs1_data", "rs2", "rs2_data", "rd", "rd_data", "mem_op", "mem_addr", "mem_data"));

   endfunction : print_header
   
endclass : uvma_rvfi_mon_trn_logger_c


`endif // __UVMA_RVFI_MON_TRN_LOGGER_SV__
