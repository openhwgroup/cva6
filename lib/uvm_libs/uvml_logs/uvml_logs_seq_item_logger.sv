// 
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// 
// Licensed under the Solderpad Hardware License, Version 2.0 (the "License");
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


`ifndef __UVML_LOGS_SEQ_ITEM_LOGGER_SV__
`define __UVML_LOGS_SEQ_ITEM_LOGGER_SV__


/**
 * Logger writing sequence items debug info to disk.
 */
class uvml_logs_seq_item_logger_c#(
   type T_TRN   = uvml_trn_seq_item_c,
   type T_CFG   = uvm_object        ,
   type T_CNTXT = uvm_object
) extends uvm_subscriber#(
   .T(T_TRN)
);
   
   // Objects
   T_CFG    cfg;
   T_CNTXT  cntxt;
   
   // IO constants
   string  cli_args   = uvml_logs_default_sim_dir_cli_arg ;
   string  sub_dir    = uvml_logs_default_trn_log_dir_name;
   string  fextension = uvml_logs_default_trn_fextension  ;
   
   // IO variables
   bit           fhandle_valid   = 0;
   int unsigned  fhandle         = 0;
   string        cli_args_result = "";
   string        fpath           = "";
   string        name            = "";
   
   
   `uvm_component_param_utils_begin(uvml_logs_seq_item_logger_c#(T_TRN, T_CFG, T_CNTXT))
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
      
      `uvm_field_string(cli_args  , UVM_DEFAULT)
      `uvm_field_string(sub_dir   , UVM_DEFAULT)
      `uvm_field_string(fextension, UVM_DEFAULT)
      
      `uvm_field_int   (fhandle_valid  , UVM_DEFAULT)
      `uvm_field_int   (fhandle        , UVM_DEFAULT)
      `uvm_field_string(cli_args_result, UVM_DEFAULT)
      `uvm_field_string(fpath          , UVM_DEFAULT)
      `uvm_field_string(name           , UVM_DEFAULT)
   `uvm_component_utils_end
   
   
   /**
    * Default constructor
    */
   extern function new(string name="uvml_logs_seq_item_logger", uvm_component parent=null);
   
   /**
    * 1. Ensures cfg & cntxt handles are not null
    * 2. Opens fhandle for write access
    * 3. Prints banner into fhandle
    */
   extern virtual function void build_phase(uvm_phase phase);
   
   /**
    * TODO Describe uvml_logs_seq_item_logger_c::end_of_elaboration_phase()
    */
   extern virtual function void end_of_elaboration_phase(uvm_phase phase);
   
   /**
    * Closes fhandle access
    */
   extern virtual function void final_phase(uvm_phase phase);
   
   /**
    * Writes contents of t to disk
    */
   extern virtual function void write(T_TRN t);
   
   /**
    * Writes log header to disk
    */
   extern virtual function void print_header();
   
   /**
    * Writes msg to disk
    * Waiving Verissimo SVTB.32.2.0: Pass strings by reference unless otherwise needed
    */
   extern function void fwrite(string msg); //@DVT_LINTER_WAIVER "MT20211228_4" disable SVTB.32.2.0
   
endclass : uvml_logs_seq_item_logger_c


function uvml_logs_seq_item_logger_c::new(string name="uvml_logs_seq_item_logger", uvm_component parent=null);
   
   super.new(name, parent);
   
endfunction : new


function void uvml_logs_seq_item_logger_c::build_phase(uvm_phase phase);
   
   super.build_phase(phase);
   
   void'(uvm_config_db#(T_CFG)::get(this, "", "cfg", cfg));
   if (!cfg) begin
     `uvm_fatal("CFG", "Configuration handle is null")
   end
   
   void'(uvm_config_db#(T_CNTXT)::get(this, "", "cntxt", cntxt));
   if (!cntxt) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end
   
   // Retrieve simulation path from CLI argument
   void'(uvm_cmdline_proc.get_arg_value({"+", cli_args}, cli_args_result));
   
endfunction : build_phase


function void uvml_logs_seq_item_logger_c::end_of_elaboration_phase(uvm_phase phase);
   
   uvm_component  parent = get_parent();
   
   super.end_of_elaboration_phase(phase);
   
   // Assemble final path
   if (name == "") begin
      fpath = {parent.get_full_name(), ".seq_item.", fextension};
   end
   else begin
      fpath = {parent.get_full_name(), name, ".seq_item.", fextension};
   end
   
   // Opem file handle and check 
   fhandle       = $fopen(fpath, "w");
   fhandle_valid = (fhandle != 0);
   
   print_header();
   
endfunction : end_of_elaboration_phase


function void uvml_logs_seq_item_logger_c::final_phase(uvm_phase phase);
   
   super.final_phase(phase);
   
   $fclose(fhandle);
   
endfunction : final_phase


function void uvml_logs_seq_item_logger_c::write(T_TRN t);
   
   `uvm_fatal("LOGGER", "Call to pure virtual function")
   
endfunction : write


function void uvml_logs_seq_item_logger_c::print_header();
   
   `uvm_fatal("LOGGER", "Call to pure virtual function")
   
endfunction : print_header


function void uvml_logs_seq_item_logger_c::fwrite(string msg);
   
   if (fhandle_valid) begin
      $fwrite(fhandle, {msg, "\n"});
   end
   
endfunction : fwrite


`endif // __UVML_LOGS_SEQ_ITEM_LOGGER_SV__
