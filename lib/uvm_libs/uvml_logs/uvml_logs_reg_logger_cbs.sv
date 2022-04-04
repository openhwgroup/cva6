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


`ifndef __UVML_LOGS_REG_LOGGER_CBS_SV__
`define __UVML_LOGS_REG_LOGGER_CBS_SV__


/**
 * Callback implementation which logs all read/write debug info to disk.
 */
class uvml_logs_reg_logger_cbs_c extends uvm_reg_cbs;
   
   // IO constants
   string  cli_args  = "SIM_DIR_RESULTS";
   string  fname     = "reg.log";
   
   // IO variables
   bit           fopen_attempted = 0;
   bit           fhandle_valid   = 0;
   int unsigned  fhandle         = 0;
   string        cli_args_result = "";
   string        fpath           = "";
   
   
   `uvm_object_utils_begin(uvml_logs_reg_logger_cbs_c)
     `uvm_field_string(cli_args, UVM_DEFAULT)
     `uvm_field_string(fname   , UVM_DEFAULT)
     
     `uvm_field_int   (fhandle_valid  , UVM_DEFAULT)
     `uvm_field_int   (fhandle        , UVM_DEFAULT)
     `uvm_field_string(cli_args_result, UVM_DEFAULT)
     `uvm_field_string(fpath          , UVM_DEFAULT)
   `uvm_object_utils_end
   
   
   /**
    * Opens log file for writing
    */
   extern function new(string name="uvml_logs_reg_logger_cbs");
   
   /**
    * TODO Describe uvml_logs_reg_logger_cbs_c::post_read()
    */
   extern virtual task post_read(uvm_reg_item rw);
   
   /**
    * TODO Describe uvml_logs_reg_logger_cbs_c::post_write()
    */
   extern virtual task post_write(uvm_reg_item rw);
   
   /**
    * TODO Describe uvml_logs_reg_logger_cbs_c::print_reg()
    */
   extern virtual function void print_reg(uvm_reg_item rw);
   
   /**
    * TODO Describe uvml_logs_reg_logger_cbs_c::print_reg_field()
    */
   extern virtual function void print_reg_field(uvm_reg_field field);
   
   /**
    * Obtains IO file handle
    */
   extern virtual function void fopen();
   
   /**
    * Writes msg to disk
    */
   // Waiving Verissimo linter SVTB.32.2.0: Pass strings by reference unless otherwise needed
   extern function void fwrite(string msg); //@DVT_LINTER_WAIVER "MT20211228_7" disable SVTB.32.2.0
   
endclass


function uvml_logs_reg_logger_cbs_c::new(string name="uvml_logs_reg_logger_cbs");
   
   uvm_cmdline_processor  cli_proc = uvm_cmdline_processor::get_inst();
   
   super.new(name);
   
   // Retrieve simulation path from CLI argument
   void'(cli_proc.get_arg_value({"+", cli_args}, cli_args_result));
   
endfunction : new


task uvml_logs_reg_logger_cbs_c::post_read(uvm_reg_item rw);
   
   super.post_read(rw);
   fopen();
   print_reg(rw);
   
endtask : post_read


task uvml_logs_reg_logger_cbs_c::post_write(uvm_reg_item rw);
   
   super.post_write(rw);
   fopen();
   print_reg(rw);
   
endtask : post_write


function void uvml_logs_reg_logger_cbs_c::print_reg(uvm_reg_item rw);
   
   bit            done = 0;
   uvm_reg_block  reg_block_data;
   uvm_reg        reg_data;
   uvm_reg_field  field_data;
   uvm_reg_field  sub_fields[$];
   
   string  access_str   = "";
   string  addr_str     = "";
   string  data_str     = "";
   string  reg_name_str = "";
   
   case(rw.element_kind)
     UVM_REG: begin
       if (!$cast(reg_data, rw.element)) begin
         `uvm_fatal("REG_CB", $sformatf("Failed to cast rw.element (%s) into reg_data (%s)", $typename(rw.element), $typename(reg_data)))
       end
     end
     
     UVM_FIELD: begin
       if (!$cast(field_data, rw.element)) begin
         `uvm_fatal("REG_CB", $sformatf("Failed to cast rw.element (%s) into field_data (%s)", $typename(rw.element), $typename(field_data)))
       end
       reg_data = field_data.get_parent();
     end
     
     default: return;
   endcase
   
   // Prepare strings
   case(rw.kind)
     UVM_READ : access_str = "R";
     UVM_WRITE: access_str = "W";
   endcase
   addr_str = $sformatf("0x%8h", reg_data.get_address());
   data_str = $sformatf("0x%8h", reg_data.get());
   
   reg_name_str   = reg_data.get_name();
   reg_block_data = reg_data.get_parent();
   
   do begin
     if (reg_block_data != null) begin
       reg_name_str = {reg_block_data.get_name(), ".", reg_name_str};
       reg_block_data = reg_block_data.get_parent();
     end
     else begin
       done = 1;
     end
   end while (done);
   
   fwrite($sformatf("%0t", $realtime()));
   fwrite("|ACC|----ADDR----|----DATA----|");
   fwrite($sformatf("| %s | %s | %s | %s", access_str, addr_str, data_str, reg_name_str));
   fwrite("|---|------------|------------|");
   
   reg_data.get_fields(sub_fields);
   foreach (sub_fields[ii]) begin
     print_reg_field(sub_fields[ii]);
   end
   
   fwrite("");
   
endfunction : print_reg


function void uvml_logs_reg_logger_cbs_c::print_reg_field(uvm_reg_field field);
   
   int unsigned  lsb = field.get_lsb_pos();
   int unsigned  msb = lsb + field.get_n_bits();
   
   string  bits_str = $sformatf("%02d:%02d", msb, lsb);
   string  data_str = $sformatf("0x%8h", field.get());
   
   fwrite($sformatf("        %s      %s   %s", bits_str, data_str, field.get_name()));
   
endfunction : print_reg_field


function void uvml_logs_reg_logger_cbs_c::fopen();
   
   if (!fopen_attempted) begin
      fopen_attempted = 1;
      
      // Assemble final path
      fpath = {cli_args_result, "/", fname};
      
      // Open file handle and check validity
      fhandle       = $fopen(fpath, "w");
      fhandle_valid = (fhandle != 0);
   end
   
endfunction : fopen


function void uvml_logs_reg_logger_cbs_c::fwrite(string msg);
   
   if (fhandle_valid) begin
      $fwrite(fhandle, {msg, "\n"});
   end
   
endfunction : fwrite


`endif // __UVML_LOGS_REG_LOGGER_CBS_SV__

