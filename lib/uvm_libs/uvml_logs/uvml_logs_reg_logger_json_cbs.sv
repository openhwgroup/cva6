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


`ifndef __UVML_LOGS_REG_LOGGER_JSON_CBS_SV__
`define __UVML_LOGS_REG_LOGGER_JSON_CBS_SV__


/**
 * Callback implementation which logs all read/write debug info to disk.
 */
class uvml_logs_reg_logger_json_cbs_c extends uvml_logs_reg_logger_cbs_c;
   
   `uvm_object_utils(uvml_logs_reg_logger_json_cbs_c)
   
   
   /**
    * Opens log file for writing
    */
   extern function new(string name="uvml_logs_reg_logger_json_cbs");
   
   /**
    * TODO Describe uvml_logs_reg_logger_json_cbs_c::print_reg()
    */
   extern virtual function void print_reg(uvm_reg_item rw);
   
   /**
    * TODO Describe uvml_logs_reg_logger_json_cbs_c::print_reg_field()
    */
   extern virtual function void print_reg_field(uvm_reg_field field);
   
endclass


function uvml_logs_reg_logger_json_cbs_c::new(string name="uvml_logs_reg_logger_json_cbs");
   
   super.new(name);
   fname = "reg.json";
   
endfunction : new


function void uvml_logs_reg_logger_json_cbs_c::print_reg(uvm_reg_item rw);
   
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
      UVM_READ : access_str = "read";
      UVM_WRITE: access_str = "write";
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
   
   fwrite({"{",
      $sformatf("\"time\":\"%0t\","     , $realtime()),
      $sformatf("\"access\":\"%s\","    , access_str ),
      $sformatf("\"address\":\"0x%0h\",", addr_str   ),
      $sformatf("\"data\":\"0x%0h\","   , data_str   ),
      "\"fields\":["
   });
   
   reg_data.get_fields(sub_fields);
   foreach (sub_fields[ii]) begin
      print_reg_field(sub_fields[ii]);
   end
   
   fwrite("]}");
   
endfunction : print_reg


function void uvml_logs_reg_logger_json_cbs_c::print_reg_field(uvm_reg_field field);
   
   int unsigned  lsb = field.get_lsb_pos();
   int unsigned  msb = lsb + field.get_n_bits();
   
   string  bits_str = $sformatf("%02d:%02d", msb, lsb);
   string  data_str = $sformatf("0x%8h", field.get());
   
   fwrite({
      $sformatf("\"name\":\"%s\"," , field.get_name()),
      $sformatf("\"bits\":\"%s\",", bits_str        ),
      $sformatf("\"data\":\"%s\",", data_str        )
   });
   
endfunction : print_reg_field


`endif // __UVML_LOGS_REG_LOGGER_JSON_CBS_SV__

