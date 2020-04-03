// 
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
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


`ifndef __UVMA_CLKNRST_SEQ_ITEM_LOGGER_SV__
`define __UVMA_CLKNRST_SEQ_ITEM_LOGGER_SV__


/**
 * Component writing Clock & Reset sequence items debug data to disk as plain
 * text.
 */
class uvma_clknrst_seq_item_logger_c extends uvml_logs_seq_item_logger_c#(
   .T_TRN  (uvma_clknrst_seq_item_c),
   .T_CFG  (uvma_clknrst_cfg_c     ),
   .T_CNTXT(uvma_clknrst_cntxt_c   )
);
   
   `uvm_component_utils(uvma_clknrst_seq_item_logger_c)
   
   
   /**
    * Default constructor.
    */
   function new(string name="uvma_clknrst_seq_item_logger", uvm_component parent=null);
      
      super.new(name, parent);
      
   endfunction : new
   
   /**
    * Writes contents of t to disk.
    */
   virtual function void write(uvma_clknrst_seq_item_c t);
      
      string  action_str = "";
      string  period_str = "";
      
      case (t.action)
         UVMA_CLKNRST_SEQ_ITEM_ACTION_START_CLK: begin
            action_str = "START CLK ";
            period_str = $sformatf("%0t", t.clk_period);
         end
         
         UVMA_CLKNRST_SEQ_ITEM_ACTION_STOP_CLK: begin
            action_str = "STOP  CLK ";
         end
         
         UVMA_CLKNRST_SEQ_ITEM_ACTION_ASSERT_RESET: begin
            action_str = "ASSERT RST";
            period_str = $sformatf("%0t", t.rst_deassert_period);
         end
      endcase
      
      fwrite($sformatf(" %t | %s | %s |", $realtime(), action_str, period_str));
      
   endfunction : write
   
   /**
    * Writes log header to disk.
    */
   virtual function void print_header();
      
      fwrite("--------------------------------");
      fwrite("    TIME    |  ACTION  | PERIOD ");
      fwrite("--------------------------------");
      
   endfunction : print_header
   
endclass : uvma_clknrst_seq_item_logger_c


/**
 * Component writing Clock & Reset monitor transactions debug data to disk as
 * JavaScript Object Notation (JSON).
 */
class uvma_clknrst_seq_item_logger_json_c extends uvma_clknrst_seq_item_logger_c;
   
   `uvm_component_utils(uvma_clknrst_seq_item_logger_json_c)
   
   
   /**
    * Set file extension to '.json'.
    */
   function new(string name="uvma_clknrst_seq_item_logger_json", uvm_component parent=null);
      
      super.new(name, parent);
      fextension = "json";
      
   endfunction : new
   
   /**
    * Writes contents of t to disk.
    */
   virtual function void write(uvma_clknrst_seq_item_c t);
      
      string  action_str = "";
      string  period_str = "";
      
      case (t.action)
         UVMA_CLKNRST_SEQ_ITEM_ACTION_START_CLK: begin
            action_str = "START CLK ";
            period_str = $sformatf("%0t", t.clk_period);
         end
         
         UVMA_CLKNRST_SEQ_ITEM_ACTION_STOP_CLK: begin
            action_str = "STOP  CLK ";
         end
         
         UVMA_CLKNRST_SEQ_ITEM_ACTION_ASSERT_RESET: begin
            action_str = "ASSERT RST";
            period_str = $sformatf("%0t", t.rst_deassert_period);
         end
      endcase
      
      fwrite({"{",
         $sformatf("\"time\":\"%0t\",", $realtime()),
         $sformatf("\"action\":%s,"   , action_str ),
         $sformatf("\"period\":%s,"   , period_str ),
      "},"});
      
   endfunction : write
   
   /**
    * Empty function.
    */
   virtual function void print_header();
      
      // Do nothing: JSON files do not use headers.
      
   endfunction : print_header
   
endclass : uvma_clknrst_seq_item_logger_json_c


`endif // __UVMA_CLKNRST_SEQ_ITEM_LOGGER_SV__
