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


`ifndef __UVMA_CLKNRST_MON_TRN_LOGGER_SV__
`define __UVMA_CLKNRST_MON_TRN_LOGGER_SV__


/**
 * Component writing Clock & Reset monitor transactions debug data to disk as
 * plain text.
 */
class uvma_clknrst_mon_trn_logger_c extends uvml_logs_mon_trn_logger_c#(
   .T_TRN  (uvma_clknrst_mon_trn_c),
   .T_CFG  (uvma_clknrst_cfg_c    ),
   .T_CNTXT(uvma_clknrst_cntxt_c  )
);
   
   `uvm_component_utils(uvma_clknrst_mon_trn_logger_c)
   
   
   /**
    * Default constructor.
    */
   function new(string name="uvma_clknrst_mon_trn_logger", uvm_component parent=null);
      
      super.new(name, parent);
      
   endfunction : new
   
   /**
    * Writes contents of t to disk
    */
   virtual function void write(uvma_clknrst_mon_trn_c t);
      
      string  event_str       = "";
      string  clk_period_str  = "";
      string  reset_pulse_str = "";
      
      case (t.event_type)
         UVMA_CLKNRST_MON_TRN_EVENT_CLK_STARTED: begin
            event_str       = "CLK START";
            clk_period_str  = $sformatf("%0t", t.clk_period);
         end
         
         UVMA_CLKNRST_MON_TRN_EVENT_CLK_STOPPED: begin
            event_str = "CLK STOP";
         end
         
         UVMA_CLKNRST_MON_TRN_EVENT_RESET_ASSERTED: begin
            event_str = "RST ASSRT";
         end
         
         UVMA_CLKNRST_MON_TRN_EVENT_RESET_DEASSERTED: begin
            event_str       = "RST DEASRT";
            reset_pulse_str = $sformatf("%0d", t.reset_pulse_length);
         end
      endcase
      
      fwrite($sformatf(" %t | %s | %s | %s |", $realtime(), event_str, clk_period_str, reset_pulse_str));
      
   endfunction : write
   
   /**
    * Writes log header to disk
    */
   virtual function void print_header();
      
      fwrite("----------------------------------------------------");
      fwrite("   TIME   | EVENT | CLK PERIOD | RESET PULSE LENGTH ");
      fwrite("----------------------------------------------------");
      
   endfunction : print_header
   
endclass : uvma_clknrst_mon_trn_logger_c


/**
 * Component writing CLKNRST monitor transactions debug data to disk as
 * JavaScript Object Notation (JSON).
 */
class uvma_clknrst_mon_trn_logger_json_c extends uvma_clknrst_mon_trn_logger_c;
   
   `uvm_component_utils(uvma_clknrst_mon_trn_logger_json_c)
   
   
   /**
    * Set file extension to '.json'.
    */
   function new(string name="uvma_clknrst_mon_trn_logger_json", uvm_component parent=null);
      
      super.new(name, parent);
      fextension = "json";
      
   endfunction : new
   
   /**
    * Writes contents of t to disk.
    */
   virtual function void write(uvma_clknrst_mon_trn_c t);
      
      string  event_str       = "";
      string  clk_period_str  = "";
      string  reset_pulse_str = "";
      
      case (t.event_type)
         UVMA_CLKNRST_MON_TRN_EVENT_CLK_STARTED: begin
            event_str       = "CLK START";
            clk_period_str  = $sformatf("%0t", t.clk_period);
         end
         
         UVMA_CLKNRST_MON_TRN_EVENT_CLK_STOPPED: begin
            event_str = "CLK STOP";
         end
         
         UVMA_CLKNRST_MON_TRN_EVENT_RESET_ASSERTED: begin
            event_str = "RST ASSRT";
         end
         
         UVMA_CLKNRST_MON_TRN_EVENT_RESET_DEASSERTED: begin
            event_str       = "RST DEASRT";
            reset_pulse_str = $sformatf("%0d", t.reset_pulse_length);
         end
      endcase
      
      fwrite({"{",
         $sformatf("\"time\":\"%0t\","         , $realtime()    ),
         $sformatf("\"event\":%h,"             , event_str      ),
         $sformatf("\"clock period\":%b,"      , clk_period_str ),
         $sformatf("\"reset pulse length\":%d,", reset_pulse_str),
      "},"});
      
   endfunction : write
   
   /**
    * Empty function.
    */
   virtual function void print_header();
      
      // Do nothing: JSON files do not use headers.
      
   endfunction : print_header
   
endclass : uvma_clknrst_mon_trn_logger_json_c


`endif // __UVMA_CLKNRST_MON_TRN_LOGGER_SV__
