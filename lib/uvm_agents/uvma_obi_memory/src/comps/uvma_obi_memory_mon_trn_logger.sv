// 
// Copyright 2021 OpenHW Group
// Copyright 2021 Datum Technology Corporation
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// 
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may
// not use this file except in compliance with the License, or, at your option,
// the Apache License version 2.0. You may obtain a copy of the License at
// 
//     https://solderpad.org/licenses/SHL-2.1/
// 
// Unless required by applicable law or agreed to in writing, any work
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
// License for the specific language governing permissions and limitations
// under the License.
// 


`ifndef __UVMA_OBI_MEMORY_MON_TRN_LOGGER_SV__
`define __UVMA_OBI_MEMORY_MON_TRN_LOGGER_SV__


/**
 * Component writing Open Bus Interface monitor transactions debug data to disk as plain text.
 */
class uvma_obi_memory_mon_trn_logger_c extends uvml_logs_mon_trn_logger_c#(
   .T_TRN  (uvma_obi_memory_mon_trn_c),
   .T_CFG  (uvma_obi_memory_cfg_c    ),
   .T_CNTXT(uvma_obi_memory_cntxt_c  )
);
   
   `uvm_component_utils(uvma_obi_memory_mon_trn_logger_c)
   
   
   /**
    * Default constructor.
    */
   function new(string name="uvma_obi_memory_mon_trn_logger", uvm_component parent=null);
      
      super.new(name, parent);
      
   endfunction : new
   
   /**
    * Writes contents of t to disk
    */
   virtual function void write(uvma_obi_memory_mon_trn_c t);
      
      string access_str = "";
      string err_str    = "";
      string be_str     = "";
      string data_str   = "";
      string auser_str  = "";
      string wuser_str  = "";
      string ruser_str  = "";
      string id_str     = "";
      
      case (t.access_type)
         UVMA_OBI_MEMORY_ACCESS_READ : access_str = "R  ";
         UVMA_OBI_MEMORY_ACCESS_WRITE: access_str = "  W";
         default              : access_str = " ? ";
      endcase
      
      case (t.err)
         0: err_str = "    ";
         1: err_str = " ERR";
      endcase
      
      case (t.access_type)
         UVMA_OBI_MEMORY_ACCESS_READ : ruser_str = $sformatf("%h", t.ruser);
         UVMA_OBI_MEMORY_ACCESS_WRITE: wuser_str = $sformatf("%h", t.wuser);
      endcase
      
      data_str  = $sformatf("%b", t.data );
      auser_str = $sformatf("%h", t.auser);
      be_str    = $sformatf("%b", t.be   );
      id_str    = $sformatf("%b", t.id   );
      
      fwrite($sformatf(" %t | %s | %s | %s | %s | %s | %s | %h | %s | %s ", $realtime(), access_str, id_str, auser_str, wuser_str, ruser_str, err_str, t.address, be_str, data_str));
      
   endfunction : write
   
   /**
    * Writes log header to disk
    */
   virtual function void print_header();
      
      fwrite("---------------------------------------------------------------------------------");
      fwrite("        TIME        | R/W |  ID  | AUSER | WUSER | RUSER | ERR | ADDRESS  |  BE  | DATA");
      fwrite("---------------------------------------------------------------------------------");
      
   endfunction : print_header
   
endclass : uvma_obi_memory_mon_trn_logger_c


/**
 * Component writing OBI monitor transactions debug data to disk as JavaScript Object Notation (JSON).
 */
class uvma_obi_memory_mon_trn_logger_json_c extends uvma_obi_memory_mon_trn_logger_c;
   
   `uvm_component_utils(uvma_obi_memory_mon_trn_logger_json_c)
   
   
   /**
    * Set file extension to '.json'.
    */
   function new(string name="uvma_obi_memory_mon_trn_logger_json", uvm_component parent=null);
      
      super.new(name, parent);
      fextension = "json";
      
   endfunction : new
   
   /**
    * Writes contents of t to disk.
    */
   virtual function void write(uvma_obi_memory_mon_trn_c t);
      
      // TODO Implement uvma_obi_memory_mon_trn_logger_json_c::write()
      // Ex: fwrite({"{",
      //       $sformatf("\"time\":\"%0t\",", $realtime()),
      //       $sformatf("\"a\":%h,"        , t.a        ),
      //       $sformatf("\"b\":%b,"        , t.b        ),
      //       $sformatf("\"c\":%d,"        , t.c        ),
      //       $sformatf("\"d\":%h,"        , t.c        ),
      //     "},"});
      
   endfunction : write
   
   /**
    * Empty function.
    */
   virtual function void print_header();
      
      // Do nothing: JSON files do not use headers.
      
   endfunction : print_header
   
endclass : uvma_obi_memory_mon_trn_logger_json_c


`endif // __UVMA_OBI_MEMORY_MON_TRN_LOGGER_SV__
