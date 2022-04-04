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

      string format_header_str_1p1 = "%15s | %6s | %2s | %8s | %4s | %8s";
      string format_header_str_1p2 = "%15s | %6s | %2s | %8s | %4s | %8s | %2s | %2s | %2s | %2s | %2s | %2s | %2s";
      string log_msg;

      // Log the 1p1 signals
      log_msg = $sformatf("%15s | %6s | %2s | %08x |  %1x | %8s",
                          $sformatf("%t", $time),
                          cfg.mon_logger_name,
                          t.access_type == UVMA_OBI_MEMORY_ACCESS_READ ? "R" : "W",
                          t.address,
                          t.be,
                          t.get_data_str());


      if (cfg.version == UVMA_OBI_MEMORY_VERSION_1P2) begin
         log_msg = $sformatf("%s | %2x |    %1x |   %2x | %3s",
                             log_msg,
                             t.aid,
                             t.prot,
                             t.atop,
                             t.err ? "ERR" : "OK");
         if (cfg.auser_width > 0)
            log_msg = $sformatf("%s |     %1x", log_msg, t.auser);
         if (cfg.wuser_width > 0)
            log_msg = $sformatf("%s |     %1x", log_msg, t.wuser);
         if (cfg.ruser_width > 0)
            log_msg = $sformatf("%s |     %1x", log_msg, t.ruser);
      end

      fwrite(log_msg);

   endfunction : write

   /**
    * Writes log header to disk
    */
   virtual function void print_header();

      if (cfg.version == UVMA_OBI_MEMORY_VERSION_1P1) begin
         string banner_str = {80{"-"}};
         string format_header_str_1p1 = "%15s | %6s | %2s | %8s | %2s | %8s";


         fwrite(banner_str);
         fwrite($sformatf(format_header_str_1p1,
                          "TIME", "OBI", "RW", "ADDR", "BE", "DATA"));
         fwrite(banner_str);
      end
      else begin
         string banner_str = {106{"-"}};
         string format_header_str_1p2 = "%15s | %6s | %2s | %8s | %2s | %8s | %2s | %2s | %2s | %2s";
         string header_str;

         header_str = $sformatf(format_header_str_1p2,
                                "TIME", "OBI", "RW", "ADDR", "BE", "DATA",
                                "ID", "PROT", "ATOP", "ERR");

         if (cfg.auser_width > 0)
            header_str = $sformatf("%s | %2s", header_str, "AUSER");
         if (cfg.ruser_width > 0)
            header_str = $sformatf("%s | %2s", header_str, "RUSER");
         if (cfg.wuser_width > 0)
            header_str = $sformatf("%s | %2s", header_str, "WUSER");

         fwrite(banner_str);
         fwrite(header_str);
         fwrite(banner_str);
      end

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
