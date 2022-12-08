// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)


`ifndef __UVMA_AXI_SEQ_ITEM_LOGGER_SV__
`define __UVMA_AXI_SEQ_ITEM_LOGGER_SV__


/**
 * Component writing Open Bus Interface sequence items debug data to disk as plain text.
 */
class uvma_axi_seq_item_logger_c extends uvml_logs_seq_item_logger_c #(
   .T_TRN  (uvma_axi_base_seq_item_c),
   .T_CFG  (uvma_axi_cfg_c          ),
   .T_CNTXT(uvma_axi_cntxt_c        )
);

   `uvm_component_utils(uvma_axi_seq_item_logger_c)


   /**
    * Default constructor.
    */
   function new(string name="uvma_axi_seq_item_logger", uvm_component parent=null);
      super.new(name, parent);
   endfunction : new

   /**
    * Writes contents of t to disk.
    */
   virtual function void write(uvma_axi_base_seq_item_c trs);
      if(cntxt.reset_state == UVMA_AXI_RESET_STATE_POST_RESET)begin

         string write_address_access = "";
         string aw_access_type  = "";
         string aw_address   = "";
         string aw_id_str     = "";

         string write_data_access = "";
         string w_data    = "";
         string w_access_complet = "";

         string write_response_access = "";
         string b_err    = "";
         string b_id_str     = "";

         string read_address_access = "";
         string ar_access_type  = "";
         string ar_address   = "";
         string ar_id_str     = "";

         string read_data_access = "";
         string r_err    = "";
         string r_data   = "";
         string r_id_str     = "";
         string r_access_complet = "";

         if(trs.aw_valid && trs.aw_ready) begin

            write_address_access = "write_address_access";
            if(trs.aw_lock) begin
               aw_access_type = "Exclusive_access";
            end else begin
               aw_access_type = "Normal_access";
            end
            aw_address = $sformatf("%h", trs.aw_addr);
            aw_id_str = $sformatf("%b", trs.aw_id);
            fwrite($sformatf("----> %t | %s | %s | %s | %s", $realtime(), write_address_access, aw_address, aw_access_type, aw_id_str));

         end else begin

            write_address_access = "";
            aw_access_type  = "";
            aw_address   = "";
            aw_id_str     = "";

         end

         if(trs.w_valid && trs.w_ready) begin

            write_data_access = "write_data_access";
            w_data = $sformatf("%h", trs.w_data);
            if(trs.w_last) begin
               w_access_complet = "Yes";
            end else begin
               w_access_complet = "No";
            end
            fwrite($sformatf("----> %t | %s | %s | %s", $realtime(), write_data_access, w_data, w_access_complet));

         end else begin

            write_data_access = "";
            w_data  = "";
            w_access_complet   = "";

         end

         if(trs.b_valid && trs.b_ready) begin

            write_response_access = "write_response_access";
            case (trs.b_resp)
               00 : b_err = "No Err";
               01 : b_err  = "Err";
               10 : b_err  = "Err";
               11 : b_err  = "Err";
               default : b_err = " ? ";
            endcase
            b_id_str = $sformatf("%b", trs.b_id);
            fwrite($sformatf("----> %t | %s | __ | %s | __ | %s", $realtime(), write_response_access, b_id_str, b_err));

         end else begin

            write_response_access = "";
            b_err  = "";
            b_id_str     = "";

         end

         if(trs.ar_valid && trs.ar_ready) begin

            read_address_access = "read_address_access";
            if(trs.ar_lock) begin
               ar_access_type = "Exclusive_access";
            end else begin
               ar_access_type = "Normal_access";
            end
            ar_address = $sformatf("%h", trs.ar_addr);
            ar_id_str = $sformatf("%b", trs.ar_id);
            fwrite($sformatf("----> %t | %s | %s | %s | %s", $realtime(), read_address_access, ar_address, ar_access_type, ar_id_str));

         end else begin

            read_address_access = "";
            ar_address  = "";
            ar_access_type  = "";
            ar_id_str     = "";

         end

         if(trs.r_valid && trs.r_ready) begin

            read_data_access = "read_data_access";
            r_data = $sformatf("%h", trs.r_data);
            r_id_str = $sformatf("%b", trs.r_id);
            if(trs.r_last) begin
               r_access_complet = "Yes";
            end else begin
               r_access_complet = "No";
            end
            case (trs.r_resp)
               00 : r_err = "No Err";
               01 : r_err  = "Err";
               10 : r_err  = "Err";
               11 : r_err  = "Err";
               default : r_err = " ? ";
            endcase
            fwrite($sformatf("----> %t | %s | %s | %s | %s | %s", $realtime(), read_data_access, r_data, r_access_complet, r_id_str, r_err));

         end else begin

            read_data_access = "";
            r_data  = "";
            r_access_complet   = "";
            r_err   = "";
            r_id_str     = "";

         end
      end
   endfunction : write

// A significant chunk of the write_mstr method is common between this
// sequence item logger and the monitor transaction logger.  Given that
// much of this code is template generated, and is not expected to be edited
// further, the duplicated code has a lint waiver.
//
//@DVT_LINTER_WAIVER_START "MT20210901_2" disable SVTB.33.1.0, SVTB.33.2.0
   /**
    * Writes contents of mstr t to disk.
    */

   /**
    * Writes log header to disk.
    */
   virtual function void print_header();

      fwrite("-------------------------------------------------------------------------------------------");
      fwrite("        TIME        | AW/W/B/AR/R | ADDRESS : AW/AR | ACCESS TYPE : AW/AR | ID | ERR : B/R ");
      fwrite("        TIME        |   ACCESS    |  DATA   : W/R   | LAST DATA   : W/R   |    |           ");
      fwrite("-------------------------------------------------------------------------------------------");

   endfunction : print_header

endclass : uvma_axi_seq_item_logger_c

/**
 * Component writing Open Bus Interface monitor transactions debug data to disk as JavaScript Object Notation (JSON).
 */
class uvma_axi_seq_item_logger_json_c extends uvma_axi_seq_item_logger_c;

   `uvm_component_utils(uvma_axi_seq_item_logger_json_c)

   /**
    * Set file extension to '.json'.
    */
   function new(string name="uvma_axi_seq_item_logger_json", uvm_component parent=null);

      super.new(name, parent);
      fextension = "json";

   endfunction : new

   /**
    * Writes contents of t to disk.
    */
   virtual function void write(uvma_axi_base_seq_item_c t);

      // TODO Implement uvma_obi_memory_seq_item_logger_json_c::write()
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

endclass : uvma_axi_seq_item_logger_json_c


`endif // __UVMA_AXI_SEQ_ITEM_LOGGER_SV__
