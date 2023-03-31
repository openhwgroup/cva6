// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)

//=============================================================================
// Description: Sequence for agent axi_r
//=============================================================================

`ifndef UVMA_AXI_R_SEQ_SV
`define UVMA_AXI_R_SEQ_SV

class uvma_axi_r_seq_c extends uvm_sequence#(uvma_axi_r_item_c);


   int i = 0;

   `uvm_object_utils(uvma_axi_r_seq_c)
   `uvm_declare_p_sequencer(uvma_axi_r_sqr_c)

   // Agent handles
   uvma_axi_cfg_c    cfg;
   uvma_axi_cntxt_c  cntxt;

   uvma_axi_r_item_c  resp_item;
   uvma_axi_r_item_c  pre_resp;
   uvma_axi_ar_item_c req_item;
   uvma_axi_ar_item_c req_requette[][];

   int selected_id;
   int ar_id_tr[];
   int enable_change_id = 1;
   bit[1:0] inject_error;
   int selected_indice = 0;
   int status[];
   int r_latency;


   extern function new(string name = "");
   extern function void create_item();
   extern task body();
   extern function int  check_tab(int tab[]);
   extern function void prepare_resp(uvma_axi_ar_item_c req_item, uvma_axi_r_item_c resp_item, int error);
   extern function int  select_first_id(int tab[], int id);

endclass : uvma_axi_r_seq_c

function uvma_axi_r_seq_c::new(string name = "");

   super.new(name);

endfunction : new

function void uvma_axi_r_seq_c::create_item();

   resp_item = uvma_axi_r_item_c::type_id::create("resp_item");
   pre_resp = uvma_axi_r_item_c::type_id::create("pre_resp");
   req_item = uvma_axi_ar_item_c::type_id::create("req_item");

endfunction : create_item

task uvma_axi_r_seq_c::body();

   create_item();

   forever begin

      cfg   = p_sequencer.cfg  ;
      cntxt = p_sequencer.cntxt;

      `uvm_info(get_type_name(), "READ DATA sequence starting", UVM_HIGH)

      p_sequencer.ar_req_export.get(req_item);
      p_sequencer.r_resp_fifo.get(pre_resp);

      start_item(resp_item);

         if(req_item.ar_valid && req_item.ar_ready) begin

            `uvm_info(get_type_name(), "Read request registere", UVM_HIGH)
            if(req_item.ar_id >= ar_id_tr.size()) begin

               ar_id_tr = new[req_item.ar_id+1] (ar_id_tr);
               ar_id_tr[req_item.ar_id] = 1;
               req_requette = new[req_item.ar_id + 1] (req_requette);
               req_requette[req_item.ar_id] = new[1];
               req_requette[req_item.ar_id][0] = new req_item;

            end else begin

               ar_id_tr[req_item.ar_id]++;
               req_requette[req_item.ar_id] = new[ar_id_tr[req_item.ar_id]] (req_requette[req_item.ar_id]);
               req_requette[req_item.ar_id][ar_id_tr[req_item.ar_id] - 1] = new req_item;

            end
            `uvm_info(get_type_name(), "Read request registred", UVM_HIGH)
            status = new[status.size() + 1] (status);
            status[status.size() - 1] = req_item.ar_id;
         end

         if(enable_change_id == 1) begin
            selected_id = check_tab(status);
            inject_error = cfg.random_err();
            r_latency = -1;
         end

         if(r_latency > -1 && pre_resp.r_ready && selected_id != -1) begin

            `uvm_info(get_type_name(), "transfert termine", UVM_HIGH)
            if(ar_id_tr[selected_id] > 0) begin
               if(resp_item.r_last  == 1'b1) begin

                  foreach(req_requette[i,j]) begin
                     if(j < req_requette[selected_id].size()-1) begin
                        req_requette[selected_id][j] = req_requette[selected_id][j+1];
                     end
                  end
                  req_requette[selected_id] = new[ar_id_tr[selected_id] - 1] (req_requette[selected_id]);

                  ar_id_tr[selected_id]--;

                  selected_indice = select_first_id(status, selected_id);
                  foreach(status[j]) begin
                     if(selected_indice + j < status.size()-1) begin
                        status[selected_indice + j] = status[selected_indice + j + 1];
                     end
                  end
                  status = new[status.size() - 1] (status);

               end
            end

            selected_id = check_tab(status);
            inject_error = cfg.random_err();
            r_latency = -1;

            if(selected_id == -1) begin
               enable_change_id = 1;
            end else begin
               enable_change_id = 0;
            end

         end

         `uvm_info(get_type_name(), $sformatf("selected id = %d || LATENCY = %d",selected_id, r_latency), UVM_HIGH)

         if(selected_id != -1) begin
            if(r_latency == -1) begin

			   `uvm_info(get_type_name(), "read item", UVM_HIGH)
               prepare_resp(req_requette[selected_id][0], resp_item, inject_error);
               if(req_requette[selected_id][0].ar_len == 0) begin
                  `uvm_info(get_type_name()," last will be asserted ",UVM_HIGH)
                  resp_item.r_last  = 1'b1;
               end else begin
                  req_requette[selected_id][0].ar_len--;
                  resp_item.r_last  = 1'b0;
                  req_requette[selected_id][0].ar_addr = req_requette[selected_id][0].ar_addr + 2**req_requette[selected_id][0].ar_size;
               end
               enable_change_id = 0;

            end
            r_latency++;
         end else begin
            resp_item.r_id    = 0;
            resp_item.r_data  = 0;
            resp_item.r_resp  = 0;
            resp_item.r_valid = 1'b0;
            resp_item.r_user  = 1'b0;
            resp_item.r_last  = 1'b0;
         end

      finish_item(resp_item);
   end
   `uvm_info(get_type_name(), "Default sequence completed", UVM_HIGH)

endtask : body

function void uvma_axi_r_seq_c::prepare_resp(uvma_axi_ar_item_c req_item, uvma_axi_r_item_c resp_item, int error);

   resp_item.r_id = req_item.ar_id;
   for(int i = 0; i < 2**req_item.ar_size; i++) begin
         resp_item.r_data [((i+1)*8-1)-:8]   = cntxt.mem.read(req_item.ar_addr + i);
         if($isunknown(resp_item.r_data[((i+1)*8-1)-:8])) begin
            resp_item.r_data[((i+1)*8-1)-:8] = 2'h00;
         end
   end
   resp_item.r_resp  = error;
   resp_item.r_valid = 1'b1;
   resp_item.r_user  = 1'b0;

endfunction : prepare_resp

function int uvma_axi_r_seq_c::check_tab(int tab[]);
   int j = -1;
   if (status.size() != 0) begin
      j = status[0];
   end
   return j;
endfunction : check_tab

function int uvma_axi_r_seq_c::select_first_id(int tab[], int id);
   int j = -1;
   foreach(tab[i]) begin
      if(tab[i] == id) begin
         j = i;
         return j;
      end
   end
   return j;
endfunction : select_first_id

`endif
