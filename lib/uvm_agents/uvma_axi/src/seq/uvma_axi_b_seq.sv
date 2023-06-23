// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)


//=============================================================================
// Description: Sequence for agent axi_b
//=============================================================================

`ifndef UVMA_AXI_B_SEQ_SV
`define UVMA_AXI_B_SEQ_SV

class uvma_axi_b_seq_c extends uvm_sequence#(uvma_axi_b_item_c);

   `uvm_object_utils(uvma_axi_b_seq_c)
   `uvm_declare_p_sequencer(uvma_axi_b_sqr_c)

   // Agent handles
   uvma_axi_cfg_c    cfg;
   uvma_axi_cntxt_c  cntxt;

   uvma_axi_b_item_c   b_resp_item;
   uvma_axi_b_item_c   b_preresp_item;
   uvma_axi_aw_item_c  aw_req_item;
   uvma_axi_aw_item_c  req_requette[][];
   uvma_axi_w_item_c   w_req_item;

   int aw_id_tr[];
   int req_status[][];
   int status[];
   int first_req = 0;
   int selected_id;
   int enable_change_id = 1;
   bit[1:0] inject_error;

   extern function new(string name = "");
   extern function void create_item();
   extern task body();
   extern function int check_tab(int tab[]);

endclass : uvma_axi_b_seq_c

function uvma_axi_b_seq_c::new(string name = "");
   super.new(name);
endfunction : new

function void uvma_axi_b_seq_c::create_item();

   b_resp_item = uvma_axi_b_item_c::type_id::create("b_resp_item");
   b_preresp_item = uvma_axi_b_item_c::type_id::create("b_preresp_item");
   aw_req_item = uvma_axi_aw_item_c::type_id::create("aw_req_item");
   w_req_item = uvma_axi_w_item_c::type_id::create("w_req_item");

endfunction : create_item

task uvma_axi_b_seq_c::body();

   create_item();

   forever begin

      cfg   = p_sequencer.cfg  ;
      cntxt = p_sequencer.cntxt;

      `uvm_info(get_type_name(), "WRITE RESPONSE sequence starting", UVM_HIGH)

      p_sequencer.aw_req_export.get(aw_req_item);
      p_sequencer.w_req_export.get(w_req_item);
      p_sequencer.b_resp_fifo.get(b_preresp_item);

      start_item(b_resp_item);

          if(aw_req_item.aw_valid && aw_req_item.aw_ready) begin

            `uvm_info(get_type_name(), "read request registere", UVM_HIGH)
            if(aw_req_item.aw_id >= aw_id_tr.size()) begin

               aw_id_tr = new[aw_req_item.aw_id+1] (aw_id_tr);
               aw_id_tr[aw_req_item.aw_id] = 1;
               req_requette = new[aw_req_item.aw_id + 1] (req_requette);
               req_requette[aw_req_item.aw_id] = new[1];
               req_requette[aw_req_item.aw_id][0] = new aw_req_item;

            end else begin

               aw_id_tr[aw_req_item.aw_id]++;
               req_requette[aw_req_item.aw_id] = new[aw_id_tr[aw_req_item.aw_id]] (req_requette[aw_req_item.aw_id]);
               req_requette[aw_req_item.aw_id][aw_id_tr[aw_req_item.aw_id] - 1] = new aw_req_item;

            end

            req_status = new[req_status.size() + 1] (req_status);
            req_status[req_status.size() - 1] = new[aw_req_item.aw_id + 1];
            req_status[req_status.size() - 1][aw_req_item.aw_id] = 1;

            `uvm_info(get_type_name(), "read request registred", UVM_HIGH)
         end

         if((w_req_item.w_valid && w_req_item.w_ready && w_req_item.w_last) || (first_req == 1)) begin

            `uvm_info(get_type_name(), "write data registred", UVM_HIGH)
            if(req_status.size() != 0) begin

               foreach(req_status[i,j]) begin

                  if(req_status[0][j] == 1) begin
                     status = new[status.size() + 1] (status);
                     status[status.size() - 1] = j;
                  end

               end

               foreach(req_status[i,j]) begin
                  if(i < req_status.size()-1) begin
                     req_status[i] = req_status[i+1];
                  end
               end
               req_status = new[req_status.size() - 1] (req_status);
               first_req = 0;

            end else begin
               first_req = 1;
            end
            `uvm_info(get_type_name(), "write data registred", UVM_HIGH)
         end


         if(enable_change_id == 1) begin
            selected_id = check_tab(status);
            inject_error = cfg.random_err();
         end
 
         `uvm_info(get_type_name(), $sformatf("selected id = %d", selected_id), UVM_HIGH)

         if(selected_id != -1) begin
            `uvm_info(get_type_name(), "send resp", UVM_HIGH)

            b_resp_item.b_id = req_requette[selected_id][0].aw_id;
            b_resp_item.b_resp  = inject_error;
            b_resp_item.b_valid = 1;
            b_resp_item.b_user  = 0;

            if(b_preresp_item.b_ready) begin

               foreach(req_requette[i,j]) begin
                  if(j < req_requette[selected_id].size()-1) begin
                     req_requette[selected_id][j] = req_requette[selected_id][j+1];
                  end
               end
               req_requette[selected_id] = new[aw_id_tr[selected_id] - 1] (req_requette[selected_id]);
               aw_id_tr[selected_id]--;
 
               foreach(status[i]) begin
                  if(i < status.size()-1) begin
                     status[i] = status[i+1];
                  end
               end
               status = new[status.size() - 1] (status);

               enable_change_id = 1;
            end else begin
               enable_change_id = 0;
            end
            
         end else begin

            `uvm_info(get_type_name(), " No resp to send ", UVM_HIGH)
            b_resp_item.b_valid = 0;
            b_resp_item.b_id    = 0;
            b_resp_item.b_resp  = 0;
            b_resp_item.b_user  = 0;

         end

      finish_item(b_resp_item);
      `uvm_info(get_type_name(), "Default sequence completed", UVM_HIGH)
   end
endtask : body

function int uvma_axi_b_seq_c::check_tab(int tab[]);
   int j = -1;
   if (status.size() != 0) begin
      j = status[0];
   end
   return j;
endfunction : check_tab

`endif
