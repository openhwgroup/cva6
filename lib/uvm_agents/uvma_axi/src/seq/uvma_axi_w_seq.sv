// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)
// Co-Author: Abdelaali Khardazi

//=============================================================================
// Description: Sequence for agent axi_w
//=============================================================================

`ifndef UVMA_AXI_W_SEQ_SV
`define UVMA_AXI_W_SEQ_SV

class uvma_axi_w_seq_c extends uvm_sequence#(uvma_axi_w_item_c);

   `uvm_object_utils(uvma_axi_w_seq_c)
   `uvm_declare_p_sequencer(uvma_axi_w_sqr_c)

   // Agent handles
   uvma_axi_cfg_c    cfg;
   uvma_axi_cntxt_c  cntxt;

   uvma_axi_aw_item_c  aw_req_item;
   uvma_axi_aw_item_c  req_requette[];
   uvma_axi_w_item_c   write_data_req[];
   uvma_axi_w_item_c   w_req_item;

   int latency;
   int w_ready_latency;
   int status = 0;
   bit write_status = 0;
   int check_ready = 0;
   int aw_latency[];

   extern function new(string name = "");
   extern function void add_latencies(uvma_axi_w_item_c master_req);
   extern task body();

endclass : uvma_axi_w_seq_c


function uvma_axi_w_seq_c::new(string name = "");
   super.new(name);
endfunction : new

function void uvma_axi_w_seq_c::add_latencies(uvma_axi_w_item_c master_req);

   master_req.w_latency = cfg.calc_random_latency();

endfunction : add_latencies

task uvma_axi_w_seq_c::body();

   aw_req_item = uvma_axi_aw_item_c::type_id::create("aw_req_item");
   w_req_item  = uvma_axi_w_item_c::type_id::create("w_req_item");

   forever begin

      cfg   = p_sequencer.cfg;
      cntxt = p_sequencer.cntxt;

      `uvm_info(get_type_name(), "WRITE DATA sequence starting", UVM_HIGH)

      p_sequencer.aw_req_export.get(aw_req_item);
      p_sequencer.w_req_fifo.get(w_req_item);

      if(aw_req_item.aw_valid || check_ready == 1) begin

         if(aw_req_item.aw_valid) begin
            req_requette = new[req_requette.size() + 1] (req_requette);
            req_requette[req_requette.size() - 1] = new aw_req_item;
         end

         if(!check_ready) begin
            aw_latency = new[aw_latency.size() + 1] (aw_latency);
            aw_latency[aw_latency.size() - 1] = -2;
         end

         aw_latency[aw_latency.size() - 1]++;
         check_ready = 1;

         if(aw_req_item.aw_ready && aw_latency[aw_latency.size() - 1] != -1) begin
            check_ready = 0;
            status = 1;
            if(aw_req_item.aw_valid) begin
               check_ready = 1;
               aw_latency = new[aw_latency.size() + 1] (aw_latency);
               aw_latency[aw_latency.size() - 1] = -1;
            end
         end
      end

      start_item(w_req_item);
         if(w_req_item.w_valid) begin

            if(latency == 0) begin
               add_latencies(w_req_item);
               w_ready_latency = w_req_item.w_latency;
            end

            w_req_item.w_ready = 0;

            if(latency == w_ready_latency) begin
               w_req_item.w_ready = 1;
               latency = 0;
            end else begin
               latency++;
            end

            if(w_req_item.w_ready) begin
               write_data_req = new[write_data_req.size() + 1] (write_data_req);
               write_data_req[write_data_req.size() - 1] = new w_req_item;
               write_status = 1;
            end

         end else begin
            w_req_item.w_ready = 0;
         end

         `uvm_info(get_type_name(), $sformatf("status = %d et  write_status = %d", status, write_status), UVM_HIGH)
         if(status == 1 && write_status == 1) begin

            longint aligned_addr;
            `uvm_info(get_type_name(), $sformatf("AXI_ADDR_WIDTH = %d et  AXI_ADDR_WIDTH_BYTE = %d", AXI_ADDR_WIDTH, AXI_ADDR_WIDTH/8), UVM_HIGH)
            aligned_addr = req_requette[0].aw_addr - req_requette[0].aw_addr % (AXI_ADDR_WIDTH/8);
            if(write_data_req[0].w_strb[0]) cntxt.mem.write(aligned_addr+0, write_data_req[0].w_data[07:00]);
            if(write_data_req[0].w_strb[1]) cntxt.mem.write(aligned_addr+1, write_data_req[0].w_data[15:08]);
            if(write_data_req[0].w_strb[2]) cntxt.mem.write(aligned_addr+2, write_data_req[0].w_data[23:16]);
            if(write_data_req[0].w_strb[3]) cntxt.mem.write(aligned_addr+3, write_data_req[0].w_data[31:24]);
            if(write_data_req[0].w_strb[4]) cntxt.mem.write(aligned_addr+4, write_data_req[0].w_data[39:32]);
            if(write_data_req[0].w_strb[5]) cntxt.mem.write(aligned_addr+5, write_data_req[0].w_data[47:40]);
            if(write_data_req[0].w_strb[6]) cntxt.mem.write(aligned_addr+6, write_data_req[0].w_data[55:48]);
            if(write_data_req[0].w_strb[7]) cntxt.mem.write(aligned_addr+7, write_data_req[0].w_data[63:56]);

            if(write_data_req[0].w_last) begin
		       foreach(req_requette[i]) begin
                  if(i < req_requette.size() - aw_latency[0] - 1) begin
                     req_requette[i] = req_requette[(i  + aw_latency[0]) +1];
                  end
               end
               req_requette = new[req_requette.size() - (1 + aw_latency[0])] (req_requette);

               foreach(aw_latency[i]) begin
                  if(i < aw_latency.size() - 1) begin
                     aw_latency[i] = aw_latency[i + 1];
                  end
               end
               aw_latency = new[aw_latency.size() - 1] (aw_latency);

               status =0;
            end

            foreach(write_data_req[i]) begin
               if(i < write_data_req.size() - 1) begin
                  write_data_req[i] = write_data_req[i+1];
               end
            end
            write_data_req = new[write_data_req.size() - 1] (write_data_req);
            if(write_data_req.size() == 0) begin
               write_status =0;
            end

         end
      finish_item(w_req_item);
   end
   `uvm_info(get_type_name(), "Write data sequence completed", UVM_HIGH)

endtask : body

`endif

