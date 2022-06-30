// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Zineb EL KACIMI (zineb.el-kacimi@external.thalesgroup.com)


`ifndef __UVMA_CVXIF_DRV_SV__
`define __UVMA_CVXIF_DRV_SV__


class uvma_cvxif_drv_c extends uvm_driver #(uvma_cvxif_resp_item_c);

   uvma_cvxif_resp_item_c resp_item;

   // Objects
   uvma_cvxif_cfg_c    cfg;
   uvma_cvxif_cntxt_c  cntxt;

   `uvm_component_utils_begin(uvma_cvxif_drv_c)
      `uvm_field_object(cfg   , UVM_DEFAULT)
      `uvm_field_object(cntxt , UVM_DEFAULT)
   `uvm_component_utils_end

   string info_tag = "CVXIF_DRV";

   drv_result resp_queue [$];
   drv_result res_resp;
   drv_result aux_item;
   logic go=1;
   logic res_ready;

   extern function new(string name="uvma_cvxif_drv", uvm_component parent=null);

   extern virtual function void build_phase(uvm_phase phase);

   extern virtual task reset_phase(uvm_phase phase);

   extern virtual task run_phase(uvm_phase phase);

   //generate randomly the issue_ready signal
   extern virtual task gen_slv_random_ready();

   //get response item and call task to drive the issue reponse to the vif
   extern virtual task slv_get_item_proc();

   //fill res_resp typdef with responses received from seq
   extern virtual task fill_slv_res_resp(input uvma_cvxif_resp_item_c res_item);

   //drive issue response
   extern virtual task drv_slv_issue_resp(input uvma_cvxif_resp_item_c item);

   //de-assert issue_response
   extern virtual task deassert_slv_issue();

   //drive results in order fashion
   extern virtual task drv_slv_result_in_order_proc();

   //drive results in out of order fashion
   extern virtual task drv_slv_result_out_of_order_proc();

   //drive result response
   extern virtual task drv_slv_result_resp(input drv_result item);

   //de-assert result signals
   extern virtual task deassert_slv_result();

endclass : uvma_cvxif_drv_c

function uvma_cvxif_drv_c::new(string name="uvma_cvxif_drv", uvm_component parent=null);

   super.new(name, parent);

endfunction : new

function void uvma_cvxif_drv_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvma_cvxif_cfg_c)::get(this, "", "cfg", cfg));
   if (cfg == null) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   uvm_config_db#(uvma_cvxif_cfg_c)::set(this, "*", "cfg", cfg);

   void'(uvm_config_db#(uvma_cvxif_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (cntxt == null) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end
   uvm_config_db#(uvma_cvxif_cntxt_c)::set(this, "*", "cntxt", cntxt);

endfunction : build_phase

task uvma_cvxif_drv_c::reset_phase(uvm_phase phase);

   // init value of slave
   cntxt.vif.cvxif_req_i.x_commit_valid         <= 0;
   cntxt.vif.cvxif_req_i.x_commit.x_commit_kill <= 0;
   cntxt.vif.cvxif_req_i.x_commit.id            <= 0;

   cntxt.vif.cvxif_req_i.x_issue_valid          <= 0;
   cntxt.vif.cvxif_req_i.x_issue_req.id         <= 0;
   cntxt.vif.cvxif_req_i.x_issue_req.rs         <= 0;
   cntxt.vif.cvxif_req_i.x_issue_req.mode       <= 0;
   cntxt.vif.cvxif_req_i.x_issue_req.rs_valid   <= 0;

   cntxt.vif.cvxif_req_i.x_compressed_valid     <= 0;
   cntxt.vif.cvxif_req_i.x_compressed_req.id    <= 0;
   cntxt.vif.cvxif_req_i.x_compressed_req.mode  <= 0;
   cntxt.vif.cvxif_req_i.x_compressed_req.instr <= 0;

endtask

task uvma_cvxif_drv_c::run_phase(uvm_phase phase);

   fork
      begin
         forever begin
            if (cfg.ready_mode == UVMA_CVXIF_ISSUE_READY_FIX) begin
               @(posedge cntxt.vif.clk);
               break;
            end
            else begin
               gen_slv_random_ready();
            end
         end
      end

      begin
         forever begin
            fork
               begin
                  slv_get_item_proc();
               end
               begin
                  if (cfg.in_order) begin
                     drv_slv_result_in_order_proc();
                  end
                  else begin
                     drv_slv_result_out_of_order_proc();
                  end
               end
            join_any
         end
      end
   join_any

endtask

task uvma_cvxif_drv_c::gen_slv_random_ready();

   cfg.randomize(uvma_cvxif_issue_ready);
   cfg.randomize(uvma_cvxif_issue_not_ready);
   repeat(cfg.uvma_cvxif_issue_ready) @(posedge cntxt.vif.clk);
      cntxt.vif.cvxif_resp_o.x_issue_ready <= 0;
   repeat(cfg.uvma_cvxif_issue_not_ready) @(posedge cntxt.vif.clk);
      cntxt.vif.cvxif_resp_o.x_issue_ready <= 1;

endtask

task uvma_cvxif_drv_c::slv_get_item_proc();

   // 1. Get the response item from sequencer
   seq_item_port.get_next_item(resp_item);
   fill_slv_res_resp(resp_item);
   aux_item = res_resp;

   // 2. save the result resp in a queue
   resp_queue.push_back(aux_item);

   // 3. Drive the response on the vif
   drv_slv_issue_resp(resp_item);
   @(posedge cntxt.vif.clk);
   deassert_slv_issue();

   // 4. Tell sequencer we're ready for the next sequence item
   seq_item_port.item_done();
   `uvm_info(info_tag, $sformatf("item_done"), UVM_HIGH);

endtask


task uvma_cvxif_drv_c::drv_slv_issue_resp(input uvma_cvxif_resp_item_c item);

   //issue_resp in same cycle as issue_req
   cntxt.vif.cvxif_resp_o.x_issue_resp.accept    <= item.issue_resp.accept;
   cntxt.vif.cvxif_resp_o.x_issue_resp.writeback <= item.issue_resp.writeback;
   cntxt.vif.cvxif_resp_o.x_issue_resp.dualwrite <= item.issue_resp.dualwrite;
   cntxt.vif.cvxif_resp_o.x_issue_resp.dualread  <= item.issue_resp.dualread;
   cntxt.vif.cvxif_resp_o.x_issue_resp.exc       <= item.issue_resp.exc;
   `uvm_info(info_tag, $sformatf("Driving issue_resp, accept = %d", item.issue_resp.accept), UVM_LOW);

endtask

task uvma_cvxif_drv_c::deassert_slv_issue();

   cntxt.vif.cvxif_resp_o.x_issue_resp.accept    <= 0;
   cntxt.vif.cvxif_resp_o.x_issue_resp.writeback <= 0;
   cntxt.vif.cvxif_resp_o.x_issue_resp.dualwrite <= 0;
   cntxt.vif.cvxif_resp_o.x_issue_resp.dualread  <= 0;
   cntxt.vif.cvxif_resp_o.x_issue_resp.exc       <= 0;

endtask

task uvma_cvxif_drv_c::drv_slv_result_in_order_proc();

   while (!go) begin
      @(posedge cntxt.vif.clk);
   end
   forever begin
      if (resp_queue.size()==0) begin
         @(posedge cntxt.vif.clk);
         go=1;
         break;
      end
      else begin
         go=0;
         repeat(resp_queue[0].rnd_delay) @(posedge cntxt.vif.clk);
         drv_slv_result_resp(resp_queue[0]);
         resp_queue.pop_front();
         do @(posedge cntxt.vif.clk);
         while (!resp_queue[0].result_ready);
         deassert_slv_result();
         go=1;
         break;
      end
   end

endtask

task uvma_cvxif_drv_c::drv_slv_result_out_of_order_proc();

   while (!go) begin
     @(posedge cntxt.vif.clk);
   end
   forever begin

     if (resp_queue.size()==0) begin
       @(posedge cntxt.vif.clk);
       go=1;
       break;
     end
     else begin
       fork
         //ctrl_process()
         begin
           for (int i=0; i<resp_queue.size(); i++) begin
              if ( resp_queue[i].rnd_delay==0 ) begin
                 go=0;
                 drv_slv_result_resp(resp_queue[i]);
                 res_ready = resp_queue[i].result_ready;
                 resp_queue.delete(i);
                 do @(posedge cntxt.vif.clk);
                 while (!res_ready);
                 break;
              end
           end
         end

         //decr_process()
         begin
           @(posedge cntxt.vif.clk);
           for (int i=0; i<resp_queue.size(); i++) begin
             if (resp_queue[i].rnd_delay!=0) begin
                resp_queue[i].rnd_delay = (resp_queue[i].rnd_delay)-1;
                aux_item = resp_queue[i];
                resp_queue.delete(i);
                resp_queue.push_back(aux_item);
             end
           end
         end

       join
     end
     deassert_slv_result;
     go=1;
     break;

   end

endtask

task uvma_cvxif_drv_c::drv_slv_result_resp(input drv_result item);

   cntxt.vif.cvxif_resp_o.x_result_valid   <= item.result_valid;
   cntxt.vif.cvxif_resp_o.x_result.id      <= item.id;
   cntxt.vif.cvxif_resp_o.x_result.exc     <= item.exc;
   cntxt.vif.cvxif_resp_o.x_result.rd      <= item.rd;
   cntxt.vif.cvxif_resp_o.x_result.data    <= item.data;
   cntxt.vif.cvxif_resp_o.x_result.we      <= item.we;
   cntxt.vif.cvxif_resp_o.x_result.exccode <= item.exccode;
   `uvm_info(info_tag, $sformatf("Driving result_resp, id = %d", item.id), UVM_LOW);

endtask

task uvma_cvxif_drv_c::deassert_slv_result();

   cntxt.vif.cvxif_resp_o.x_result_valid   <= 0;
   cntxt.vif.cvxif_resp_o.x_result.id      <= 0;
   cntxt.vif.cvxif_resp_o.x_result.exc     <= 0;
   cntxt.vif.cvxif_resp_o.x_result.rd      <= 0;
   cntxt.vif.cvxif_resp_o.x_result.data    <= 0;
   cntxt.vif.cvxif_resp_o.x_result.we      <= 0;
   cntxt.vif.cvxif_resp_o.x_result.exccode <= 0;

endtask

task uvma_cvxif_drv_c::fill_slv_res_resp(input uvma_cvxif_resp_item_c res_item);

   res_resp.result_valid = res_item.result_valid;
   res_resp.id           = res_item.result.id;
   res_resp.data         = res_item.result.data;
   res_resp.rd           = res_item.result.rd;
   res_resp.we           = res_item.result.we;
   res_resp.exc          = res_item.result.exc;
   res_resp.exccode      = res_item.result.exccode;
   res_resp.result_ready = res_item.result_ready;
   res_resp.rnd_delay    = res_item.rnd_delay;

endtask


`endif // __UVMA_CVXIF_DRV_SV__
