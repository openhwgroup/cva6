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

   // Handles to virtual interface
   virtual uvma_cvxif_if  cvxif_vif;

   `uvm_component_utils_begin(uvma_cvxif_drv_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
   `uvm_component_utils_end

   string info_tag = "CVXIF_DRV";

   uvma_cvxif_resp_item_c resp_item;
   string info_tag = "CVXIF_DRV";

   extern function new(string name="uvma_cvxif_drv", uvm_component parent=null);

   extern virtual function void build_phase(uvm_phase phase);

   extern virtual task reset_phase(uvm_phase phase);

   extern virtual task run_phase(uvm_phase phase);

   extern virtual task gen_random_ready();

   extern virtual task drive_issue_resp(input uvma_cvxif_resp_item_c item);

   extern virtual task drive_result_resp(input uvma_cvxif_resp_item_c item);

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

  //Get the virtual interface handle from the configuration db
   if (! uvm_config_db#(virtual uvma_cvxif_if)::get(this, "", "cvxif_vif", cvxif_vif)) begin
     `uvm_fatal (get_type_name (), "DUT interface not found")
   end

endfunction : build_phase

task uvma_cvxif_drv_c::reset_phase(uvm_phase phase);

   // init value of slave
   cvxif_vif.cvxif_req_i.x_commit_valid         <= 0;
   cvxif_vif.cvxif_req_i.x_commit.x_commit_kill <= 0;
   cvxif_vif.cvxif_req_i.x_commit.id            <= 0;

   cvxif_vif.cvxif_req_i.x_issue_valid          <= 0;
   cvxif_vif.cvxif_req_i.x_issue_req.id         <= 0;
   cvxif_vif.cvxif_req_i.x_issue_req.rs         <= 0;
   cvxif_vif.cvxif_req_i.x_issue_req.mode       <= 0;
   cvxif_vif.cvxif_req_i.x_issue_req.rs_valid   <= 0;

   cvxif_vif.cvxif_req_i.x_compressed_valid     <= 0;
   cvxif_vif.cvxif_req_i.x_compressed_req.id    <= 0;
   cvxif_vif.cvxif_req_i.x_compressed_req.mode  <= 0;
   cvxif_vif.cvxif_req_i.x_compressed_req.instr <= 0;

endtask

task uvma_cvxif_drv_c::run_phase(uvm_phase phase);

   fork
      begin
         forever begin
            if (cfg.ready_mode == UVMA_CVXIF_ISSUE_READY_FIX) begin
               @(posedge cvxif_vif.clk);
               break;
            end
            else gen_random_ready();
         end
      end

      begin
         forever begin
            // 1. Get the response item from sequencer
            seq_item_port.get_next_item(resp_item);

            // 2. Drive the response on the vif
            fork
               begin
                  drive_issue_resp(resp_item);
               end
               begin
                  drive_result_resp(resp_item);
               end
            join_any

            // 3. Tell sequencer we're ready for the next sequence item
            seq_item_port.item_done();
            `uvm_info(info_tag, $sformatf("item_done"), UVM_LOW);
         end
      end
   join_any

endtask

task uvma_cvxif_drv_c::gen_random_ready();

      cfg.randomize(uvma_cvxif_issue_ready);
      cfg.randomize(uvma_cvxif_issue_not_ready);
      repeat(cfg.uvma_cvxif_issue_ready) @(posedge cvxif_vif.clk);
         cvxif_vif.cvxif_resp_o.x_issue_ready <= 0;
      repeat(cfg.uvma_cvxif_issue_not_ready) @(posedge cvxif_vif.clk);
         cvxif_vif.cvxif_resp_o.x_issue_ready <= 1;

endtask

task uvma_cvxif_drv_c::drive_issue_resp(input uvma_cvxif_resp_item_c item);

     //issue_resp in same cycle as issue_req
     cvxif_vif.cvxif_resp_o.x_issue_resp.accept <= item.issue_resp.accept;
     cvxif_vif.cvxif_resp_o.x_issue_resp.writeback <= item.issue_resp.writeback;
     cvxif_vif.cvxif_resp_o.x_issue_resp.dualwrite <= item.issue_resp.dualwrite;
     cvxif_vif.cvxif_resp_o.x_issue_resp.dualread <= item.issue_resp.dualread;
     cvxif_vif.cvxif_resp_o.x_issue_resp.exc <= item.issue_resp.exc;
     `uvm_info(info_tag, $sformatf("Driving issue_resp, accept = %d", item.issue_resp.accept), UVM_LOW);
     @(posedge cvxif_vif.clk);
     cvxif_vif.cvxif_resp_o.x_issue_resp.accept <= 0;
     cvxif_vif.cvxif_resp_o.x_issue_resp.writeback <= 0;
     cvxif_vif.cvxif_resp_o.x_issue_resp.dualwrite <= 0;
     cvxif_vif.cvxif_resp_o.x_issue_resp.dualread <= 0;
     cvxif_vif.cvxif_resp_o.x_issue_resp.exc <= 0;

endtask

task uvma_cvxif_drv_c::drive_result_resp(input uvma_cvxif_resp_item_c item);

     //drive resul_resp after one clk cycle
     @(posedge cvxif_vif.clk);
     cvxif_vif.cvxif_resp_o.x_result_valid <= item.result_valid;
     cvxif_vif.cvxif_resp_o.x_result.id <= item.result.id;
     cvxif_vif.cvxif_resp_o.x_result.exc <= item.result.exc;
     cvxif_vif.cvxif_resp_o.x_result.rd <= item.result.rd;
     cvxif_vif.cvxif_resp_o.x_result.data <= item.result.data;
     cvxif_vif.cvxif_resp_o.x_result.we <= item.result.we;
     cvxif_vif.cvxif_resp_o.x_result.exccode <= item.result.exccode;
     `uvm_info(info_tag, $sformatf("Driving result_resp, id = %d", item.result.id), UVM_LOW);
     do @(posedge cvxif_vif.clk);
     while (!item.result_ready);
     cvxif_vif.cvxif_resp_o.x_result_valid <= 0;
     cvxif_vif.cvxif_resp_o.x_result.id <= 0;
     cvxif_vif.cvxif_resp_o.x_result.exc <= 0;
     cvxif_vif.cvxif_resp_o.x_result.rd <= 0;
     cvxif_vif.cvxif_resp_o.x_result.data <= 0;
     cvxif_vif.cvxif_resp_o.x_result.we <= 0;
     cvxif_vif.cvxif_resp_o.x_result.exccode <= 0;

endtask


`endif // __UVMA_CVXIF_DRV_SV__
