// Copyright 2023 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com) – sub-contractor MU-Electronics for Thales group


`ifndef __UVME_AXI_EXT_COVG_SV__
`define __UVME_AXI_EXT_COVG_SV__

   /*
   * Covergroups
   * Decalred at package-level to enable mutliple instances per monitor class (e.g. read/write)
   */

covergroup cg_axi_aw_order(string name)
   with function sample(uvma_axi_transaction_c item[], int t_b1_to_aw, int t_w1_to_aw, bit RVA);

   option.per_instance = 1;
   option.name         = name;

   outstanding_resp: coverpoint (t_b1_to_aw < 0){
      bins normal      = {0};
      bins outstanding = {1};
   }

   awlock1: coverpoint (item[0].aw_lock){
      bins lock[]    = {[0:1]};
      ignore_bins IGN_EXCLUSIVE = {1} iff(!RVA);
   }

   awlock2: coverpoint (item[1].aw_lock){
      bins lock[]    = {[0:1]};
      ignore_bins IGN_EXCLUSIVE = {1} iff(!RVA);
   }

   aw_axi_cross: cross outstanding_resp, awlock1, awlock2;
endgroup : cg_axi_aw_order

covergroup cg_axi_ar_order(string name)
   with function sample(uvma_axi_transaction_c item[], int t_r1_to_ar, int t_r1l_to_ar, int t_r1_to_r2, int t_r1l_to_r2l, bit RVA);

   option.per_instance = 1;
   option.name         = name;

   outstanding_resp: coverpoint (t_r1_to_ar < 0){
      bins normal      = {0};
      bins outstanding = {1};
   }

   outstanding_last_resp: coverpoint (t_r1l_to_ar < 0 && t_r1_to_ar > 0){
      bins normal      = {0};
      bins outstanding = {1};
   }

   outoforder_resp_id0: coverpoint (t_r1_to_r2 < 0){
      bins normal      = {0} iff(item[0].ar_id == 0);
      bins outoforder  = {1} iff(item[0].ar_id == 0);
   }

   outoforder_resp_id1: coverpoint (t_r1_to_r2 < 0){
      bins normal      = {0} iff(item[0].ar_id == 1);
      bins outoforder  = {1} iff(item[0].ar_id == 1);
   }

   outoforder_last_resp_id0: coverpoint (t_r1l_to_r2l < 0){
      bins normal      = {0} iff(item[0].ar_id == 0);
      bins outoforder  = {1} iff(item[0].ar_id == 0);
   }

   outoforder_last_resp_id1: coverpoint (t_r1l_to_r2l < 0){
      bins normal      = {0} iff(item[0].ar_id == 1);
      bins outoforder  = {1} iff(item[0].ar_id == 1);
   }

   arid1: coverpoint (item[0].ar_id){
      bins id[] = {[0:1]};
   }

   arlen1: coverpoint (item[0].ar_len){
      bins len[] = {[0:1]};
   }

   arlock1: coverpoint (item[0].ar_lock){
      bins lock[]    = {[0:1]};
      ignore_bins IGN_EXCLUSIVE = {1} iff(!RVA);
   }

   arid2: coverpoint (item[1].ar_id){
      bins id[] = {[0:1]};
   }

   arlen2: coverpoint (item[1].ar_len){
      bins len[] = {[0:1]};
   }

   arlock2: coverpoint (item[1].ar_lock){
      bins lock[]    = {[0:1]};
      ignore_bins IGN_EXCLUSIVE = {1} iff(!RVA);
   }

   ar_axi_outstanding_cross: cross outstanding_resp, outstanding_last_resp, arid1, arlen1, arlock1, arid2, arlen2, arlock2{
      ignore_bins IGN_CROSS1 = binsof(outstanding_resp) intersect{1} && 
                               binsof(outstanding_last_resp) intersect{1};
   }

   aw_axi_outoforder_id0_cross: cross outoforder_resp_id0, outoforder_last_resp_id0, arlen1, arlock1, arlen2, arlock2{
      ignore_bins IGN_CROSS1 = binsof(outoforder_resp_id0) intersect{1} &&
                               binsof(outoforder_last_resp_id0) intersect{0} &&
                               binsof(arlen2) intersect{0};
      ignore_bins IGN_CROSS2 = binsof(outoforder_resp_id0) intersect{0} && 
                               binsof(outoforder_last_resp_id0) intersect{1} &&
                               binsof(arlen1) intersect{0};
   }

   aw_axi_outoforder_id1_cross: cross outoforder_resp_id1, outoforder_last_resp_id1, arlen1, arlock1, arlen2, arlock2{
      ignore_bins IGN_CROSS1 = binsof(outoforder_resp_id1) intersect{1} && 
                               binsof(outoforder_last_resp_id1) intersect{0} &&
                               binsof(arlen2) intersect{0};
      ignore_bins IGN_CROSS2 = binsof(outoforder_resp_id1) intersect{0} && 
                               binsof(outoforder_last_resp_id1) intersect{1} &&
                               binsof(arlen1) intersect{0};
   }
endgroup : cg_axi_ar_order

/**
 * Component encapsulating Open Bus Interface functional coverage model.
 */
class uvme_axi_ext_covg_c extends uvm_component;

   // Objects
   uvme_cva6_cntxt_c         cntxt;
   uvme_cva6_cfg_c           cfg;
   bit RVA;

   // Time between write transfer
   int t_b1_to_aw;  // <0 (outstanding)
   int t_w1_to_aw;  // <0 (outstanding)

   // Time between read transfer
   int t_r1_to_ar;   // <0 (outstanding)
   int t_r1l_to_ar;  // <0 (outstanding)
   int t_r1_to_r2;   // <0 (r2 run before r1)
   int t_r1l_to_r2l; // <0 (last r2 run before last r1)

   // Covergroup instances
   cg_axi_aw_order       aw_axi_order_cg;
   cg_axi_ar_order       ar_axi_order_cg;

   //
   uvma_axi_transaction_c    aw_trs_fifo[];
   uvma_axi_transaction_c    ar_trs_fifo[];

   int order_resp;

   // TLM
   uvm_tlm_analysis_fifo #(uvma_axi_transaction_c)    uvme_axi_cov_fifo;

   `uvm_component_utils_begin(uvme_axi_ext_covg_c)
   `uvm_component_utils_end

   /**
    * Default constructor.
    */
   extern function new(string name="uvme_axi_ext_covg", uvm_component parent=null);

   /**
    * 1. Ensures cfg & cntxt handles are not null.
    * 2. Builds fifos.
    */
   extern virtual function void build_phase(uvm_phase phase);

   /**
    * Forks all sampling loops
    */
   extern virtual task run_phase(uvm_phase phase);

   /**
    * Forks all sampling loops
    */
    extern virtual function int aw_time_operations();

   /**
    * Forks all sampling loops
    */
    extern virtual function int ar_time_operations();

endclass : uvme_axi_ext_covg_c


function uvme_axi_ext_covg_c::new(string name="uvme_axi_ext_covg", uvm_component parent=null);

   super.new(name, parent);

endfunction : new

function void uvme_axi_ext_covg_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvme_cva6_cfg_c)::get(this, "", "cfg", cfg));
   if (cfg == null) begin
      `uvm_fatal("cfg", "Context handle is null")
   end

   void'(uvm_config_db#(uvme_cva6_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (cntxt == null) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end

   RVA = cfg.ext_a_supported;

   aw_axi_order_cg  = new("aw_axi_order_cg");
   ar_axi_order_cg  = new("ar_axi_order_cg");

   uvme_axi_cov_fifo = new("uvme_axi_cov_fifo"   , this);

endfunction : build_phase

task uvme_axi_ext_covg_c::run_phase(uvm_phase phase);

   super.run_phase(phase);
   forever begin
      uvma_axi_transaction_c  resp_item;

      uvme_axi_cov_fifo.get(resp_item);
      case (resp_item.access_type)

         UVMA_AXI_ACCESS_WRITE : begin

             aw_trs_fifo = new [aw_trs_fifo.size()+1] (aw_trs_fifo);
             aw_trs_fifo[aw_trs_fifo.size()-1] = new resp_item;
             if(aw_trs_fifo.size() == 2) begin
                order_resp = aw_time_operations();
                aw_axi_order_cg.sample(aw_trs_fifo, t_b1_to_aw, t_w1_to_aw, RVA);
                if(order_resp == 1) aw_trs_fifo[0] = new aw_trs_fifo[1];
                aw_trs_fifo = new [aw_trs_fifo.size()-1] (aw_trs_fifo);
             end

         end
         UVMA_AXI_ACCESS_READ : begin

             ar_trs_fifo = new [ar_trs_fifo.size()+1] (ar_trs_fifo);
             ar_trs_fifo[ar_trs_fifo.size()-1] = new resp_item;

             if(ar_trs_fifo.size() == 2) begin

                order_resp = ar_time_operations();
                ar_axi_order_cg.sample(ar_trs_fifo, t_r1_to_ar, t_r1l_to_ar, t_r1_to_r2, t_r1l_to_r2l, RVA);
                if(order_resp == 1) ar_trs_fifo[0] = new ar_trs_fifo[1];
                ar_trs_fifo = new [ar_trs_fifo.size()-1] (ar_trs_fifo);

             end

         end
      endcase
   end

endtask : run_phase

function int uvme_axi_ext_covg_c::ar_time_operations();
   int order_resp = 1;
   uvma_axi_transaction_c axi_transaction;

   if(ar_trs_fifo[0].ar_start_time > ar_trs_fifo[1].ar_start_time) begin

      axi_transaction = new ar_trs_fifo[0];
      ar_trs_fifo[0]  = new ar_trs_fifo[1];
      ar_trs_fifo[1]  = new axi_transaction;
      order_resp = 0;

   end

   t_r1_to_ar   = ar_trs_fifo[1].ar_start_time - ar_trs_fifo[0].r_data_trs[0].r_start_time;
   t_r1l_to_ar  = ar_trs_fifo[1].ar_start_time - ar_trs_fifo[0].r_data_trs[ar_trs_fifo[0].r_data_trs.size()-1].r_start_time;
   t_r1_to_r2   = ar_trs_fifo[1].r_data_trs[0].r_start_time - ar_trs_fifo[0].r_data_trs[0].r_start_time;
   t_r1l_to_r2l = ar_trs_fifo[1].r_data_trs[ar_trs_fifo[1].r_data_trs.size()-1].r_start_time - ar_trs_fifo[0].r_data_trs[ar_trs_fifo[0].r_data_trs.size()-1].r_start_time;

   return order_resp;

endfunction : ar_time_operations

function int uvme_axi_ext_covg_c::aw_time_operations();
   int order_resp = 1;
   uvma_axi_transaction_c axi_transaction;

   if(aw_trs_fifo[0].aw_start_time > aw_trs_fifo[1].aw_start_time) begin

      axi_transaction = new aw_trs_fifo[0];
      aw_trs_fifo[0]  = new aw_trs_fifo[1];
      aw_trs_fifo[1]  = new axi_transaction;
      order_resp = 0;

   end

   t_b1_to_aw = aw_trs_fifo[1].aw_start_time - aw_trs_fifo[0].b_start_time;
   t_w1_to_aw = aw_trs_fifo[1].aw_start_time - aw_trs_fifo[0].w_data_trs[0].w_start_time;

   return order_resp;

endfunction : aw_time_operations

`endif // __UVME_AXI_EXT_COVG_SV__
