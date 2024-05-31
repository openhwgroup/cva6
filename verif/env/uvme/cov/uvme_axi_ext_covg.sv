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
   with function sample(int t_b1_to_aw, int t_w1_to_aw);

   option.per_instance = 1;
   option.name         = name;

   outstanding_resp: coverpoint (t_b1_to_aw < 0){
      bins normal      = {0};
      bins outstanding = {1};
   }

endgroup : cg_axi_aw_order

covergroup cg_axi_ar_order(string name)
   with function sample(uvma_axi_transaction_c item[], int t_r1_to_ar, int t_r1l_to_ar, int t_r1_to_r2, int t_r1l_to_r2l);

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
      bins normal      = {0} iff(item[0].m_id == 0);
      bins outoforder  = {1} iff(item[0].m_id == 0);
   }

   outoforder_resp_id1: coverpoint (t_r1_to_r2 < 0){
      bins normal      = {0} iff(item[0].m_id == 1);
      bins outoforder  = {1} iff(item[0].m_id == 1);
   }

   outoforder_last_resp_id0: coverpoint (t_r1l_to_r2l < 0){
      bins normal      = {0} iff(item[0].m_id == 0);
      bins outoforder  = {1} iff(item[0].m_id == 0);
   }

   outoforder_last_resp_id1: coverpoint (t_r1l_to_r2l < 0){
      bins normal      = {0} iff(item[0].m_id == 1);
      bins outoforder  = {1} iff(item[0].m_id == 1);
   }

   arid1: coverpoint (item[0].m_id){
      bins id[] = {[0:1]};
   }

   arlen1: coverpoint (item[0].m_len){
      bins len[] = {[0:1]};
   }

   arid2: coverpoint (item[1].m_id){
      bins id[] = {[0:1]};
   }

   arlen2: coverpoint (item[1].m_len){
      bins len[] = {[0:1]};
   }

   ar_axi_outstanding_cross: cross outstanding_resp, outstanding_last_resp, arid1, arlen1, arid2, arlen2{
      ignore_bins IGN_CROSS1 = binsof(outstanding_resp) intersect{1} && 
                               binsof(outstanding_last_resp) intersect{1};
   }

   aw_axi_outoforder_id0_cross: cross outoforder_resp_id0, outoforder_last_resp_id0, arlen1, arlen2{
      ignore_bins IGN_CROSS1 = binsof(outoforder_resp_id0) intersect{1} &&
                               binsof(outoforder_last_resp_id0) intersect{0} &&
                               binsof(arlen2) intersect{0};
      ignore_bins IGN_CROSS2 = binsof(outoforder_resp_id0) intersect{0} && 
                               binsof(outoforder_last_resp_id0) intersect{1} &&
                               binsof(arlen1) intersect{0};
   }

   aw_axi_outoforder_id1_cross: cross outoforder_resp_id1, outoforder_last_resp_id1, arlen1, arlen2{
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

   // Time between write transfer
   int t_b1_to_aw;  // <0 (outstanding)
   int t_w1_to_aw;  // <0 (outstanding)

   // Time between read transfer
   int t_r1_to_ar;   // <0 (outstanding)
   int t_r1l_to_ar;  // <0 (outstanding)
   int t_r1_to_r2;   // <0 (r2 run before r1)
   int t_r1l_to_r2l; // <0 (last r2 run before last r1)
   
   int write_resp_status = 0;
   int read_resp_status  = 0;

   // Covergroup instances
   cg_axi_aw_order       aw_axi_order_cg;
   cg_axi_ar_order       ar_axi_order_cg;

   //
   uvma_axi_transaction_c    aw_trs_fifo[];
   uvma_axi_transaction_c    ar_trs_fifo[];

   // TLM
   uvm_tlm_analysis_fifo #(uvma_axi_transaction_c)    uvme_axi_cov_aw_req_fifo;
   uvm_tlm_analysis_fifo #(uvma_axi_transaction_c)    uvme_axi_cov_b_resp_fifo;
   uvm_tlm_analysis_fifo #(uvma_axi_transaction_c)    uvme_axi_cov_ar_req_fifo;
   uvm_tlm_analysis_fifo #(uvma_axi_transaction_c)    uvme_axi_cov_r_resp_fifo;

   `uvm_component_utils_begin(uvme_axi_ext_covg_c)
   `uvm_component_utils_end

   /**
    * Default constructor.
    */
   extern function new(string name="uvme_axi_ext_covg", uvm_component parent=null);

   /**
    * Builds fifos.
    */
   extern virtual function void build_phase(uvm_phase phase);

   /**
    * Forks all sampling loops
    */
   extern virtual task run_phase(uvm_phase phase);

   /**
    * get transaction from monitor
    */
    extern virtual task get_ar_item();

   /**
    * get transaction from monitor
    */
    extern virtual task get_r_item();

   /**
    * get transaction from monitor
    */
    extern virtual task get_aw_item();

   /**
    * get transaction from monitor
    */
    extern virtual task get_b_item();

   /**
    * Forks all sampling loops
    */
    extern virtual function void aw_time_operations();

   /**
    * Forks all sampling loops
    */
    extern virtual function void ar_time_operations();

endclass : uvme_axi_ext_covg_c


function uvme_axi_ext_covg_c::new(string name="uvme_axi_ext_covg", uvm_component parent=null);

   super.new(name, parent);

endfunction : new

function void uvme_axi_ext_covg_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   aw_axi_order_cg  = new("aw_axi_order_cg");
   ar_axi_order_cg  = new("ar_axi_order_cg");

   uvme_axi_cov_b_resp_fifo  = new("uvme_axi_cov_b_resp_fifo"   , this);
   uvme_axi_cov_r_resp_fifo  = new("uvme_axi_cov_r_resp_fifo"   , this);
   uvme_axi_cov_ar_req_fifo  = new("uvme_axi_cov_ar_req_fifo"   , this);
   uvme_axi_cov_aw_req_fifo  = new("uvme_axi_cov_aw_req_fifo"   , this);

endfunction : build_phase

task uvme_axi_ext_covg_c::run_phase(uvm_phase phase);

   super.run_phase(phase);
   forever begin

     fork
        get_aw_item();
        get_b_item();
        get_ar_item();
        get_r_item();
     join_any
     
     if(aw_trs_fifo.size() == 2 && write_resp_status == 2) begin
        aw_time_operations();
        aw_axi_order_cg.sample(t_b1_to_aw, t_w1_to_aw);
        aw_trs_fifo = new [aw_trs_fifo.size()-1] (aw_trs_fifo);
        write_resp_status--;
     end

     if(ar_trs_fifo.size() == 2 && read_resp_status == 2) begin
        ar_time_operations();
        ar_axi_order_cg.sample(ar_trs_fifo, t_r1_to_ar, t_r1l_to_ar, t_r1_to_r2, t_r1l_to_r2l);
        ar_trs_fifo = new [ar_trs_fifo.size()-1] (ar_trs_fifo);
        read_resp_status--;
     end
     
     disable fork;
   end

endtask : run_phase


task uvme_axi_ext_covg_c::get_aw_item();

   uvma_axi_transaction_c  aw_item;
   uvme_axi_cov_aw_req_fifo.get(aw_item);
   `uvm_info(get_type_name(), $sformatf("WRITE REQ ITEM DETECTED"), UVM_LOW)
   aw_trs_fifo = new [aw_trs_fifo.size()+1] (aw_trs_fifo);
   aw_trs_fifo[aw_trs_fifo.size()-1] = new aw_item;

endtask : get_aw_item


task uvme_axi_ext_covg_c::get_ar_item();

   uvma_axi_transaction_c  ar_item;
   uvme_axi_cov_ar_req_fifo.get(ar_item);
   `uvm_info(get_type_name(), $sformatf("READ REQ ITEM DETECTED"), UVM_LOW)
   ar_trs_fifo = new [ar_trs_fifo.size()+1] (ar_trs_fifo);
   ar_trs_fifo[ar_trs_fifo.size()-1] = new ar_item;

endtask : get_ar_item


task uvme_axi_ext_covg_c::get_b_item();

   uvma_axi_transaction_c  b_item;
   uvme_axi_cov_b_resp_fifo.get(b_item);
   `uvm_info(get_type_name(), $sformatf("WRITE RESP ITEM DETECTED"), UVM_LOW)
   foreach(aw_trs_fifo[i]) begin
      if (aw_trs_fifo[i].m_id == b_item.m_id) begin
         aw_trs_fifo[i].m_resp = b_item.m_resp;
         aw_trs_fifo[i].m_timestamp_b = b_item.m_timestamp_b;
         aw_trs_fifo = new [aw_trs_fifo.size()+1] (aw_trs_fifo);
         aw_trs_fifo[aw_trs_fifo.size()-1] = new aw_trs_fifo[i];
         write_resp_status++;
         break;
      end
   end

endtask : get_b_item


task uvme_axi_ext_covg_c::get_r_item();

   uvma_axi_transaction_c  r_item;
   uvme_axi_cov_r_resp_fifo.get(r_item);
   `uvm_info(get_type_name(), $sformatf("READ RESP ITEM DETECTED"), UVM_LOW)
   foreach(ar_trs_fifo[i]) begin
      if (ar_trs_fifo[i].m_id == r_item.m_id) begin
         ar_trs_fifo[i].m_resp.push_back(r_item.m_resp[0]);
         ar_trs_fifo[i].m_data.push_back(r_item.m_data[0]);
         ar_trs_fifo[i].m_timestamp_x.push_back(r_item.m_timestamp_x[0]);
         ar_trs_fifo = new [ar_trs_fifo.size()+1] (ar_trs_fifo);
         ar_trs_fifo[ar_trs_fifo.size()-1] = new ar_trs_fifo[i];
         read_resp_status++;
         break;
      end
   end

endtask : get_r_item


function void uvme_axi_ext_covg_c::ar_time_operations();

   t_r1_to_ar   = ar_trs_fifo[1].m_timestamp_ax - ar_trs_fifo[0].m_timestamp_x[0];
   t_r1l_to_ar  = ar_trs_fifo[1].m_timestamp_ax - ar_trs_fifo[0].m_timestamp_x[ar_trs_fifo[0].m_timestamp_x.size()-1];
   t_r1_to_r2   = ar_trs_fifo[1].m_timestamp_x[0] - ar_trs_fifo[0].m_timestamp_x[0];
   t_r1l_to_r2l = ar_trs_fifo[1].m_timestamp_x[ar_trs_fifo[1].m_timestamp_x.size()-1] - ar_trs_fifo[0].m_timestamp_x[ar_trs_fifo[0].m_timestamp_x.size()-1];

endfunction : ar_time_operations


function void uvme_axi_ext_covg_c::aw_time_operations();

   t_b1_to_aw = aw_trs_fifo[1].m_timestamp_ax - aw_trs_fifo[0].m_timestamp_b;
   t_w1_to_aw = aw_trs_fifo[1].m_timestamp_ax - aw_trs_fifo[0].m_timestamp_x[0];

endfunction : aw_time_operations

`endif // __UVME_AXI_EXT_COVG_SV__
